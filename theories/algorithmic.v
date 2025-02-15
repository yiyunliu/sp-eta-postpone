Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax
  common typing preservation admissible fp_red structural soundness.
From Hammer Require Import Tactics.
Require Import ssreflect ssrbool.
Require Import Psatz.
From stdpp Require Import relations (rtc(..), nsteps(..)).
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Cdcl.Itauto.

Module HRed.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a b :
    R (PApp (PAbs a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

  (*************** Congruence ********************)
  | AppCong a0 a1 b :
    R a0 a1 ->
    R (PApp a0 b) (PApp a1 b)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1).

  Lemma ToRRed n (a b : PTm n) : HRed.R a b -> RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:RRed.R. Qed.

  Lemma preservation n Γ (a b A : PTm n) : Γ ⊢ a ∈ A -> HRed.R a b -> Γ ⊢ b ∈ A.
  Proof.
    sfirstorder use:subject_reduction, ToRRed.
  Qed.

  Lemma ToEq n Γ (a b : PTm n) A : Γ ⊢ a ∈ A -> HRed.R a b -> Γ ⊢ a ≡ b ∈ A.
  Proof. sfirstorder use:ToRRed, RRed_Eq. Qed.

End HRed.

Module HReds.
  Lemma preservation n Γ (a b A : PTm n) : Γ ⊢ a ∈ A -> rtc HRed.R a b -> Γ ⊢ b ∈ A.
  Proof. induction 2; sfirstorder use:HRed.preservation. Qed.

  Lemma ToEq n Γ (a b : PTm n) A : Γ ⊢ a ∈ A -> rtc HRed.R a b -> Γ ⊢ a ≡ b ∈ A.
  Proof.
    induction 2; sauto lq:on use:HRed.ToEq, E_Transitive, HRed.preservation.
  Qed.
End HReds.

Lemma T_Conv_E n Γ (a : PTm n) A B i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ A ≡ B ∈ PUniv i \/ Γ ⊢ B ≡ A ∈ PUniv i ->
  Γ ⊢ a ∈ B.
Proof. qauto use:T_Conv, Su_Eq, E_Symmetric. Qed.

Lemma E_Conv_E n Γ (a b : PTm n) A B i :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ A ≡ B ∈ PUniv i \/ Γ ⊢ B ≡ A ∈ PUniv i ->
  Γ ⊢ a ≡ b ∈ B.
Proof. qauto use:E_Conv, Su_Eq, E_Symmetric. Qed.

Lemma Sub_Bind_InvR n Γ p (A : PTm n) B C :
  Γ ⊢ PBind p A B ≲ C ->
  exists i A0 B0, Γ ⊢ C ≡ PBind p A0 B0 ∈ PUniv i.
Proof.
Admitted.

Lemma Sub_Bind_InvL n Γ p (A : PTm n) B C :
  Γ ⊢ C ≲ PBind p A B ->
  exists i A0 B0, Γ ⊢ PBind p A0 B0 ≡ C ∈ PUniv i.
Proof.
Admitted.

Lemma Sub_Univ_InvR n (Γ : fin n -> PTm n) i C :
  Γ ⊢ PUniv i ≲ C ->
  exists j, Γ ⊢ C ≡ PUniv j ∈ PUniv (S j).
Proof.
Admitted.

Lemma T_Abs_Inv n Γ (a0 a1 : PTm (S n)) U :
  Γ ⊢ PAbs a0 ∈ U ->
  Γ ⊢ PAbs a1 ∈ U ->
  exists Δ V, Δ ⊢ a0 ∈ V /\ Δ ⊢ a1 ∈ V.
Proof.
  move /Abs_Inv => [A0][B0][wt0]hU0.
  move /Abs_Inv => [A1][B1][wt1]hU1.
  move /Sub_Bind_InvR : (hU0) => [i][A2][B2]hE.
  have hSu : Γ ⊢ PBind PPi A1 B1 ≲ PBind PPi A2 B2 by eauto using Su_Eq, Su_Transitive.
  have hSu' : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Eq, Su_Transitive.
  exists (funcomp (ren_PTm shift) (scons A2 Γ)), B2.
  have [k ?] : exists k, Γ ⊢ A2 ∈ PUniv k by hauto lq:on use:regularity, Bind_Inv.
  split.
  - have /Su_Pi_Proj2_Var ? := hSu'.
    have /Su_Pi_Proj1 ? := hSu'.
    move /regularity_sub0 : hSu' => [j] /Bind_Inv [k0 [? ?]].
    apply T_Conv with (A := B0); eauto.
    apply : ctx_eq_subst_one; eauto.
  - have /Su_Pi_Proj2_Var ? := hSu.
    have /Su_Pi_Proj1 ? := hSu.
    move /regularity_sub0 : hSu => [j] /Bind_Inv [k0 [? ?]].
    apply T_Conv with (A := B1); eauto.
    apply : ctx_eq_subst_one; eauto.
Qed.

(* Coquand's algorithm with subtyping *)
Reserved Notation "a ∼ b" (at level 70).
Reserved Notation "a ↔ b" (at level 70).
Reserved Notation "a ⇔ b" (at level 70).
Reserved Notation "a ≪ b" (at level 70).
Reserved Notation "a ⋖ b" (at level 70).
Inductive CoqEq {n} : PTm n -> PTm n -> Prop :=
| CE_AbsAbs a b :
  a ⇔ b ->
  (* --------------------- *)
  PAbs a ↔ PAbs b

| CE_AbsNeu a u :
  ishne u ->
  a ⇔ PApp (ren_PTm shift u) (VarPTm var_zero) ->
  (* --------------------- *)
  PAbs a ↔ u

| CE_NeuAbs a u :
  ishne u ->
  PApp (ren_PTm shift u) (VarPTm var_zero) ⇔ a ->
  (* --------------------- *)
  u ↔ PAbs a

| CE_PairPair a0 a1 b0 b1 :
  a0 ⇔ a1 ->
  b0 ⇔ b1 ->
  (* ---------------------------- *)
  PPair a0 b0 ↔ PPair a1 b1

| CE_PairNeu a0 a1 u :
  ishne u ->
  a0 ⇔ PProj PL u ->
  a1 ⇔ PProj PR u ->
  (* ----------------------- *)
  PPair a0 a1 ↔ u

| CE_NeuPair a0 a1 u :
  ishne u ->
  PProj PL u ⇔ a0 ->
  PProj PR u ⇔ a1 ->
  (* ----------------------- *)
  u ↔ PPair a0 a1

| CE_UnivCong i :
  (* -------------------------- *)
  PUniv i ↔ PUniv i

| CE_BindCong p A0 A1 B0 B1 :
  A0 ⇔ A1 ->
  B0 ⇔ B1 ->
  (* ---------------------------- *)
  PBind p A0 B0 ↔ PBind p A1 B1

| CE_NeuNeu a0 a1 :
  a0 ∼ a1 ->
  a0 ↔ a1

with CoqEq_Neu  {n} : PTm n -> PTm n -> Prop :=
| CE_VarCong i :
  (* -------------------------- *)
  VarPTm i ∼ VarPTm i

| CE_ProjCong p u0 u1 :
  ishne u0 ->
  ishne u1 ->
  u0 ∼ u1 ->
  (* ---------------------  *)
  PProj p u0 ∼ PProj p u1

| CE_AppCong u0 u1 a0 a1 :
  ishne u0 ->
  ishne u1 ->
  u0 ∼ u1 ->
  a0 ⇔ a1 ->
  (* ------------------------- *)
  PApp u0 a0 ∼ PApp u1 a1

with CoqEq_R {n} : PTm n -> PTm n -> Prop :=
| CE_HRed a a' b b'  :
  rtc HRed.R a a' ->
  rtc HRed.R b b' ->
  a' ↔ b' ->
  (* ----------------------- *)
  a ⇔ b
where "a ↔ b" := (CoqEq a b) and "a ⇔ b" := (CoqEq_R a b) and "a ∼ b" := (CoqEq_Neu a b).

Lemma CE_HRedL n (a a' b : PTm n)  :
  HRed.R a a' ->
  a' ⇔ b ->
  a ⇔ b.
Proof.
  hauto lq:on ctrs:rtc, CoqEq_R inv:CoqEq_R.
Qed.

Scheme
  coqeq_neu_ind := Induction for CoqEq_Neu Sort Prop
  with coqeq_ind := Induction for CoqEq Sort Prop
  with coqeq_r_ind := Induction for CoqEq_R Sort Prop.

Combined Scheme coqeq_mutual from coqeq_neu_ind, coqeq_ind, coqeq_r_ind.

Lemma coqeq_symmetric_mutual : forall n,
    (forall (a b : PTm n), a ∼ b -> b ∼ a) /\
    (forall (a b : PTm n), a ↔ b -> b ↔ a) /\
    (forall (a b : PTm n), a ⇔ b -> b ⇔ a).
Proof. apply coqeq_mutual; qauto l:on ctrs:CoqEq,CoqEq_R, CoqEq_Neu. Qed.

(* Lemma Sub_Univ_InvR *)

Lemma coqeq_sound_mutual : forall n,
    (forall (a b : PTm n), a ∼ b -> forall Γ A B, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> exists C,
       Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ≡ b ∈ C) /\
    (forall (a b : PTm n), a ↔ b -> forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> Γ ⊢ a ≡ b ∈ A) /\
    (forall (a b : PTm n), a ⇔ b -> forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> Γ ⊢ a ≡ b ∈ A).
Proof.
  move => [:hAppL hPairL].
  apply coqeq_mutual.
  - move => n i Γ A B hi0 hi1.
    move /Var_Inv : hi0 => [hΓ h0].
    move /Var_Inv : hi1 => [_ h1].
    exists (Γ i).
    repeat split => //=.
    apply E_Refl. eauto using T_Var.
  - move => n [] u0 u1 hu0 hu1 hu ihu Γ A B hu0' hu1'.
    + move /Proj1_Inv : hu0'.
      move => [A0][B0][hu0']hu0''.
      move /Proj1_Inv : hu1'.
      move => [A1][B1][hu1']hu1''.
      specialize ihu with (1 := hu0') (2 := hu1').
      move : ihu.
      move => [C][ih0][ih1]ih.
      have [i[A2[B2 h2]]] : exists i A2 B2, Γ ⊢ PBind PSig A2 B2 ≡ C ∈ PUniv i by sfirstorder use:Sub_Bind_InvL.
      exists  A2.
      have [h3 h4] : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0 /\ Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1 by qauto l:on use:Su_Eq, Su_Transitive.
      repeat split;
        eauto using Su_Sig_Proj1, Su_Transitive;[idtac].
      apply E_Proj1 with (B := B2); eauto using E_Conv_E.
    + move /Proj2_Inv : hu0'.
      move => [A0][B0][hu0']hu0''.
      move /Proj2_Inv : hu1'.
      move => [A1][B1][hu1']hu1''.
      specialize ihu with (1 := hu0') (2 := hu1').
      move : ihu.
      move => [C][ih0][ih1]ih.
      have [A2 [B2 [i hi]]] : exists A2 B2 i, Γ ⊢ PBind PSig A2 B2 ≡ C ∈ PUniv i by hauto q:on use:Sub_Bind_InvL.
      have [h3 h4] : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0 /\ Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1 by qauto l:on use:Su_Eq, Su_Transitive.
      have h5 : Γ ⊢ u0 ≡ u1 ∈ PBind PSig A2 B2 by eauto using E_Conv_E.
      exists (subst_PTm (scons (PProj PL u0) VarPTm) B2).
      have [? ?] : Γ ⊢ u0 ∈ PBind PSig A2 B2 /\ Γ ⊢ u1 ∈ PBind PSig A2 B2 by hauto l:on use:regularity.
      repeat split => //=.
      apply : Su_Transitive ;eauto.
      apply : Su_Sig_Proj2; eauto.
      apply E_Refl. eauto using T_Proj1.
      apply : Su_Transitive ;eauto.
      apply : Su_Sig_Proj2; eauto.
      apply : E_Proj1; eauto.
      apply : E_Proj2; eauto.
  - move => n u0 u1 a0 a1 neu0 neu1 hu ihu ha iha Γ A B wta0 wta1.
    move /App_Inv : wta0 => [A0][B0][hu0][ha0]hU.
    move /App_Inv : wta1 => [A1][B1][hu1][ha1]hU1.
    move : ihu hu0 hu1. repeat move/[apply].
    move => [C][hC0][hC1]hu01.
    have [i [A2 [B2 hPi]]] : exists i A2 B2, Γ ⊢ PBind PPi A2 B2 ≡ C ∈ PUniv i by sfirstorder use:Sub_Bind_InvL.
    have ? : Γ ⊢ PBind PPi A2 B2 ≲ PBind PPi A0 B0 by eauto using Su_Eq, Su_Transitive.
    have h : Γ ⊢ PBind PPi A2 B2 ≲ PBind PPi A1 B1 by eauto using Su_Eq, Su_Transitive.
    have ha' : Γ ⊢ a0 ≡ a1 ∈ A2 by
      sauto lq:on use:Su_Transitive, Su_Pi_Proj1.
    have hwf : Γ ⊢ PBind PPi A2 B2 ∈ PUniv i by hauto l:on use:regularity.
    have [j hj'] : exists j,Γ ⊢ A2 ∈ PUniv j by hauto l:on use:regularity.
    have ? : ⊢ Γ by sfirstorder use:wff_mutual.
    exists (subst_PTm (scons a0 VarPTm) B2).
    repeat split. apply : Su_Transitive; eauto.
    apply : Su_Pi_Proj2';  eauto using E_Refl.
    apply : Su_Transitive; eauto.
    have ? : Γ ⊢ A1 ≲ A2 by eauto using Su_Pi_Proj1.
    apply Su_Transitive with (B := subst_PTm (scons a1 VarPTm) B2);
      first by sfirstorder use:bind_inst.
    apply : Su_Pi_Proj2';  eauto using E_Refl.
    apply E_App with (A := A2); eauto using E_Conv_E.
  - move => n a b ha iha Γ A h0 h1.
    move /Abs_Inv : h0 => [A0][B0][h0]h0'.
    move /Abs_Inv : h1 => [A1][B1][h1]h1'.
    have [i [A2 [B2 h]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PPi A2 B2 ∈ PUniv i by hauto l:on use:Sub_Bind_InvR.
    have hp0 : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
    have hp1 : Γ ⊢ PBind PPi A1 B1 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
    have [j ?] : exists j, Γ ⊢ A0 ∈ PUniv j by qauto l:on use:Wff_Cons_Inv, wff_mutual.
    have [k ?] : exists j, Γ ⊢ A1 ∈ PUniv j by qauto l:on use:Wff_Cons_Inv, wff_mutual.
    have [l ?] : exists j, Γ ⊢ A2 ∈ PUniv j by hauto lq:on rew:off use:regularity, Bind_Inv.
    have [h2 h3] : Γ ⊢ A2 ≲ A0 /\ Γ ⊢ A2 ≲ A1 by hauto l:on use:Su_Pi_Proj1.
    apply E_Conv with (A := PBind PPi A2 B2); cycle 1.
    eauto using E_Symmetric, Su_Eq.
    apply : E_Abs; eauto. hauto l:on use:regularity.
    apply iha.
    move /Su_Pi_Proj2_Var in hp0.
    apply : T_Conv; eauto.
    eapply ctx_eq_subst_one with (A0 := A0); eauto.
    move /Su_Pi_Proj2_Var in hp1.
    apply : T_Conv; eauto.
    eapply ctx_eq_subst_one with (A0 := A1); eauto.
  - abstract : hAppL.
    move => n a u hneu ha iha Γ A wta wtu.
    move /Abs_Inv : wta => [A0][B0][wta]hPi.
    have [i [A2 [B2 h]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PPi A2 B2 ∈ PUniv i by hauto l:on use:Sub_Bind_InvR.
    have hPi'' : Γ ⊢ PBind PPi A2 B2 ≲ A by eauto using Su_Eq, Su_Transitive, E_Symmetric.
    have [j0 ?] : exists j0, Γ ⊢ A0 ∈ PUniv j0 by move /regularity_sub0 in hPi; hauto lq:on use:Bind_Inv.
    have [j2 ?] : exists j0, Γ ⊢ A2 ∈ PUniv j0 by move /regularity_sub0 in hPi''; hauto lq:on use:Bind_Inv.
    have hPi' : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Eq, Su_Transitive.
    have hPidup := hPi'.
    apply E_Conv with (A := PBind PPi A2 B2); eauto.
    have /regularity_sub0 [i' hPi0] := hPi.
    have : Γ ⊢ PAbs (PApp (ren_PTm shift u) (VarPTm var_zero)) ≡ u ∈ PBind PPi A2 B2.
    apply : E_AppEta; eauto.
    sfirstorder use:wff_mutual.
    hauto l:on use:regularity.
    apply T_Conv with (A := A);eauto.
    eauto using Su_Eq.
    move => ?.
    suff : Γ ⊢ PAbs a ≡ PAbs (PApp (ren_PTm shift u) (VarPTm var_zero)) ∈ PBind PPi A2 B2
      by eauto using E_Transitive.
    apply : E_Abs; eauto. hauto l:on use:regularity.
    apply iha.
    move /Su_Pi_Proj2_Var in hPi'.
    apply : T_Conv; eauto.
    eapply ctx_eq_subst_one with (A0 := A0); eauto.
    sfirstorder use:Su_Pi_Proj1.

    (* move /Su_Pi_Proj2_Var in hPidup. *)
    (* apply : T_Conv; eauto. *)
    eapply T_App' with (A := ren_PTm shift A2) (B := ren_PTm (upRen_PTm_PTm shift) B2). by asimpl.
    eapply weakening_wt' with (a := u) (A := PBind PPi A2 B2);eauto.
    by eauto using T_Conv_E. apply T_Var. apply : Wff_Cons'; eauto.
  (* Mirrors the last case *)
  - move => n a u hu ha iha Γ A hu0 ha0.
    apply E_Symmetric.
    apply : hAppL; eauto.
    sfirstorder use:coqeq_symmetric_mutual.
    sfirstorder use:E_Symmetric.
  - move => {hAppL hPairL} n a0 a1 b0 b1 ha iha hb ihb Γ A.
    move /Pair_Inv => [A0][B0][h00][h01]h02.
    move /Pair_Inv => [A1][B1][h10][h11]h12.
    have [i[A2[B2 h2]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PSig A2 B2 ∈ PUniv i by hauto l:on use:Sub_Bind_InvR.
    apply E_Conv with (A := PBind PSig A2 B2); last by eauto using E_Symmetric, Su_Eq.
    have h0 : Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A2 B2 by eauto using Su_Transitive, Su_Eq, E_Symmetric.
    have h1 : Γ ⊢ PBind PSig A1 B1 ≲ PBind PSig A2 B2 by eauto using Su_Transitive, Su_Eq, E_Symmetric.
    have /Su_Sig_Proj1 h0' := h0.
    have /Su_Sig_Proj1 h1' := h1.
    move => [:eqa].
    apply : E_Pair; eauto. hauto l:on use:regularity.
    abstract : eqa. apply iha; eauto using T_Conv.
    apply ihb.
    + apply T_Conv with (A := subst_PTm (scons a0 VarPTm) B0); eauto.
      have : Γ ⊢ a0 ≡ a0 ∈A0 by eauto using E_Refl.
      hauto l:on use:Su_Sig_Proj2.
    + apply T_Conv with (A := subst_PTm (scons a1 VarPTm) B2); eauto; cycle 1.
      move /E_Symmetric in eqa.
      have ? : Γ ⊢ PBind PSig A2 B2 ∈ PUniv i by hauto use:regularity.
      apply:bind_inst; eauto.
      apply : T_Conv; eauto.
      have : Γ ⊢ a1 ≡ a1 ∈ A1 by eauto using E_Refl.
      hauto l:on use:Su_Sig_Proj2.
  - move => {hAppL}.
    abstract : hPairL.
    move => {hAppL}.
    move => n a0 a1 u neu h0 ih0 h1 ih1 Γ A ha hu.
    move /Pair_Inv : ha => [A0][B0][ha0][ha1]ha.
    have [i [A2 [B2 hA]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PSig A2 B2 ∈ PUniv i by hauto l:on use:Sub_Bind_InvR.
    have hA' : Γ ⊢ PBind PSig A2 B2 ≲ A by eauto using E_Symmetric, Su_Eq.
    move /E_Conv : (hA'). apply.
    have hSig : Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A2 B2 by eauto using E_Symmetric, Su_Eq, Su_Transitive.
    have hA02 : Γ ⊢ A0 ≲ A2 by sfirstorder use:Su_Sig_Proj1.
    have hu'  : Γ ⊢ u ∈ PBind PSig A2 B2 by eauto using T_Conv_E.
    move => [:ih0'].
    apply : E_Transitive; last (apply E_Symmetric; apply : E_PairEta).
    apply : E_Pair; eauto. hauto l:on use:regularity.
    abstract : ih0'.
    apply ih0. apply : T_Conv; eauto.
    by eauto using T_Proj1.
    apply ih1. apply : T_Conv; eauto.
    move /E_Refl in ha0.
    hauto l:on use:Su_Sig_Proj2.
    move /T_Proj2 in hu'.
    apply : T_Conv; eauto.
    move /E_Symmetric in ih0'.
    move /regularity_sub0 in hA'.
    hauto l:on use:bind_inst.
    hauto l:on use:regularity.
    eassumption.
  (* Same as before *)
  - move {hAppL}.
    move => *. apply E_Symmetric. apply : hPairL;
      sfirstorder use:coqeq_symmetric_mutual, E_Symmetric.
  - sfirstorder use:E_Refl.
  - move => {hAppL hPairL} n p A0 A1 B0 B1 hA ihA hB ihB Γ A hA0 hA1.
    move /Bind_Inv : hA0 => [i][hA0][hB0]hU.
    move /Bind_Inv : hA1 => [j][hA1][hB1]hU1.
    have [l [k hk]] : exists l k, Γ ⊢ A ≡ PUniv k ∈ PUniv l
        by hauto lq:on use:Sub_Univ_InvR.
    have hjk : Γ ⊢ PUniv j ≲ PUniv k by eauto using Su_Eq, Su_Transitive.
    have hik : Γ ⊢ PUniv i ≲ PUniv k by eauto using Su_Eq, Su_Transitive.
    apply E_Conv with (A := PUniv k); last by eauto using Su_Eq, E_Symmetric.
    move => [:eqA].
    apply E_Bind. abstract : eqA. apply ihA.
    apply T_Conv with (A := PUniv i); eauto.
    apply T_Conv with (A := PUniv j); eauto.
    apply ihB.
    apply T_Conv with (A := PUniv i); eauto.
    move : weakening_su hik hA0. by repeat move/[apply].
    apply T_Conv with (A := PUniv j); eauto.
    apply : ctx_eq_subst_one; eauto. apply : Su_Eq; apply eqA.
    move : weakening_su hjk hA0. by repeat move/[apply].
  - hauto lq:on ctrs:Eq,LEq,Wt.
  - move => n a a' b b' ha hb hab ihab Γ A ha0 hb0.
    have [*] : Γ ⊢ a' ∈ A /\ Γ ⊢ b' ∈ A by eauto using HReds.preservation.
    hauto lq:on use:HReds.ToEq, E_Symmetric, E_Transitive.
Qed.

Definition algo_metric {n} k (a b : PTm n) :=
  exists i j va vb v, nsteps LoRed.R i a va /\ nsteps LoRed.R j b vb /\ rtc ERed.R va v /\ rtc ERed.R vb v /\ nf va /\ nf vb /\ size_PTm va + size_PTm vb + i + j <= k.

Lemma ne_hne n (a : PTm n) : ne a -> ishne a.
Proof. elim : a => //=; sfirstorder b:on. Qed.

Lemma hf_hred_lored n (a b : PTm n) :
  ~~ ishf a ->
  LoRed.R a b ->
  HRed.R a b \/ ishne a.
Proof.
  move => + h. elim : n a b/ h=>//=.
  - hauto l:on use:HRed.AppAbs.
  - hauto l:on use:HRed.ProjPair.
  - hauto lq:on ctrs:HRed.R.
  - sfirstorder use:ne_hne.
  - hauto lq:on ctrs:HRed.R.
Qed.
Lemma algo_metric_case n k (a b : PTm n) :
  algo_metric k a b ->
  (ishf a \/ ishne a) \/ exists k' a', HRed.R a a' /\ algo_metric k' a' b /\ k' < k.
Proof.
  move=>[i][j][va][vb][v][h0][h1][h2][h3][h4][h5]h6.
  case : a h0 => //=; try firstorder.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.AppAbs unfold:algo_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia.
    + sfirstorder qb:on use:ne_hne.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.ProjPair unfold:algo_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia.
Qed.

Lemma algo_metric_sym n k (a b : PTm n) :
  algo_metric k a b -> algo_metric k b a.
Proof. hauto lq:on unfold:algo_metric solve+:lia. Qed.

Lemma hred_hne n (a b : PTm n) :
  HRed.R a b ->
  ishne a ->
  False.
Proof. induction 1; sfirstorder. Qed.

Lemma hf_not_hne n (a : PTm n) :
  ishf a -> ishne a -> False.
Proof. case : a => //=. Qed.

(* Lemma algo_metric_hf_case n Γ k a b (A : PTm n) : *)
(*   Γ ⊢ a ∈ A -> *)
(*   Γ ⊢ b ∈ A -> *)
(*   algo_metric k a b -> ishf a -> ishf b -> *)
(*   (exists a' b' k', a = PAbs a' /\ b = PAbs b' /\ algo_metric k' a' b' /\ k' < k) \/ *)
(*   (exists a0' a1' b0' b1' ka kb, a = PPair a0' a1' /\ b = PPair b0' b1' /\ algo_metric ka a0' b0' /\ algo_metric ) *)

Lemma T_AbsPair_Imp n Γ a (b0 b1 : PTm n) A :
  Γ ⊢ PAbs a ∈ A ->
  Γ ⊢ PPair b0 b1 ∈ A ->
  False.
Proof.
  move /Abs_Inv => [A0][B0][_]haU.
  move /Pair_Inv => [A1][B1][_][_]hbU.
  move /Sub_Bind_InvR : haU => [i][A2][B2]h2.
  have : Γ ⊢ PBind PSig A1 B1 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_inj.
Qed.

Lemma T_PairBind_Imp n Γ (a0 a1 : PTm n) p A0 B0 U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PBind p A0 B0  ∈ U ->
  False.
Proof.
  move /Pair_Inv => [A1][B1][_][_]hbU.
  move /Bind_Inv => [i][_ [_ haU]].
  move /Sub_Univ_InvR : haU => [j]hU.
  have : Γ ⊢ PBind PSig A1 B1 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_univ_noconf.
Qed.

Lemma Univ_Inv n Γ i U :
  Γ ⊢ @PUniv n i ∈ U ->
  Γ ⊢ PUniv i ∈ PUniv (S i)  /\ Γ ⊢ PUniv (S i) ≲ U.
Proof.
  move E : (PUniv i) => u hu.
  move : i E. elim : n Γ u U / hu => n //=.
  - hauto l:on use:E_Refl, Su_Eq, T_Univ.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma T_PairUniv_Imp n Γ (a0 a1 : PTm n) i U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PUniv i ∈ U ->
  False.
Proof.
  move /Pair_Inv => [A1][B1][_][_]hbU.
  move /Univ_Inv => [h0 h1].
  move /Sub_Univ_InvR : h1 => [j hU].
  have : Γ ⊢ PBind PSig A1 B1 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub.
  hauto lq:on use:Sub.bind_univ_noconf.
Qed.

Lemma T_AbsUniv_Imp n Γ a i (A : PTm n) :
  Γ ⊢ PAbs a ∈ A ->
  Γ ⊢ PUniv i ∈ A ->
  False.
Proof.
  move /Abs_Inv => [A0][B0][_]haU.
  move /Univ_Inv => [h0 h1].
  move /Sub_Univ_InvR : h1 => [j hU].
  have : Γ ⊢ PBind PPi A0 B0 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub.
  hauto lq:on use:Sub.bind_univ_noconf.
Qed.

Lemma T_AbsBind_Imp n Γ a p A0 B0 (U : PTm n) :
  Γ ⊢ PAbs a ∈ U ->
  Γ ⊢ PBind p A0 B0 ∈ U ->
  False.
Proof.
  move /Abs_Inv => [A1][B1][_ ha].
  move /Bind_Inv => [i [_ [_ h]]].
  move /Sub_Univ_InvR : h => [j hU].
  have : Γ ⊢ PBind PPi A1 B1 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub.
  hauto lq:on use:Sub.bind_univ_noconf.
Qed.

Lemma T_Bot_Imp n Γ (A : PTm n) :
  Γ ⊢ PBot ∈ A -> False.
  move E : PBot => u hu.
  move : E.
  induction hu => //=.
Qed.

Lemma lored_nsteps_abs_inv k n (a : PTm (S n)) b :
  nsteps LoRed.R k (PAbs a) b -> exists b', nsteps LoRed.R k a b' /\ b = PAbs b'.
Proof.
  move E : (PAbs a) => u hu.
  move : a E.
  elim : u b /hu.
  - hauto l:on.
  - hauto lq:on ctrs:nsteps inv:LoRed.R.
Qed.

Lemma lored_hne_preservation n (a b : PTm n) :
    LoRed.R a b -> ishne a -> ishne b.
Proof.  induction 1; sfirstorder. Qed.

Lemma lored_nsteps_app_inv k n (a0 b0 C : PTm n) :
    nsteps LoRed.R k (PApp a0 b0) C ->
    ishne a0 ->
    exists i j a1 b1,
      i <= k /\ j <= k /\
        C = PApp a1 b1 /\
        nsteps LoRed.R i a0 a1 /\
        nsteps LoRed.R j b0 b1.
Proof.
  move E : (PApp a0 b0) => u hu. move : a0 b0 E.
  elim : k u C / hu.
  - sauto lq:on.
  - move => k a0 a1 a2 ha01 ha12 ih a3 b0 ?.  subst.
    inversion ha01; subst => //=.
    spec_refl.
    move => h.
    have : ishne a4 by sfirstorder use:lored_hne_preservation.
    move : ih => /[apply]. move => [i][j][a1][b1][?][?][?][h0]h1.
    subst. exists (S i),j,a1,b1. sauto lq:on solve+:lia.
    spec_refl. move : ih => /[apply].
    move => [i][j][a1][b1][?][?][?][h0]h1. subst.
    exists i, (S j), a1, b1. sauto lq:on solve+:lia.
Qed.

Lemma algo_metric_app n k (a0 b0 a1 b1 : PTm n) :
  algo_metric k (PApp a0 b0) (PApp a1 b1) ->
  ishne a0 ->
  ishne a1 ->
  exists j, j < k /\ algo_metric j a0 a1 /\ algo_metric j b0 b1.
Proof.
  move => [i][j][va][vb][v][h0][h1][h2][h3][h4][h5]h6.
  move => hne0 hne1.
  move : lored_nsteps_app_inv h0 (hne0);repeat move/[apply].
  move => [i0][i1][a2][b2][?][?][?][ha02]hb02. subst.
  move : lored_nsteps_app_inv h1 (hne1);repeat move/[apply].
  move => [j0][j1][a3][b3][?][?][?][ha13]hb13. subst.
  simpl in *. exists (k - 1).
  split. lia.
  split.
  + rewrite /algo_metric.
    have : exists a4 b4, rtc ERed.R a2 a4 /\ ERed.R
    exists i0,i1,a2,b2.

Lemma algo_metric_join n k (a b : PTm n) :
  algo_metric k a b ->
  DJoin.R a b.
  rewrite /algo_metric.
  move => [i][j][va][vb][v][h0][h1][h2][h3]h4.
  have {}h0 : rtc LoRed.R a va by hauto lq:on use:@relations.rtc_nsteps.
  have {}h1 : rtc LoRed.R b vb by hauto lq:on use:@relations.rtc_nsteps.
  apply REReds.FromEReds in h2,h3.
  apply LoReds.ToRReds in h0,h1.
  apply REReds.FromRReds in h0,h1.
  rewrite /DJoin.R. exists v. sfirstorder use:@relations.rtc_transitive.
Qed.

Lemma coqeq_complete n k (a b : PTm n) :
  algo_metric k a b ->
  (forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> a ⇔ b) /\
  (forall Γ A B, ishne a -> ishne b -> Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ exists C, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B).
Proof.
  move : k n a b.
  elim /Wf_nat.lt_wf_ind.
  move => n ih.
  move => k a b /[dup] h /algo_metric_case. move : k a b h => [:hstepL].
  move => k a b h.
  (* Cases where a and b can take steps *)
  case; cycle 1.
  move : k a b h.
  abstract : hstepL. qauto l:on use:HRed.preservation, CE_HRedL, hred_hne.
  move  /algo_metric_sym /algo_metric_case : (h).
  case; cycle 1.
  move {ih}. move /algo_metric_sym : h.
  move : hstepL => /[apply].
  hauto lq:on use:coqeq_symmetric_mutual, algo_metric_sym.
  (* Cases where a and b can't take wh steps *)
  move {hstepL}.
  move : k a b h. move => [:hnfneu].
  move => k a b h.
  case => fb; case => fa.
  - split; last by sfirstorder use:hf_not_hne.
    move {hnfneu}.
    case : a h fb fa => //=.
    + case : b => //=; try qauto depth:1 use:T_AbsPair_Imp, T_AbsBind_Imp, T_AbsUniv_Imp.
      move => a0 a1 ha0 _ _ Γ A wt0 wt1.
      move : T_Abs_Inv wt0 wt1; repeat move/[apply]. move  => [Δ [V [wt1 wt0]]].
      apply : CE_HRed; eauto using rtc_refl.
      apply CE_AbsAbs.
      suff [l [h0 h1]] : exists l, l < n /\ algo_metric l a1 a0 by eapply ih; eauto.
      have ? : n > 0 by sauto solve+:lia.
      exists (n - 1). split; first by lia.
      move : ha0. rewrite /algo_metric.
      move => [i][j][va][vb][v][hr0][hr1][hr0'][hr1'][nfva][nfvb]har.
      apply lored_nsteps_abs_inv in hr0, hr1.
      move : hr0 => [va' [hr00 hr01]].
      move : hr1 => [vb' [hr10 hr11]]. move {ih}.
      exists i,j,va',vb'. subst.
      suff [v0 [hv00 hv01]] : exists v0, rtc ERed.R va' v0 /\ rtc ERed.R vb' v0.
      exists v0. repeat split =>//=. simpl in har. lia.
      admit.
    + case : b => //=; try qauto depth:1 use:T_AbsPair_Imp, T_PairBind_Imp, T_PairUniv_Imp.
      move => a1 b1 a0 b0 h _ _ Γ A hu0 hu1.
      apply : CE_HRed; eauto using rtc_refl.
      admit.
      (* suff : exists l, l < n /\ algo_metric l a0 b0 /\ algo_metric l a1 b1. *)
      (* move => [l [hl [hal0 hal1]]]. *)
      (* apply CE_PairPair. eapply ih; eauto. *)
      (* by eapply ih; eauto. *)
    + admit.
    + admit.
  - move : k a b h fb fa. abstract : hnfneu.
    admit.
  - move {ih}.
    move /algo_metric_sym in h.
    qauto l:on use:coqeq_symmetric_mutual.
  - move {hnfneu}.

    (* Clear out some trivial cases *)
    suff : (forall (Γ : fin k -> PTm k) (A B : PTm k), Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ (exists C : PTm k, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B)).
    move => h0.
    split. move => *. apply : CE_HRed; eauto using rtc_refl. apply CE_NeuNeu. by firstorder.
    by firstorder.

    case : a h fb fa => //=.
    + case : b => //=.
      move => i j hi _ _.
      * have ? : j = i by hauto lq:on use:algo_metric_join, DJoin.var_inj. subst.
        move => Γ A B hA hB.
        split. apply CE_VarCong.
        exists (Γ i). hauto l:on use:Var_Inv.
      * admit.
      * admit.
      * sfirstorder use:T_Bot_Imp.
    + case : b => //=.
      * admit.
      (* real case *)
      * move => b1 a1 b0 a0 halg hne1 hne0 Γ A B wtA wtB.
        move /App_Inv : wtA => [A0][B0][hb0][ha0]hS0.
        move /App_Inv : wtB => [A1][B1][hb1][ha1]hS1.
        have : DJoin.R (PApp b0 a0) (PApp b1 a1)
          by hauto l:on use:algo_metric_join.
        move : DJoin.hne_app_inj (hne0) (hne1). repeat move/[apply].
        move => [hjb hja].
        split. apply CE_AppCong => //=.
        eapply ih; eauto.
        admit.
      * admit.
      * sfirstorder use:T_Bot_Imp.
    + case : b => //=.
      * admit.
      * admit.
      (* real case *)
      * admit.
      * sfirstorder use:T_Bot_Imp.
    + sfirstorder use:T_Bot_Imp.
Admitted.
