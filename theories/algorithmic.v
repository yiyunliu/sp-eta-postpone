Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax
  common typing preservation admissible fp_red structural.
From Hammer Require Import Tactics.
Require Import ssreflect ssrbool.
Require Import Psatz.
From stdpp Require Import relations (rtc(..), nsteps(..)).
Require Import Coq.Logic.FunctionalExtensionality.

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

Definition algo_metric n (a b : PTm n) :=
  exists i j va vb, nsteps LoRed.R i a va /\ nsteps LoRed.R j a vb /\ nf va /\ nf vb /\ size_PTm va + size_PTm vb + i + j = n.

Lemma ishne_red n (a : PTm n) : SN a -> ~ ishne a -> exists b, HRed.R a b.
Admitted.

Lemma coqeq_complete n (a b : PTm n) :
  algo_metric n a b -> DJoin.R a b ->
  (forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> a ⇔ b) /\
  (forall Γ A B, ishne a -> ishne b -> Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ exists C, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B).
Proof.
  move : n a b.
  elim /Wf_nat.lt_wf_ind.
  move => n ih.
  move => a.
  case /orP : (orNb (ishf a)).
