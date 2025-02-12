Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax common typing preservation admissible.
From Hammer Require Import Tactics.
Require Import ssreflect ssrbool.
Require Import Psatz.
From stdpp Require Import relations (rtc(..)).
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
End HRed.

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

Lemma Var_Inv n Γ (i : fin n) A :
  Γ ⊢ VarPTm i ∈ A ->
  ⊢ Γ /\ Γ ⊢ Γ i ≲ A.
Proof.
  move E : (VarPTm i) => u hu.
  move : i E.
  elim : n Γ u A / hu=>//=.
  - move => n Γ i hΓ i0 [?]. subst.
    repeat split => //=.
    have h : Γ ⊢ VarPTm i ∈ Γ i by eauto using T_Var.
    eapply structural.regularity in h.
    move : h => [i0]?.
    apply : Su_Eq. apply E_Refl; eassumption.
  - sfirstorder use:Su_Transitive.
Qed.

Lemma coqeq_sound_mutual : forall n,
    (forall (a b : PTm n), a ∼ b -> forall Γ A B, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> exists C,
       Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ≡ b ∈ C) /\
    (forall (a b : PTm n), a ↔ b -> forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> Γ ⊢ a ≡ b ∈ A) /\
    (forall (a b : PTm n), a ⇔ b -> forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> Γ ⊢ a ≡ b ∈ A).
Proof.
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
      have [A2 [B2 [{}ih0 [{}ih1 {}ih]]]] : exists A2 B2, Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0 /\ Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1 /\ Γ ⊢ u0 ≡ u1 ∈ PBind PSig A2 B2 by admit.

      have /Su_Sig_Proj1 hs0 := ih0.
      have /Su_Sig_Proj1 hs1 := ih1.
      exists A2.
      repeat split; eauto using Su_Transitive.
      apply : E_Proj1; eauto.
    + move /Proj2_Inv : hu0'.
      move => [A0][B0][hu0']hu0''.
      move /Proj2_Inv : hu1'.
      move => [A1][B1][hu1']hu1''.
      specialize ihu with (1 := hu0') (2 := hu1').
      move : ihu.
      move => [C][ih0][ih1]ih.
      have [A2 [B2 [{}ih0 [{}ih1 {}ih]]]] : exists A2 B2, Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0 /\ Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1 /\ Γ ⊢ u0 ≡ u1 ∈ PBind PSig A2 B2 by admit.
      exists (subst_PTm (scons (PProj PL u0) VarPTm) B2).
      have [? ?] : Γ ⊢ u0 ∈ PBind PSig A2 B2 /\ Γ ⊢ u1 ∈ PBind PSig A2 B2 by hauto l:on use:structural.regularity.
      repeat split => //=.
      apply : Su_Transitive ;eauto.
      apply : Su_Sig_Proj2; eauto.
      apply E_Refl. eauto using T_Proj1.
      apply : Su_Transitive ;eauto.
      apply : Su_Sig_Proj2; eauto.
      apply : E_Proj1; eauto.
      move /regularity_sub0 : ih1 => [i ?].
      apply : E_Proj2; eauto.
  - move => n u0 u1 a0 a1 neu0 neu1 hu ihu ha iha Γ A B wta0 wta1.
    admit.
  - move => n a b ha iha Γ A h0 h1.
    move /Abs_Inv : h0 => [A0][B0][h0]h0'.
    move /Abs_Inv : h1 => [A1][B1][h1]h1'.
    have [i [A2 [B2 h]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PPi A2 B2 ∈ PUniv i by admit.
    have ? : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
    have ? : Γ ⊢ PBind PPi A1 B1 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
    have [h2 h3] : Γ ⊢ A2 ≲ A0 /\ Γ ⊢ A2 ≲ A1 by hauto l:on use:Su_Pi_Proj1.
    apply E_Conv with (A := PBind PPi A2 B2); cycle 1.
    eauto using E_Symmetric, Su_Eq.
    apply : E_Abs; eauto. hauto l:on use:structural.regularity.
    apply iha.
    eapply structural.ctx_eq_subst_one with (A0 := A0); eauto.
    admit.
    admit.
    admit.
    eapply structural.ctx_eq_subst_one with (A0 := A1); eauto.
    admit.
    admit.
    admit.
    (* Need to use the fundamental lemma to show that U normalizes to a Pi type *)
  - move => n a u hneu ha iha Γ A wta wtu.
    move /Abs_Inv : wta => [A0][B0][wta]hPi.
    have [i [A2 [B2 h]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PPi A2 B2 ∈ PUniv i by admit.
    have hPi'' : Γ ⊢ PBind PPi A2 B2 ≲ A by eauto using Su_Eq, Su_Transitive, E_Symmetric.
    have hPi' : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Eq, Su_Transitive.
    apply E_Conv with (A := PBind PPi A2 B2); eauto.
    have /regularity_sub0 [i' hPi0] := hPi.
    have : Γ ⊢ PAbs (PApp (ren_PTm shift u) (VarPTm var_zero)) ≡ u ∈ PBind PPi A2 B2.
    apply : E_AppEta; eauto.
    sfirstorder use:structural.wff_mutual.
    hauto l:on use:structural.regularity.
    apply T_Conv with (A := A);eauto.
    eauto using Su_Eq.
    move => ?.
    suff : Γ ⊢ PAbs a ≡ PAbs (PApp (ren_PTm shift u) (VarPTm var_zero)) ∈ PBind PPi A2 B2
      by eauto using E_Transitive.
    apply : E_Abs; eauto. hauto l:on use:structural.regularity.
    apply iha.
    admit.
    admit.
  (* Mirrors the last case *)
  - admit.
  - admit.
  - admit.
  - admit.
  - sfirstorder use:E_Refl.
  - admit.
  - hauto lq:on ctrs:Eq,LEq,Wt.
  - move => n a a' b b' ha hb.
    admit.
Admitted.
