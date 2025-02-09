Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax common typing.
From Hammer Require Import Tactics.
Require Import ssreflect.


Lemma wff_mutual :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> True) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> ⊢ Γ)  /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> ⊢ Γ) /\
  (forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> ⊢ Γ).
Proof. apply wt_mutual; eauto. Qed.

#[export]Hint Constructors Wt Wff Eq : wt.

Lemma renaming_up n m (ξ : fin n -> fin m) Δ Γ A :
  renaming_ok Δ Γ ξ ->
  renaming_ok (funcomp (ren_PTm shift) (scons (ren_PTm ξ A) Δ)) (funcomp (ren_PTm shift) (scons A Γ)) (upRen_PTm_PTm ξ) .
Proof.
  move => h i.
  destruct i as [i|].
  asimpl. rewrite /renaming_ok in h.
  rewrite /funcomp. rewrite -h.
  by asimpl.
  by asimpl.
Qed.

Lemma Su_Wt n Γ a i :
  Γ ⊢ a ∈ @PUniv n i ->
  Γ ⊢ a ≲ a.
Proof. hauto lq:on ctrs:LEq, Eq. Qed.

Lemma Wt_Univ n Γ a A i
  (h : Γ ⊢ a ∈ A) :
  Γ ⊢ @PUniv n i ∈ PUniv (S i).
Proof.
  hauto lq:on ctrs:Wt use:wff_mutual.
Qed.


Lemma Pi_Inv n Γ (A : PTm n) B U :
  Γ ⊢ PBind PPi A B ∈ U ->
  exists i, Γ ⊢ A ∈ PUniv i /\
  funcomp (ren_PTm shift) (scons A Γ) ⊢ B ∈ PUniv i /\
  Γ ⊢ PUniv i ≲ U.
Proof.
  move E :(PBind PPi A B) => T h.
  move : A B E.
  elim : n Γ T U / h => //=.
  - hauto lq:on ctrs:Wt,LEq,Eq use:Wt_Univ.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

(* Lemma regularity : *)
(*   (forall n (Γ : fin n -> PTm n), ⊢ Γ -> forall i, exists j, Γ ⊢ Γ i ∈ PUniv j) /\ *)
(*   (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> exists i, Γ ⊢ A ∈ PUniv i)  /\ *)
(*   (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A /\ exists i, Γ ⊢ A ∈ PUniv i) /\ *)
(*   (forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> exists i, Γ ⊢ A ∈ PUniv i /\ Γ ⊢ A ∈ PUniv i). *)
(* Proof. *)
(*   apply wt_mutual => //=. *)
(*   - admit. *)
(*   - admit. *)

Lemma T_App' n Γ (b a : PTm n) A B U :
  U = subst_PTm (scons a VarPTm) B ->
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ PApp b a ∈ U.
Proof. move => ->. apply T_App. Qed.

Lemma T_Pair' n Γ (a b : PTm n) A B i U :
  U = subst_PTm (scons a VarPTm) B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ U ->
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ PPair a b ∈ PBind PSig A B.
Proof.
  move => ->. eauto using T_Pair.
Qed.

Lemma T_Proj2' n Γ (a : PTm n) A B U :
  U = subst_PTm (scons (PProj PL a) VarPTm) B ->
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ∈ U.
Proof. move => ->. apply T_Proj2. Qed.

Lemma E_Bind' n Γ i p (A0 A1 : PTm n) B0 B1 :
  Γ ⊢ A0 ≡ A1 ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A0 Γ) ⊢ B0 ≡ B1 ∈ PUniv i ->
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i.
Proof. hauto lq:on use:E_Bind, wff_mutual. Qed.

Lemma renaming :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> True) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> forall m Δ (ξ : fin n -> fin m), ⊢ Δ -> renaming_ok Δ Γ ξ ->
     Δ ⊢ ren_PTm ξ a ∈ ren_PTm ξ A) /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> forall m Δ (ξ : fin n -> fin m), ⊢ Δ -> renaming_ok Δ Γ ξ ->
     Δ ⊢ ren_PTm ξ a ≡ ren_PTm ξ b ∈ ren_PTm ξ A) /\
  (forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> forall  m Δ (ξ : fin n -> fin m), ⊢ Δ -> renaming_ok Δ Γ ξ ->
    Δ ⊢ ren_PTm ξ A ≲ ren_PTm ξ B).
Proof.
  apply wt_mutual => //=; eauto 3 with wt.
  - move => n Γ i hΓ _ m Δ ξ hΔ hξ.
    rewrite hξ.
    by apply T_Var.
  - hauto lq:on rew:off ctrs:Wt, Wff  use:renaming_up.
  - move => n Γ a A B i hP ihP ha iha m Δ ξ hΔ hξ.
    apply : T_Abs; eauto.
    move : ihP(hΔ) (hξ); repeat move/[apply]. move/Pi_Inv.
    hauto lq:on rew:off ctrs:Wff,Wt use:renaming_up.
  - move => *. apply : T_App'; eauto. by asimpl.
  - move => n Γ a A b B i hA ihA hB ihB hS ihS m Δ ξ hξ hΔ.
    eapply T_Pair' with (U := ren_PTm ξ (subst_PTm (scons a VarPTm) B));eauto. by asimpl.
  - move => n Γ a A B ha iha m Δ ξ hΔ hξ. apply : T_Proj2'; eauto. by asimpl.
  - hauto lq:on ctrs:Wt,LEq.
  - hauto lq:on ctrs:Eq.
  - move => n Γ i p A0 A1 B0 B1 hΓ _ hA ihA hB ihB m Δ ξ hΔ hξ.
    apply E_Bind'; eauto.
    apply ihB; last by hauto l:on use:renaming_up.
