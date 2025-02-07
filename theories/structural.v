Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax common typing.
From Hammer Require Import Tactics.
Require Import ssreflect.


Lemma lem :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> True) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> )  /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> ...).
Proof. apply wt_mutual. ...


Lemma wff_mutual :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> True) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> ⊢ Γ)  /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> ⊢ Γ).
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

Lemma renaming :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> True) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> forall m Δ (ξ : fin n -> fin m), ⊢ Δ -> renaming_ok Δ Γ ξ ->
     Δ ⊢ ren_PTm ξ a ∈ ren_PTm ξ A) /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> forall m Δ (ξ : fin n -> fin m), ⊢ Δ -> renaming_ok Δ Γ ξ ->
     Δ ⊢ ren_PTm ξ a ≡ ren_PTm ξ b ∈ ren_PTm ξ A).
Proof.
  apply wt_mutual => //=; eauto 3 with wt.
  - move => n Γ i hΓ _ m Δ ξ hΔ hξ.
    rewrite hξ.
    by apply T_Var.
  - hauto lq:on rew:off ctrs:Wt, Wff  use:renaming_up.
  - move => n Γ a A B i hP ihP ha iha m Δ ξ hΔ hξ.
    apply : T_Abs; eauto.
    apply iha; last by apply renaming_up.
    econstructor; eauto.
    by apply renaming_up.
