Require Import Autosubst2.unscoped Autosubst2.syntax.
Require Import fp_red logrel typing.
From Hammer Require Import Tactics.

Theorem fundamental_theorem :
  (forall Γ, ⊢ Γ -> ⊨ Γ) /\
  (forall Γ a A, Γ ⊢ a ∈ A -> Γ ⊨ a ∈ A)  /\
  (forall Γ a b A, Γ ⊢ a ≡ b ∈ A -> Γ ⊨ a ≡ b ∈ A) /\
  (forall Γ a b, Γ ⊢ a ≲ b -> Γ ⊨ a ≲ b).
  apply wt_mutual; eauto with sem; [hauto l:on use:SE_Pair].
  Unshelve. all : exact 0.
Qed.

Lemma synsub_to_usub : forall Γ (a b : PTm), Γ ⊢ a ≲ b -> SN a /\ SN b /\ Sub.R a b.
Proof. hauto lq:on rew:off use:fundamental_theorem, SemLEq_SN_Sub. Qed.
