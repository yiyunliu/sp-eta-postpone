Require Import Autosubst2.fintype Autosubst2.syntax.
Require Import fp_red logrel typing.
From Hammer Require Import Tactics.

Theorem fundamental_theorem :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> ⊨ Γ) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> Γ ⊨ a ∈ A)  /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> Γ ⊨ a ≡ b ∈ A) /\
  (forall n Γ (a b : PTm n), Γ ⊢ a ≲ b -> Γ ⊨ a ≲ b).
  apply wt_mutual; eauto with sem; [hauto l:on use:SE_Pair].
  Unshelve. all : exact 0.
Qed.

Lemma synsub_to_usub : forall n Γ (a b : PTm n), Γ ⊢ a ≲ b -> SN a /\ SN b /\ Sub.R a b.
Proof. hauto lq:on rew:off use:fundamental_theorem, SemLEq_SN_Sub. Qed.
