Require Import Autosubst2.fintype Autosubst2.syntax.
Require Import fp_red logrel typing.
From Hammer Require Import Tactics.

Theorem fundamental_theorem :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> ⊨ Γ) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> Γ ⊨ a ∈ A)  /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> Γ ⊨ a ≡ b ∈ A).
  apply wt_mutual; eauto with sem;[idtac].
  hauto l:on use:SE_Pair.
Qed.
