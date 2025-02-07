Require Import Autosubst2.fintype Autosubst2.syntax.
Definition renaming_ok {n m} (Γ : fin n -> PTm n) (Δ : fin m -> PTm m) (ξ : fin m -> fin n) :=
  forall (i : fin m), ren_PTm ξ (Δ i) = Γ (ξ i).
