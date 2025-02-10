Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax common typing structural.
From Hammer Require Import Tactics.
Require Import ssreflect.
Require Import Psatz.
Require Import Coq.Logic.FunctionalExtensionality.

Derive Dependent Inversion wff_inv with (forall n (Γ : fin n -> PTm n), ⊢ Γ) Sort Prop.

Lemma Wff_Cons_Inv n Γ (A : PTm n) :
  ⊢ funcomp (ren_PTm shift) (scons A Γ) ->
  ⊢ Γ /\ exists i, Γ ⊢ A ∈ PUniv i.
Proof.
  elim /wff_inv => //= _.
  move => n0 Γ0 A0 i0 hΓ0 hA0 [? _]. subst.
  Equality.simplify_dep_elim.
  have h : forall i, (funcomp (ren_PTm shift) (scons A0 Γ0)) i = (funcomp (ren_PTm shift) (scons A Γ)) i by scongruence.
  move /(_ var_zero) : (h).
  rewrite /funcomp. asimpl.
  move /ren_injective. move /(_ ltac:(hauto lq:on rew:off inv:option)).
  move => ?. subst.
  have : Γ0 = Γ. extensionality i.
  move /(_ (Some i)) : h.
  rewrite /funcomp. asimpl.
  move /ren_injective. move /(_ ltac:(hauto lq:on rew:off inv:option)).
  done.
  move => ?. subst. sfirstorder.
Qed.

Lemma T_Abs n Γ (a : PTm (S n)) A B :
  funcomp (ren_PTm shift) (scons A Γ) ⊢ a ∈ B ->
  Γ ⊢ PAbs a ∈ PBind PPi A B.
Proof.
  move => ha.
  have [i hB] : exists i, funcomp (ren_PTm shift) (scons A Γ) ⊢ B ∈ PUniv i by sfirstorder use:regularity.
  have hΓ : ⊢ funcomp (ren_PTm shift) (scons A Γ) by sfirstorder use:wff_mutual.
  move /Wff_Cons_Inv : hΓ => [hΓ][j]hA.
  hauto lq:on rew:off use:T_Bind', typing.T_Abs.
Qed.

Lemma E_Bind n Γ i p (A0 A1 : PTm n) B0 B1 :
  Γ ⊢ A0 ≡ A1 ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A0 Γ) ⊢ B0 ≡ B1 ∈ PUniv i ->
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i.
Proof.
  move => h0 h1.
  have : Γ ⊢ A0 ∈ PUniv i by hauto l:on use:regularity.
  have : ⊢ Γ by sfirstorder use:wff_mutual.
  move : E_Bind h0 h1; repeat move/[apply].
  firstorder.
Qed.

Lemma E_App n Γ (b0 b1 a0 a1 : PTm n) A B :
  Γ ⊢ b0 ≡ b1 ∈ PBind PPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ PApp b0 a0 ≡ PApp b1 a1 ∈ subst_PTm (scons a0 VarPTm) B.
Proof.
  move => h.
  have [i] : exists i, Γ ⊢ PBind PPi A B ∈ PUniv i by hauto l:on use:regularity.
  move : E_App h. by repeat move/[apply].
Qed.

Lemma E_Proj2 n Γ (a b : PTm n) A B :
  Γ ⊢ a ≡ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ≡ PProj PR b ∈ subst_PTm (scons (PProj PL a) VarPTm) B.
Proof.
  move => h.
  have [i] : exists i, Γ ⊢ PBind PSig A B ∈ PUniv i by hauto l:on use:regularity.
  move : E_Proj2 h; by repeat move/[apply].
Qed.
