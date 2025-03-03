Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common typing structural.
From Hammer Require Import Tactics.
Require Import ssreflect.
Require Import Psatz.
Require Import Coq.Logic.FunctionalExtensionality.

Derive Inversion wff_inv with (forall Γ, ⊢ Γ) Sort Prop.

Lemma T_Abs Γ (a : PTm ) A B :
  (cons A Γ) ⊢ a ∈ B ->
  Γ ⊢ PAbs a ∈ PBind PPi A B.
Proof.
  move => ha.
  have [i hB] : exists i, (cons A Γ) ⊢ B ∈ PUniv i by sfirstorder use:regularity.
  have hΓ : ⊢  (cons A Γ) by sfirstorder use:wff_mutual.
  hauto lq:on rew:off inv:Wff use:T_Bind', typing.T_Abs.
Qed.

Lemma E_Bind Γ i p (A0 A1 : PTm) B0 B1 :
  Γ ⊢ A0 ≡ A1 ∈ PUniv i ->
  (cons A0 Γ) ⊢ B0 ≡ B1 ∈ PUniv i ->
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i.
Proof.
  move => h0 h1.
  have : Γ ⊢ A0 ∈ PUniv i by hauto l:on use:regularity.
  have : ⊢ Γ by sfirstorder use:wff_mutual.
  move : E_Bind h0 h1; repeat move/[apply].
  firstorder.
Qed.

Lemma E_App Γ (b0 b1 a0 a1 : PTm ) A B :
  Γ ⊢ b0 ≡ b1 ∈ PBind PPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ PApp b0 a0 ≡ PApp b1 a1 ∈ subst_PTm (scons a0 VarPTm) B.
Proof.
  move => h.
  have [i] : exists i, Γ ⊢ PBind PPi A B ∈ PUniv i by hauto l:on use:regularity.
  move : E_App h. by repeat move/[apply].
Qed.

Lemma E_Proj2 Γ (a b : PTm) A B :
  Γ ⊢ a ≡ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ≡ PProj PR b ∈ subst_PTm (scons (PProj PL a) VarPTm) B.
Proof.
  move => h.
  have [i] : exists i, Γ ⊢ PBind PSig A B ∈ PUniv i by hauto l:on use:regularity.
  move : E_Proj2 h; by repeat move/[apply].
Qed.
