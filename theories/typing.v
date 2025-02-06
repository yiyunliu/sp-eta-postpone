Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.

Reserved Notation "Γ ⊢ a ∈ A" (at level 70).
Reserved Notation "Γ ⊢ a ≡ b ∈ A" (at level 70).
Reserved Notation "⊢ Γ" (at level 70).
Inductive Wt {n} : (fin n -> PTm n) -> PTm n -> PTm n -> Prop :=
| T_Var Γ (i : fin n) :
  ⊢ Γ ->
  Γ ⊢ VarPTm i ∈ Γ i

| T_Bind Γ i j p (A : PTm n) (B : PTm (S n)) :
  Γ ⊢ A ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A Γ) ⊢ B ∈ PUniv j ->
  Γ ⊢ PBind p A B ∈ PUniv (max i j)

| T_Abs Γ (a : PTm (S n)) A B i :
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  funcomp (ren_PTm shift) (scons A Γ) ⊢ a ∈ B ->
  Γ ⊢ PAbs a ∈ PBind PPi A B

| T_App Γ (b a : PTm n) A B :
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ PApp b a ∈ subst_PTm (scons a VarPTm) B

| T_Pair Γ (a b : PTm n) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PPair a b ∈ PBind PSig A B

| T_Proj1 Γ (a : PTm n) A B :
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PProj PL a ∈ A

| T_Proj2 Γ (a : PTm n) A B :
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ∈ subst_PTm (scons (PProj PL a) VarPTm) B

| T_Conv Γ (a : PTm n) A B i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ A ≡ B ∈ PUniv i ->
  Γ ⊢ a ∈ B

with Eq {n} : (fin n -> PTm n) -> PTm n -> PTm n -> PTm n -> Prop :=

with Wff {n} : (fin n -> PTm n) -> Prop :=
  where
  "Γ ⊢ a ∈ A" := (Wt Γ a A) and "⊢ Γ" := (Wff Γ) and "Γ ⊢ a ≡ b ∈ A" := (Eq Γ a b A).
