Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.

Reserved Notation "Γ ⊢ a ∈ A" (at level 70).
Reserved Notation "Γ ⊢ a ≡ b ∈ A" (at level 70).
Reserved Notation "⊢ Γ" (at level 70).
Inductive Wt : forall {n}, (fin n -> PTm n) -> PTm n -> PTm n -> Prop :=
| T_Var n Γ (i : fin n) :
  ⊢ Γ ->
  Γ ⊢ VarPTm i ∈ Γ i

| T_Bind n Γ i j p (A : PTm n) (B : PTm (S n)) :
  Γ ⊢ A ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A Γ) ⊢ B ∈ PUniv j ->
  Γ ⊢ PBind p A B ∈ PUniv (max i j)

| T_Abs n Γ (a : PTm (S n)) A B i :
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  funcomp (ren_PTm shift) (scons A Γ) ⊢ a ∈ B ->
  Γ ⊢ PAbs a ∈ PBind PPi A B

| T_App n Γ (b a : PTm n) A B :
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ PApp b a ∈ subst_PTm (scons a VarPTm) B

| T_Pair n Γ (a b : PTm n) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PPair a b ∈ PBind PSig A B

| T_Proj1 n Γ (a : PTm n) A B :
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PProj PL a ∈ A

| T_Proj2 n Γ (a : PTm n) A B :
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ∈ subst_PTm (scons (PProj PL a) VarPTm) B

| T_Univ n Γ i j :
  i < j ->
  Γ ⊢ PUniv i : PTm n ∈ PUniv j

| T_Conv n Γ (a : PTm n) A B i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ A ≡ B ∈ PUniv i ->
  Γ ⊢ a ∈ B

with Eq : forall {n}, (fin n -> PTm n) -> PTm n -> PTm n -> PTm n -> Prop :=
| E_Refl n Γ (a : PTm n) A :
  Γ ⊢ a ∈ A ->
  Γ ⊢ a ≡ a ∈ A

| E_Symmetric n Γ (a b : PTm n) A :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ b ≡ a ∈ A

| E_Transitive n Γ (a b c : PTm n) A :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ b ≡ c ∈ A ->
  Γ ⊢ a ≡ c ∈ A

| E_Bind n Γ i j p (A0 A1 : PTm n) B0 B1 :
  ⊢ Γ ->
  Γ ⊢ A0 ≡ A1 ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A0 Γ) ⊢ B0 ≡ B1 ∈ PUniv j ->
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv (max i j)

| E_Abs n Γ (a b : PTm (S n)) A B i :
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  funcomp (ren_PTm shift) (scons A Γ) ⊢ a ≡ b ∈ B ->
  Γ ⊢ PAbs a ≡ PAbs b ∈ PBind PPi A B

| E_App n Γ i (b0 b1 a0 a1 : PTm n) A B :
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  Γ ⊢ b0 ≡ b1 ∈ PBind PPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ PApp b0 a0 ≡ PApp b1 a1 ∈ subst_PTm (scons a0 VarPTm) B

| E_Pair n Γ (a0 a1 b0 b1 : PTm n) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ b0 ≡ b1 ∈ subst_PTm (scons a0 VarPTm) B ->
  Γ ⊢ PPair a0 b0 ≡ PPair a1 b1 ∈ PBind PSig A B

| E_Proj1 n Γ (a b : PTm n) A B :
  Γ ⊢ a ≡ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PL a ≡ PProj PL b ∈ A

| E_Proj2 n Γ i (a b : PTm n) A B :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ≡ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ≡ PProj PR b ∈ subst_PTm (scons (PProj PL a) VarPTm) B

| E_Conv n Γ (a b : PTm n) A B i :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ B ∈ PUniv i ->
  Γ ⊢ A ≡ B ∈ PUniv i ->
  Γ ⊢ a ≡ b ∈ B

| E_Bind_Proj1 n Γ p (A0 A1 : PTm n) B0 B1 i :
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i ->
  Γ ⊢ A0 ≡ A1 ∈ PUniv i

| E_Bind_Proj2 n Γ p (a0 a1 A0 A1 : PTm n) B0 B1 i :
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i ->
  Γ ⊢ a0 ≡ a1 ∈ A0 ->
  Γ ⊢ subst_PTm (scons a0 VarPTm) B0 ≡ subst_PTm (scons a1 VarPTm) B1 ∈ PUniv i

with Wff : forall {n}, (fin n -> PTm n) -> Prop :=
| Wff_Nil :
  ⊢ null
| Wff_Cons n Γ (A : PTm n) i :
  ⊢ Γ ->
  Γ ⊢ A ∈ PUniv i ->
  (* -------------------------------- *)
  ⊢ funcomp (ren_PTm shift) (scons A Γ)

where
"Γ ⊢ a ∈ A" := (Wt Γ a A) and "⊢ Γ" := (Wff Γ) and "Γ ⊢ a ≡ b ∈ A" := (Eq Γ a b A).

Scheme wf_ind := Induction for Wff Sort Prop
  with wt_ind := Induction for Wt Sort Prop
  with eq_ind := Induction for Eq Sort Prop.

Combined Scheme wt_mutual from wf_ind, wt_ind, eq_ind.
