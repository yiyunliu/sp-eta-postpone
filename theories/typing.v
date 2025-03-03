Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common.

Reserved Notation "Γ ⊢ a ∈ A" (at level 70).
Reserved Notation "Γ ⊢ a ≡ b ∈ A" (at level 70).
Reserved Notation "Γ ⊢ A ≲ B" (at level 70).
Reserved Notation "⊢ Γ" (at level 70).
Inductive Wt : list PTm -> PTm -> PTm -> Prop :=
| T_Var i Γ A :
  ⊢ Γ ->
  lookup i Γ A ->
  Γ ⊢ VarPTm i ∈ A

| T_Bind Γ i p (A : PTm) (B : PTm) :
  Γ ⊢ A ∈ PUniv i ->
  cons A Γ ⊢ B ∈ PUniv i ->
  Γ ⊢ PBind p A B ∈ PUniv i

| T_Abs Γ (a : PTm) A B i :
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  (cons A Γ) ⊢ a ∈ B ->
  Γ ⊢ PAbs a ∈ PBind PPi A B

| T_App Γ (b a : PTm) A B :
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ PApp b a ∈ subst_PTm (scons a VarPTm) B

| T_Pair Γ (a b : PTm) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PPair a b ∈ PBind PSig A B

| T_Proj1 Γ (a : PTm) A B :
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PProj PL a ∈ A

| T_Proj2 Γ (a : PTm) A B :
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ∈ subst_PTm (scons (PProj PL a) VarPTm) B

| T_Univ Γ i :
  ⊢ Γ ->
  Γ ⊢ PUniv i ∈ PUniv (S i)

| T_Nat Γ i :
  ⊢ Γ ->
  Γ ⊢ PNat ∈ PUniv i

| T_Zero Γ :
  ⊢ Γ ->
  Γ ⊢ PZero ∈ PNat

| T_Suc Γ (a : PTm) :
  Γ ⊢ a ∈ PNat ->
  Γ ⊢ PSuc a ∈ PNat

| T_Ind Γ P (a : PTm) b c i :
  cons PNat Γ ⊢ P ∈ PUniv i ->
  Γ ⊢ a ∈ PNat ->
  Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P ->
  (cons P (cons PNat Γ)) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊢ PInd P a b c ∈ subst_PTm (scons a VarPTm) P

| T_Conv Γ (a : PTm) A B :
  Γ ⊢ a ∈ A ->
  Γ ⊢ A ≲ B ->
  Γ ⊢ a ∈ B

with Eq : list PTm -> PTm -> PTm -> PTm -> Prop :=
(* Structural *)
| E_Refl Γ (a : PTm ) A :
  Γ ⊢ a ∈ A ->
  Γ ⊢ a ≡ a ∈ A

| E_Symmetric Γ (a b : PTm) A :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ b ≡ a ∈ A

| E_Transitive Γ (a b c : PTm) A :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ b ≡ c ∈ A ->
  Γ ⊢ a ≡ c ∈ A

(* Congruence *)
| E_Bind Γ i p (A0 A1 : PTm) B0 B1 :
  Γ ⊢ A0 ∈ PUniv i ->
  Γ ⊢ A0 ≡ A1 ∈ PUniv i ->
  (cons A0 Γ) ⊢ B0 ≡ B1 ∈ PUniv i ->
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i

| E_Abs Γ (a b : PTm) A B i :
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  (cons A Γ) ⊢ a ≡ b ∈ B ->
  Γ ⊢ PAbs a ≡ PAbs b ∈ PBind PPi A B

| E_App Γ i (b0 b1 a0 a1 : PTm) A B :
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  Γ ⊢ b0 ≡ b1 ∈ PBind PPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ PApp b0 a0 ≡ PApp b1 a1 ∈ subst_PTm (scons a0 VarPTm) B

| E_Pair Γ (a0 a1 b0 b1 : PTm) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ b0 ≡ b1 ∈ subst_PTm (scons a0 VarPTm) B ->
  Γ ⊢ PPair a0 b0 ≡ PPair a1 b1 ∈ PBind PSig A B

| E_Proj1 Γ (a b : PTm) A B :
  Γ ⊢ a ≡ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PL a ≡ PProj PL b ∈ A

| E_Proj2 Γ i (a b : PTm) A B :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ≡ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ≡ PProj PR b ∈ subst_PTm (scons (PProj PL a) VarPTm) B

| E_IndCong Γ P0 P1 (a0 a1 : PTm) b0 b1 c0 c1 i :
  (cons PNat Γ) ⊢ P0 ∈ PUniv i ->
  (cons PNat Γ) ⊢ P0 ≡ P1 ∈ PUniv i ->
  Γ ⊢ a0 ≡ a1 ∈ PNat ->
  Γ ⊢ b0 ≡ b1 ∈ subst_PTm (scons PZero VarPTm) P0 ->
  (cons P0 ((cons PNat Γ))) ⊢ c0 ≡ c1 ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P0) ->
  Γ ⊢ PInd P0 a0 b0 c0 ≡ PInd P1 a1 b1 c1 ∈ subst_PTm (scons a0 VarPTm) P0

| E_SucCong Γ (a b : PTm) :
  Γ ⊢ a ≡ b ∈ PNat ->
  Γ ⊢ PSuc a ≡ PSuc b ∈ PNat

| E_Conv Γ (a b : PTm) A B :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ A ≲ B ->
  Γ ⊢ a ≡ b ∈ B

(* Beta *)
| E_AppAbs Γ (a : PTm) b A B i:
  Γ ⊢ PBind PPi A B ∈ PUniv i ->
  Γ ⊢ b ∈ A ->
  (cons A Γ) ⊢ a ∈ B ->
  Γ ⊢ PApp (PAbs a) b ≡ subst_PTm (scons b VarPTm) a ∈ subst_PTm (scons b VarPTm ) B

| E_ProjPair1 Γ (a b : PTm) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PProj PL (PPair a b) ≡ a ∈ A

| E_ProjPair2 Γ (a b : PTm) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PProj PR (PPair a b) ≡ b ∈ subst_PTm (scons a VarPTm) B

| E_IndZero Γ P i (b : PTm) c :
  (cons PNat Γ) ⊢ P ∈ PUniv i ->
  Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P ->
  (cons P (cons PNat Γ)) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊢ PInd P PZero b c ≡ b ∈ subst_PTm (scons PZero VarPTm) P

| E_IndSuc Γ P (a : PTm) b c i :
  (cons PNat Γ) ⊢ P ∈ PUniv i ->
  Γ ⊢ a ∈ PNat ->
  Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P ->
  (cons P (cons PNat Γ)) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊢ PInd P (PSuc a) b c ≡ (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c) ∈ subst_PTm (scons (PSuc a) VarPTm) P

(* Eta *)
| E_AppEta Γ (b : PTm) A B i :
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ PAbs (PApp (ren_PTm shift b) (VarPTm var_zero)) ≡ b ∈ PBind PPi A B

| E_PairEta Γ (a : PTm ) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ a ≡ PPair (PProj PL a) (PProj PR a) ∈ PBind PSig A B

with LEq : list PTm -> PTm -> PTm -> Prop :=
(* Structural *)
| Su_Transitive Γ (A B C : PTm) :
  Γ ⊢ A ≲ B ->
  Γ ⊢ B ≲ C ->
  Γ ⊢ A ≲ C

(* Congruence *)
| Su_Univ Γ i j :
  ⊢ Γ ->
  i <= j ->
  Γ ⊢ PUniv i ≲ PUniv j

| Su_Pi Γ (A0 A1 : PTm) B0 B1 i :
  Γ ⊢ A0 ∈ PUniv i ->
  Γ ⊢ A1 ≲ A0 ->
  (cons A0 Γ) ⊢ B0 ≲ B1 ->
  Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A1 B1

| Su_Sig Γ (A0 A1 : PTm) B0 B1 i :
  Γ ⊢ A1 ∈ PUniv i ->
  Γ ⊢ A0 ≲ A1 ->
  (cons A1 Γ) ⊢ B0 ≲ B1 ->
  Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A1 B1

(* Injecting from equalities *)
| Su_Eq Γ (A : PTm) B i  :
  Γ ⊢ A ≡ B ∈ PUniv i ->
  Γ ⊢ A ≲ B

(* Projection axioms *)
| Su_Pi_Proj1 Γ (A0 A1 : PTm) B0 B1 :
  Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A1 B1 ->
  Γ ⊢ A1 ≲ A0

| Su_Sig_Proj1 Γ (A0 A1 : PTm) B0 B1 :
  Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A1 B1 ->
  Γ ⊢ A0 ≲ A1

| Su_Pi_Proj2 Γ (a0 a1 A0 A1 : PTm ) B0 B1 :
  Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A1 B1 ->
  Γ ⊢ a0 ≡ a1 ∈ A1 ->
  Γ ⊢ subst_PTm (scons a0 VarPTm) B0 ≲ subst_PTm (scons a1 VarPTm) B1

| Su_Sig_Proj2 Γ (a0 a1 A0 A1 : PTm) B0 B1 :
  Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A1 B1 ->
  Γ ⊢ a0 ≡ a1 ∈ A0 ->
  Γ ⊢ subst_PTm (scons a0 VarPTm) B0 ≲ subst_PTm (scons a1 VarPTm) B1

with Wff : list PTm -> Prop :=
| Wff_Nil :
  ⊢ nil
| Wff_Cons Γ (A : PTm) i :
  ⊢ Γ ->
  Γ ⊢ A ∈ PUniv i ->
  (* -------------------------------- *)
  ⊢ (cons A Γ)

where
"Γ ⊢ a ∈ A" := (Wt Γ a A) and "⊢ Γ" := (Wff Γ) and "Γ ⊢ a ≡ b ∈ A" := (Eq Γ a b A) and "Γ ⊢ A ≲ B" := (LEq Γ A B).

Scheme wf_ind := Induction for Wff Sort Prop
  with wt_ind := Induction for Wt Sort Prop
  with eq_ind := Induction for Eq Sort Prop
  with le_ind := Induction for LEq Sort Prop.

Combined Scheme wt_mutual from wf_ind, wt_ind, eq_ind, le_ind.

(* Lemma lem : *)
(*   (forall n (Γ : fin n -> PTm n), ⊢ Γ -> ...) /\ *)
(*   (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> ...)  /\ *)
(*   (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> ...) /\ *)
(*   (forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> ...). *)
(* Proof. apply wt_mutual. ... *)
