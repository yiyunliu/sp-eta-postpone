Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.

Reserved Notation "Γ ⊢ a ∈ A" (at level 70).
Reserved Notation "Γ ⊢ a ≡ b ∈ A" (at level 70).
Reserved Notation "Γ ⊢ A ≲ B" (at level 70).
Reserved Notation "⊢ Γ" (at level 70).
Inductive Wt : forall {n}, (fin n -> PTm n) -> PTm n -> PTm n -> Prop :=
| T_Var n Γ (i : fin n) :
  ⊢ Γ ->
  Γ ⊢ VarPTm i ∈ Γ i

| T_Bind n Γ i p (A : PTm n) (B : PTm (S n)) :
  Γ ⊢ A ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A Γ) ⊢ B ∈ PUniv i ->
  Γ ⊢ PBind p A B ∈ PUniv i

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

| T_Univ n Γ i :
  ⊢ Γ ->
  Γ ⊢ PUniv i : PTm n ∈ PUniv (S i)

| T_Nat n Γ i :
  ⊢ Γ ->
  Γ ⊢ PNat : PTm n ∈ PUniv i

| T_Zero n Γ :
  ⊢ Γ ->
  Γ ⊢ PZero : PTm n ∈ PNat

| T_Suc n Γ (a : PTm n) :
  Γ ⊢ a ∈ PNat ->
  Γ ⊢ PSuc a ∈ PNat

| T_Ind s Γ P (a : PTm s) b c i :
  funcomp (ren_PTm shift) (scons PNat Γ) ⊢ P ∈ PUniv i ->
  Γ ⊢ a ∈ PNat ->
  Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P ->
  funcomp (ren_PTm shift)(scons P (funcomp (ren_PTm shift) (scons PNat Γ))) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊢ PInd P a b c ∈ subst_PTm (scons a VarPTm) P

| T_Conv n Γ (a : PTm n) A B :
  Γ ⊢ a ∈ A ->
  Γ ⊢ A ≲ B ->
  Γ ⊢ a ∈ B

with Eq : forall {n}, (fin n -> PTm n) -> PTm n -> PTm n -> PTm n -> Prop :=
(* Structural *)
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

(* Congruence *)
| E_Bind n Γ i p (A0 A1 : PTm n) B0 B1 :
  ⊢ Γ ->
  Γ ⊢ A0 ∈ PUniv i ->
  Γ ⊢ A0 ≡ A1 ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A0 Γ) ⊢ B0 ≡ B1 ∈ PUniv i ->
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i

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

| E_IndCong n Γ P0 P1 (a0 a1 : PTm n) b0 b1 c0 c1 i :
  funcomp (ren_PTm shift) (scons PNat Γ) ⊢ P0 ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons PNat Γ) ⊢ P0 ≡ P1 ∈ PUniv i ->
  Γ ⊢ a0 ≡ a1 ∈ PNat ->
  Γ ⊢ b0 ≡ b1 ∈ subst_PTm (scons PZero VarPTm) P0 ->
  funcomp (ren_PTm shift) (scons P0 (funcomp (ren_PTm shift) (scons PNat Γ))) ⊢ c0 ≡ c1 ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P0) ->
  Γ ⊢ PInd P0 a0 b0 c0 ≡ PInd P1 a1 b1 c1 ∈ subst_PTm (scons a0 VarPTm) P0

| E_SucCong n Γ (a b : PTm n) :
  Γ ⊢ a ≡ b ∈ PNat ->
  Γ ⊢ PSuc a ≡ PSuc b ∈ PNat

| E_Conv n Γ (a b : PTm n) A B :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ A ≲ B ->
  Γ ⊢ a ≡ b ∈ B

(* Beta *)
| E_AppAbs n Γ (a : PTm (S n)) b A B i:
  Γ ⊢ PBind PPi A B ∈ PUniv i ->
  Γ ⊢ b ∈ A ->
  funcomp (ren_PTm shift) (scons A Γ) ⊢ a ∈ B ->
  Γ ⊢ PApp (PAbs a) b ≡ subst_PTm (scons b VarPTm) a ∈ subst_PTm (scons b VarPTm ) B

| E_ProjPair1 n Γ (a b : PTm n) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PProj PL (PPair a b) ≡ a ∈ A

| E_ProjPair2 n Γ (a b : PTm n) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PProj PR (PPair a b) ≡ b ∈ subst_PTm (scons a VarPTm) B

| E_IndZero n Γ P i (b : PTm n) c :
  funcomp (ren_PTm shift) (scons PNat Γ) ⊢ P ∈ PUniv i ->
  Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P ->
  funcomp (ren_PTm shift)(scons P (funcomp (ren_PTm shift) (scons PNat Γ))) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊢ PInd P PZero b c ≡ b ∈ subst_PTm (scons PZero VarPTm) P

| E_IndSuc s Γ P (a : PTm s) b c i :
  funcomp (ren_PTm shift) (scons PNat Γ) ⊢ P ∈ PUniv i ->
  Γ ⊢ a ∈ PNat ->
  Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P ->
  funcomp (ren_PTm shift)(scons P (funcomp (ren_PTm shift) (scons PNat Γ))) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊢ PInd P (PSuc a) b c ≡ (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c) ∈ subst_PTm (scons (PSuc a) VarPTm) P

(* Eta *)
| E_AppEta n Γ (b : PTm n) A B i :
  ⊢ Γ ->
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ PAbs (PApp (ren_PTm shift b) (VarPTm var_zero)) ≡ b ∈ PBind PPi A B

| E_PairEta n Γ (a : PTm n) A B i :
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ a ≡ PPair (PProj PL a) (PProj PR a) ∈ PBind PSig A B

with LEq : forall {n}, (fin n -> PTm n) -> PTm n -> PTm n -> Prop :=
(* Structural *)
| Su_Transitive  n Γ (A B C : PTm n) :
  Γ ⊢ A ≲ B ->
  Γ ⊢ B ≲ C ->
  Γ ⊢ A ≲ C

(* Congruence *)
| Su_Univ n Γ i j :
  ⊢ Γ ->
  i <= j ->
  Γ ⊢ PUniv i : PTm n ≲ PUniv j

| Su_Pi n Γ (A0 A1 : PTm n) B0 B1 i :
  ⊢ Γ ->
  Γ ⊢ A0 ∈ PUniv i ->
  Γ ⊢ A1 ≲ A0 ->
  funcomp (ren_PTm shift) (scons A0 Γ) ⊢ B0 ≲ B1 ->
  Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A1 B1

| Su_Sig n Γ (A0 A1 : PTm n) B0 B1 i :
  ⊢ Γ ->
  Γ ⊢ A1 ∈ PUniv i ->
  Γ ⊢ A0 ≲ A1 ->
  funcomp (ren_PTm shift) (scons A1 Γ) ⊢ B0 ≲ B1 ->
  Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A1 B1

(* Injecting from equalities *)
| Su_Eq n Γ (A : PTm n) B i  :
  Γ ⊢ A ≡ B ∈ PUniv i ->
  Γ ⊢ A ≲ B

(* Projection axioms *)
| Su_Pi_Proj1 n Γ (A0 A1 : PTm n) B0 B1 :
  Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A1 B1 ->
  Γ ⊢ A1 ≲ A0

| Su_Sig_Proj1 n Γ (A0 A1 : PTm n) B0 B1 :
  Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A1 B1 ->
  Γ ⊢ A0 ≲ A1

| Su_Pi_Proj2 n Γ (a0 a1 A0 A1 : PTm n) B0 B1 :
  Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A1 B1 ->
  Γ ⊢ a0 ≡ a1 ∈ A1 ->
  Γ ⊢ subst_PTm (scons a0 VarPTm) B0 ≲ subst_PTm (scons a1 VarPTm) B1

| Su_Sig_Proj2 n Γ (a0 a1 A0 A1 : PTm n) B0 B1 :
  Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A1 B1 ->
  Γ ⊢ a0 ≡ a1 ∈ A0 ->
  Γ ⊢ subst_PTm (scons a0 VarPTm) B0 ≲ subst_PTm (scons a1 VarPTm) B1

with Wff : forall {n}, (fin n -> PTm n) -> Prop :=
| Wff_Nil :
  ⊢ null
| Wff_Cons n Γ (A : PTm n) i :
  ⊢ Γ ->
  Γ ⊢ A ∈ PUniv i ->
  (* -------------------------------- *)
  ⊢ funcomp (ren_PTm shift) (scons A Γ)

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
