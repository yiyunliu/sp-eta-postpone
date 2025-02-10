Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax common typing.
From Hammer Require Import Tactics.
Require Import ssreflect ssrbool.
Require Import Psatz.
From stdpp Require Import relations (rtc(..)).
Require Import Coq.Logic.FunctionalExtensionality.

Module HRed.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a b :
    R (PApp (PAbs a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

  (*************** Congruence ********************)
  | AppCong a0 a1 b :
    R a0 a1 ->
    R (PApp a0 b) (PApp a1 b)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1).
End HRed.

(* Coquand's algorithm with subtyping *)
Reserved Notation "a ⇔ b" (at level 70).
Reserved Notation "a ↔ b" (at level 70).
Reserved Notation "a ≪ b" (at level 70).
Reserved Notation "a ⋖ b" (at level 70).
Inductive CoqEq {n} : PTm n -> PTm n -> Prop :=
| CE_AbsAbs a b :
  a ↔ b ->
  (* --------------------- *)
  PAbs a ⇔ PAbs b

| CE_AbsNeu a u :
  ishne u ->
  a ↔ PApp (ren_PTm shift u) (VarPTm var_zero) ->
  (* --------------------- *)
  PAbs a ⇔ u

| CE_NeuAbs a u :
  ishne u ->
  PApp (ren_PTm shift u) (VarPTm var_zero) ↔ a ->
  (* --------------------- *)
  u ⇔ PAbs a

| CE_PairPair a0 a1 b0 b1 :
  a0 ↔ a1 ->
  b0 ↔ b1 ->
  (* ---------------------------- *)
  PPair a0 b0 ⇔ PPair a1 b1

| CE_PairNeu a0 a1 u :
  ishne u ->
  a0 ↔ PProj PL u ->
  a1 ↔ PProj PR u ->
  (* ----------------------- *)
  PPair a0 a1 ⇔ u

| CE_NeuPair a0 a1 u :
  ishne u ->
  PProj PL u ↔ a0 ->
  PProj PR u ↔ a1 ->
  (* ----------------------- *)
  u ⇔ PPair a0 a1

| CE_ProjCong p u0 u1 :
  ishne u0 ->
  ishne u1 ->
  u0 ⇔ u1 ->
  (* ---------------------  *)
  PProj p u0 ⇔ PProj p u1

| CE_AppCong u0 u1 a0 a1 :
  ishne u0 ->
  ishne u1 ->
  u0 ⇔ u1 ->
  a0 ↔ a1 ->
  (* ------------------------- *)
  PApp u0 a0 ⇔ PApp u1 a1

| CE_VarCong i :
  (* -------------------------- *)
  VarPTm i ⇔ VarPTm i

| CE_UnivCong i :
  (* -------------------------- *)
  PUniv i ⇔ PUniv i

| CE_BindCong p A0 A1 B0 B1 :
  A0 ↔ A1 ->
  B0 ↔ B1 ->
  (* ---------------------------- *)
  PBind p A0 B0 ⇔ PBind p A1 B1

with CoqEq_R {n} : PTm n -> PTm n -> Prop :=
| CE_HRed a a' b b'  :
  rtc HRed.R a a' ->
  rtc HRed.R b b' ->
  a' ⇔ b' ->
  (* ----------------------- *)
  a ↔ b
where "a ⇔ b" := (CoqEq a b) and "a ↔ b" := (CoqEq_R a b).
