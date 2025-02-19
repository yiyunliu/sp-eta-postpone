From Equations Require Import Equations.
Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax
  common typing preservation admissible fp_red structural soundness.
Require Import algorithmic.
From stdpp Require Import relations (rtc(..), nsteps(..)).
Require Import ssreflect ssrbool.

Inductive algo_dom {n} : PTm n -> PTm n -> Prop :=
| A_AbsAbs a b :
  algo_dom a b ->
  (* --------------------- *)
  algo_dom (PAbs a) (PAbs b)

| A_AbsNeu a u :
  ishne u ->
  algo_dom a (PApp (ren_PTm shift u) (VarPTm var_zero)) ->
  (* --------------------- *)
  algo_dom (PAbs a) u

| A_NeuAbs a u :
  ishne u ->
  algo_dom (PApp (ren_PTm shift u) (VarPTm var_zero)) a ->
  (* --------------------- *)
  algo_dom u (PAbs a)

| A_PairPair a0 a1 b0 b1 :
  algo_dom a0 a1 ->
  algo_dom b0 b1 ->
  (* ---------------------------- *)
  algo_dom (PPair a0 b0) (PPair a1 b1)

| A_PairNeu a0 a1 u :
  ishne u ->
  algo_dom a0 (PProj PL u) ->
  algo_dom a1 (PProj PR u) ->
  (* ----------------------- *)
  algo_dom (PPair a0 a1) u

| A_NeuPair a0 a1 u :
  ishne u ->
  algo_dom (PProj PL u) a0 ->
  algo_dom (PProj PR u) a1 ->
  (* ----------------------- *)
  algo_dom u (PPair a0 a1)

| A_UnivCong i j :
  (* -------------------------- *)
  algo_dom (PUniv i) (PUniv j)

| A_BindCong p0 p1 A0 A1 B0 B1 :
  algo_dom A0 A1 ->
  algo_dom B0 B1 ->
  (* ---------------------------- *)
  algo_dom (PBind p0 A0 B0) (PBind p1 A1 B1)

| A_VarCong i j :
  (* -------------------------- *)
  algo_dom (VarPTm i) (VarPTm j)

| A_ProjCong p0 p1 u0 u1 :
  ishne u0 ->
  ishne u1 ->
  algo_dom u0 u1 ->
  (* ---------------------  *)
  algo_dom (PProj p0 u0) (PProj p1 u1)

| A_AppCong u0 u1 a0 a1 :
  ishne u0 ->
  ishne u1 ->
  algo_dom u0 u1 ->
  algo_dom a0 a1 ->
  (* ------------------------- *)
  algo_dom (PApp u0 a0) (PApp u1 a1)

| A_HRedL a a' b  :
  HRed.R a a' ->
  algo_dom a' b ->
  (* ----------------------- *)
  algo_dom a b

| A_HRedR a b b'  :
  ishne a \/ ishf a ->
  HRed.R b b' ->
  algo_dom a b' ->
  (* ----------------------- *)
  algo_dom a b.

Search (Bool.reflect (is_true _) _).
Check idP.


Definition metric {n} k (a b : PTm n) :=
  exists i j va vb, nsteps LoRed.R i a va /\ nsteps LoRed.R j b vb /\
  nf va /\ nf vb /\ size_PTm va + size_PTm vb + i + j <= k.

Search (nat -> nat -> bool).

Equations check_equal {n k} (a b : PTm n) (h : metric k a b) :
  bool by wf k lt :=
  check_equal (PAbs a) (PAbs b) h := check_equal a b _;
  check_equal (PPair a0 b0) (PPair a1 b1) h :=
    check_equal a0 b0 _ && check_equal a1 b1 _;
  check_equal (PUniv i) (PUniv j) _ := _;
  check_equal _ _ _ := _.
