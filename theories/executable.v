From Equations Require Import Equations.
Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax
  common typing preservation admissible fp_red structural soundness.
Require Import algorithmic.
From stdpp Require Import relations (rtc(..), nsteps(..)).
Require Import ssreflect ssrbool.

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
