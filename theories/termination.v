Require Import common Autosubst2.core Autosubst2.unscoped Autosubst2.syntax algorithmic fp_red executable.
From Hammer Require Import Tactics.
Require Import ssreflect ssrbool.
From stdpp Require Import relations (nsteps (..)).

Definition term_metric k (a b : PTm) :=
  exists i j va vb, nsteps LoRed.R i a va /\ nsteps LoRed.R j b vb /\ nf va /\ nf vb /\ size_PTm va + size_PTm vb + i + j <= k.

Lemma term_metric_algo_dom : forall k a b, term_metric k a b -> algo_dom_r a b.
Proof.
  elim /Wf_nat.lt_wf_ind.
  move => n ih a b h.
  case : (fancy_hred a); cycle 1.
  move => [a' ha']. apply : A_HRedL; eauto.
