Require Import common Autosubst2.core Autosubst2.unscoped Autosubst2.syntax algorithmic fp_red executable.
From Hammer Require Import Tactics.
Require Import ssreflect ssrbool.
From stdpp Require Import relations (nsteps (..), rtc(..)).
Import Psatz.

Lemma sn_term_metric (a b : PTm) : SN a -> SN b -> exists k, term_metric k a b.
Proof.
  move /LoReds.FromSN => [va [ha0 ha1]].
  move /LoReds.FromSN => [vb [hb0 hb1]].
  eapply relations.rtc_nsteps in ha0.
  eapply relations.rtc_nsteps in hb0.
  hauto lq:on unfold:term_metric solve+:lia.
Qed.

Lemma sn_algo_dom a b : SN a -> SN b -> algo_dom_r a b.
Proof.
  move : sn_term_metric; repeat move/[apply].
  move => [k]+.
  eauto using term_metric_algo_dom.
Qed.
