From Ltac2 Require Ltac2.
Import Ltac2.Notations.

Import Ltac2.Control.
Require Import ssreflect ssrbool.
Require Import FunInd.
Require Import Arith.Wf_nat (well_founded_lt_compat).
Require Import Psatz.
From stdpp Require Import relations (rtc (..), rtc_once, rtc_r, sn).
From Hammer Require Import Tactics.
Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common fp_red.

Fixpoint nostuck (a : PTm) :=
  match a with
  | VarPTm i => true
  | PAbs a => nostuck a
  | PApp a b => (ishf a ==> isabs a) && nostuck a && nostuck b
  | PBind _ A B => nostuck A && nostuck B
  | PPair a b => nostuck a && nostuck b
  | PProj _ a => (ishf a ==> ispair a) && nostuck a
  | PZero => true
  | PSuc a => nostuck a
  | PInd P a b c => (ishf a ==> iszero a || issuc a) && nostuck b && nostuck c
  | PNat => true
  | PUniv _ => true
  end.


CoInductive safe a : Prop :=
  safe_intro {safe_ok : nostuck a; safe_red : forall b,RRed.R a b -> safe b}.

Arguments safe_intro {a}.
Arguments safe_ok {a}.
Arguments safe_red {a}.

Lemma safe_coind P : (forall a, P a -> nostuck a /\  (forall b, RRed.R a b -> P b)) ->  forall a, P a -> safe a.
  move => h.
  cofix ih.
  move => a ha. apply h in ha.
  destruct ha as [ha0 ha1].
  apply safe_intro.
  apply ha0.
  move => b hb. apply ha1 in hb. apply ih. apply hb.
Qed.
