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
Require Import Btauto.

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
  | PInd P a b c => nostuck P && (ishf a ==> iszero a || issuc a) && nostuck b && nostuck c
  | PNat => true
  | PUniv _ => true
  end.


CoInductive safe a : Prop :=
  safe_intro :
    nostuck a ->
    (forall b,RRed.R a b -> safe b) ->
    safe a.

Arguments safe_intro {a}.

Lemma safe_coind P : (forall a, P a -> nostuck a /\  (forall b, RRed.R a b -> P b)) ->  forall a, P a -> safe a.
  move => h.
  cofix ih.
  move => a ha. apply h in ha.
  destruct ha as [ha0 ha1].
  apply safe_intro.
  apply ha0.
  move => b hb. apply ha1 in hb. apply ih. apply hb.
Qed.

Lemma safe_app_inv0  : forall a b, safe (PApp a b) -> safe a.
Proof.
  suff : forall a, (exists b, safe (PApp a b)) -> safe a by firstorder.
  apply safe_coind.
  sauto lqb:on.
Qed.

Lemma safe_app_inv1  : forall a b, safe (PApp a b) -> safe b.
Proof.
  suff : forall b, (exists a, safe (PApp a b)) -> safe b by firstorder.
  apply safe_coind.
  sauto lqb:on.
Qed.

Lemma safe_abs_inv : forall a, safe (PAbs a) -> safe a.
Proof.
  apply safe_coind.
  sauto lqb:on.
Qed.

Lemma nostuck_antisubstitution : forall ρ a, nostuck (subst_PTm ρ a) -> nostuck a.
Proof.
  suff : forall (ρ : nat -> PTm) (a : PTm), nostuck (subst_PTm ρ a) ==> nostuck a by sauto lqb:on.
  move => /[swap]. elim => //=.
  - move => *. rewrite !Bool.implb_orb /is_true. btauto.
  - move => b ihb a iha ρ.
    move /(_ ρ) : ihb. apply /implyP.
    move /(_ ρ) : iha. apply /implyP.
    case : b => //= *; rewrite /is_true !Bool.implb_orb; btauto.
  - move => a iha b ihb ρ.
    move /(_ ρ) : ihb. apply /implyP.
    move /(_ ρ) : iha. apply /implyP.
    rewrite /is_true !Bool.implb_orb; btauto.
  - move => p u hu ρ.
    move /(_ ρ) : hu. apply /implyP.
    case : u => //= *; rewrite /is_true !Bool.implb_orb; btauto.
  - move => _ a iha b ihb ρ.
    move /(_ (up_PTm_PTm ρ)) : ihb. apply /implyP.
    move /(_ ρ) : iha. apply /implyP.
    rewrite /is_true !Bool.implb_orb; btauto.
  - move => P ihP a iha b ihb c ihc ρ.
    move /(_ (up_PTm_PTm ρ)) : ihP. apply /implyP.
    move /(_ ρ) : iha. apply /implyP.
    move /(_ ρ) : ihb. apply /implyP.
    move /(_ (up_PTm_PTm (up_PTm_PTm ρ))) : ihc. apply /implyP.
    case : a => //= *; rewrite /is_true !Bool.implb_orb; btauto.
Qed.

Lemma safe_antisubstitution : forall ρ a, safe (subst_PTm ρ a) -> safe a.
Proof.
  suff : forall a, (exists ρ, safe (subst_PTm ρ a)) -> safe a by firstorder.
  apply safe_coind.
  move => a [ρ ha].
  split.
  have {}ha : nostuck (subst_PTm ρ a) by hauto lq:on inv:safe lq:on.
  by eauto using nostuck_antisubstitution.
  move => b hr. exists ρ.
  inversion ha as [ha0 ha1].
  hauto lq:on use:RRed.substing.
Qed.
