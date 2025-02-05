Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.
Require Import fp_red.
From Hammer Require Import Tactics.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.
Require Import Logic.PropExtensionality (propositional_extensionality).
From stdpp Require Import relations (rtc(..), rtc_subrel).
Import Psatz.

Definition ProdSpace {n} (PA : PTm n -> Prop)
  (PF : PTm n -> (PTm n -> Prop) -> Prop) b : Prop :=
  forall a PB, PA a -> PF a PB -> PB (PApp b a).

Definition SumSpace {n} (PA : PTm n -> Prop)
  (PF : PTm n -> (PTm n -> Prop) -> Prop) t : Prop :=
  (exists v, rtc TRedSN t v /\ SNe v) \/ exists a b, rtc TRedSN t (PPair a b) /\ PA a /\ (forall PB, PF a PB -> PB b).

Definition BindSpace {n} p := if p is PPi then @ProdSpace n else SumSpace.

Reserved Notation "⟦ A ⟧ i ;; I ↘ S" (at level 70).

Inductive InterpExt {n} i (I : nat -> PTm n -> Prop) : PTm n -> (PTm n -> Prop) -> Prop :=
| InterpExt_Ne A :
  SNe A ->
  ⟦ A ⟧ i ;; I ↘ (fun a => exists v, rtc TRedSN a v /\ SNe v)
| InterpExt_Bind p A B PA PF :
  ⟦ A ⟧ i ;; I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ subst_PTm (scons a VarPTm) B ⟧ i ;; I ↘ PB) ->
  ⟦ PBind p A B ⟧ i ;; I ↘ BindSpace p PA PF

| InterpExt_Univ j :
  j < i ->
  ⟦ PUniv j ⟧ i ;; I ↘ (I j)

| InterpExt_Step A A0 PA :
  TRedSN A A0 ->
  ⟦ A0 ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I ↘ PA
where "⟦ A ⟧ i ;; I ↘ S" := (InterpExt i I A S).


Lemma InterpExt_Univ' n i  I j (PF : PTm n -> Prop) :
  PF = I j ->
  j < i ->
  ⟦ PUniv j ⟧ i ;; I ↘ PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Infix "<?" := Compare_dec.lt_dec (at level 60).

Equations InterpUnivN n (i : nat) : PTm n -> (PTm n -> Prop) -> Prop by wf i lt :=
  InterpUnivN n i := @InterpExt n i
                     (fun j A =>
                        match j <? i  with
                        | left _ => exists PA, InterpUnivN n j A PA
                        | right _ => False
                        end).
Arguments InterpUnivN {n}.

Lemma InterpExt_lt_impl n i I I' A (PA : PTm n -> Prop) :
  (forall j, j < i -> I j = I' j) ->
  ⟦ A ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I' ↘ PA.
Proof.
  move => hI h.
  elim : A PA /h.
  - hauto q:on ctrs:InterpExt.
  - hauto lq:on rew:off ctrs:InterpExt.
  - hauto q:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_eq n i I I' A (PA : PTm n -> Prop) :
  (forall j, j < i -> I j = I' j) ->
  ⟦ A ⟧ i ;; I ↘ PA =
  ⟦ A ⟧ i ;; I' ↘ PA.
Proof.
  move => hI. apply propositional_extensionality.
  have : forall j, j < i -> I' j = I j by sfirstorder.
  firstorder using InterpExt_lt_impl.
Qed.

Notation "⟦ A ⟧ i ↘ S" := (InterpUnivN i A S) (at level 70).

Lemma InterpUnivN_nolt n i :
  @InterpUnivN n i = @InterpExt n i (fun j (A : PTm n) => exists PA, ⟦ A ⟧ j ↘ PA).
Proof.
  simp InterpUnivN.
  extensionality A. extensionality PA.
  set I0 := (fun _ => _).
  set I1 := (fun _ => _).
  apply InterpExt_lt_eq.
  hauto q:on.
Qed.

#[export]Hint Rewrite @InterpUnivN_nolt : InterpUniv.

Lemma InterpUniv_ind
     : forall (n i : nat) (P : PTm n -> (PTm n -> Prop) -> Prop),
       (forall A : PTm n, SNe A -> P A (fun a : PTm n => exists v : PTm n, rtc TRedSN a v /\ SNe v)) ->
       (forall (p : BTag) (A : PTm n) (B : PTm (S n)) (PA : PTm n -> Prop)
          (PF : PTm n -> (PTm n -> Prop) -> Prop),
        ⟦ A ⟧ i ↘ PA ->
        P A PA ->
        (forall a : PTm n, PA a -> exists PB : PTm n -> Prop, PF a PB) ->
        (forall (a : PTm n) (PB : PTm n -> Prop), PF a PB -> ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) ->
        (forall (a : PTm n) (PB : PTm n -> Prop), PF a PB -> P (subst_PTm (scons a VarPTm) B) PB) ->
        P (PBind p A B) (BindSpace p PA PF)) ->
       (forall j : nat, j < i -> P (PUniv j) (fun A => exists PA, ⟦ A ⟧ j ↘ PA)) ->
       (forall (A A0 : PTm n) (PA : PTm n -> Prop), TRedSN A A0 -> ⟦ A0 ⟧ i ↘ PA -> P A0 PA -> P A PA) ->
       forall (p : PTm n) (P0 : PTm n -> Prop), ⟦ p ⟧ i ↘ P0 -> P p P0.
Proof.
  elim /Wf_nat.lt_wf_ind => n ih i . simp InterpUniv.
  apply InterpExt_ind.
Qed.

Derive Dependent Inversion iinv with (forall n i I (A : PTm n) PA, InterpExt i I A PA) Sort Prop.

Lemma InterpExt_cumulative n i j I (A : PTm n) PA :
  i <= j ->
   ⟦ A ⟧ i ;; I ↘ PA ->
   ⟦ A ⟧ j ;; I ↘ PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt solve+:(by lia).
Qed.

Lemma InterpUniv_cumulative n i (A : PTm n) PA :
   ⟦ A ⟧ i ↘ PA -> forall j, i <= j ->
   ⟦ A ⟧ j ↘ PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

Definition CR {n} (P : PTm n -> Prop) :=
  (forall a, P a -> SN a) /\
    (forall a, SNe a -> P a).

Lemma N_Exps n (a b : PTm n) :
  rtc TRedSN a b ->
  SN b ->
  SN a.
Proof.
  induction 1; eauto using N_Exp.
Qed.

Lemma adequacy_ext i n I A PA
  (hI0 : forall j,  j < i -> forall a b, (TRedSN a b) ->  I j b -> I j a)
  (hI : forall j, j < i -> CR (I j))
  (h :  ⟦ A : PTm n ⟧ i ;; I ↘ PA) :
  CR PA /\ SN A.
Proof.
  elim : A PA / h.
  - hauto l:on use:N_Exps ctrs:SN,SNe.
  - move => p A B PA PF hPA [ihA0 ihA1] hTot hRes ihPF.
    have hb : PA PBot by hauto q:on ctrs:SNe.
    have hb' : SN PBot by hauto q:on ctrs:SN, SNe.
    rewrite /CR.
    repeat split.
    + case : p =>//=.
      * rewrite /ProdSpace.
        qauto use:SN_AppInv unfold:CR.
      * hauto q:on unfold:SumSpace use:N_SNe, N_Pair,N_Exps.
    + move => a ha.
      case : p=>/=.
      * rewrite /ProdSpace => a0 *.
        suff : SNe (PApp a a0) by sfirstorder.
        hauto q:on use:N_App.
      * sfirstorder.
    + apply N_Bind=>//=.
      have : SN (PApp (PAbs B) PBot).
      apply : N_Exp; eauto using N_β.
      hauto lq:on.
      qauto l:on use:SN_AppInv, SN_NoForbid.P_AbsInv.
  - sfirstorder.
  - hauto l:on ctrs:SN unfold:CR.
Qed.

Lemma InterpExt_Steps i n I A A0 PA :
  rtc TRedSN A A0 ->
  ⟦ A0 : PTm n ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I ↘ PA.
Proof. induction 1; eauto using InterpExt_Step. Qed.

Lemma InterpUniv_Steps i n A A0 PA :
  rtc TRedSN A A0 ->
  ⟦ A0 : PTm n ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PA.
Proof. hauto l:on use:InterpExt_Steps rew:db:InterpUniv. Qed.

Lemma adequacy i n A PA
  (h :  ⟦ A : PTm n ⟧ i ↘ PA) :
  CR PA /\ SN A.
Proof.
  move : i A PA h.
  elim /Wf_nat.lt_wf_ind => i ih A PA.
  simp InterpUniv.
  apply adequacy_ext.
  hauto lq:on ctrs:rtc use:InterpUniv_Steps.
  hauto l:on use:InterpExt_Ne rew:db:InterpUniv.
Qed.

Lemma InterpExt_back_clos n i I (A : PTm n) PA
  (hI1 : forall j, j < i -> CR (I j))
  (hI : forall j,  j < i -> forall a b, TRedSN a b ->  I j b -> I j a) :
    ⟦ A ⟧ i ;; I ↘ PA ->
    forall a b, TRedSN a b ->
           PA b -> PA a.
Proof.
  move => h.
  elim : A PA /h; eauto.
  hauto q:on ctrs:rtc.

  move => p A B PA PF hPA ihPA hTot hRes ihPF a b hr.
  case : p => //=.
  - rewrite /ProdSpace.
    move => hba a0 PB ha hPB.
    suff : TRedSN  (PApp a a0) (PApp b a0) by hauto lq:on.
    apply N_AppL => //=.
    hauto q:on use:adequacy_ext.
  - hauto lq:on ctrs:rtc unfold:SumSpace.
Qed.

Lemma InterpUniv_back_clos n i (A : PTm n) PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, TRedSN a b ->
           PA b -> PA a.
Proof.
  simp InterpUniv. apply InterpExt_back_clos;
  hauto l:on use:adequacy unfold:CR ctrs:InterpExt rew:db:InterpUniv.
Qed.

Lemma InterpUniv_back_closs n i (A : PTm n) PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, rtc TRedSN a b ->
           PA b -> PA a.
Proof.
  induction 2; hauto lq:on ctrs:rtc use:InterpUniv_back_clos.
Qed.

Lemma InterpExt_Join n i I (A B : PTm n) PA PB :
  ⟦ A ⟧ i ;; I ↘ PA ->
  ⟦ B ⟧ i ;; I ↘ PB ->
  DJoin.R A B ->
  PA = PB.
Proof.
