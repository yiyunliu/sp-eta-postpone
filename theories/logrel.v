Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.
Require Import fp_red.
From Hammer Require Import Tactics.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.
Require Import Logic.PropExtensionality (propositional_extensionality).
From stdpp Require Import relations (rtc(..), rtc_subrel).
Import Psatz.
Require Import Cdcl.Itauto.

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
  : forall n (P : nat -> PTm n -> (PTm n -> Prop) -> Prop),
       (forall i (A : PTm n), SNe A -> P i A (fun a : PTm n => exists v : PTm n, rtc TRedSN a v /\ SNe v)) ->
       (forall i (p : BTag) (A : PTm n) (B : PTm (S n)) (PA : PTm n -> Prop)
          (PF : PTm n -> (PTm n -> Prop) -> Prop),
        ⟦ A ⟧ i ↘ PA ->
        P i A PA ->
        (forall a : PTm n, PA a -> exists PB : PTm n -> Prop, PF a PB) ->
        (forall (a : PTm n) (PB : PTm n -> Prop), PF a PB -> ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) ->
        (forall (a : PTm n) (PB : PTm n -> Prop), PF a PB -> P i (subst_PTm (scons a VarPTm) B) PB) ->
        P i (PBind p A B) (BindSpace p PA PF)) ->
       (forall i j : nat, j < i ->  (forall A PA, ⟦ A ⟧ j ↘ PA -> P j A PA) -> P i (PUniv j) (fun A => exists PA, ⟦ A ⟧ j ↘ PA)) ->
       (forall i (A A0 : PTm n) (PA : PTm n -> Prop), TRedSN A A0 -> ⟦ A0 ⟧ i ↘ PA -> P i A0 PA -> P i A PA) ->
       forall i (p : PTm n) (P0 : PTm n -> Prop), ⟦ p ⟧ i ↘ P0 -> P i p P0.
Proof.
  move => n P  hSN hBind hUniv hRed.
  elim /Wf_nat.lt_wf_ind => i ih . simp InterpUniv.
  move => A PA. move => h. set I := fun _ => _ in h.
  elim : A PA / h; rewrite -?InterpUnivN_nolt; eauto.
Qed.

Derive Dependent Inversion iinv with (forall n i I (A : PTm n) PA, InterpExt i I A PA) Sort Prop.

Lemma InterpUniv_Ne n i (A : PTm n) :
  SNe A ->
  ⟦ A ⟧ i ↘ (fun a => exists v, rtc TRedSN a v /\ SNe v).
Proof. simp InterpUniv. apply InterpExt_Ne. Qed.

Lemma InterpUniv_Bind n i p A B PA PF :
  ⟦ A : PTm n ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) ->
  ⟦ PBind p A B ⟧ i ↘ BindSpace p PA PF.
Proof. simp InterpUniv. apply InterpExt_Bind. Qed.

Lemma InterpUniv_Univ n i j :
  j < i -> ⟦ PUniv j : PTm n ⟧ i ↘ (fun A => exists PA, ⟦ A ⟧ j ↘ PA).
Proof.
  simp InterpUniv. simpl.
  apply InterpExt_Univ'. by simp InterpUniv.
Qed.

Lemma InterpUniv_Step i n A A0 PA :
  TRedSN A A0 ->
  ⟦ A0 : PTm n ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PA.
Proof. simp InterpUniv. apply InterpExt_Step. Qed.


#[export]Hint Resolve InterpUniv_Bind InterpUniv_Step InterpUniv_Ne InterpUniv_Univ : InterpUniv.

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

Lemma adequacy : forall i n A PA,
   ⟦ A : PTm n ⟧ i ↘ PA ->
  CR PA /\ SN A.
Proof.
  move => + n. apply : InterpUniv_ind.
  - hauto l:on use:N_Exps ctrs:SN,SNe.
  - move => i p A B PA PF hPA [ihA0 ihA1] hTot hRes ihPF.
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
  - hauto l:on ctrs:InterpExt rew:db:InterpUniv.
  - hauto l:on ctrs:SN unfold:CR.
Qed.

Lemma InterpUniv_Steps i n A A0 PA :
  rtc TRedSN A A0 ->
  ⟦ A0 : PTm n ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PA.
Proof. induction 1; hauto l:on use:InterpUniv_Step. Qed.

Lemma InterpUniv_back_clos n i (A : PTm n) PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, TRedSN a b ->
           PA b -> PA a.
Proof.
  move : i A PA . apply : InterpUniv_ind; eauto.
  - hauto q:on ctrs:rtc.
  - move => i p A B PA PF hPA ihPA hTot hRes ihPF a b hr.
    case : p => //=.
    + rewrite /ProdSpace.
    move => hba a0 PB ha hPB.
    suff : TRedSN  (PApp a a0) (PApp b a0) by hauto lq:on.
    apply N_AppL => //=.
    hauto q:on use:adequacy.
    + hauto lq:on ctrs:rtc unfold:SumSpace.
  - hauto l:on use:InterpUniv_Step.
Qed.

Lemma InterpUniv_back_closs n i (A : PTm n) PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, rtc TRedSN a b ->
           PA b -> PA a.
Proof.
  induction 2; hauto lq:on ctrs:rtc use:InterpUniv_back_clos.
Qed.


Lemma InterpUniv_case n i (A : PTm n) PA :
  ⟦ A ⟧ i ↘ PA ->
  exists H, rtc TRedSN A H /\  ⟦ H ⟧ i ↘ PA /\ (SNe H \/ isbind H \/ isuniv H).
Proof.
  move : i A PA. apply InterpUniv_ind => //=.
  hauto lq:on ctrs:rtc use:InterpUniv_Ne.
  hauto l:on use:InterpUniv_Bind.
  hauto l:on use:InterpUniv_Univ.
  hauto lq:on ctrs:rtc.
Qed.

Lemma redsn_preservation_mutual n :
  (forall (a : PTm n) (s : SNe a), forall b, TRedSN a b -> False) /\
    (forall (a : PTm n) (s : SN a), forall b, TRedSN a b -> SN b) /\
  (forall (a b : PTm n) (_ : TRedSN a b), forall c, TRedSN a c -> b = c).
Proof.
  move : n. apply sn_mutual; sauto lq:on rew:off.
Qed.

Lemma redsns_preservation : forall n a b, @SN n a -> rtc TRedSN a b -> SN b.
Proof. induction 2; sfirstorder use:redsn_preservation_mutual ctrs:rtc. Qed.

#[export]Hint Resolve DJoin.sne_bind_noconf DJoin.sne_univ_noconf DJoin.bind_univ_noconf : noconf.

Lemma InterpUniv_SNe_inv n i (A : PTm n) PA :
  SNe A ->
  ⟦ A ⟧ i ↘ PA ->
  PA = (fun a => exists v, rtc TRedSN a v /\ SNe v).
Proof.
  simp InterpUniv.
  hauto lq:on rew:off inv:InterpExt,SNe use:redsn_preservation_mutual.
Qed.

Lemma InterpUniv_Bind_inv n i p A B S :
  ⟦ PBind p A B ⟧ i ↘ S -> exists PA PF,
  ⟦ A : PTm n ⟧ i ↘ PA /\
  (forall a, PA a -> exists PB, PF a PB) /\
  (forall a PB, PF a PB -> ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) /\
  S = BindSpace p PA PF.
Proof. simp InterpUniv.
       inversion 1; try hauto inv:SNe q:on use:redsn_preservation_mutual.
       rewrite -!InterpUnivN_nolt.
       sauto lq:on.
Qed.

Lemma InterpUniv_Univ_inv n i j S :
  ⟦ PUniv j : PTm n ⟧ i ↘ S ->
  S = (fun A => exists PA, ⟦ A ⟧ j ↘ PA) /\ j < i.
Proof.
  simp InterpUniv. inversion 1;
    try hauto inv:SNe use:redsn_preservation_mutual.
  rewrite -!InterpUnivN_nolt. sfirstorder.
  subst. hauto lq:on inv:TRedSN.
Qed.


Lemma InterpUniv_Join n i (A B : PTm n) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ B ⟧ i ↘ PB ->
  DJoin.R A B ->
  PA = PB.
Proof.
  move => hA.
  move : i A PA hA B PB.
  apply : InterpUniv_ind.
  - move => i A hA B PB hPB hAB.
    have [*] : SN B /\ SN A by hauto l:on use:adequacy.
    move /InterpUniv_case : hPB.
    move => [H [/DJoin.FromRedSNs h [h1 h0]]].
    have {hAB} {}h : DJoin.R A H by eauto using DJoin.transitive.
    have {}h0 : SNe H.
    suff : ~ isbind H /\ ~ isuniv H by itauto.
    move : h hA. clear. hauto lq:on db:noconf.
    hauto lq:on use:InterpUniv_SNe_inv.
  - move => i p A B PA PF hPA ihPA hTot hRes ihPF U PU hU.
    have hU' : SN U by hauto l:on use:adequacy.
    move /InterpUniv_case : hU => [H [/DJoin.FromRedSNs h [h1 h0]]] hU.
    have {hU} {}h : DJoin.R (PBind p A B) H by eauto using DJoin.transitive.
    have{h0} : isbind H.
    suff : ~ SNe H /\ ~ isuniv H by itauto.
    have : isbind (PBind p A B) by scongruence.
    hauto l:on use: DJoin.sne_bind_noconf, DJoin.bind_univ_noconf, DJoin.symmetric.
    case : H h1 h => //=.
    move => p0 A0 B0 h0 /DJoin.bind_inj.
    move => [? [hA hB]] _. subst.
    move /InterpUniv_Bind_inv : h0.
    move => [PA0][PF0][hPA0][hTot0][hRes0 ?]. subst.
    have ? : PA0 = PA by qauto l:on. subst.
    have : forall a PB PB', PA a -> PF a PB -> PF0 a PB' -> PB = PB'.
    move => a PB PB' ha hPB hPB'. apply : ihPF; eauto.
    have hj0 : DJoin.R (PAbs B) (PAbs B0) by eauto using DJoin.AbsCong.
    have {}hj0 : DJoin.R (PApp (PAbs B) a) (PApp (PAbs B0) a) by eauto using DJoin.AppCong, DJoin.refl.
    have ? : SN (PApp (PAbs B) a)
      by hauto lq:on rew:off use:N_Exp, N_β, adequacy.
    have ? : SN (PApp (PAbs B0) a)
      by hauto lq:on rew:off use:N_Exp, N_β, adequacy.
    have : DJoin.R (PApp (PAbs B0) a) (subst_PTm (scons a VarPTm) B0)
      by hauto lq:on ctrs:RRed.R use:DJoin.FromRRed0.
    have : DJoin.R (subst_PTm (scons a VarPTm) B) (PApp (PAbs B) a)
      by hauto lq:on ctrs:RRed.R use:DJoin.FromRRed1.
    eauto using DJoin.transitive.

    move => hI.
    case : p0 => //=.
    + rewrite /ProdSpace.
      extensionality b.
      apply propositional_extensionality.
      split.
      move =>  hPF a PB.

      move => a PB hPB.

  - move => i j jlti ih B PB hPB.
    have ? : SN B by hauto l:on use:adequacy.
    move /InterpUniv_case : hPB => [H [/DJoin.FromRedSNs h [h1 h0]]].
    move => hj.
    have {hj}{}h : DJoin.R (PUniv j) H by eauto using DJoin.transitive.
    have {h0} : isuniv H.
    suff : ~ SNe H /\ ~ isbind H by tauto.
    hauto l:on use: DJoin.sne_univ_noconf, DJoin.bind_univ_noconf, DJoin.symmetric.
    case : H h1 h => //=.
    move => j' hPB h _.
    have {}h : j' = j by admit. subst.
    hauto lq:on use:InterpUniv_Univ_inv.
  - move => i A A0 PA hr hPA ihPA B PB hPB hAB.
    have /DJoin.symmetric ? : DJoin.R A A0 by hauto lq:on rew:off ctrs:rtc use:DJoin.FromRedSNs.
    have ? : SN A0 by hauto l:on use:adequacy.
    have ? : SN A by eauto using N_Exp.
    have : DJoin.R A0 B by eauto using DJoin.transitive.
    eauto.
Admitted.
