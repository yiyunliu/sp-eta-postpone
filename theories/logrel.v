Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax.
Require Import common fp_red.
From Hammer Require Import Tactics.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.
Require Import Logic.PropExtensionality (propositional_extensionality).
From stdpp Require Import relations (rtc(..), rtc_subrel).
Import Psatz.


Definition ProdSpace (PA : PTm -> Prop)
  (PF : PTm -> (PTm -> Prop) -> Prop) b : Prop :=
  forall a PB, PA a -> PF a PB -> PB (PApp b a).

Definition SumSpace (PA : PTm -> Prop)
  (PF : PTm -> (PTm -> Prop) -> Prop) t : Prop :=
  (exists v, rtc TRedSN t v /\ SNe v) \/ exists a b, rtc TRedSN t (PPair a b) /\ PA a /\ (forall PB, PF a PB -> PB b).

Definition BindSpace p := if p is PPi then ProdSpace else SumSpace.

Reserved Notation "⟦ A ⟧ i ;; I ↘ S" (at level 70).

Inductive InterpExt i (I : nat -> PTm -> Prop) : PTm -> (PTm -> Prop) -> Prop :=
| InterpExt_Ne A :
  SNe A ->
  ⟦ A ⟧ i ;; I ↘ (fun a => exists v, rtc TRedSN a v /\ SNe v)

| InterpExt_Bind p A B PA PF :
  ⟦ A ⟧ i ;; I ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ subst_PTm (scons a VarPTm) B ⟧ i ;; I ↘ PB) ->
  ⟦ PBind p A B ⟧ i ;; I ↘ BindSpace p PA PF

| InterpExt_Nat :
  ⟦ PNat ⟧ i ;; I ↘ SNat

| InterpExt_Univ j :
  j < i ->
  ⟦ PUniv j ⟧ i ;; I ↘ (I j)

| InterpExt_Step A A0 PA :
  TRedSN A A0 ->
  ⟦ A0 ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I ↘ PA
where "⟦ A ⟧ i ;; I ↘ S" := (InterpExt i I A S).

Lemma InterpExt_Univ' i  I j (PF : PTm -> Prop) :
  PF = I j ->
  j < i ->
  ⟦ PUniv j ⟧ i ;; I ↘ PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Infix "<?" := Compare_dec.lt_dec (at level 60).

Equations InterpUnivN (i : nat) : PTm -> (PTm -> Prop) -> Prop by wf i lt :=
  InterpUnivN i := @InterpExt i
                     (fun j A =>
                        match j <? i  with
                        | left _ => exists PA, InterpUnivN j A PA
                        | right _ => False
                        end).

Lemma InterpExt_lt_impl i I I' A (PA : PTm -> Prop) :
  (forall j, j < i -> I j = I' j) ->
  ⟦ A ⟧ i ;; I ↘ PA ->
  ⟦ A ⟧ i ;; I' ↘ PA.
Proof.
  move => hI h.
  elim : A PA /h.
  - hauto q:on ctrs:InterpExt.
  - hauto lq:on rew:off ctrs:InterpExt.
  - hauto q:on ctrs:InterpExt.
  - hauto q:on ctrs:InterpExt.
  - hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_eq i I I' A (PA : PTm -> Prop) :
  (forall j, j < i -> I j = I' j) ->
  ⟦ A ⟧ i ;; I ↘ PA =
  ⟦ A ⟧ i ;; I' ↘ PA.
Proof.
  move => hI. apply propositional_extensionality.
  have : forall j, j < i -> I' j = I j by sfirstorder.
  firstorder using InterpExt_lt_impl.
Qed.

Notation "⟦ A ⟧ i ↘ S" := (InterpUnivN i A S) (at level 70).

Lemma InterpUnivN_nolt i :
  @InterpUnivN i = @InterpExt i (fun j (A : PTm ) => exists PA, ⟦ A ⟧ j ↘ PA).
Proof.
  simp InterpUnivN.
  extensionality A. extensionality PA.
  apply InterpExt_lt_eq.
  hauto q:on.
Qed.

#[export]Hint Rewrite @InterpUnivN_nolt : InterpUniv.

Lemma InterpUniv_ind
  : forall (P : nat -> PTm -> (PTm -> Prop) -> Prop),
       (forall i (A : PTm), SNe A -> P i A (fun a : PTm => exists v : PTm , rtc TRedSN a v /\ SNe v)) ->
       (forall i (p : BTag) (A : PTm ) (B : PTm ) (PA : PTm  -> Prop)
          (PF : PTm  -> (PTm  -> Prop) -> Prop),
        ⟦ A ⟧ i ↘ PA ->
        P i A PA ->
        (forall a : PTm , PA a -> exists PB : PTm  -> Prop, PF a PB) ->
        (forall (a : PTm ) (PB : PTm  -> Prop), PF a PB -> ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) ->
        (forall (a : PTm ) (PB : PTm  -> Prop), PF a PB -> P i (subst_PTm (scons a VarPTm) B) PB) ->
        P i (PBind p A B) (BindSpace p PA PF)) ->
       (forall i, P i PNat SNat) ->
       (forall i j : nat, j < i ->  (forall A PA, ⟦ A ⟧ j ↘ PA -> P j A PA) -> P i (PUniv j) (fun A => exists PA, ⟦ A ⟧ j ↘ PA)) ->
       (forall i (A A0 : PTm ) (PA : PTm  -> Prop), TRedSN A A0 -> ⟦ A0 ⟧ i ↘ PA -> P i A0 PA -> P i A PA) ->
       forall i (p : PTm ) (P0 : PTm  -> Prop), ⟦ p ⟧ i ↘ P0 -> P i p P0.
Proof.
  move => P  hSN hBind hNat hUniv hRed.
  elim /Wf_nat.lt_wf_ind => i ih . simp InterpUniv.
  move => A PA. move => h. set I := fun _ => _ in h.
  elim : A PA / h; rewrite -?InterpUnivN_nolt; eauto.
Qed.

Derive Dependent Inversion iinv with (forall i I (A : PTm ) PA, InterpExt i I A PA) Sort Prop.

Lemma InterpUniv_Ne i (A : PTm) :
  SNe A ->
  ⟦ A ⟧ i ↘ (fun a => exists v, rtc TRedSN a v /\ SNe v).
Proof. simp InterpUniv. apply InterpExt_Ne. Qed.

Lemma InterpUniv_Bind  i p A B PA PF :
  ⟦ A ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PF a PB -> ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) ->
  ⟦ PBind p A B ⟧ i ↘ BindSpace p PA PF.
Proof. simp InterpUniv. apply InterpExt_Bind. Qed.

Lemma InterpUniv_Univ i j :
  j < i -> ⟦ PUniv j ⟧ i ↘ (fun A => exists PA, ⟦ A ⟧ j ↘ PA).
Proof.
  simp InterpUniv. simpl.
  apply InterpExt_Univ'. by simp InterpUniv.
Qed.

Lemma InterpUniv_Step i A A0 PA :
  TRedSN A A0 ->
  ⟦ A0 ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PA.
Proof. simp InterpUniv. apply InterpExt_Step. Qed.

Lemma InterpUniv_Nat i :
  ⟦ PNat  ⟧ i ↘ SNat.
Proof. simp InterpUniv. apply InterpExt_Nat. Qed.

#[export]Hint Resolve InterpUniv_Bind InterpUniv_Step InterpUniv_Ne InterpUniv_Univ : InterpUniv.

Lemma InterpExt_cumulative i j I (A : PTm ) PA :
  i <= j ->
   ⟦ A ⟧ i ;; I ↘ PA ->
   ⟦ A ⟧ j ;; I ↘ PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt solve+:(by lia).
Qed.

Lemma InterpUniv_cumulative i (A : PTm) PA :
   ⟦ A ⟧ i ↘ PA -> forall j, i <= j ->
   ⟦ A ⟧ j ↘ PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

Definition CR (P : PTm -> Prop) :=
  (forall a, P a -> SN a) /\
    (forall a, SNe a -> P a).

Lemma N_Exps (a b : PTm) :
  rtc TRedSN a b ->
  SN b ->
  SN a.
Proof.
  induction 1; eauto using N_Exp.
Qed.

Lemma CR_SNat : CR SNat.
Proof.
  rewrite /CR.
  split.
  induction 1; hauto q:on ctrs:SN,SNe.
  hauto lq:on ctrs:SNat.
Qed.

Lemma adequacy : forall i A PA,
   ⟦ A ⟧ i ↘ PA ->
  CR PA /\ SN A.
Proof.
  apply : InterpUniv_ind.
  - hauto l:on use:N_Exps ctrs:SN,SNe.
  - move => i p A B PA PF hPA [ihA0 ihA1] hTot hRes ihPF.
    set PBot := (VarPTm var_zero).
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
  - sfirstorder use:CR_SNat.
  - hauto l:on ctrs:InterpExt rew:db:InterpUniv.
  - hauto l:on ctrs:SN unfold:CR.
Qed.

Lemma InterpUniv_Steps i A A0 PA :
  rtc TRedSN A A0 ->
  ⟦ A0 ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PA.
Proof. induction 1; hauto l:on use:InterpUniv_Step. Qed.

Lemma InterpUniv_back_clos i (A : PTm ) PA :
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
  - hauto lq:on ctrs:SNat.
  - hauto l:on use:InterpUniv_Step.
Qed.

Lemma InterpUniv_back_closs i (A : PTm) PA :
    ⟦ A ⟧ i ↘ PA ->
    forall a b, rtc TRedSN a b ->
           PA b -> PA a.
Proof.
  induction 2; hauto lq:on ctrs:rtc use:InterpUniv_back_clos.
Qed.

Lemma InterpUniv_case i (A : PTm) PA :
  ⟦ A ⟧ i ↘ PA ->
  exists H, rtc TRedSN A H /\  ⟦ H ⟧ i ↘ PA /\ (SNe H \/ isbind H \/ isuniv H \/ isnat H).
Proof.
  move : i A PA. apply InterpUniv_ind => //=.
  hauto lq:on ctrs:rtc use:InterpUniv_Ne.
  hauto l:on use:InterpUniv_Bind.
  hauto l:on use:InterpUniv_Nat.
  hauto l:on use:InterpUniv_Univ.
  hauto lq:on ctrs:rtc.
Qed.

Lemma redsn_preservation_mutual :
  (forall (a : PTm) (s : SNe a), forall b, TRedSN a b -> False) /\
    (forall (a : PTm) (s : SN a), forall b, TRedSN a b -> SN b) /\
  (forall (a b : PTm) (_ : TRedSN a b), forall c, TRedSN a c -> b = c).
Proof.
  apply sn_mutual; sauto lq:on rew:off.
Qed.

Lemma redsns_preservation : forall a b, SN a -> rtc TRedSN a b -> SN b.
Proof. induction 2; sfirstorder use:redsn_preservation_mutual ctrs:rtc. Qed.

#[export]Hint Resolve Sub.sne_bind_noconf Sub.sne_univ_noconf Sub.bind_univ_noconf
  Sub.bind_sne_noconf Sub.univ_sne_noconf Sub.univ_bind_noconf Sub.nat_bind_noconf Sub.bind_nat_noconf Sub.sne_nat_noconf Sub.nat_sne_noconf Sub.univ_nat_noconf Sub.nat_univ_noconf: noconf.

Lemma InterpUniv_SNe_inv i (A : PTm) PA :
  SNe A ->
  ⟦ A ⟧ i ↘ PA ->
  PA = (fun a => exists v, rtc TRedSN a v /\ SNe v).
Proof.
  simp InterpUniv.
  hauto lq:on rew:off inv:InterpExt,SNe use:redsn_preservation_mutual.
Qed.

Lemma InterpUniv_Bind_inv i p A B S :
  ⟦ PBind p A B ⟧ i ↘ S -> exists PA PF,
  ⟦ A ⟧ i ↘ PA /\
  (forall a, PA a -> exists PB, PF a PB) /\
  (forall a PB, PF a PB -> ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) /\
  S = BindSpace p PA PF.
Proof. simp InterpUniv.
       inversion 1; try hauto inv:SNe q:on use:redsn_preservation_mutual.
       rewrite -!InterpUnivN_nolt.
       sauto lq:on.
Qed.

Lemma InterpUniv_Nat_inv i S :
  ⟦ PNat  ⟧ i ↘ S -> S = SNat.
Proof.
  simp InterpUniv.
  inversion 1; try hauto inv:SNe q:on use:redsn_preservation_mutual.
  sauto lq:on.
Qed.

Lemma InterpUniv_Univ_inv i j S :
  ⟦ PUniv j ⟧ i ↘ S ->
  S = (fun A => exists PA, ⟦ A ⟧ j ↘ PA) /\ j < i.
Proof.
  simp InterpUniv. inversion 1;
    try hauto inv:SNe use:redsn_preservation_mutual.
  rewrite -!InterpUnivN_nolt. sfirstorder.
  subst. hauto lq:on inv:TRedSN.
Qed.

Lemma bindspace_impl p (PA PA0 : PTm -> Prop) PF PF0 b  :
  (forall x, if p is PPi then (PA0 x -> PA x) else (PA x -> PA0 x)) ->
  (forall (a : PTm ) (PB PB0 : PTm  -> Prop), PA0 a -> PF a PB -> PF0 a PB0 -> (forall x, PB x ->  PB0 x)) ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a, PA0 a -> exists PB0, PF0 a PB0) ->
  (BindSpace p PA PF b -> BindSpace p PA0 PF0 b).
Proof.
  rewrite /BindSpace => hSA h hPF hPF0.
  case : p hSA => /= hSA.
  - rewrite /ProdSpace.
    move => h1 a PB ha hPF'.
    have {}/hPF : PA a by sfirstorder.
    specialize hPF0 with (1 := ha).
    hauto lq:on.
  - rewrite /SumSpace.
    case. sfirstorder.
    move => [a0][b0][h0][h1]h2. right.
    hauto lq:on.
Qed.

Lemma InterpUniv_Sub' i (A B : PTm) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ B ⟧ i ↘ PB ->
  ((Sub.R A B -> forall x, PA x -> PB x) /\
  (Sub.R B A -> forall x, PB x -> PA x)).
Proof.
  move => hA.
  move : i A PA hA B PB.
  apply : InterpUniv_ind.
  - move => i A hA B PB hPB. split.
    + move => hAB a ha.
      have [? ?] : SN B /\ SN A by hauto l:on use:adequacy.
      move /InterpUniv_case : hPB.
      move => [H [/DJoin.FromRedSNs h [h1 h0]]].
      have {h}{}hAB : Sub.R A H by qauto l:on use:Sub.FromJoin, DJoin.symmetric, Sub.transitive.
      have {}h0 : SNe H.
      suff : ~ isbind H /\ ~ isuniv H /\ ~ isnat H by sfirstorder b:on.
      move : hA hAB. clear. hauto lq:on db:noconf.
      move : InterpUniv_SNe_inv h1 h0. repeat move/[apply]. move => ?. subst.
      tauto.
    + move => hAB a ha.
      have [? ?] : SN B /\ SN A by hauto l:on use:adequacy.
      move /InterpUniv_case : hPB.
      move => [H [/DJoin.FromRedSNs h [h1 h0]]].
      have {h}{}hAB : Sub.R H A by qauto l:on use:Sub.FromJoin, DJoin.symmetric, Sub.transitive.
      have {}h0 : SNe H.
      suff : ~ isbind H /\ ~ isuniv H /\ ~ isnat H by sfirstorder b:on.
      move : hAB hA h0. clear. hauto lq:on db:noconf.
      move : InterpUniv_SNe_inv h1 h0. repeat move/[apply]. move => ?. subst.
      tauto.
  - move => i p A B PA PF hPA ihPA hTot hRes ihPF U PU hU. split.
    + have hU' : SN U by hauto l:on use:adequacy.
      move /InterpUniv_case : hU => [H [/DJoin.FromRedSNs h [h1 h0]]] hU.
      have {hU} {}h : Sub.R (PBind p A B) H
        by move : hU hU' h; clear; hauto q:on use:Sub.FromJoin, DJoin.symmetric, Sub.transitive.
      have{h0} : isbind H.
      suff : ~ SNe H /\ ~ isuniv H /\ ~ isnat H by sfirstorder b:on.
      have : isbind (PBind p A B) by scongruence.
      move : h. clear. hauto l:on db:noconf.
      case : H h1 h => //=.
      move => p0 A0 B0 h0 /Sub.bind_inj.
      move => [? [hA hB]] _. subst.
      move /InterpUniv_Bind_inv : h0.
      move => [PA0][PF0][hPA0][hTot0][hRes0 ?]. subst.
      move => x. apply bindspace_impl; eauto;[idtac|idtac]. hauto l:on.
      move => a PB PB' ha hPB hPB'.
      move : hRes0 hPB'. repeat move/[apply].
      move : ihPF hPB. repeat move/[apply].
      move => h. eapply h.
      apply Sub.cong => //=; eauto using DJoin.refl.
    + have hU' : SN U by hauto l:on use:adequacy.
      move /InterpUniv_case : hU => [H [/DJoin.FromRedSNs h [h1 h0]]] hU.
      have {hU} {}h : Sub.R H (PBind p A B)
        by move : hU hU' h; clear; hauto q:on use:Sub.FromJoin, DJoin.symmetric, Sub.transitive.
      have{h0} : isbind H.
      suff : ~ SNe H /\ ~ isuniv H /\ ~ isnat H by sfirstorder b:on.
      have : isbind (PBind p A B) by scongruence.
      move : h. clear. move : (PBind p A B). hauto lq:on db:noconf.
      case : H h1 h => //=.
      move => p0 A0 B0 h0 /Sub.bind_inj.
      move => [? [hA hB]] _. subst.
      move /InterpUniv_Bind_inv : h0.
      move => [PA0][PF0][hPA0][hTot0][hRes0 ?]. subst.
      move => x. apply bindspace_impl; eauto;[idtac|idtac]. hauto l:on.
      move => a PB PB' ha hPB hPB'.
      eapply ihPF; eauto.
      apply Sub.cong => //=; eauto using DJoin.refl.
  - move =>  i B PB h. split.
    + move => hAB a ha.
      have ? : SN B by hauto l:on use:adequacy.
      move /InterpUniv_case : h.
      move => [H [/DJoin.FromRedSNs h [h1 h0]]].
      have {h}{}hAB : Sub.R PNat H by qauto l:on use:Sub.FromJoin, DJoin.symmetric, Sub.transitive.
      have {}h0 : isnat H.
      suff : ~ isbind H /\ ~ isuniv H /\ ~ SNe H by sfirstorder b:on.
      have : @isnat PNat by simpl.
      move : h0 hAB. clear. qauto l:on db:noconf.
      case : H h1 hAB h0 => //=.
      move /InterpUniv_Nat_inv. scongruence.
    + move => hAB a ha.
      have ? : SN B by hauto l:on use:adequacy.
      move /InterpUniv_case : h.
      move => [H [/DJoin.FromRedSNs h [h1 h0]]].
      have {h}{}hAB : Sub.R H PNat by qauto l:on use:Sub.FromJoin, DJoin.symmetric, Sub.transitive.
      have {}h0 : isnat H.
      suff : ~ isbind H /\ ~ isuniv H /\ ~ SNe H by sfirstorder b:on.
      have : @isnat PNat by simpl.
      move : h0 hAB. clear. qauto l:on db:noconf.
      case : H h1 hAB h0 => //=.
      move /InterpUniv_Nat_inv. scongruence.
  - move => i j jlti ih B PB hPB. split.
    + have ? : SN B by hauto l:on use:adequacy.
      move /InterpUniv_case : hPB => [H [/DJoin.FromRedSNs h [h1 h0]]].
      move => hj.
      have {hj}{}h : Sub.R (PUniv j) H by eauto using Sub.transitive, Sub.FromJoin.
      have {h0} : isuniv H.
      suff : ~ SNe H /\ ~ isbind H /\ ~ isnat H by tauto. move : h. clear. hauto lq:on db:noconf.
      case : H h1 h => //=.
      move => j' hPB h _.
      have {}h : j <= j' by hauto lq:on use: Sub.univ_inj. subst.
      move /InterpUniv_Univ_inv : hPB => [? ?]. subst.
      have ? : j <= i by lia.
      move => A. hauto l:on use:InterpUniv_cumulative.
    + have ? : SN B by hauto l:on use:adequacy.
      move /InterpUniv_case : hPB => [H [/DJoin.FromRedSNs h [h1 h0]]].
      move => hj.
      have {hj}{}h : Sub.R H (PUniv j) by eauto using Sub.transitive, Sub.FromJoin, DJoin.symmetric.
      have {h0} : isuniv H.
      suff : ~ SNe H /\ ~ isbind H /\ ~ isnat H by tauto. move : h. clear. hauto lq:on db:noconf.
      case : H h1 h => //=.
      move => j' hPB h _.
      have {}h : j' <= j by hauto lq:on use: Sub.univ_inj.
      move /InterpUniv_Univ_inv : hPB => [? ?]. subst.
      move => A. hauto l:on use:InterpUniv_cumulative.
  - move => i A A0 PA hr hPA ihPA B PB hPB.
    have ? : SN A by sauto lq:on use:adequacy.
    split.
    + move => ?.
      have {}hr : Sub.R A0 A by hauto lq:on  ctrs:rtc use:DJoin.FromRedSNs, DJoin.symmetric, Sub.FromJoin.
      have : Sub.R A0 B by eauto using Sub.transitive.
      qauto l:on.
    + move => ?.
      have {}hr : Sub.R A A0 by hauto lq:on  ctrs:rtc use:DJoin.FromRedSNs, DJoin.symmetric, Sub.FromJoin.
      have : Sub.R B A0 by eauto using Sub.transitive.
      qauto l:on.
Qed.

Lemma InterpUniv_Sub0 i (A B : PTm) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ B ⟧ i ↘ PB ->
  Sub.R A B -> forall x, PA x -> PB x.
Proof.
  move : InterpUniv_Sub'. repeat move/[apply].
  move => [+ _]. apply.
Qed.

Lemma InterpUniv_Sub i j (A B : PTm) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ B ⟧ j ↘ PB ->
  Sub.R A B -> forall x, PA x -> PB x.
Proof.
  have [? ?] : i <= max i j /\ j <= max i j by lia.
  move => hPA hPB.
  have : ⟦ B ⟧ (max i j) ↘ PB by eauto using InterpUniv_cumulative.
  have : ⟦ A ⟧ (max i j) ↘ PA by eauto using InterpUniv_cumulative.
  move : InterpUniv_Sub0. repeat move/[apply].
  apply.
Qed.

Lemma InterpUniv_Join i (A B : PTm) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ B ⟧ i ↘ PB ->
  DJoin.R A B ->
  PA = PB.
Proof.
  move => + + /[dup] /Sub.FromJoin + /DJoin.symmetric /Sub.FromJoin.
  move : InterpUniv_Sub'; repeat move/[apply]. move => h.
  move => h1 h2.
  extensionality x.
  apply propositional_extensionality.
  firstorder.
Qed.

Lemma InterpUniv_Functional i  (A : PTm) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PB ->
  PA = PB.
Proof. hauto l:on use:InterpUniv_Join, DJoin.refl. Qed.

Lemma InterpUniv_Join' i j (A B : PTm) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ B ⟧ j ↘ PB ->
  DJoin.R A B ->
  PA = PB.
Proof.
  have [? ?] : i <= max i j /\ j <= max i j by lia.
  move => hPA hPB.
  have : ⟦ A ⟧ (max i j) ↘ PA by eauto using InterpUniv_cumulative.
  have : ⟦ B ⟧ (max i j) ↘ PB by eauto using InterpUniv_cumulative.
  eauto using InterpUniv_Join.
Qed.

Lemma InterpUniv_Functional' i j A PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ A ⟧ j ↘ PB ->
  PA = PB.
Proof.
  hauto l:on use:InterpUniv_Join', DJoin.refl.
Qed.

Lemma InterpUniv_Bind_inv_nopf i p A B P (h :  ⟦PBind p A B ⟧ i ↘ P) :
  exists (PA : PTm -> Prop),
     ⟦ A ⟧ i ↘ PA /\
    (forall a, PA a -> exists PB, ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) /\
      P = BindSpace p PA (fun a PB => ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB).
Proof.
  move /InterpUniv_Bind_inv : h.
  move => [PA][PF][hPA][hPF][hPF']?. subst.
  exists PA. repeat split => //.
  - sfirstorder.
  - extensionality b.
    case : p => /=.
    + extensionality a.
      extensionality PB.
      extensionality ha.
      apply propositional_extensionality.
      split.
      * move => h hPB.  apply h.
        have {}/hPF := ha.
        move => [PB0 hPB0].
        have {}/hPF' := hPB0 => ?.
        have : PB = PB0 by hauto l:on use:InterpUniv_Functional.
        congruence.
      * sfirstorder.
    + rewrite /SumSpace. apply propositional_extensionality.
      split; hauto q:on use:InterpUniv_Functional.
Qed.

Definition ρ_ok (Γ : list PTm) (ρ : nat -> PTm) := forall i k A PA,
    lookup i Γ A ->
    ⟦ subst_PTm ρ A ⟧ k ↘ PA -> PA (ρ i).

Definition SemWt Γ (a A : PTm) := forall ρ, ρ_ok Γ ρ -> exists k PA, ⟦ subst_PTm ρ A ⟧ k ↘ PA /\ PA (subst_PTm ρ a).
Notation "Γ ⊨ a ∈ A" := (SemWt Γ a A) (at level 70).

Definition SemEq Γ (a b A : PTm) := DJoin.R a b /\ forall ρ, ρ_ok Γ ρ -> exists k PA, ⟦ subst_PTm ρ A ⟧ k ↘ PA /\ PA (subst_PTm ρ a) /\ PA (subst_PTm ρ b).
Notation "Γ ⊨ a ≡ b ∈ A" := (SemEq Γ a b A) (at level 70).

Definition SemLEq Γ (A B : PTm) := Sub.R A B /\ exists i, forall ρ, ρ_ok Γ ρ -> exists S0 S1, ⟦ subst_PTm ρ A ⟧ i ↘ S0 /\ ⟦ subst_PTm ρ B ⟧ i ↘ S1.
Notation "Γ ⊨ a ≲ b" := (SemLEq Γ a b) (at level 70).

Lemma SemWt_Univ Γ (A : PTm) i  :
  Γ ⊨ A ∈ PUniv i <->
  forall ρ, ρ_ok Γ ρ -> exists S, ⟦ subst_PTm ρ A ⟧ i ↘ S.
Proof.
  rewrite /SemWt.
  split.
  - hauto lq:on rew:off use:InterpUniv_Univ_inv.
  - move => /[swap] ρ /[apply].
    move => [PA hPA].
    exists (S i). eexists.
    split.
    + simp InterpUniv. apply InterpExt_Univ. lia.
    + simpl. eauto.
Qed.

Lemma SemEq_SemWt Γ (a b A : PTm) : Γ ⊨ a ≡ b ∈ A -> Γ ⊨ a ∈ A /\ Γ ⊨ b ∈ A /\ DJoin.R a b.
Proof. hauto lq:on rew:off unfold:SemEq, SemWt. Qed.

Lemma SemLEq_SemWt Γ (A B : PTm) : Γ ⊨ A ≲ B -> Sub.R A B /\ exists i, Γ ⊨ A ∈ PUniv i /\ Γ ⊨ B ∈ PUniv i.
Proof. hauto q:on use:SemWt_Univ. Qed.

Lemma SemWt_SemEq Γ (a b A : PTm) : Γ ⊨ a ∈ A -> Γ ⊨ b ∈ A -> (DJoin.R a b) -> Γ ⊨ a ≡ b ∈ A.
Proof.
  move => ha hb heq. split => //= ρ hρ.
  have {}/ha := hρ.
  have {}/hb := hρ.
  move => [k][PA][hPA]hpb.
  move => [k0][PA0][hPA0]hpa.
  have : PA = PA0 by hauto l:on use:InterpUniv_Functional'.
  hauto lq:on.
Qed.

Lemma SemWt_SemLEq Γ (A B : PTm) i j :
  Γ ⊨ A ∈ PUniv i -> Γ ⊨ B ∈ PUniv j -> Sub.R A B -> Γ ⊨ A ≲ B.
Proof.
  move => ha hb heq. split => //.
  exists (Nat.max i j).
  have [? ?] : i <= Nat.max i j /\ j <= Nat.max i j by lia.
  move => ρ hρ.
  have {}/ha := hρ.
  have {}/hb := hρ.
  move => [k][PA][/= /InterpUniv_Univ_inv [? hPA]]hpb.
  move => [k0][PA0][/= /InterpUniv_Univ_inv [? hPA0]]hpa. subst.
  move : hpb => [PA]hPA'.
  move : hpa => [PB]hPB'.
  exists PB, PA.
  split; apply : InterpUniv_cumulative; eauto.
Qed.

Lemma ρ_ok_id Γ :
  ρ_ok Γ VarPTm.
Proof.
  rewrite /ρ_ok.
  hauto q:on use:adequacy ctrs:SNe.
Qed.

Lemma ρ_ok_cons i Γ ρ a PA A :
  ⟦ subst_PTm ρ A ⟧ i ↘ PA -> PA a ->
  ρ_ok Γ ρ ->
  ρ_ok (cons A Γ) (scons a ρ).
Proof.
  move => h0 h1 h2.
  rewrite /ρ_ok.
  case => [|j]; cycle 1.
  - move => m PA0. asimpl => ?.
    inversion 1; subst; asimpl.
    hauto lq:on unfold:ρ_ok.
  - move => m A0 PA0.
    inversion 1; subst. asimpl => h.
    have ? : PA0 = PA by eauto using InterpUniv_Functional'.
    by subst.
Qed.

Lemma ρ_ok_cons' i Γ ρ a PA A  Δ :
  Δ = (cons A Γ) ->
  ⟦ subst_PTm ρ A ⟧ i ↘ PA -> PA a ->
  ρ_ok Γ ρ ->
  ρ_ok Δ (scons a ρ).
Proof. move => ->. apply ρ_ok_cons. Qed.

Lemma ρ_ok_renaming (Γ : list PTm) ρ :
  forall (Δ : list PTm) ξ,
    renaming_ok Γ Δ ξ ->
    ρ_ok Γ ρ ->
    ρ_ok Δ (funcomp ρ ξ).
Proof.
  move => Δ ξ hξ hρ.
  rewrite /ρ_ok => i m' A PA.
  rewrite /renaming_ok in hξ.
  rewrite /ρ_ok in hρ.
  move => PA0 h.
  rewrite /funcomp.
  eapply hρ with (k := m'); eauto.
  move : h. by asimpl.
Qed.

Lemma renaming_SemWt Γ a A :
  Γ ⊨ a ∈ A ->
  forall Δ (ξ : nat -> nat),
    renaming_ok Δ Γ ξ ->
    Δ ⊨ ren_PTm ξ a ∈ ren_PTm ξ A.
Proof.
  rewrite /SemWt => h  Δ ξ hξ ρ hρ.
  have /h hρ' : (ρ_ok Γ (funcomp ρ ξ)) by eauto using ρ_ok_renaming.
  hauto q:on solve+:(by asimpl).
Qed.

Definition smorphing_ok Δ Γ ρ :=
  forall ξ, ρ_ok Δ ξ -> ρ_ok Γ (funcomp (subst_PTm ξ) ρ).

Lemma smorphing_ok_refl Δ : smorphing_ok Δ Δ VarPTm.
  rewrite /smorphing_ok => ξ. apply.
Qed.

Lemma smorphing_ren Ξ Δ Γ
  (ρ : nat -> PTm) (ξ : nat -> nat) :
  renaming_ok Ξ Δ ξ -> smorphing_ok Δ Γ ρ ->
  smorphing_ok Ξ Γ (funcomp (ren_PTm ξ) ρ).
Proof.
  move => hξ hρ τ.
  move /ρ_ok_renaming : hξ => /[apply].
  move => h.
  rewrite /smorphing_ok in hρ.
  asimpl.
  Check (funcomp τ ξ).
  set u := funcomp _ _.
  have : u = funcomp (subst_PTm (funcomp τ ξ)) ρ.
  subst u. extensionality i. by asimpl.
  move => ->. by apply hρ.
Qed.

Lemma smorphing_ext Δ Γ (ρ : nat -> PTm) (a : PTm) (A : PTm)  :
  smorphing_ok Δ Γ ρ ->
  Δ ⊨ a ∈ subst_PTm ρ A ->
  smorphing_ok
    Δ (cons A Γ) (scons a ρ).
Proof.
  move => h ha τ. move => /[dup] hτ.
  move : ha => /[apply].
  move => [k][PA][h0]h1.
  apply h in hτ.
  case => [|i]; cycle 1.
  - move => k0 A0 PA0. asimpl. rewrite {2}/funcomp.
    asimpl. elim /lookup_inv => //= _.
    move => i0 Γ0 A1 B + [?][? ?]?. subst.
    asimpl.
    move : hτ; by repeat move/[apply].
  - move => k0 A0 PA0. asimpl. rewrite {2}/funcomp. asimpl.
    elim /lookup_inv => //=_ A1 Γ0 _ [? ?] ?. subst. asimpl.
    move => *. suff : PA0 = PA by congruence.
    move : h0. asimpl.
    eauto using InterpUniv_Functional'.
Qed.

Lemma morphing_SemWt : forall Γ (a A : PTm ),
    Γ ⊨ a ∈ A -> forall  Δ (ρ : nat -> PTm ),
      smorphing_ok Δ Γ ρ -> Δ ⊨ subst_PTm ρ a ∈ subst_PTm ρ A.
Proof.
  move => Γ a A ha Δ ρ hρ τ hτ.
  have {}/hρ {}/ha := hτ.
  asimpl. eauto.
Qed.

Lemma morphing_SemWt_Univ : forall Γ (a : PTm) i,
    Γ ⊨ a ∈ PUniv i -> forall Δ (ρ : nat -> PTm),
      smorphing_ok Δ Γ ρ -> Δ ⊨ subst_PTm ρ a ∈ PUniv i.
Proof.
  move => Γ a i ha Δ ρ.
  have -> : PUniv i = subst_PTm ρ (PUniv i) by reflexivity.
  by apply morphing_SemWt.
Qed.

Lemma weakening_Sem Γ (a : PTm) A B i
  (h0 : Γ ⊨ B ∈ PUniv i)
  (h1 : Γ ⊨ a ∈ A) :
   (cons B Γ) ⊨ ren_PTm shift a ∈ ren_PTm shift A.
Proof.
  apply : renaming_SemWt; eauto.
  hauto lq:on ctrs:lookup unfold:renaming_ok.
Qed.

Lemma weakening_Sem_Univ Γ (a : PTm) B i j
  (h0 : Γ ⊨ B ∈ PUniv i)
  (h1 : Γ ⊨ a ∈ PUniv j) :
   (cons B Γ) ⊨ ren_PTm shift a ∈ PUniv j.
Proof.
  move : weakening_Sem h0 h1; repeat move/[apply]. done.
Qed.

Reserved Notation "⊨ Γ"  (at level 70).

Inductive SemWff : list PTm -> Prop :=
| SemWff_nil :
  ⊨ nil
| SemWff_cons Γ A i :
  ⊨ Γ ->
  Γ ⊨ A ∈ PUniv i ->
  (* -------------- *)
  ⊨ (cons A Γ)
where "⊨ Γ" := (SemWff Γ).

(* Semantic context wellformedness *)
Lemma SemWff_lookup Γ :
  ⊨ Γ ->
  forall (i : nat) A, lookup i Γ A -> exists j, Γ ⊨ A ∈ PUniv j.
Proof.
  move => h. elim : Γ / h.
  - by inversion 1.
  - move => Γ A i hΓ ihΓ hA  j B.
    elim /lookup_inv => //=_.
    + move => ? ? ? [*]. subst.
      eauto using weakening_Sem_Univ.
    + move => i0 Γ0 A0 B0 hl ? [*]. subst.
      move : ihΓ hl => /[apply]. move => [j hA0].
      eauto using weakening_Sem_Univ.
Qed.

Lemma SemWt_SN Γ (a : PTm) A :
  Γ ⊨ a ∈ A ->
  SN a /\ SN A.
Proof.
  move => h.
  have {}/h := ρ_ok_id  Γ => h.
  have : SN (subst_PTm VarPTm A) by hauto l:on use:adequacy.
  have : SN (subst_PTm VarPTm a)by hauto l:on use:adequacy.
  by asimpl.
Qed.

Lemma SemEq_SN_Join Γ (a b A : PTm) :
  Γ ⊨ a ≡ b ∈ A ->
  SN a /\ SN b /\ SN A /\ DJoin.R a b.
Proof. hauto l:on use:SemEq_SemWt, SemWt_SN. Qed.

Lemma SemLEq_SN_Sub Γ (a b : PTm) :
  Γ ⊨ a ≲ b ->
  SN a /\ SN b /\ Sub.R a b.
Proof. hauto l:on use:SemLEq_SemWt, SemWt_SN. Qed.

(* Semantic typing rules *)
Lemma ST_Var' Γ (i : nat) A j :
  lookup i Γ A ->
  Γ ⊨ A ∈ PUniv j ->
  Γ ⊨ VarPTm i ∈ A.
Proof.
  move => hl /SemWt_Univ h.
  rewrite /SemWt => ρ /[dup] hρ {}/h [S hS].
  exists j,S.
  asimpl. hauto q:on unfold:ρ_ok.
Qed.

Lemma ST_Var Γ (i : nat) A :
  ⊨ Γ ->
  lookup i Γ A ->
  Γ ⊨ VarPTm i ∈ A.
Proof. hauto l:on use:ST_Var', SemWff_lookup. Qed.

Lemma InterpUniv_Bind_nopf p i (A : PTm) B PA :
  ⟦ A ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) ->
  ⟦ PBind p A B ⟧ i ↘ (BindSpace p PA (fun a PB => ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB)).
Proof.
  move => h0 h1. apply InterpUniv_Bind => //=.
Qed.


Lemma ST_Bind' Γ i j p (A : PTm) (B : PTm) :
  Γ ⊨ A ∈ PUniv i ->
  (cons A Γ) ⊨ B ∈ PUniv j ->
  Γ ⊨ PBind p A B ∈ PUniv (max i j).
Proof.
  move => /SemWt_Univ h0 /SemWt_Univ h1.
  apply SemWt_Univ => ρ hρ.
  move /h0 : (hρ){h0} => [S hS].
  eexists => /=.
  have ? : i <= Nat.max i j by lia.
  apply InterpUniv_Bind_nopf; eauto.
  - eauto using InterpUniv_cumulative.
  - move => *. asimpl. hauto l:on use:InterpUniv_cumulative, ρ_ok_cons.
Qed.

Lemma ST_Bind Γ i p (A : PTm) (B : PTm) :
  Γ ⊨ A ∈ PUniv i ->
  cons A Γ ⊨ B ∈ PUniv i ->
  Γ ⊨ PBind p A B ∈ PUniv i.
Proof.
  move => h0 h1.
  replace i with (max i i) by lia.
  move : h0 h1.
  apply ST_Bind'.
Qed.

Lemma ST_Abs Γ (a : PTm) A B i :
  Γ ⊨ PBind PPi A B ∈ (PUniv i) ->
  (cons A Γ) ⊨ a ∈ B ->
  Γ ⊨ PAbs a ∈ PBind PPi A B.
Proof.
  rename a into b.
  move /SemWt_Univ => + hb ρ hρ.
  move /(_ _ hρ) => [PPi hPPi].
  exists i, PPi. split => //.
  simpl in hPPi.
  move /InterpUniv_Bind_inv_nopf : hPPi.
  move => [PA [hPA [hTot ?]]]. subst=>/=.
  move => a PB ha. asimpl => hPB.
  move : ρ_ok_cons (hPA) (hρ) (ha). repeat move/[apply].
  move /hb.
  intros (m & PB0 & hPB0 & hPB0').
  replace PB0 with PB in * by hauto l:on use:InterpUniv_Functional'.
  apply : InterpUniv_back_clos; eauto.
  apply N_β'. by asimpl.
  move : ha hPA. clear. hauto q:on use:adequacy.
Qed.

Lemma ST_App Γ (b a : PTm) A B :
  Γ ⊨ b ∈ PBind PPi A B ->
  Γ ⊨ a ∈ A ->
  Γ ⊨ PApp b a ∈ subst_PTm (scons a VarPTm) B.
Proof.
  move => hf hb ρ hρ.
  move /(_ ρ hρ) : hf; intros (i & PPi & hPi & hf).
  move /(_ ρ hρ) : hb; intros (j & PA & hPA & hb).
  simpl in hPi.
  move /InterpUniv_Bind_inv_nopf : hPi. intros (PA0 & hPA0 & hTot & ?). subst.
  have ? : PA0 = PA by eauto using InterpUniv_Functional'. subst.
  move  : hf (hb). move/[apply].
  move : hTot hb. move/[apply].
  asimpl. hauto lq:on.
Qed.

Lemma ST_App' Γ (b a : PTm) A B U :
  U = subst_PTm (scons a VarPTm) B ->
  Γ ⊨ b ∈ PBind PPi A B ->
  Γ ⊨ a ∈ A ->
  Γ ⊨ PApp b a ∈ U.
Proof. move => ->. apply ST_App. Qed.

Lemma ST_Pair Γ (a b : PTm) A B i :
  Γ ⊨ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊨ a ∈ A ->
  Γ ⊨ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊨ PPair a b ∈ PBind PSig A B.
Proof.
  move /SemWt_Univ => + ha hb ρ hρ.
  move /(_ _ hρ) => [PPi hPPi].
  exists i, PPi. split => //.
  simpl in hPPi.
  move /InterpUniv_Bind_inv_nopf : hPPi.
  move => [PA [hPA [hTot ?]]]. subst=>/=.
  rewrite /SumSpace. right.
  exists (subst_PTm ρ a), (subst_PTm ρ b).
  split.
  - apply rtc_refl.
  - move /ha : (hρ){ha}.
    move => [m][PA0][h0]h1.
    move /hb : (hρ){hb}.
    move => [k][PB][h2]h3.
    have ? : PA0 = PA by eauto using InterpUniv_Functional'. subst.
    split => // PB0.
    move : h2. asimpl => *.
    have ? : PB0 = PB by eauto using InterpUniv_Functional'. by subst.
Qed.

Lemma N_Projs p (a b : PTm) :
  rtc TRedSN a b ->
  rtc TRedSN (PProj p a) (PProj p b).
Proof. induction 1; hauto lq:on ctrs:rtc, TRedSN. Qed.

Lemma ST_Proj1 Γ (a : PTm) A B :
  Γ ⊨ a ∈ PBind PSig A B ->
  Γ ⊨ PProj PL a ∈ A.
Proof.
  move => h ρ /[dup]hρ {}/h [m][PA][/= /InterpUniv_Bind_inv_nopf h0]h1.
  move : h0 => [S][h2][h3]?. subst.
  move : h1 => /=.
  rewrite /SumSpace.
  case.
  - move => [v [h0 h1]].
    have {}h0 : rtc TRedSN (PProj PL (subst_PTm ρ a)) (PProj PL v) by hauto lq:on use:N_Projs.
    have {}h1 : SNe (PProj PL v) by hauto lq:on ctrs:SNe.
    hauto q:on use:InterpUniv_back_closs,adequacy.
  - move => [a0 [b0 [h4 [h5 h6]]]].
    exists m, S. split => //=.
    have {}h4 : rtc TRedSN (PProj PL (subst_PTm ρ a)) (PProj PL (PPair a0 b0)) by eauto using N_Projs.
    have ? : rtc TRedSN (PProj PL (PPair a0 b0)) a0 by hauto q:on ctrs:rtc, TRedSN use:adequacy.
    have : rtc TRedSN (PProj PL (subst_PTm ρ a)) a0 by hauto q:on ctrs:rtc use:@relations.rtc_r.
    move => h.
    apply : InterpUniv_back_closs; eauto.
Qed.

Lemma ST_Proj2 Γ (a : PTm) A B :
  Γ ⊨ a ∈ PBind PSig A B ->
  Γ ⊨ PProj PR a ∈ subst_PTm (scons (PProj PL a) VarPTm) B.
Proof.
  move => h ρ hρ.
  move : (hρ) => {}/h [m][PA][/= /InterpUniv_Bind_inv_nopf h0]h1.
  move : h0 => [S][h2][h3]?. subst.
  move : h1 => /=.
  rewrite /SumSpace.
  case.
  - move => h.
    move : h => [v [h0 h1]].
    have hp : forall p, SNe (PProj p v) by hauto lq:on ctrs:SNe.
    have hp' : forall p, rtc TRedSN (PProj p(subst_PTm ρ a)) (PProj p v) by eauto using N_Projs.
    have hp0 := hp PL. have hp1 := hp PR => {hp}.
    have hp0' := hp' PL. have hp1' := hp' PR => {hp'}.
    have : S (PProj PL (subst_PTm ρ a)). apply : InterpUniv_back_closs; eauto. hauto q:on use:adequacy.
    move /h3 => [PB]. asimpl => hPB.
    do 2 eexists. split; eauto.
    apply : InterpUniv_back_closs; eauto. hauto q:on use:adequacy.
  - move => [a0 [b0 [h4 [h5 h6]]]].
    have h3_dup := h3.
    specialize h3 with (1 := h5).
    move : h3 => [PB hPB].
    have hr : forall p, rtc TRedSN (PProj p (subst_PTm ρ a)) (PProj p (PPair a0 b0)) by hauto l:on use: N_Projs.
    have hSN : SN a0 by move : h5 h2; clear; hauto q:on use:adequacy.
    have hSN' : SN b0 by hauto q:on use:adequacy.
    have hrl : TRedSN (PProj PL (PPair a0 b0)) a0 by hauto lq:on ctrs:TRedSN.
    have hrr : TRedSN (PProj PR (PPair a0 b0)) b0 by hauto lq:on ctrs:TRedSN.
    exists m, PB.
    asimpl. split.
    + have hr' : rtc TRedSN (PProj PL (subst_PTm ρ a)) a0 by hauto l:on use:@relations.rtc_r.
      have : S (PProj PL (subst_PTm ρ a)) by hauto lq:on use:InterpUniv_back_closs.
      move => {}/h3_dup.
      move => [PB0]. asimpl => hPB0.
      suff : PB = PB0 by congruence.
      move : hPB. asimpl => hPB.
      suff : DJoin.R (subst_PTm (scons (PProj PL (subst_PTm ρ a)) ρ) B) (subst_PTm (scons a0 ρ) B).
      move : InterpUniv_Join hPB0 hPB; repeat move/[apply]. done.
      apply DJoin.cong.
      apply DJoin.FromRedSNs.
      hauto lq:on ctrs:rtc unfold:BJoin.R.
    + hauto lq:on use:@relations.rtc_r, InterpUniv_back_closs.
Qed.

Lemma ST_Conv' Γ (a : PTm) A B i :
  Γ ⊨ a ∈ A ->
  Γ ⊨ B ∈ PUniv i ->
  Sub.R A B ->
  Γ ⊨ a ∈ B.
Proof.
  move => ha /SemWt_Univ h h0.
  move => ρ hρ.
  have {}h0 : Sub.R (subst_PTm ρ A) (subst_PTm ρ B) by
    eauto using Sub.substing.
  move /ha : (hρ){ha} => [m [PA [h1 h2]]].
  move /h : (hρ){h} => [S hS].
  have h3 : forall x, PA x -> S x.
  move : InterpUniv_Sub h0 h1 hS; by repeat move/[apply].
  hauto lq:on.
Qed.

Lemma ST_Conv_E Γ (a : PTm) A B i :
  Γ ⊨ a ∈ A ->
  Γ ⊨ B ∈ PUniv i ->
  DJoin.R A B ->
  Γ ⊨ a ∈ B.
Proof.
  hauto l:on use:ST_Conv', Sub.FromJoin.
Qed.

Lemma ST_Conv Γ (a : PTm) A B :
  Γ ⊨ a ∈ A ->
  Γ ⊨ A ≲ B ->
  Γ ⊨ a ∈ B.
Proof. hauto l:on use:ST_Conv', SemLEq_SemWt. Qed.

Lemma SE_Refl Γ (a : PTm) A :
  Γ ⊨ a ∈ A ->
  Γ ⊨ a ≡ a ∈ A.
Proof. hauto lq:on unfold:SemWt,SemEq use:DJoin.refl. Qed.

Lemma SE_Symmetric Γ (a b : PTm) A :
  Γ ⊨ a ≡ b ∈ A ->
  Γ ⊨ b ≡ a ∈ A.
Proof. hauto q:on unfold:SemEq. Qed.

Lemma SE_Transitive Γ (a b c : PTm) A :
  Γ ⊨ a ≡ b ∈ A ->
  Γ ⊨ b ≡ c ∈ A ->
  Γ ⊨ a ≡ c ∈ A.
Proof.
  move => ha hb.
  apply SemEq_SemWt in ha, hb.
  have ? : SN b by hauto l:on use:SemWt_SN.
  apply SemWt_SemEq; try tauto.
  hauto l:on use:DJoin.transitive.
Qed.

Definition Γ_sub' Γ Δ := forall ρ, ρ_ok Δ ρ -> ρ_ok Γ ρ.

Definition Γ_eq' Γ Δ := forall ρ, ρ_ok Δ ρ <-> ρ_ok Γ ρ.

Lemma Γ_sub'_refl Γ : Γ_sub' Γ Γ.
  rewrite /Γ_sub'. sfirstorder b:on. Qed.

Lemma Γ_sub'_cons Γ Δ A B i j :
  Sub.R B A ->
  Γ_sub' Γ Δ ->
  Γ ⊨ A ∈ PUniv i ->
  Δ ⊨ B ∈ PUniv j ->
  Γ_sub' (cons A Γ) (cons B Δ).
Proof.
  move => hsub hsub' hA hB ρ hρ.
  move => k k' A0 PA.
  have hρ_inv : ρ_ok Δ (funcomp ρ shift).
  move : hρ. clear.
  move => hρ i.
  (* specialize (hρ (shift i)). *)
  move => k A PA.
  move /there. move /(_ B).
  rewrite /ρ_ok in hρ.
  move /hρ. asimpl. by apply.
  elim /lookup_inv => //=hl.
  move => A1 Γ0 ? [? ?] ?. subst.
  - asimpl.
    move => h.
    have {}/hsub' hρ' := hρ_inv.
    move /SemWt_Univ : (hA) (hρ')=> /[apply].
    move => [S]hS.
    move /SemWt_Univ : (hB) (hρ_inv)=>/[apply].
    move => [S1]hS1.
    move /(_ var_zero j (ren_PTm shift B) S1) : hρ (hS1). asimpl.
    move => /[apply].
    move /(_ ltac:(apply here)).
    move => *.
    suff : forall x, S1 x -> PA x by firstorder.
    apply : InterpUniv_Sub; eauto.
    by apply Sub.substing.
  - rewrite /Γ_sub' in hsub'.
    asimpl.
    move => i0 Γ0 A1 B0 hi0 ? [? ?]?. subst.
    move /(_ (funcomp ρ shift) hρ_inv) in hsub'.
    move : hsub' hi0 => /[apply]. move => /[apply]. by asimpl.
Qed.

Lemma Γ_sub'_SemWt Γ Δ a A  :
  Γ_sub' Γ Δ ->
  Γ ⊨ a ∈ A ->
  Δ ⊨ a ∈ A.
Proof.
  move => hs  ha ρ hρ.
  have {}/hs hρ' := hρ.
  hauto l:on.
Qed.

Lemma Γ_eq_sub Γ Δ : Γ_eq' Γ Δ <-> Γ_sub' Γ Δ /\ Γ_sub' Δ Γ.
Proof. rewrite /Γ_eq' /Γ_sub'. hauto l:on. Qed.

Lemma Γ_eq'_cons Γ Δ A B i j :
  DJoin.R B A ->
  Γ_eq' Γ Δ ->
  Γ ⊨ A ∈ PUniv i ->
  Δ ⊨ B ∈ PUniv j ->
  Γ_eq' (cons A Γ) (cons B Δ).
Proof.
  move => h.
  have {h} [h0 h1] : Sub.R A B /\ Sub.R B A by hauto lq:on use:Sub.FromJoin, DJoin.symmetric.
  repeat rewrite ->Γ_eq_sub.
  hauto l:on use:Γ_sub'_cons.
Qed.

Lemma Γ_eq'_refl Γ : Γ_eq' Γ Γ.
Proof. rewrite /Γ_eq'. firstorder. Qed.

Lemma SE_Bind' Γ i j p (A0 A1 : PTm) B0 B1 :
  Γ ⊨ A0 ≡ A1 ∈ PUniv i ->
  cons A0 Γ ⊨ B0 ≡ B1 ∈ PUniv j ->
  Γ ⊨ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv (max i j).
Proof.
  move => hA hB.
  apply SemEq_SemWt in hA, hB.
  apply SemWt_SemEq; last by hauto l:on use:DJoin.BindCong.
  hauto l:on use:ST_Bind'.
  apply ST_Bind'; first by tauto.
  move => ρ hρ.
  suff : ρ_ok (cons A0 Γ) ρ by hauto l:on.
  move : hρ.
  suff : Γ_sub' (A0 :: Γ) (A1 :: Γ) by hauto l:on unfold:Γ_sub'.
  apply : Γ_sub'_cons.
  apply /Sub.FromJoin /DJoin.symmetric. tauto.
  apply Γ_sub'_refl. hauto lq:on.
  hauto lq:on.
Qed.

Lemma SE_Bind Γ i p (A0 A1 : PTm) B0 B1 :
  Γ ⊨ A0 ≡ A1 ∈ PUniv i ->
  cons A0 Γ ⊨ B0 ≡ B1 ∈ PUniv i ->
  Γ ⊨ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i.
Proof.
  move => *. replace i with (max i i) by lia. auto using SE_Bind'.
Qed.

Lemma SE_Abs Γ (a b : PTm) A B i :
  Γ ⊨ PBind PPi A B ∈ (PUniv i) ->
  cons A Γ ⊨ a ≡ b ∈ B ->
  Γ ⊨ PAbs a ≡ PAbs b ∈ PBind PPi A B.
Proof.
  move => hPi /SemEq_SemWt [ha][hb]he.
  apply SemWt_SemEq; eauto using DJoin.AbsCong, ST_Abs.
Qed.

Lemma SBind_inv1 Γ i p (A : PTm) B :
  Γ ⊨ PBind p A B ∈ PUniv i ->
  Γ ⊨ A ∈ PUniv i.
  move /SemWt_Univ => h. apply SemWt_Univ.
  hauto lq:on rew:off  use:InterpUniv_Bind_inv.
Qed.

Lemma SE_AppEta Γ (b : PTm) A B i :
  Γ ⊨ PBind PPi A B ∈ (PUniv i) ->
  Γ ⊨ b ∈ PBind PPi A B ->
  Γ ⊨ PAbs (PApp (ren_PTm shift b) (VarPTm var_zero)) ≡ b ∈ PBind PPi A B.
Proof.
  move => h0 h1. apply SemWt_SemEq; eauto.
  apply : ST_Abs; eauto.
  have hA : Γ ⊨ A ∈ PUniv i by eauto using SBind_inv1.
  eapply ST_App' with (A := ren_PTm shift A)(B:= ren_PTm (upRen_PTm_PTm shift) B). asimpl. by rewrite subst_scons_id.
  2 : {
    apply : ST_Var'.
    apply here.
    apply : weakening_Sem_Univ; eauto.
  }
  change (PBind PPi (ren_PTm shift A) (ren_PTm (upRen_PTm_PTm shift) B)) with
    (ren_PTm shift (PBind PPi A B)).
  apply : weakening_Sem; eauto.
  hauto q:on ctrs:rtc,RERed.R.
Qed.

Lemma SE_AppAbs Γ (a : PTm) b A B i:
  Γ ⊨ PBind PPi A B ∈ PUniv i ->
  Γ ⊨ b ∈ A ->
  (cons A Γ) ⊨ a ∈ B ->
  Γ ⊨ PApp (PAbs a) b ≡ subst_PTm (scons b VarPTm) a ∈ subst_PTm (scons b VarPTm ) B.
Proof.
  move => h h0 h1. apply SemWt_SemEq; eauto using ST_App, ST_Abs.
  move => ρ hρ.
  have {}/h0 := hρ.
  move => [k][PA][hPA]hb.
  move : ρ_ok_cons hPA hb (hρ); repeat move/[apply].
  move => {}/h1.
  by asimpl.
  apply DJoin.FromRRed0.
  apply RRed.AppAbs.
Qed.

Lemma SE_Conv' Γ (a b : PTm) A B i :
  Γ ⊨ a ≡ b ∈ A ->
  Γ ⊨ B ∈ PUniv i ->
  Sub.R A B ->
  Γ ⊨ a ≡ b ∈ B.
Proof.
  move /SemEq_SemWt => [ha][hb]he hB hAB.
  apply SemWt_SemEq; eauto using ST_Conv'.
Qed.

Lemma SE_Conv Γ (a b : PTm) A B :
  Γ ⊨ a ≡ b ∈ A ->
  Γ ⊨ A ≲ B ->
  Γ ⊨ a ≡ b ∈ B.
Proof.
  move => h /SemLEq_SemWt [h0][h1][ha]hb.
  eauto using SE_Conv'.
Qed.

Lemma SBind_inst Γ p i (A : PTm) B (a : PTm) :
  Γ ⊨ a ∈ A ->
  Γ ⊨ PBind p A B ∈ PUniv i ->
  Γ ⊨ subst_PTm (scons a VarPTm) B ∈ PUniv i.
Proof.
  move => ha /SemWt_Univ hb.
  apply SemWt_Univ.
  move => ρ hρ.
  have {}/hb := hρ.
  asimpl. move => /= [S hS].
  move /InterpUniv_Bind_inv_nopf : hS.
  move => [PA][hPA][hPF]?. subst.
  have {}/ha := hρ.
  move => [k][PA0][hPA0]ha.
  have ? : PA0 = PA by hauto l:on use:InterpUniv_Functional'. subst.
  have {}/hPF := ha.
  move => [PB]. asimpl.
  hauto lq:on.
Qed.

Lemma SE_Pair Γ (a0 a1 b0 b1 : PTm) A B i :
  Γ ⊨ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊨ a0 ≡ a1 ∈ A ->
  Γ ⊨ b0 ≡ b1 ∈ subst_PTm (scons a0 VarPTm) B ->
  Γ ⊨ PPair a0 b0 ≡ PPair a1 b1 ∈ PBind PSig A B.
Proof.
  move => h /SemEq_SemWt [ha0][ha1]hae /SemEq_SemWt [hb0][hb1]hbe.
  apply SemWt_SemEq; eauto using ST_Pair, DJoin.PairCong, SBind_inst, DJoin.cong, ST_Conv_E, ST_Pair.
Qed.

Lemma SE_Proj1 Γ (a b : PTm) A B :
  Γ ⊨ a ≡ b ∈ PBind PSig A B ->
  Γ ⊨ PProj PL a ≡ PProj PL b ∈ A.
Proof.
  move => /SemEq_SemWt [ha][hb]he.
  apply SemWt_SemEq; eauto using DJoin.ProjCong, ST_Proj1.
Qed.

Lemma SE_Proj2 Γ i (a b : PTm ) A B :
  Γ ⊨ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊨ a ≡ b ∈ PBind PSig A B ->
  Γ ⊨ PProj PR a ≡ PProj PR b ∈ subst_PTm (scons (PProj PL a) VarPTm) B.
Proof.
  move => hS.
  move => /SemEq_SemWt [ha][hb]he.
  apply SemWt_SemEq; eauto using DJoin.ProjCong, ST_Proj2.
  have h : Γ ⊨ PProj PR b ∈ subst_PTm (scons (PProj PL b) VarPTm) B by eauto using ST_Proj2.
  apply : ST_Conv_E. apply h.
  apply : SBind_inst. eauto using ST_Proj1.
  eauto.
  hauto lq:on use: DJoin.cong,  DJoin.ProjCong.
Qed.


Lemma ST_Nat Γ i :
  Γ ⊨ PNat ∈ PUniv i.
Proof.
  move => ?. apply SemWt_Univ. move => ρ hρ.
  eexists. by apply InterpUniv_Nat.
Qed.

Lemma ST_Zero Γ :
  Γ ⊨ PZero ∈ PNat.
Proof.
  move => ρ hρ. exists 0, SNat. simpl. split.
  apply InterpUniv_Nat.
  apply S_Zero.
Qed.

Lemma ST_Suc Γ (a : PTm) :
  Γ ⊨ a ∈ PNat ->
  Γ ⊨ PSuc a ∈ PNat.
Proof.
  move => ha ρ.
  move : ha => /[apply] /=.
  move => [k][PA][h0 h1].
  move /InterpUniv_Nat_inv : h0 => ?. subst.
  exists 0, SNat. split. apply InterpUniv_Nat.
  eauto using S_Suc.
Qed.


Lemma sn_unmorphing' : (forall (a : PTm) (s : SN a), forall (ρ : nat -> PTm) b, a = subst_PTm ρ b -> SN b).
Proof. hauto l:on use:sn_unmorphing. Qed.

Lemma sn_bot_up (a : PTm) i (ρ : nat -> PTm) :
  SN (subst_PTm (scons (VarPTm i) ρ) a) -> SN (subst_PTm (up_PTm_PTm ρ) a).
  rewrite /up_PTm_PTm.
  move => h. eapply sn_unmorphing' with (ρ := (scons (VarPTm i) VarPTm)); eauto.
  by asimpl.
Qed.

Lemma sn_bot_up2 (a : PTm) j i (ρ : nat -> PTm) :
  SN ((subst_PTm (scons (VarPTm j) (scons (VarPTm i) ρ)) a)) -> SN (subst_PTm (up_PTm_PTm (up_PTm_PTm ρ)) a).
  rewrite /up_PTm_PTm.
  move => h. eapply sn_unmorphing' with (ρ := (scons (VarPTm j) (scons (VarPTm i) VarPTm))); eauto.
  by asimpl.
Qed.

Lemma SNat_SN (a : PTm) : SNat a -> SN a.
  induction 1; hauto lq:on ctrs:SN. Qed.

Lemma ST_Ind Γ P (a : PTm) b c i :
  (cons PNat Γ) ⊨ P ∈ PUniv i ->
  Γ ⊨ a ∈ PNat ->
  Γ ⊨ b ∈ subst_PTm (scons PZero VarPTm) P ->
  (cons P (cons PNat Γ)) ⊨ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊨ PInd P a b c ∈ subst_PTm (scons a VarPTm) P.
Proof.
  move => hA hc ha hb ρ hρ.
  move /(_ ρ hρ) : ha => [m][PA][ha0]ha1.
  move /(_ ρ hρ) : hc => [n][PA0][/InterpUniv_Nat_inv ->].
  simpl.
  (* Use localiaztion to block asimpl from simplifying pind *)
  set x := PInd _ _ _ _. asimpl. subst x. move : {a} (subst_PTm ρ a) .
  move : (subst_PTm ρ b) ha1 => {}b ha1.
  move => u hu.
  have hρb : ρ_ok (cons PNat Γ) (scons (VarPTm var_zero) ρ) by apply : ρ_ok_cons; hauto lq:on ctrs:SNat, SNe use:(@InterpUniv_Nat 0).
  have hρbb : ρ_ok (cons P (cons PNat Γ)) (scons (VarPTm var_zero) (scons (VarPTm var_zero) ρ)).
  move /SemWt_Univ /(_ _ hρb) : hA => [S ?].
  apply : ρ_ok_cons; eauto. sauto lq:on use:adequacy.

  (* have snP : SN P by hauto l:on use:SemWt_SN. *)
  have snb : SN b by hauto q:on use:adequacy.
  have snP : SN (subst_PTm (up_PTm_PTm ρ) P)
    by eapply sn_bot_up; move : hA hρb => /[apply]; hauto lq:on use:adequacy.
  have snc : SN (subst_PTm (up_PTm_PTm (up_PTm_PTm ρ)) c)
    by apply: sn_bot_up2; move : hb hρbb => /[apply]; hauto lq:on use:adequacy.

  elim : u /hu.
  + exists m, PA. split.
    * move : ha0. by asimpl.
    * apply : InterpUniv_back_clos; eauto.
      apply N_IndZero; eauto.
  + move => a snea.
    have hρ' : ρ_ok (cons PNat Γ) (scons a ρ)by
      apply : ρ_ok_cons; eauto using (InterpUniv_Nat 0); hauto ctrs:SNat.
    move /SemWt_Univ : (hA) hρ' => /[apply].
    move => [S0 hS0].
    exists i, S0. split=>//.
    eapply adequacy; eauto.
    apply N_Ind; eauto.
  + move => a ha [j][S][h0]h1.
    have hρ' : ρ_ok (cons PNat Γ) (scons (PSuc a) ρ)by
      apply : ρ_ok_cons; eauto using (InterpUniv_Nat 0); hauto ctrs:SNat.
    move /SemWt_Univ : (hA) (hρ') => /[apply].
    move => [S0 hS0].
    exists i, S0. split => //.
    apply : InterpUniv_back_clos; eauto.
    apply N_IndSuc; eauto using SNat_SN.
    move : (PInd (subst_PTm (up_PTm_PTm ρ) P) a b
              (subst_PTm (up_PTm_PTm (up_PTm_PTm ρ)) c))  h1.
    move => r hr.
    have hρ'' :  ρ_ok
                   (cons P (cons PNat Γ)) (scons r (scons a ρ)) by
      eauto using ρ_ok_cons, (InterpUniv_Nat 0).
    move : hb hρ'' => /[apply].
    move => [k][PA1][h2]h3.
    move : h2. asimpl => ?.
    have ? : PA1 = S0 by  eauto using InterpUniv_Functional'.
    by subst.
  + move => a a' hr ha' [k][PA1][h0]h1.
    have : ρ_ok (cons PNat Γ) (scons a ρ)
      by apply : ρ_ok_cons; hauto l:on use:S_Red,(InterpUniv_Nat 0).
    move /SemWt_Univ : hA => /[apply]. move => [PA2]h2.
    exists i, PA2. split => //.
    apply : InterpUniv_back_clos; eauto.
    apply N_IndCong; eauto.
    suff : PA1 = PA2 by congruence.
    move : h0 h2. move : InterpUniv_Join'; repeat move/[apply]. apply.
    apply DJoin.FromRReds.
    apply RReds.FromRPar.
    apply RPar.morphing; last by apply RPar.refl.
    eapply LoReds.FromSN_mutual in hr.
    move /LoRed.ToRRed /RPar.FromRRed in hr.
    hauto lq:on inv:nat use:RPar.refl.
Qed.

Lemma SE_SucCong Γ (a b : PTm) :
  Γ ⊨ a ≡ b ∈ PNat ->
  Γ ⊨ PSuc a ≡ PSuc b ∈ PNat.
Proof.
  move /SemEq_SemWt => [ha][hb]he.
  apply SemWt_SemEq; eauto using ST_Suc.
  hauto q:on use:REReds.suc_inv, REReds.SucCong.
Qed.

Lemma SE_IndCong Γ P0 P1 (a0 a1 : PTm ) b0 b1 c0 c1 i :
  cons PNat Γ ⊨ P0 ≡ P1 ∈ PUniv i ->
  Γ ⊨ a0 ≡ a1 ∈ PNat ->
  Γ ⊨ b0 ≡ b1 ∈ subst_PTm (scons PZero VarPTm) P0 ->
  cons P0 (cons PNat Γ) ⊨ c0 ≡ c1 ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P0) ->
  Γ ⊨ PInd P0 a0 b0 c0 ≡ PInd P1 a1 b1 c1 ∈ subst_PTm (scons a0 VarPTm) P0.
Proof.
  move /SemEq_SemWt=>[hP0][hP1]hPe.
  move /SemEq_SemWt=>[ha0][ha1]hae.
  move /SemEq_SemWt=>[hb0][hb1]hbe.
  move /SemEq_SemWt=>[hc0][hc1]hce.
  apply SemWt_SemEq; eauto using ST_Ind, DJoin.IndCong.
  apply ST_Conv_E with (A := subst_PTm (scons a1 VarPTm) P1) (i := i);
    last by eauto using DJoin.cong', DJoin.symmetric.
  apply : ST_Ind; eauto. eapply ST_Conv_E with (i := i); eauto.
  apply : morphing_SemWt_Univ; eauto.
  apply smorphing_ext. rewrite /smorphing_ok.
  move => ξ. rewrite /funcomp. by asimpl.
  by apply ST_Zero.
  by apply DJoin.substing.
  eapply ST_Conv_E with (i := i); eauto.
  apply : Γ_sub'_SemWt; eauto.
  apply : Γ_sub'_cons; eauto using DJoin.symmetric, Sub.FromJoin.
  apply : Γ_sub'_cons; eauto using Sub.refl, Γ_sub'_refl, (@ST_Nat _ 0).
  apply : weakening_Sem_Univ; eauto. move : hP1.
  move /morphing_SemWt. apply. apply smorphing_ext.
  have -> : (funcomp VarPTm shift) = funcomp (ren_PTm shift) (VarPTm) by asimpl.
  apply : smorphing_ren; eauto using smorphing_ok_refl. hauto l:on inv:option.
  apply ST_Suc. apply ST_Var' with (j := 0). apply here.
  apply ST_Nat.
  apply DJoin.renaming. by apply DJoin.substing.
  apply : morphing_SemWt_Univ; eauto.
  apply smorphing_ext; eauto using smorphing_ok_refl.
Qed.

Lemma SE_IndZero Γ P i (b : PTm) c :
  (cons PNat Γ) ⊨ P ∈ PUniv i ->
  Γ ⊨ b ∈ subst_PTm (scons PZero VarPTm) P ->
  (cons P (cons PNat Γ)) ⊨ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊨ PInd P PZero b c ≡ b ∈ subst_PTm (scons PZero VarPTm) P.
Proof.
  move => hP hb hc.
  apply SemWt_SemEq; eauto using ST_Zero, ST_Ind.
  apply DJoin.FromRRed0. apply RRed.IndZero.
Qed.

Lemma SE_IndSuc Γ P (a : PTm) b c i :
  (cons PNat Γ) ⊨ P ∈ PUniv i ->
  Γ ⊨ a ∈ PNat ->
  Γ ⊨ b ∈ subst_PTm (scons PZero VarPTm) P ->
  (cons P (cons PNat Γ)) ⊨ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊨ PInd P (PSuc a) b c ≡ (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c) ∈ subst_PTm (scons (PSuc a) VarPTm) P.
Proof.
  move => hP ha hb hc.
  apply SemWt_SemEq; eauto using ST_Suc, ST_Ind.
  set Δ := (X in X ⊨ _ ∈ _) in hc.
  have : smorphing_ok Γ Δ (scons (PInd P a b c) (scons a VarPTm)).
  apply smorphing_ext. apply smorphing_ext. apply smorphing_ok_refl.
  done. eauto using ST_Ind.
  move : morphing_SemWt hc; repeat move/[apply].
  by asimpl.
  apply DJoin.FromRRed0.
  apply RRed.IndSuc.
Qed.

Lemma SE_ProjPair1 Γ (a b : PTm) A B i :
  Γ ⊨ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊨ a ∈ A ->
  Γ ⊨ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊨ PProj PL (PPair a b) ≡ a ∈ A.
Proof.
  move => h0 h1 h2.
  apply SemWt_SemEq; eauto using ST_Proj1, ST_Pair.
  apply DJoin.FromRRed0. apply RRed.ProjPair.
Qed.

Lemma SE_ProjPair2 Γ (a b : PTm) A B i :
  Γ ⊨ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊨ a ∈ A ->
  Γ ⊨ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊨ PProj PR (PPair a b) ≡ b ∈ subst_PTm (scons a VarPTm) B.
Proof.
  move => h0 h1 h2.
  apply SemWt_SemEq; eauto using ST_Proj2, ST_Pair.
  apply : ST_Conv_E. apply : ST_Proj2; eauto. apply : ST_Pair; eauto.
  hauto l:on use:SBind_inst.
  apply DJoin.cong. apply DJoin.FromRRed0. apply RRed.ProjPair.
  apply DJoin.FromRRed0. apply RRed.ProjPair.
Qed.

Lemma SE_PairEta Γ (a : PTm) A B i :
  Γ ⊨ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊨ a ∈ PBind PSig A B ->
  Γ ⊨ a ≡ PPair (PProj PL a) (PProj PR a) ∈ PBind PSig A B.
Proof.
  move => h0 h. apply SemWt_SemEq; eauto.
  apply : ST_Pair; eauto using ST_Proj1, ST_Proj2.
  rewrite /DJoin.R. hauto lq:on ctrs:rtc,RERed.R.
Qed.

Lemma SE_FunExt Γ (a b : PTm) A B i :
  Γ ⊨ PBind PPi A B ∈ PUniv i ->
  Γ ⊨ a ∈ PBind PPi A B ->
  Γ ⊨ b ∈ PBind PPi A B ->
  A :: Γ ⊨ PApp (ren_PTm shift a) (VarPTm var_zero) ≡ PApp (ren_PTm shift b) (VarPTm var_zero) ∈ B ->
  Γ ⊨ a ≡ b ∈ PBind PPi A B.
Proof.
  move => hpi ha hb he.
  move : SE_Abs (hpi) he. repeat move/[apply]. move => he.
  have /SE_Symmetric : Γ ⊨ PAbs (PApp (ren_PTm shift a) (VarPTm var_zero)) ≡ a ∈ PBind PPi A B by eauto using SE_AppEta.
  have : Γ ⊨ PAbs (PApp (ren_PTm shift b) (VarPTm var_zero)) ≡ b ∈ PBind PPi A B by eauto using SE_AppEta.
  eauto using SE_Transitive.
Qed.

Lemma SE_Nat Γ (a b : PTm) :
  Γ ⊨ a ≡ b ∈ PNat ->
  Γ ⊨ PSuc a ≡ PSuc b ∈ PNat.
Proof.
  move /SemEq_SemWt => [ha][hb]hE.
  apply SemWt_SemEq; eauto using ST_Suc.
  eauto using DJoin.SucCong.
Qed.

Lemma SE_App Γ i (b0 b1 a0 a1 : PTm) A B :
  Γ ⊨ PBind PPi A B ∈ (PUniv i) ->
  Γ ⊨ b0 ≡ b1 ∈ PBind PPi A B ->
  Γ ⊨ a0 ≡ a1 ∈ A ->
  Γ ⊨ PApp b0 a0 ≡ PApp b1 a1 ∈ subst_PTm (scons a0 VarPTm) B.
Proof.
  move => hPi.
  move => /SemEq_SemWt [hb0][hb1]hb /SemEq_SemWt [ha0][ha1]ha.
  apply SemWt_SemEq; eauto using DJoin.AppCong, ST_App.
  apply : ST_Conv_E; eauto using ST_App, DJoin.cong, DJoin.symmetric, SBind_inst.
Qed.

Lemma SSu_Eq Γ (A B : PTm) i :
  Γ ⊨ A ≡ B ∈ PUniv i ->
  Γ ⊨ A ≲ B.
Proof. move /SemEq_SemWt => h.
       qauto l:on use:SemWt_SemLEq, Sub.FromJoin.
Qed.

Lemma SSu_Transitive Γ (A B C : PTm) :
  Γ ⊨ A ≲ B ->
  Γ ⊨ B ≲ C ->
  Γ ⊨ A ≲ C.
Proof.
  move => ha hb.
  apply SemLEq_SemWt in ha, hb.
  have ? : SN B by hauto l:on use:SemWt_SN.
  move : ha => [ha0 [i [ha1 ha2]]]. move : hb => [hb0 [j [hb1 hb2]]].
  qauto l:on use:SemWt_SemLEq, Sub.transitive.
Qed.

Lemma ST_Univ' Γ i j :
  i < j ->
  Γ ⊨ PUniv i ∈ PUniv j.
Proof.
  move => ?.
  apply SemWt_Univ. move => ρ hρ. eexists. by apply InterpUniv_Univ.
Qed.

Lemma ST_Univ Γ i :
  Γ ⊨ PUniv i ∈ PUniv (S i).
Proof.
  apply ST_Univ'. lia.
Qed.

Lemma SSu_Univ Γ i j :
  i <= j ->
  Γ ⊨ PUniv i ≲ PUniv j.
Proof.
  move => h. apply : SemWt_SemLEq; eauto using ST_Univ.
  sauto lq:on.
Qed.

Lemma SSu_Pi Γ (A0 A1 : PTm ) B0 B1 :
  Γ ⊨ A1 ≲ A0 ->
  cons A0 Γ ⊨ B0 ≲ B1 ->
  Γ ⊨ PBind PPi A0 B0 ≲ PBind PPi A1 B1.
Proof.
  move =>  hA hB.
  have ? : SN A0 /\ SN A1 /\ SN B0 /\ SN B1
    by hauto l:on use:SemLEq_SN_Sub.
  apply SemLEq_SemWt in hA, hB.
  move : hA => [hA0][i][hA1]hA2.
  move : hB => [hB0][j][hB1]hB2.
  apply : SemWt_SemLEq; last by hauto l:on use:Sub.PiCong.
  hauto l:on use:ST_Bind'.
  apply ST_Bind'; eauto.
  move => ρ hρ.
  suff : ρ_ok (cons A0 Γ) ρ by hauto l:on.
  move : hρ. suff : Γ_sub' (A0 :: Γ) (A1 :: Γ)
    by hauto l:on unfold:Γ_sub'.
  apply : Γ_sub'_cons; eauto. apply Γ_sub'_refl.
Qed.

Lemma SSu_Sig Γ (A0 A1 : PTm) B0 B1 :
  Γ ⊨ A0 ≲ A1 ->
  cons A1 Γ ⊨ B0 ≲ B1 ->
  Γ ⊨ PBind PSig A0 B0 ≲ PBind PSig A1 B1.
Proof.
  move => hA hB.
  have ? : SN A0 /\ SN A1 /\ SN B0 /\ SN B1
    by hauto l:on use:SemLEq_SN_Sub.
  apply SemLEq_SemWt in hA, hB.
  move : hA => [hA0][i][hA1]hA2.
  move : hB => [hB0][j][hB1]hB2.
  apply : SemWt_SemLEq; last by hauto l:on use:Sub.SigCong.
  2 : { hauto l:on use:ST_Bind'. }
  apply ST_Bind'; eauto.
  move => ρ hρ.
  suff : ρ_ok (cons A1 Γ) ρ by hauto l:on.
  move : hρ. suff : Γ_sub' (A1 :: Γ) (A0 :: Γ) by hauto l:on.
  apply : Γ_sub'_cons; eauto.
  apply Γ_sub'_refl.
Qed.

Lemma SSu_Pi_Proj1 Γ (A0 A1 : PTm) B0 B1 :
  Γ ⊨ PBind PPi A0 B0 ≲ PBind PPi A1 B1 ->
  Γ ⊨ A1 ≲ A0.
Proof.
  move /SemLEq_SemWt => [h0][h1][h2]he.
  apply : SemWt_SemLEq; eauto using SBind_inv1.
  hauto lq:on rew:off use:Sub.bind_inj.
Qed.

Lemma SSu_Sig_Proj1 Γ (A0 A1 : PTm) B0 B1 :
  Γ ⊨ PBind PSig A0 B0 ≲ PBind PSig A1 B1 ->
  Γ ⊨ A0 ≲ A1.
Proof.
  move /SemLEq_SemWt => [h0][h1][h2]he.
  apply : SemWt_SemLEq; eauto using SBind_inv1.
  hauto lq:on rew:off use:Sub.bind_inj.
Qed.

Lemma SSu_Pi_Proj2 Γ (a0 a1 A0 A1 : PTm) B0 B1 :
  Γ ⊨ PBind PPi A0 B0 ≲ PBind PPi A1 B1 ->
  Γ ⊨ a0 ≡ a1 ∈ A1 ->
  Γ ⊨ subst_PTm (scons a0 VarPTm) B0 ≲ subst_PTm (scons a1 VarPTm) B1.
Proof.
  move /SemLEq_SemWt => [/Sub.bind_inj [_ [h1 h2]]].
  move => [i][hP0]hP1 /SemEq_SemWt [ha0][ha1]ha.
  apply : SemWt_SemLEq; eauto using SBind_inst;
    last by hauto l:on use:Sub.cong.
  apply SBind_inst with (p := PPi) (A := A0); eauto.
  apply : ST_Conv'; eauto. hauto l:on use:SBind_inv1.
Qed.

Lemma SSu_Sig_Proj2 Γ (a0 a1 A0 A1 : PTm) B0 B1 :
  Γ ⊨ PBind PSig A0 B0 ≲ PBind PSig A1 B1 ->
  Γ ⊨ a0 ≡ a1 ∈ A0 ->
  Γ ⊨ subst_PTm (scons a0 VarPTm) B0 ≲ subst_PTm (scons a1 VarPTm) B1.
Proof.
  move /SemLEq_SemWt => [/Sub.bind_inj [_ [h1 h2]]].
  move => [i][hP0]hP1 /SemEq_SemWt [ha0][ha1]ha.
  apply : SemWt_SemLEq; eauto using SBind_inst;
    last by hauto l:on use:Sub.cong.
  apply SBind_inst with (p := PSig) (A := A1); eauto.
  apply : ST_Conv'; eauto. hauto l:on use:SBind_inv1.
Qed.

#[export]Hint Resolve ST_Var ST_Bind ST_Abs ST_App ST_Pair ST_Proj1 ST_Proj2 ST_Univ ST_Conv
  SE_Refl SE_Symmetric SE_Transitive SE_Bind SE_Abs SE_App SE_Proj1 SE_Proj2
  SE_Conv SSu_Pi_Proj1 SSu_Pi_Proj2 SSu_Sig_Proj1 SSu_Sig_Proj2 SSu_Eq SSu_Transitive SSu_Pi SSu_Sig SemWff_nil SemWff_cons SSu_Univ SE_AppAbs SE_ProjPair1 SE_ProjPair2 SE_AppEta SE_PairEta ST_Nat ST_Ind ST_Suc ST_Zero SE_IndCong SE_SucCong SE_IndZero SE_IndSuc SE_SucCong : sem.
