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

Lemma bindspace_iff n p (PA : PTm n -> Prop) PF PF0 b  :
  (forall (a : PTm n) (PB PB0 : PTm n -> Prop), PA a -> PF a PB -> PF0 a PB0 -> PB = PB0) ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a, PA a -> exists PB0, PF0 a PB0) ->
  (BindSpace p PA PF b <-> BindSpace p PA PF0 b).
Proof.
  rewrite /BindSpace => h hPF hPF0.
  case : p => /=.
  - rewrite /ProdSpace.
    split.
    move => h1 a PB ha hPF'.
    specialize hPF with (1 := ha).
    specialize hPF0 with (1 := ha).
    sblast.
    move => ? a PB ha.
    specialize hPF with (1 := ha).
    specialize hPF0 with (1 := ha).
    sblast.
  - rewrite /SumSpace.
    hauto lq:on rew:off.
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
    have [? ?] : SN (PApp (PAbs B) a) /\ SN (PApp (PAbs B0) a) by
      hauto lq:on rew:off use:N_Exp, N_β, adequacy.
    have [? ?] : DJoin.R (PApp (PAbs B0) a) (subst_PTm (scons a VarPTm) B0) /\
           DJoin.R (subst_PTm (scons a VarPTm) B) (PApp (PAbs B) a)
      by hauto lq:on ctrs:RRed.R use:DJoin.FromRRed0, DJoin.FromRRed1.
    eauto using DJoin.transitive.
    move => h. extensionality b. apply propositional_extensionality.
    hauto l:on use:bindspace_iff.
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
    have {}h : j' = j by hauto lq:on use: DJoin.univ_inj. subst.
    hauto lq:on use:InterpUniv_Univ_inv.
  - move => i A A0 PA hr hPA ihPA B PB hPB hAB.
    have /DJoin.symmetric ? : DJoin.R A A0 by hauto lq:on rew:off ctrs:rtc use:DJoin.FromRedSNs.
    have ? : SN A0 by hauto l:on use:adequacy.
    have ? : SN A by eauto using N_Exp.
    have : DJoin.R A0 B by eauto using DJoin.transitive.
    eauto.
Qed.

Lemma InterpUniv_Functional n i  (A : PTm n) PA PB :
  ⟦ A ⟧ i ↘ PA ->
  ⟦ A ⟧ i ↘ PB ->
  PA = PB.
Proof. hauto use:InterpUniv_Join, DJoin.refl. Qed.

Lemma InterpUniv_Join' n i j (A B : PTm n) PA PB :
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

Lemma InterpUniv_Functional' n i j A PA PB :
  ⟦ A : PTm n ⟧ i ↘ PA ->
  ⟦ A ⟧ j ↘ PB ->
  PA = PB.
Proof.
  hauto l:on use:InterpUniv_Join', DJoin.refl.
Qed.

Lemma InterpUniv_Bind_inv_nopf n i p A B P (h :  ⟦PBind p A B ⟧ i ↘ P) :
  exists (PA : PTm n -> Prop),
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

Definition ρ_ok {n} (Γ : fin n -> PTm n) (ρ : fin n -> PTm 0) := forall i k PA,
    ⟦ subst_PTm ρ (Γ i) ⟧ k ↘ PA -> PA (ρ i).

Definition Γ_eq {n} (Γ Δ : fin n -> PTm n)  := forall i, DJoin.R (Γ i) (Δ i).

Definition SemWt {n} Γ (a A : PTm n) := forall ρ, ρ_ok Γ ρ -> exists k PA, ⟦ subst_PTm ρ A ⟧ k ↘ PA /\ PA (subst_PTm ρ a).
Notation "Γ ⊨ a ∈ A" := (SemWt Γ a A) (at level 70).

Definition SemEq {n} Γ (a b A : PTm n) := DJoin.R a b /\ forall ρ, ρ_ok Γ ρ -> exists k PA, ⟦ subst_PTm ρ A ⟧ k ↘ PA /\ PA (subst_PTm ρ a) /\ PA (subst_PTm ρ b).
Notation "Γ ⊨ a ≡ b ∈ A" := (SemEq Γ a b A) (at level 70).

Lemma SemEq_SemWt n Γ (a b A : PTm n) : Γ ⊨ a ≡ b ∈ A -> Γ ⊨ a ∈ A /\ Γ ⊨ b ∈ A /\ DJoin.R a b.
Proof. hauto lq:on rew:off unfold:SemEq, SemWt. Qed.

Lemma SemWt_SemEq n Γ (a b A : PTm n) : Γ ⊨ a ∈ A -> Γ ⊨ b ∈ A -> (DJoin.R a b) -> Γ ⊨ a ≡ b ∈ A.
Proof.
  move => ha hb heq. split => //= ρ hρ.
  have {}/ha := hρ.
  have {}/hb := hρ.
  move => [k][PA][hPA]hpb.
  move => [k0][PA0][hPA0]hpa.
  have : PA = PA0 by hauto l:on use:InterpUniv_Functional'.
  hauto lq:on.
Qed.

(* Semantic context wellformedness *)
Definition SemWff {n} Γ := forall (i : fin n), exists j, Γ ⊨ Γ i ∈ PUniv j.
Notation "⊨ Γ" := (SemWff Γ) (at level 70).

Lemma ρ_ok_bot n (Γ : fin n -> PTm n)  :
  ρ_ok Γ (fun _ => PBot).
Proof.
  rewrite /ρ_ok.
  hauto q:on use:adequacy ctrs:SNe.
Qed.

Lemma ρ_ok_cons n i (Γ : fin n -> PTm n) ρ a PA A :
  ⟦ subst_PTm ρ A ⟧ i ↘ PA -> PA a ->
  ρ_ok Γ ρ ->
  ρ_ok (funcomp (ren_PTm shift) (scons A Γ)) (scons a ρ).
Proof.
  move => h0 h1 h2.
  rewrite /ρ_ok.
  move => j.
  destruct j as [j|].
  - move => m PA0. asimpl => ?.
    asimpl.
    firstorder.
  - move => m PA0. asimpl => h3.
    have ? : PA0 = PA by eauto using InterpUniv_Functional'.
    by subst.
Qed.

Lemma ρ_ok_cons' n i (Γ : fin n -> PTm n) ρ a PA A  Δ :
  Δ = (funcomp (ren_PTm shift) (scons A Γ)) ->
  ⟦ subst_PTm ρ A ⟧ i ↘ PA -> PA a ->
  ρ_ok Γ ρ ->
  ρ_ok Δ (scons a ρ).
Proof. move => ->. apply ρ_ok_cons. Qed.

Definition renaming_ok {n m} (Γ : fin n -> PTm n) (Δ : fin m -> PTm m) (ξ : fin m -> fin n) :=
  forall (i : fin m), ren_PTm ξ (Δ i) = Γ (ξ i).

Lemma ρ_ok_renaming n m (Γ : fin n -> PTm n) ρ :
  forall (Δ : fin m -> PTm m) ξ,
    renaming_ok Γ Δ ξ ->
    ρ_ok Γ ρ ->
    ρ_ok Δ (funcomp ρ ξ).
Proof.
  move => Δ ξ hξ hρ.
  rewrite /ρ_ok => i m' PA.
  rewrite /renaming_ok in hξ.
  rewrite /ρ_ok in hρ.
  move => h.
  rewrite /funcomp.
  apply hρ with (k := m').
  move : h. rewrite -hξ.
  by asimpl.
Qed.

Lemma renaming_SemWt {n} Γ a A :
  Γ ⊨ a ∈ A ->
  forall {m} Δ (ξ : fin n -> fin m),
    renaming_ok Δ Γ ξ ->
    Δ ⊨ ren_PTm ξ a ∈ ren_PTm ξ A.
Proof.
  rewrite /SemWt => h m Δ ξ hξ ρ hρ.
  have /h hρ' : (ρ_ok Γ (funcomp ρ ξ)) by eauto using ρ_ok_renaming.
  hauto q:on solve+:(by asimpl).
Qed.

Lemma weakening_Sem n Γ (a : PTm n) A B i
  (h0 : Γ ⊨ B ∈ PUniv i)
  (h1 : Γ ⊨ a ∈ A) :
   funcomp (ren_PTm shift) (scons B Γ) ⊨ ren_PTm shift a ∈ ren_PTm shift A.
Proof.
  apply : renaming_SemWt; eauto.
  hauto lq:on inv:option unfold:renaming_ok.
Qed.

Lemma SemWt_SN n Γ (a : PTm n) A :
  Γ ⊨ a ∈ A ->
  SN a /\ SN A.
Proof.
  move => h.
  have {}/h := ρ_ok_bot _ Γ => h.
  have h0 : SN (subst_PTm (fun _ : fin n => (PBot : PTm 0)) A) by hauto l:on use:adequacy.
  have h1 : SN (subst_PTm (fun _ : fin n => (PBot : PTm 0)) a)by hauto l:on use:adequacy.
  move {h}. hauto l:on use:sn_unmorphing.
Qed.

Lemma SemWt_Univ n Γ (A : PTm n) i  :
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

(* Structural laws for Semantic context wellformedness *)
Lemma SemWff_nil : SemWff null.
Proof. case. Qed.

Lemma SemWff_cons n Γ (A : PTm n) i :
    ⊨ Γ ->
    Γ ⊨ A ∈ PUniv i ->
    (* -------------- *)
    ⊨ funcomp (ren_PTm shift) (scons A Γ).
Proof.
  move => h h0.
  move => j. destruct j as [j|].
  - move /(_ j) : h => [k hk].
    exists k. change (PUniv k) with (ren_PTm shift (PUniv k : PTm n)).
    eauto using weakening_Sem.
  - hauto q:on use:weakening_Sem.
Qed.

(* Semantic typing rules *)
Lemma ST_Var n Γ (i : fin n) :
  ⊨ Γ ->
  Γ ⊨ VarPTm i ∈ Γ i.
Proof.
  move /(_ i) => [j /SemWt_Univ h].
  rewrite /SemWt => ρ /[dup] hρ {}/h [S hS].
  exists j, S.
  asimpl. firstorder.
Qed.

Lemma InterpUniv_Bind_nopf n p i (A : PTm n) B PA :
  ⟦ A ⟧ i ↘ PA ->
  (forall a, PA a -> exists PB, ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB) ->
  ⟦ PBind p A B ⟧ i ↘ (BindSpace p PA (fun a PB => ⟦ subst_PTm (scons a VarPTm) B ⟧ i ↘ PB)).
Proof.
  move => h0 h1. apply InterpUniv_Bind => //=.
Qed.


Lemma ST_Bind n Γ i j p (A : PTm n) (B : PTm (S n)) :
  Γ ⊨ A ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A Γ) ⊨ B ∈ PUniv j ->
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

Lemma ST_Abs n Γ (a : PTm (S n)) A B i :
  Γ ⊨ PBind PPi A B ∈ (PUniv i) ->
  funcomp (ren_PTm shift) (scons A Γ) ⊨ a ∈ B ->
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

Lemma ST_App n Γ (b a : PTm n) A B :
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

Lemma ST_Pair n Γ (a b : PTm n) A B i :
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

Lemma N_Projs n p (a b : PTm n) :
  rtc TRedSN a b ->
  rtc TRedSN (PProj p a) (PProj p b).
Proof. induction 1; hauto lq:on ctrs:rtc, TRedSN. Qed.

Lemma ST_Proj1 n Γ (a : PTm n) A B :
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

Lemma ST_Proj2 n Γ (a : PTm n) A B :
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
      suff : BJoin.R (subst_PTm (scons (PProj PL (subst_PTm ρ a)) ρ) B) (subst_PTm (scons a0 ρ) B)
        by hauto q:on use:DJoin.FromBJoin.
      have : BJoin.R (PApp (PAbs (subst_PTm (up_PTm_PTm ρ) B)) (PProj PL (subst_PTm ρ a)))
               (subst_PTm (scons (PProj PL (subst_PTm ρ a)) ρ) B).
      eexists. split. apply relations.rtc_once. apply RRed.AppAbs.
      asimpl. apply rtc_refl.
      have /BJoin.symmetric : BJoin.R (PApp (PAbs (subst_PTm (up_PTm_PTm ρ)B)) a0)
                                (subst_PTm (scons a0 ρ) B).
      eexists. split. apply relations.rtc_once. apply RRed.AppAbs.
      asimpl. apply rtc_refl.
      suff : BJoin.R (PApp (PAbs (subst_PTm (up_PTm_PTm ρ) B)) (PProj PL (subst_PTm ρ a)))
               (PApp (PAbs (subst_PTm (up_PTm_PTm ρ)B)) a0) by eauto using BJoin.transitive, BJoin.symmetric.
      apply BJoin.AppCong. apply BJoin.refl.
      move /RReds.FromRedSNs : hr'.
      hauto lq:on ctrs:rtc unfold:BJoin.R.
    + hauto lq:on use:@relations.rtc_r, InterpUniv_back_closs.
Qed.

Lemma ST_Conv n Γ (a : PTm n) A B i :
  Γ ⊨ a ∈ A ->
  Γ ⊨ B ∈ PUniv i ->
  DJoin.R A B ->
  Γ ⊨ a ∈ B.
Proof.
  move => ha /SemWt_Univ h h0.
  move => ρ hρ.
  have {}h0 : DJoin.R (subst_PTm ρ A) (subst_PTm ρ B) by eauto using DJoin.substing.
  move /ha : (hρ){ha} => [m [PA [h1 h2]]].
  move /h : (hρ){h} => [S hS].
  have ? : PA = S by eauto using InterpUniv_Join'. subst.
  eauto.
Qed.

Lemma SE_Refl n Γ (a : PTm n) A :
  Γ ⊨ a ∈ A ->
  Γ ⊨ a ≡ a ∈ A.
Proof. hauto lq:on unfold:SemWt,SemEq use:DJoin.refl. Qed.

Lemma SE_Symmetric n Γ (a b : PTm n) A :
  Γ ⊨ a ≡ b ∈ A ->
  Γ ⊨ b ≡ a ∈ A.
Proof. hauto q:on unfold:SemEq. Qed.

Lemma SE_Transitive n Γ (a b c : PTm n) A :
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

Lemma Γ_eq_ρ_ok n Γ Δ (ρ : fin n -> PTm 0) : Γ_eq Γ Δ -> ⊨ Γ -> ρ_ok Γ ρ -> ρ_ok Δ ρ.
Proof.
  move => hΓΔ hΓ h.
  move => i k PA hPA.
  move : hΓ. rewrite /SemWff. move /(_ i) => [j].
  move => hΓ.
  rewrite SemWt_Univ in hΓ.
  have {}/hΓ  := h.
  move => [S hS].
  move /(_ i) in h. suff : PA = S by qauto l:on.
  move : InterpUniv_Join' hPA hS. repeat move/[apply].
  apply. move /(_ i) /DJoin.symmetric in hΓΔ.
  hauto l:on use: DJoin.substing.
Qed.

Lemma Γ_eq_refl n (Γ : fin n -> PTm n) :
  Γ_eq Γ Γ.
Proof. sfirstorder use:DJoin.refl. Qed.

Lemma Γ_eq_cons n (Γ Δ : fin n -> PTm n) A B :
  DJoin.R A B ->
  Γ_eq Γ Δ ->
  Γ_eq (funcomp (ren_PTm shift) (scons A Γ)) (funcomp (ren_PTm shift) (scons B Δ)).
Proof.
  move => h h0.
  move => i.
  destruct i as [i|].
  rewrite /funcomp. substify. apply DJoin.substing. by asimpl.
  rewrite /funcomp.
  asimpl. substify. apply DJoin.substing. by asimpl.
Qed.

Lemma Γ_eq_cons' n (Γ : fin n -> PTm n) A B :
  DJoin.R A B ->
  Γ_eq (funcomp (ren_PTm shift) (scons A Γ)) (funcomp (ren_PTm shift) (scons B Γ)).
Proof. eauto using Γ_eq_refl ,Γ_eq_cons. Qed.

Lemma SE_Bind n Γ i j p (A0 A1 : PTm n) B0 B1 :
  ⊨ Γ ->
  Γ ⊨ A0 ≡ A1 ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A0 Γ) ⊨ B0 ≡ B1 ∈ PUniv j ->
  Γ ⊨ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv (max i j).
Proof.
  move => hΓ hA hB.
  apply SemEq_SemWt in hA, hB.
  apply SemWt_SemEq; last by hauto l:on use:DJoin.BindCong.
  hauto l:on use:ST_Bind.
  apply ST_Bind; first by tauto.
  have hΓ' : ⊨ funcomp (ren_PTm shift) (scons A1 Γ) by hauto l:on use:SemWff_cons.
  move => ρ hρ.
  suff : ρ_ok (funcomp (ren_PTm shift) (scons A0 Γ)) ρ by hauto l:on.
  move : Γ_eq_ρ_ok hΓ' hρ; repeat move/[apply]. apply.


  best use:
  move => j0 k PA.
  destruct j0 as [j0|].
  asimpl.
  move /(_ (Some j0) k PA) : hρ. by asimpl.
  asimpl.
  have h : Γ ⊨ A1 ∈ PUniv i by tauto.
  rewrite /SemWff in hΓ'.
  move /(_ None) : hΓ' => [l h'].
  rewrite SemWt_Univ in h'.
  have {}/h' := hρ.
  move => [PA'].
  asimpl. move => h0 h1.
  move /(_ None l PA) : (hρ). asimpl.
  suff : PA = PA' by qauto l:on.
  move : InterpUniv_Join' h1 h0; repeat move/[apply].
  apply. apply DJoin.substing. tauto.
Qed.
