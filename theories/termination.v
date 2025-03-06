Require Import common Autosubst2.core Autosubst2.unscoped Autosubst2.syntax algorithmic fp_red executable.
From Hammer Require Import Tactics.
Require Import ssreflect ssrbool.
From stdpp Require Import relations (nsteps (..), rtc(..)).
Import Psatz.

Lemma tm_conf_sym a b : tm_conf a b = tm_conf b a.
Proof. case : a; case : b => //=. Qed.

#[export]Hint Constructors algo_dom algo_dom_r : adom.

Lemma algo_dom_r_inv a b :
  algo_dom_r a b -> exists a0 b0, algo_dom a0 b0 /\ rtc HRed.R a a0 /\ rtc HRed.R b b0.
Proof.
  induction 1; hauto lq:on ctrs:rtc.
Qed.

Lemma A_HRedsL a a' b :
  rtc HRed.R a a' ->
  algo_dom_r a' b ->
  algo_dom_r a b.
  induction 1; sfirstorder use:A_HRedL.
Qed.

Lemma A_HRedsR a b b' :
  HRed.nf a ->
  rtc HRed.R b b' ->
  algo_dom a b' ->
  algo_dom_r a b.
Proof. induction 2; sauto. Qed.

Lemma algo_dom_sym :
  (forall a b (h : algo_dom a b), algo_dom b a) /\
    (forall a b (h : algo_dom_r a b), algo_dom_r b a).
Proof.
  apply algo_dom_mutual; try qauto use:tm_conf_sym db:adom.
  move => a a' b hr h ih.
  move /algo_dom_r_inv : ih => [a0][b0][ih0][ih1]ih2.
  have nfa0 : HRed.nf a0 by sfirstorder use:algo_dom_no_hred.
  sauto use:A_HRedsL, A_HRedsR.
Qed.

Definition term_metric k (a b : PTm) :=
  exists i j va vb, nsteps LoRed.R i a va /\ nsteps LoRed.R j b vb /\ nf va /\ nf vb /\ size_PTm va + size_PTm vb + i + j <= k.

Lemma term_metric_sym k (a b : PTm) :
  term_metric k a b -> term_metric k b a.
Proof. hauto lq:on unfold:term_metric solve+:lia. Qed.

Lemma term_metric_case k (a b : PTm) :
  term_metric k a b ->
  (ishf a \/ ishne a) \/ exists k' a', HRed.R a a' /\ term_metric k' a' b /\ k' < k.
Proof.
  move=>[i][j][va][vb][h0] [h1][h2][h3]h4.
  case : a h0 => //=; try firstorder.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.AppAbs unfold:term_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:term_metric solve+:lia.
    + sfirstorder qb:on use:ne_hne.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.ProjPair unfold:term_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:term_metric solve+:lia.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.IndZero unfold:term_metric solve+:lia.
    + hauto lq:on ctrs:HRed.R use:hf_hred_lored unfold:term_metric solve+:lia.
    + sfirstorder use:ne_hne.
    + hauto lq:on ctrs:HRed.R use:hf_hred_lored unfold:term_metric solve+:lia.
    + sfirstorder use:ne_hne.
    + sfirstorder use:ne_hne.
Qed.

Lemma A_Conf' a b :
  ishf a \/ ishne a ->
  ishf b \/ ishne b ->
  tm_conf a b ->
  algo_dom_r a b.
Proof.
  move => ha hb.
  have {}ha : HRed.nf a by sfirstorder use:hf_no_hred, hne_no_hred.
  have {}hb : HRed.nf b by sfirstorder use:hf_no_hred, hne_no_hred.
  move => ?.
  apply A_NfNf.
  by apply A_Conf.
Qed.

Lemma term_metric_abs : forall k a b,
    term_metric k (PAbs a) (PAbs b) ->
    exists k', k' < k /\ term_metric k' a b.
Proof.
  move => k a b [i][j][va][vb][hva][hvb][nfa][nfb]h.
  apply lored_nsteps_abs_inv in hva, hvb.
  move : hva => [a'][hva]?. subst.
  move : hvb => [b'][hvb]?. subst.
  simpl in *. exists (k - 1).
  hauto lq:on unfold:term_metric solve+:lia.
Qed.

Lemma term_metric_pair : forall k a0 b0 a1 b1,
    term_metric k (PPair a0 b0) (PPair a1 b1) ->
    exists k', k' < k /\ term_metric k' a0 a1 /\ term_metric k' b0 b1.
Proof.
  move => k a0 b0 a1 b1 [i][j][va][vb][hva][hvb][nfa][nfb]h.
  apply lored_nsteps_pair_inv in hva, hvb.
  move : hva => [?][?][?][?][?][?][?][?]?.
  move : hvb => [?][?][?][?][?][?][?][?]?. subst.
  simpl in *. exists (k - 1).
  hauto lqb:on solve+:lia.
Qed.

Lemma term_metric_bind : forall k p0 a0 b0 p1 a1 b1,
    term_metric k (PBind p0 a0 b0) (PBind p1 a1 b1) ->
    exists k', k' < k /\ term_metric k' a0 a1 /\ term_metric k' b0 b1.
Proof.
  move => k p0 a0 b0 p1 a1 b1 [i][j][va][vb][hva][hvb][nfa][nfb]h.
  apply lored_nsteps_bind_inv in hva, hvb.
  move : hva => [?][?][?][?][?][?][?][?]?.
  move : hvb => [?][?][?][?][?][?][?][?]?. subst.
  simpl in *. exists (k - 1).
  hauto lqb:on solve+:lia.
Qed.

Lemma term_metric_suc : forall k a b,
    term_metric k (PSuc a) (PSuc b) ->
    exists k', k' < k /\ term_metric k' a b.
Proof.
  move => k a b [i][j][va][vb][hva][hvb][nfa][nfb]h.
  apply lored_nsteps_suc_inv in hva, hvb.
  move : hva => [a'][hva]?. subst.
  move : hvb => [b'][hvb]?. subst.
  simpl in *. exists (k - 1).
  hauto lq:on unfold:term_metric solve+:lia.
Qed.

Lemma term_metric_abs_neu k (a0 : PTm) u :
  term_metric k (PAbs a0) u ->
  ishne u ->
  exists j, j < k /\ term_metric j a0 (PApp (ren_PTm shift u) (VarPTm var_zero)).
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3]h4 neu.
  have neva : ne vb by hauto lq:on use:hne_nf_ne, loreds_hne_preservation, @relations.rtc_nsteps.
  move /lored_nsteps_abs_inv : h0 => [a1][h01]?. subst.
  exists (k - 1).
  simpl in *. split. lia.
  exists i,j,a1,(PApp (ren_PTm shift vb) (VarPTm var_zero)).
  repeat split => //=.
  apply lored_nsteps_app_cong.
  by apply lored_nsteps_renaming.
  by rewrite ishne_ren.
  rewrite Bool.andb_true_r.
  sfirstorder use:ne_nf_ren.
  rewrite size_PTm_ren. lia.
Qed.

Lemma term_metric_pair_neu k (a0 b0 : PTm) u :
  term_metric k (PPair a0 b0) u ->
  ishne u ->
  exists j, j < k /\ term_metric j (PProj PL u) a0 /\ term_metric j (PProj PR u) b0.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3]h4 neu.
  have neva : ne vb by hauto lq:on use:hne_nf_ne, loreds_hne_preservation, @relations.rtc_nsteps.
  move /lored_nsteps_pair_inv : h0 => [i0][j0][a1][b1][?][?][?][?]?. subst.
  exists (k-1). sauto qb:on use:lored_nsteps_proj_cong unfold:term_metric solve+:lia.
Qed.

Lemma term_metric_app k (a0 b0 a1 b1 : PTm) :
  term_metric k (PApp a0 b0) (PApp a1 b1) ->
  ishne a0 ->
  ishne a1 ->
  exists j, j < k /\ term_metric j a0 a1 /\ term_metric j b0 b1.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3]h4.
  move => hne0 hne1.
  move : lored_nsteps_app_inv h0 (hne0);repeat move/[apply].
  move => [i0][i1][a2][b2][?][?][?][ha02]hb02. subst.
  move : lored_nsteps_app_inv h1 (hne1);repeat move/[apply].
  move => [j0][j1][a3][b3][?][?][?][ha13]hb13. subst.
  simpl in *. exists (k - 1). hauto lqb:on use:lored_nsteps_app_cong, ne_nf unfold:term_metric solve+:lia.
Qed.

Lemma term_metric_proj k p0 p1 (a0 a1 : PTm) :
  term_metric k (PProj p0 a0) (PProj p1 a1) ->
  ishne a0 ->
  ishne a1 ->
  exists j, j < k /\ term_metric j a0 a1.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3]h4 hne0 hne1.
  move : lored_nsteps_proj_inv h0 (hne0);repeat move/[apply].
  move => [i0][a2][hi][?]ha02. subst.
  move : lored_nsteps_proj_inv h1 (hne1);repeat move/[apply].
  move => [i1][a3][hj][?]ha13. subst.
  exists (k- 1).  hauto q:on use:ne_nf solve+:lia.
Qed.

Lemma term_metric_ind k P0 (a0 : PTm ) b0 c0 P1 a1 b1 c1 :
  term_metric k (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1) ->
  ishne a0 ->
  ishne a1 ->
  exists j, j < k /\ term_metric j P0 P1 /\ term_metric j a0 a1 /\
         term_metric j b0 b1 /\ term_metric j c0 c1.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3]h4 hne0 hne1.
  move /lored_nsteps_ind_inv /(_ hne0) : h0.
  move =>[iP][ia][ib][ic][P2][a2][b2][c2][?][?][?][?][?][?][?][?]?. subst.
  move /lored_nsteps_ind_inv /(_ hne1) : h1.
  move =>[iP0][ia0][ib0][ic0][P3][a3][b3][c3][?][?][?][?][?][?][?][?]?. subst.
  exists (k -1). simpl in *.
  hauto lq:on rew:off use:ne_nf b:on solve+:lia.
Qed.


Lemma algo_dom_r_algo_dom : forall a b, HRed.nf a -> HRed.nf b -> algo_dom_r a b -> algo_dom a b.
Proof. hauto l:on use:algo_dom_r_inv, hreds_nf_refl. Qed.

Lemma term_metric_algo_dom : forall k a b, term_metric k a b -> algo_dom_r a b.
Proof.
  move => [:hneL].
  elim /Wf_nat.lt_wf_ind.
  move => n ih a b h.
  case /term_metric_case : (h); cycle 1.
  move => [k'][a'][h0][h1]h2.
  by apply : A_HRedL; eauto.
  case /term_metric_sym /term_metric_case : (h); cycle 1.
  move => [k'][b'][hb][/term_metric_sym h0]h1.
  move => ha. have {}ha : HRed.nf a by sfirstorder use:hf_no_hred, hne_no_hred.
  by apply : A_HRedR; eauto.
  move => /[swap].
  case => hfa; case => hfb.
  - move : hfa hfb h.
    case : a; case : b => //=; eauto 5 using A_Conf' with adom.
    + hauto lq:on use:term_metric_abs db:adom.
    + hauto lq:on use:term_metric_pair db:adom.
    + hauto lq:on use:term_metric_bind db:adom.
    + hauto lq:on use:term_metric_suc db:adom.
  - abstract : hneL n ih a b h hfa hfb.
    case : a hfa h => //=.
    + hauto lq:on use:term_metric_abs_neu db:adom.
    + scrush use:term_metric_pair_neu db:adom.
    + case : b hfb => //=; eauto 5 using A_Conf' with adom.
    + case : b hfb => //=; eauto 5 using A_Conf' with adom.
    + case : b hfb => //=; eauto 5 using A_Conf' with adom.
    + case : b hfb => //=; eauto 5 using A_Conf' with adom.
    + case : b hfb => //=; eauto 5 using A_Conf' with adom.
  - hauto q:on use:algo_dom_sym, term_metric_sym.
  - move {hneL}.
    case : b hfa hfb h => //=; case a => //=; eauto 5 using A_Conf' with adom.
    + move => a0 b0 a1 b1 nfa0 nfa1.
      move /term_metric_app /(_ nfa0  nfa1) => [j][hj][ha]hb.
      apply A_NfNf. apply A_AppCong => //; eauto.
      have {}nfa0 : HRed.nf a0 by sfirstorder use:hne_no_hred.
      have {}nfb0 : HRed.nf a1 by sfirstorder use:hne_no_hred.
      eauto using algo_dom_r_algo_dom.
    + move => p0 A0 p1 A1 neA0 neA1.
      have {}nfa0 : HRed.nf A0 by sfirstorder use:hne_no_hred.
      have {}nfb0 : HRed.nf A1 by sfirstorder use:hne_no_hred.
      hauto lq:on use:term_metric_proj, algo_dom_r_algo_dom db:adom.
    + move => P0 a0 b0 c0 P1 a1 b1 c1 nea0 nea1.
      have {}nfa0 : HRed.nf a0 by sfirstorder use:hne_no_hred.
      have {}nfb0 : HRed.nf a1 by sfirstorder use:hne_no_hred.
      hauto lq:on use:term_metric_ind, algo_dom_r_algo_dom db:adom.
Qed.

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
