Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common executable algorithmic.
Require Import ssreflect ssrbool.
From stdpp Require Import relations (rtc(..)).
From Hammer Require Import Tactics.
Require Import PeanoNat (Nat.eq_dec).

Lemma coqeqr_no_hred a b : a ∼ b -> HRed.nf a /\ HRed.nf b.
Proof. induction 1; sauto lq:on unfold:HRed.nf. Qed.

Lemma coqeq_no_hred a b : a ↔ b -> HRed.nf a /\ HRed.nf b.
Proof. induction 1;
         qauto inv:HRed.R use:coqeqr_no_hred, hne_no_hred unfold:HRed.nf.
Qed.

Lemma coqleq_no_hred a b : a ⋖ b -> HRed.nf a /\ HRed.nf b.
Proof.
  induction 1; qauto inv:HRed.R use:coqeqr_no_hred, hne_no_hred, coqeqr_no_hred unfold:HRed.nf.
Qed.

Lemma coqeq_neuneu u0 u1 :
  ishne u0 -> ishne u1 -> u0 ↔ u1 -> u0 ∼ u1.
Proof.
  inversion 3; subst => //=.
Qed.

Lemma coqeq_neuneu' u0 u1 :
  neuneu_nonconf u0 u1 ->
  u0 ↔ u1 ->
  u0 ∼ u1.
Proof.
  induction 2 => //=; destruct u => //=.
Qed.

Lemma check_equal_sound :
  (forall a b (h : algo_dom a b), check_equal a b h -> a ↔ b) /\
  (forall a b (h : algo_dom_r a b), check_equal_r a b h -> a ⇔ b).
Proof.
  apply algo_dom_mutual.
  - move => a b h.
    move => h0.
    rewrite check_equal_abs_abs.
    constructor. tauto.
  - move => a u i h0 ih h.
    apply CE_AbsNeu => //.
    apply : ih.
    by rewrite check_equal_abs_neu in h.
  - move => a u i h ih h0.
    apply CE_NeuAbs=>//.
    apply ih.
    by rewrite check_equal_neu_abs in h0.
  - move => a0 a1 b0 b1 a ha h.
    move => h0.
    rewrite check_equal_pair_pair. move /andP => [h1 h2].
    sauto lq:on.
  - move => a0 a1 u neu h ih h' ih' he.
    rewrite check_equal_pair_neu in he.
    apply CE_PairNeu => //; hauto lqb:on.
  - move => a0 a1 u i a ha a2 hb.
    rewrite check_equal_neu_pair => *.
    apply CE_NeuPair => //; hauto lqb:on.
  - sfirstorder.
  - hauto l:on use:CE_SucSuc.
  - move => i j /sumboolP.
    hauto lq:on use:CE_UnivCong.
  - move => p0 p1 A0 A1 B0 B1 h0 ih0 h1 ih1 h2.
    rewrite check_equal_bind_bind in h2.
    move : h2.
    move /andP => [/andP [h20 h21] h3].
    move /sumboolP : h20 => ?. subst.
    hauto l:on use:CE_BindCong.
  - sfirstorder.
  - move => i j /sumboolP ?.  subst.
    apply : CE_NeuNeu. apply CE_VarCong.
  - move => u0 u1 a0 a1 hu0 hu1 hdom ih hdom' ih' hE.
    rewrite check_equal_app_app in hE.
    move /andP : hE => [h0 h1].
    sauto lq:on use:coqeq_neuneu.
  - move => p0 p1 u0 u1 neu0 neu1 h ih he.
    apply CE_NeuNeu.
    rewrite check_equal_proj_proj in he.
    move /andP : he => [/sumboolP ? h1]. subst.
    sauto lq:on use:coqeq_neuneu.
  - move => P0 P1 u0 u1 b0 b1 c0 c1 neu0 neu1 domP ihP domu ihu domb ihb domc ihc.
    rewrite check_equal_ind_ind.
    move /andP => [/andP [/andP [h0 h1] h2 ] h3].
    sauto lq:on use:coqeq_neuneu.
  - move => a b n n0 i. by rewrite check_equal_conf.
  - move => a b dom h ih. apply : CE_HRed; eauto using rtc_refl.
    rewrite check_equal_nfnf in ih.
    tauto.
  - move => a a' b ha doma ih hE.
    rewrite check_equal_hredl in hE. sauto lq:on.
  - move => a b b' hu r a0 ha hb. rewrite check_equal_hredr in hb.
    sauto lq:on rew:off.
Qed.

Ltac ce_solv := move => *; autorewrite with ce_prop in *; hauto qb:on rew:off inv:CoqEq, CoqEq_Neu.

Lemma check_equal_complete :
  (forall a b (h : algo_dom a b), ~ check_equal a b h -> ~ a ↔ b) /\
  (forall a b (h : algo_dom_r a b), ~ check_equal_r a b h -> ~ a ⇔ b).
Proof.
  apply algo_dom_mutual.
  - ce_solv.
  - ce_solv.
  - ce_solv.
  - ce_solv.
  - ce_solv.
  - ce_solv.
  - ce_solv.
  - ce_solv.
  - move => i j.
    rewrite check_equal_univ.
    case : Nat.eq_dec => //=.
    ce_solv.
  - move => p0 p1 A0 A1 B0 B1 h0 ih0 h1 ih1.
    rewrite check_equal_bind_bind.
    move /negP.
    move /nandP.
    case. move /nandP.
    case. move => h. have : p0 <> p1  by sauto lqb:on.
    clear. move => ?. hauto lq:on rew:off inv:CoqEq, CoqEq_Neu.
    hauto qb:on inv:CoqEq,CoqEq_Neu.
    hauto qb:on inv:CoqEq,CoqEq_Neu.
  - done.
  - move => i j. move => h. have {h} : ~ Nat.eq_dec i j by done.
    case : Nat.eq_dec => //=. ce_solv.
  - move => u0 u1 a0 a1 hu0 hu1 h0 ih0 h1 ih1.
    rewrite check_equal_app_app.
    move /negP /nandP. sauto b:on inv:CoqEq, CoqEq_Neu.
  - move => p0 p1 u0 u1 neu0 neu1 h ih.
    rewrite check_equal_proj_proj.
    move /negP /nandP. case.
    case : PTag_eq_dec => //=. sauto lq:on.
    sauto lqb:on.
  - move => P0 P1 u0 u1 b0 b1 c0 c1 neu0 neu1 domP ihP domu ihu domb ihb domc ihc.
    rewrite check_equal_ind_ind.
    move => + h.
    inversion h; subst.
    inversion H; subst.
    move /negP /nandP.
    case. move/nandP.
    case. move/nandP.
    case. qauto b:on inv:CoqEq, CoqEq_Neu.
    sauto lqb:on inv:CoqEq, CoqEq_Neu.
    sauto lqb:on inv:CoqEq, CoqEq_Neu.
    sauto lqb:on inv:CoqEq, CoqEq_Neu.
  - rewrite /tm_conf.
    move => a b n n0 i.
    move => _. inversion 1; subst => //=.
    + destruct b => //=.
    + destruct a => //=.
    + destruct b => //=.
    + destruct a => //=.
    + hauto l:on inv:CoqEq_Neu.
  - move => a b h ih.
    rewrite check_equal_nfnf.
    move : ih => /[apply].
    move => + h0.
    have {h} [? ?] : HRed.nf a /\ HRed.nf b by sfirstorder use:algo_dom_no_hred.
    inversion h0; subst.
    hauto l:on use:hreds_nf_refl.
  - move => a a' b h dom.
    autorewrite with ce_prop => /[apply].
    move => + h1. inversion h1; subst.
    inversion H; subst.
    + sfirstorder use:coqeq_no_hred unfold:HRed.nf.
    + have ? : y = a' by eauto using hred_deter. subst.
      sauto lq:on.
  - move => a b b' u hr dom ihdom.
    rewrite check_equal_hredr.
    move => + h. inversion h; subst.
    have {}u : HRed.nf a by sfirstorder use:hne_no_hred, hf_no_hred.
    move => {}/ihdom.
    inversion H0; subst.
    + have ? : HRed.nf b'0 by hauto l:on use:coqeq_no_hred.
      sfirstorder unfold:HRed.nf.
    + sauto lq:on use:hred_deter.
Qed.

Ltac simp_sub := with_strategy opaque [check_equal] simpl in *.

Lemma check_sub_sound :
  (forall a b (h : salgo_dom a b), check_sub a b h -> a ⋖ b) /\
    (forall a b (h : salgo_dom_r a b), check_sub_r a b h -> a ≪ b).
Proof.
  apply salgo_dom_mutual; try done.
  - simpl. move => i j;
    sauto lq:on use:Reflect.Nat_leb_le.
  - move => A0 A1 B0 B1 s ihs s0 ihs0.
    autorewrite with ce_prop.
    hauto lqb:on ctrs:CoqLEq.
  - move => A0 A1 B0 B1 s ihs s0 ihs0.
    autorewrite with ce_prop.
    hauto lqb:on ctrs:CoqLEq.
  - qauto ctrs:CoqLEq.
  - move => a b i a0.
    autorewrite with ce_prop.
    move => h. apply CLE_NeuNeu.
    hauto lq:on use:check_equal_sound, coqeq_neuneu', coqeq_symmetric_mutual.
  - move => a b n n0 i.
    by autorewrite with ce_prop.
  - move => a b h ih. autorewrite with ce_prop. hauto l:on.
  - move => a a' b hr h ih.
    autorewrite with ce_prop.
    sauto lq:on rew:off.
  - move => a b b' n r dom ihdom.
    autorewrite with ce_prop.
    move : ihdom => /[apply].
    move {dom}.
    sauto lq:on rew:off.
Qed.

Lemma check_sub_complete :
  (forall a b (h : salgo_dom a b), check_sub a b h = false -> ~ a ⋖ b) /\
    (forall a b (h : salgo_dom_r a b), check_sub_r a b h = false -> ~ a ≪ b).
Proof.
  apply salgo_dom_mutual; try first [done | hauto depth:4 lq:on inv:CoqLEq, CoqEq_Neu].
  - move => i j /=.
    move => + h. inversion h; subst => //=.
    sfirstorder use:PeanoNat.Nat.leb_le.
    hauto lq:on inv:CoqEq_Neu.
  - move => A0 A1 B0 B1 s ihs s' ihs'. autorewrite with ce_prop.
    move /nandP.
    case.
    move => /negbTE {}/ihs. hauto q:on inv:CoqLEq, CoqEq_Neu.
    move => /negbTE {}/ihs'. hauto q:on inv:CoqLEq, CoqEq_Neu.
  - move => A0 A1 B0 B1 s ihs s' ihs'. autorewrite with ce_prop.
    move /nandP.
    case.
    move => /negbTE {}/ihs. hauto q:on inv:CoqLEq, CoqEq_Neu.
    move => /negbTE {}/ihs'. hauto q:on inv:CoqLEq, CoqEq_Neu.
  - move => a b i hs. autorewrite with ce_prop.
    move => + h. inversion h; subst => //=.
    move => /negP h0.
    eapply check_equal_complete in h0.
    apply h0. by constructor.
  - move => a b s ihs. autorewrite with ce_prop.
    move => h0 h1. apply ihs =>//.
    have [? ?] : HRed.nf a /\ HRed.nf b by hauto l:on use:salgo_dom_no_hred.
    inversion h1; subst.
    hauto l:on use:hreds_nf_refl.
  - move => a a' b h dom.
    autorewrite with ce_prop => /[apply].
    move => + h1. inversion h1; subst.
    inversion H; subst.
    + sfirstorder use:coqleq_no_hred unfold:HRed.nf.
    + have ? : y = a' by eauto using hred_deter. subst.
      sauto lq:on.
  - move => a b b' u hr dom ihdom.
    rewrite check_sub_hredr.
    move => + h. inversion h; subst.
    have {}u : HRed.nf a by sfirstorder use:hne_no_hred, hf_no_hred.
    move => {}/ihdom.
    inversion H0; subst.
    + have ? : HRed.nf b'0 by hauto l:on use:coqleq_no_hred.
      sfirstorder unfold:HRed.nf.
    + sauto lq:on use:hred_deter.
Qed.
