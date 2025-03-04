From Equations Require Import Equations.
Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common executable algorithmic.
Require Import ssreflect ssrbool.
From stdpp Require Import relations (rtc(..)).
From Hammer Require Import Tactics.

Scheme algo_ind := Induction for algo_dom Sort Prop
  with algor_ind := Induction for algo_dom_r Sort Prop.

Combined Scheme algo_dom_mutual from algo_ind, algor_ind.

Lemma check_equal_abs_abs a b h : check_equal (PAbs a) (PAbs b) (A_AbsAbs a b h) = check_equal_r a b h.
Proof. hauto l:on rew:db:check_equal. Qed.

Lemma check_equal_abs_neu a u neu h : check_equal (PAbs a) u (A_AbsNeu a u neu h) = check_equal_r a (PApp (ren_PTm shift u) (VarPTm var_zero)) h.
Proof. case : u neu h => //=.  Qed.

Lemma check_equal_neu_abs a u neu h : check_equal u (PAbs a) (A_NeuAbs a u neu h) = check_equal_r (PApp (ren_PTm shift u) (VarPTm var_zero)) a h.
Proof. case : u neu h => //=.  Qed.

Lemma check_equal_pair_pair a0 b0 a1 b1 a h :
  check_equal (PPair a0 b0) (PPair a1 b1) (A_PairPair a0 a1 b0 b1 a h) =
    check_equal_r a0 a1 a && check_equal_r b0 b1 h.
Proof. hauto l:on rew:db:check_equal. Qed.

Lemma check_equal_pair_neu a0 a1 u neu h h'
  : check_equal (PPair a0 a1) u (A_PairNeu a0 a1 u neu h h') = check_equal_r a0 (PProj PL u) h && check_equal_r a1 (PProj PR u) h'.
Proof.
  case : u neu h h' => //=; simp check_equal tm_to_eq_view.
Qed.

Lemma check_equal_neu_pair a0 a1 u neu h h'
  : check_equal u (PPair a0 a1) (A_NeuPair a0 a1 u neu h h') = check_equal_r  (PProj PL u) a0 h && check_equal_r (PProj PR u) a1 h'.
Proof.
  case : u neu h h' => //=; simp check_equal tm_to_eq_view.
Qed.

Lemma check_equal_bind_bind p0 A0 B0 p1 A1 B1 h0 h1 :
  check_equal (PBind p0 A0 B0) (PBind p1 A1 B1) (A_BindCong p0 p1 A0 A1 B0 B1 h0 h1) =
    BTag_eqdec p0 p1 &&  check_equal_r A0 A1 h0 && check_equal_r  B0 B1 h1.
Proof. hauto lq:on. Qed.

Lemma check_equal_proj_proj p0 u0 p1 u1 neu0 neu1 h :
  check_equal (PProj p0 u0) (PProj p1 u1) (A_ProjCong p0 p1 u0 u1 neu0 neu1 h) =
    PTag_eqdec p0 p1 && check_equal u0 u1 h.
Proof. hauto lq:on. Qed.

Lemma check_equal_app_app u0 a0 u1 a1 hu0 hu1 hdom hdom' :
  check_equal (PApp u0 a0) (PApp u1 a1) (A_AppCong u0 u1 a0 a1 hu0 hu1 hdom hdom') =
    check_equal u0 u1 hdom && check_equal_r a0 a1 hdom'.
Proof. hauto lq:on. Qed.

Lemma check_equal_ind_ind P0 u0 b0 c0 P1 u1 b1 c1 neu0 neu1 domP domu domb domc :
  check_equal (PInd P0 u0 b0 c0) (PInd P1 u1 b1 c1)
    (A_IndCong P0 P1 u0 u1 b0 b1 c0 c1 neu0 neu1 domP domu domb domc) =
    check_equal_r P0 P1 domP && check_equal u0 u1 domu && check_equal_r b0 b1 domb && check_equal_r c0 c1 domc.
Proof. hauto lq:on. Qed.

Lemma hred_none a : HRed.nf a -> hred a = None.
Proof.
  destruct (hred a) eqn:eq;
  sfirstorder use:hred_complete, hred_sound.
Qed.

Lemma check_equal_nfnf a b dom : check_equal_r a b (A_NfNf a b dom) = check_equal a b dom.
Proof.
  have [h0 h1] : (ishf a \/ ishne a) /\ (ishf b \/ ishne b) by hauto l:on use:algo_dom_hf_hne.
  have [h3 h4] : hred a = None /\ hred b = None by sfirstorder use:hf_no_hred, hne_no_hred, hred_none.
  simp check_equal.
  destruct (fancy_hred a).
  simp check_equal.
  destruct (fancy_hred b).
  simp check_equal. hauto lq:on.
  exfalso. hauto l:on use:hred_complete.
  exfalso. hauto l:on use:hred_complete.
Qed.

Lemma check_equal_hredl a b a' ha doma :
  check_equal_r a b (A_HRedL a a' b ha doma) = check_equal_r a' b doma.
Proof.
  simp check_equal.
  destruct (fancy_hred a).
  - hauto q:on unfold:HRed.nf.
  - simp check_equal.
    destruct s as [x ?]. have ? : x = a' by eauto using hred_deter. subst.
    simpl.
    simp check_equal.
    f_equal.
    apply PropExtensionality.proof_irrelevance.
Qed.

Lemma check_equal_hredr a b b' hu r a0 :
  check_equal_r a b (A_HRedR a b b' hu r a0) =
    check_equal_r a b' a0.
Proof.
  simp check_equal.
  destruct (fancy_hred a).
  - rewrite check_equal_r_clause_1_equation_1.
    destruct (fancy_hred b) as [|[b'' hb']].
    + hauto lq:on unfold:HRed.nf.
    + have ? : (b'' = b') by eauto using hred_deter. subst.
      rewrite check_equal_r_clause_1_equation_1.  simpl.
      simp check_equal. destruct (fancy_hred a). simp check_equal.
      f_equal; apply PropExtensionality.proof_irrelevance.
      simp check_equal. exfalso. sfirstorder use:hne_no_hred, hf_no_hred.
  - simp check_equal. exfalso.
    sfirstorder use:hne_no_hred, hf_no_hred.
Qed.

Lemma coqeq_neuneu u0 u1 :
  ishne u0 -> ishne u1 -> u0 ↔ u1 -> u0 ∼ u1.
Proof.
  inversion 3; subst => //=.
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
    apply : ih. simp check_equal tm_to_eq_view in h.
    have h1 : check_equal (PAbs a) u (A_AbsNeu a u i h0) = check_equal_r a (PApp (ren_PTm shift u) (VarPTm var_zero)) h0 by  clear; case : u i h0 => //=.
    hauto lq:on.
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
  - move => p0 p1 u0 u1 neu0 neu1 h ih he.
    apply CE_NeuNeu.
    rewrite check_equal_proj_proj in he.
    move /andP : he => [/sumboolP ? h1]. subst.
    sauto lq:on use:coqeq_neuneu.
  - move => u0 u1 a0 a1 hu0 hu1 hdom ih hdom' ih' hE.
    rewrite check_equal_app_app in hE.
    move /andP : hE => [h0 h1].
    sauto lq:on use:coqeq_neuneu.
  - move => P0 P1 u0 u1 b0 b1 c0 c1 neu0 neu1 domP ihP domu ihu domb ihb domc ihc.
    rewrite check_equal_ind_ind.
    move /andP => [/andP [/andP [h0 h1] h2 ] h3].
    sauto lq:on use:coqeq_neuneu.
  - move => a b dom h ih. apply : CE_HRed; eauto using rtc_refl.
    rewrite check_equal_nfnf in ih.
    tauto.
  - move => a a' b ha doma ih hE.
    rewrite check_equal_hredl in hE. sauto lq:on.
  - move => a b b' hu r a0 ha hb. rewrite check_equal_hredr in hb.
    sauto lq:on rew:off.
Qed.
