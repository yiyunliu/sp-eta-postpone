Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax
  common typing preservation admissible fp_red structural soundness.
From Hammer Require Import Tactics.
Require Import ssreflect ssrbool.
Require Import Psatz.
From stdpp Require Import relations (rtc(..), nsteps(..)).
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Cdcl.Itauto.

Module HRed.
  Lemma ToRRed (a b : PTm) : HRed.R a b -> RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:RRed.R. Qed.

  Lemma preservation Γ (a b A : PTm) : Γ ⊢ a ∈ A -> HRed.R a b -> Γ ⊢ b ∈ A.
  Proof.
    sfirstorder use:subject_reduction, ToRRed.
  Qed.

  Lemma ToEq Γ (a b : PTm ) A : Γ ⊢ a ∈ A -> HRed.R a b -> Γ ⊢ a ≡ b ∈ A.
  Proof. sfirstorder use:ToRRed, RRed_Eq. Qed.

End HRed.

Module HReds.
  Lemma preservation Γ (a b A : PTm) : Γ ⊢ a ∈ A -> rtc HRed.R a b -> Γ ⊢ b ∈ A.
  Proof. induction 2; sfirstorder use:HRed.preservation. Qed.

  Lemma ToEq Γ (a b : PTm) A : Γ ⊢ a ∈ A -> rtc HRed.R a b -> Γ ⊢ a ≡ b ∈ A.
  Proof.
    induction 2; sauto lq:on use:HRed.ToEq, E_Transitive, HRed.preservation.
  Qed.
End HReds.

Lemma T_Conv_E Γ (a : PTm) A B i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ A ≡ B ∈ PUniv i \/ Γ ⊢ B ≡ A ∈ PUniv i ->
  Γ ⊢ a ∈ B.
Proof. qauto use:T_Conv, Su_Eq, E_Symmetric. Qed.

Lemma E_Conv_E Γ (a b : PTm) A B i :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ A ≡ B ∈ PUniv i \/ Γ ⊢ B ≡ A ∈ PUniv i ->
  Γ ⊢ a ≡ b ∈ B.
Proof. qauto use:E_Conv, Su_Eq, E_Symmetric. Qed.

Lemma lored_embed Γ (a b : PTm) A :
  Γ ⊢ a ∈ A -> LoRed.R a b -> Γ ⊢ a ≡ b ∈ A.
Proof. sfirstorder use:LoRed.ToRRed, RRed_Eq. Qed.

Lemma loreds_embed Γ (a b : PTm ) A :
  Γ ⊢ a ∈ A -> rtc LoRed.R a b -> Γ ⊢ a ≡ b ∈ A.
Proof.
  move => + h. move : Γ A.
  elim : a b /h.
  - sfirstorder use:E_Refl.
  - move => a b c ha hb ih Γ A hA.
    have ? : Γ ⊢ a ≡ b ∈ A by sfirstorder use:lored_embed.
    have ? : Γ ⊢ b ∈ A by hauto l:on use:regularity.
    hauto lq:on ctrs:Eq.
Qed.

Lemma Zero_Inv Γ U :
  Γ ⊢ PZero ∈ U ->
  Γ ⊢ PNat ≲ U.
Proof.
  move E : PZero => u hu.
  move : E.
  elim : Γ u U /hu=>//=.
  by eauto using Su_Eq, E_Refl, T_Nat'.
  hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma Sub_Bind_InvR Γ p (A : PTm ) B C :
  Γ ⊢ PBind p A B ≲ C ->
  exists i A0 B0, Γ ⊢ C ≡ PBind p A0 B0 ∈ PUniv i.
Proof.
  move => /[dup] h.
  move /synsub_to_usub.
  move => [h0 [h1 h2]].
  move /LoReds.FromSN : h1.
  move => [C' [hC0 hC1]].
  have [i hC] : exists i, Γ ⊢ C ∈ PUniv i by qauto l:on use:regularity.
  have hE : Γ ⊢ C ≡ C' ∈ PUniv i by sfirstorder use:loreds_embed.
  have : Γ ⊢ PBind p A B ≲ C' by eauto using Su_Transitive, Su_Eq.
  move : hE hC1. clear.
  case : C' => //=.
  - move => k _ _ /synsub_to_usub.
    clear. move => [_ [_ h]]. exfalso.
    rewrite /Sub.R in h.
    move : h => [c][d][+ []].
    move /REReds.bind_inv => ?.
    move /REReds.var_inv => ?.
    sauto lq:on.
  - move => p0 h. exfalso.
    have {h} : Γ ⊢ PAbs p0 ∈ PUniv i by hauto l:on use:regularity.
    move /Abs_Inv => [A0][B0][_]/synsub_to_usub.
    hauto l:on use:Sub.bind_univ_noconf.
  - move => u v hC /andP [h0 h1] /synsub_to_usub ?.
    exfalso.
    suff : SNe (PApp u v) by hauto l:on use:Sub.bind_sne_noconf.
    eapply ne_nf_embed => //=. itauto.
  - move => p0 p1 hC  h  ?. exfalso.
    have {hC} : Γ ⊢ PPair p0 p1 ∈ PUniv i by hauto l:on use:regularity.
    hauto lq:on use:Sub.bind_univ_noconf, synsub_to_usub, Pair_Inv.
  - move => p0 p1 _ + /synsub_to_usub.
    hauto lq:on use:Sub.bind_sne_noconf, ne_nf_embed.
  - move => b p0 p1 h0 h1 /[dup] h2 /synsub_to_usub *.
    have ? : b = p by hauto l:on use:Sub.bind_inj. subst.
    eauto.
  - hauto lq:on use:synsub_to_usub, Sub.bind_univ_noconf.
  - move => _ _ /synsub_to_usub [_ [_ h]]. exfalso.
    apply Sub.nat_bind_noconf in h => //=.
  - move => h.
    have {}h : Γ ⊢ PZero ∈ PUniv i by hauto l:on use:regularity.
    exfalso. move : h. clear.
    move /Zero_Inv /synsub_to_usub.
    hauto l:on use:Sub.univ_nat_noconf.
  - move => a h.
    have {}h : Γ ⊢ PSuc a  ∈ PUniv i by hauto l:on use:regularity.
    exfalso. move /Suc_Inv : h => [_ /synsub_to_usub].
    hauto lq:on use:Sub.univ_nat_noconf.
  - move => P0 a0 b0 c0 h0 h1 /synsub_to_usub [_ [_ h2]].
    set u := PInd _ _ _ _ in h0.
    have hne : SNe u by sfirstorder use:ne_nf_embed.
    exfalso. move : h2 hne. hauto l:on use:Sub.bind_sne_noconf.
Qed.

Lemma Sub_Univ_InvR Γ i C :
  Γ ⊢ PUniv i ≲ C ->
  exists j k, Γ ⊢ C ≡ PUniv j ∈ PUniv k.
Proof.
  move => /[dup] h.
  move /synsub_to_usub.
  move => [h0 [h1 h2]].
  move /LoReds.FromSN : h1.
  move => [C' [hC0 hC1]].
  have [j hC] : exists i, Γ ⊢ C ∈ PUniv i by qauto l:on use:regularity.
  have hE : Γ ⊢ C ≡ C' ∈ PUniv j by sfirstorder use:loreds_embed.
  have : Γ ⊢ PUniv i ≲ C' by eauto using Su_Transitive, Su_Eq.
  move : hE hC1. clear.
  case : C' => //=.
  - move => f => _ _ /synsub_to_usub.
    move => [_ [_]].
    move => [v0][v1][/REReds.univ_inv + [/REReds.var_inv ]].
    hauto lq:on inv:Sub1.R.
  - move => p hC.
    have {hC} : Γ ⊢ PAbs p ∈ PUniv j by hauto l:on use:regularity.
    hauto lq:on rew:off use:Abs_Inv, synsub_to_usub,
            Sub.bind_univ_noconf.
  - hauto q:on use:synsub_to_usub, Sub.univ_sne_noconf, ne_nf_embed.
  - move => a b hC.
    have {hC} : Γ ⊢ PPair a b ∈ PUniv j by hauto l:on use:regularity.
    hauto lq:on rew:off use:Pair_Inv, synsub_to_usub,
            Sub.bind_univ_noconf.
  - hauto q:on use:synsub_to_usub, Sub.univ_sne_noconf, ne_nf_embed.
  - hauto lq:on use:synsub_to_usub, Sub.univ_bind_noconf.
  - sfirstorder.
  - hauto q:on use:synsub_to_usub, Sub.nat_univ_noconf.
  - move => h.
    have {}h : Γ ⊢ PZero ∈ PUniv j by hauto l:on use:regularity.
    exfalso. move : h. clear.
    move /Zero_Inv /synsub_to_usub.
    hauto l:on use:Sub.univ_nat_noconf.
  - move => a h.
    have {}h : Γ ⊢ PSuc a  ∈ PUniv j by hauto l:on use:regularity.
    exfalso. move /Suc_Inv : h => [_ /synsub_to_usub].
    hauto lq:on use:Sub.univ_nat_noconf.
  - move => P0 a0 b0 c0 h0 h1 /synsub_to_usub [_ [_ h2]].
    set u := PInd _ _ _ _ in h0.
    have hne : SNe u by sfirstorder use:ne_nf_embed.
    exfalso. move : h2 hne. hauto l:on use:Sub.univ_sne_noconf.
Qed.

Lemma Sub_Bind_InvL Γ p (A : PTm) B C :
  Γ ⊢ C ≲ PBind p A B ->
  exists i A0 B0, Γ ⊢ PBind p A0 B0 ≡ C ∈ PUniv i.
Proof.
  move => /[dup] h.
  move /synsub_to_usub.
  move => [h0 [h1 h2]].
  move /LoReds.FromSN : h0.
  move => [C' [hC0 hC1]].
  have [i hC] : exists i, Γ ⊢ C ∈ PUniv i by qauto l:on use:regularity.
  have hE : Γ ⊢ C ≡ C' ∈ PUniv i by sfirstorder use:loreds_embed.
  have : Γ ⊢ C' ≲ PBind p A B by eauto using Su_Transitive, Su_Eq, E_Symmetric.
  move : hE hC1. clear.
  case : C' => //=.
  - move => k _ _ /synsub_to_usub.
    clear. move => [_ [_ h]]. exfalso.
    rewrite /Sub.R in h.
    move : h => [c][d][+ []].
    move /REReds.var_inv => ?.
    move /REReds.bind_inv => ?.
    hauto lq:on inv:Sub1.R.
  - move => p0 h. exfalso.
    have {h} : Γ ⊢ PAbs p0 ∈ PUniv i by hauto l:on use:regularity.
    move /Abs_Inv => [A0][B0][_]/synsub_to_usub.
    hauto l:on use:Sub.bind_univ_noconf.
  - move => u v hC /andP [h0 h1] /synsub_to_usub ?.
    exfalso.
    suff : SNe (PApp u v) by hauto l:on use:Sub.sne_bind_noconf.
    eapply ne_nf_embed => //=. itauto.
  - move => p0 p1 hC  h  ?. exfalso.
    have {hC} : Γ ⊢ PPair p0 p1 ∈ PUniv i by hauto l:on use:regularity.
    hauto lq:on use:Sub.bind_univ_noconf, synsub_to_usub, Pair_Inv.
  - move => p0 p1 _ + /synsub_to_usub.
    hauto lq:on use:Sub.sne_bind_noconf, ne_nf_embed.
  - move => b p0 p1 h0 h1 /[dup] h2 /synsub_to_usub *.
    have ? : b = p by hauto l:on use:Sub.bind_inj. subst.
    eauto using E_Symmetric.
  - hauto lq:on use:synsub_to_usub, Sub.univ_bind_noconf.
  - move => _ _ /synsub_to_usub [_ [_ h]]. exfalso.
    apply Sub.bind_nat_noconf in h => //=.
  - move => h.
    have {}h : Γ ⊢ PZero ∈ PUniv i by hauto l:on use:regularity.
    exfalso. move : h. clear.
    move /Zero_Inv /synsub_to_usub.
    hauto l:on use:Sub.univ_nat_noconf.
  - move => a h.
    have {}h : Γ ⊢ PSuc a  ∈ PUniv i by hauto l:on use:regularity.
    exfalso. move /Suc_Inv : h => [_ /synsub_to_usub].
    hauto lq:on use:Sub.univ_nat_noconf.
  - move => P0 a0 b0 c0 h0 h1 /synsub_to_usub [_ [_ h2]].
    set u := PInd _ _ _ _ in h0.
    have hne : SNe u by sfirstorder use:ne_nf_embed.
    exfalso. move : h2 hne. subst u.
    hauto l:on use:Sub.sne_bind_noconf.
Qed.

Lemma T_Abs_Inv Γ (a0 a1 : PTm) U :
  Γ ⊢ PAbs a0 ∈ U ->
  Γ ⊢ PAbs a1 ∈ U ->
  exists Δ V, Δ ⊢ a0 ∈ V /\ Δ ⊢ a1 ∈ V.
Proof.
  move /Abs_Inv => [A0][B0][wt0]hU0.
  move /Abs_Inv => [A1][B1][wt1]hU1.
  move /Sub_Bind_InvR : (hU0) => [i][A2][B2]hE.
  have hSu : Γ ⊢ PBind PPi A1 B1 ≲ PBind PPi A2 B2 by eauto using Su_Eq, Su_Transitive.
  have hSu' : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Eq, Su_Transitive.
  exists ((cons A2 Γ)), B2.
  have [k ?] : exists k, Γ ⊢ A2 ∈ PUniv k by hauto lq:on use:regularity, Bind_Inv.
  split.
  - have /Su_Pi_Proj2_Var ? := hSu'.
    have /Su_Pi_Proj1 ? := hSu'.
    move /regularity_sub0 : hSu' => [j] /Bind_Inv [k0 [? ?]].
    apply T_Conv with (A := B0); eauto.
    apply : ctx_eq_subst_one; eauto.
  - have /Su_Pi_Proj2_Var ? := hSu.
    have /Su_Pi_Proj1 ? := hSu.
    move /regularity_sub0 : hSu => [j] /Bind_Inv [k0 [? ?]].
    apply T_Conv with (A := B1); eauto.
    apply : ctx_eq_subst_one; eauto.
Qed.

Lemma Abs_Pi_Inv Γ (a : PTm) A B :
  Γ ⊢ PAbs a ∈ PBind PPi A B ->
  (cons A Γ) ⊢ a ∈ B.
Proof.
  move => h.
  have [i hi] : exists i, Γ ⊢ PBind PPi A B ∈ PUniv i by hauto use:regularity.
  have  [{}i {}hi] : exists i, Γ ⊢ A ∈ PUniv i by hauto use:Bind_Inv.
  apply : subject_reduction; last apply RRed.AppAbs'.
  apply : T_App'; cycle 1.
  apply : weakening_wt'; cycle 2. apply hi.
  apply h. reflexivity. reflexivity. rewrite -/ren_PTm.
  apply T_Var with (i := var_zero).
  by eauto using Wff_Cons'.
  apply here.
  rewrite -/ren_PTm.
  by asimpl; rewrite subst_scons_id.
  rewrite -/ren_PTm.
  by asimpl; rewrite subst_scons_id.
Qed.

Lemma T_Abs_Neu_Inv Γ (a u : PTm) U :
  Γ ⊢ PAbs a ∈ U ->
  Γ ⊢ u ∈ U ->
  exists Δ V, Δ ⊢ a ∈ V /\ Δ ⊢ PApp (ren_PTm shift u) (VarPTm var_zero)  ∈ V.
Proof.
  move => /[dup] ha' + hu.
  move /Abs_Inv => [A0][B0][ha]hSu.
  move /Sub_Bind_InvR : (hSu) => [i][A2][B2]hE.
  have {}hu : Γ ⊢ u ∈ PBind PPi A2 B2 by eauto using T_Conv_E.
  have ha'' : Γ ⊢ PAbs a ∈ PBind PPi A2 B2 by eauto using T_Conv_E.
  have {}hE : Γ ⊢ PBind PPi A2 B2 ∈ PUniv i
    by hauto l:on use:regularity.
  have {i} [j {}hE] : exists j, Γ ⊢ A2 ∈ PUniv j
      by qauto l:on use:Bind_Inv.
  have hΓ : ⊢ cons A2 Γ by eauto using Wff_Cons'.
  set Δ := cons _ _ in hΓ.
  have {}hu : Δ ⊢ PApp (ren_PTm shift u) (VarPTm var_zero) ∈ B2.
  apply : T_App'; cycle 1. apply : weakening_wt' => //=; eauto.
  reflexivity.
  rewrite -/ren_PTm.
  apply T_Var; eauto using here.
  rewrite -/ren_PTm. by asimpl; rewrite subst_scons_id.
  exists Δ, B2. split => //.
  by move /Abs_Pi_Inv in ha''.
Qed.

Lemma T_Univ_Raise Γ (a : PTm) i j :
  Γ ⊢ a ∈ PUniv i ->
  i <= j ->
  Γ ⊢ a ∈ PUniv j.
Proof. hauto lq:on rew:off use:T_Conv, Su_Univ, wff_mutual. Qed.

Lemma Bind_Univ_Inv Γ p (A : PTm) B i :
  Γ ⊢ PBind p A B ∈ PUniv i ->
  Γ ⊢ A ∈ PUniv i /\ (cons A Γ) ⊢ B ∈ PUniv i.
Proof.
  move /Bind_Inv.
  move => [i0][hA][hB]h.
  move /synsub_to_usub : h => [_ [_ /Sub.univ_inj ? ]].
  sfirstorder use:T_Univ_Raise.
Qed.

Lemma Pair_Sig_Inv Γ (a b : PTm) A B :
  Γ ⊢ PPair a b ∈ PBind PSig A B ->
  Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B.
Proof.
  move => /[dup] h0 h1.
  have [i hr] : exists i, Γ ⊢ PBind PSig A B ∈ PUniv i by sfirstorder use:regularity.
  move /T_Proj1 in h0.
  move /T_Proj2 in h1.
  split.
  hauto lq:on use:subject_reduction ctrs:RRed.R.
  have hE : Γ ⊢ PProj PL (PPair a b) ≡ a ∈ A by
    hauto lq:on use:RRed_Eq ctrs:RRed.R.
  apply : T_Conv.
  move /subject_reduction : h1. apply.
  apply RRed.ProjPair.
  apply : bind_inst; eauto.
Qed.


(* Coquand's algorithm with subtyping *)
Reserved Notation "a ∼ b" (at level 70).
Reserved Notation "a ↔ b" (at level 70).
Reserved Notation "a ⇔ b" (at level 70).
Inductive CoqEq : PTm -> PTm -> Prop :=
| CE_ZeroZero :
  PZero ↔ PZero

| CE_SucSuc a b :
  a ⇔ b ->
  (* ------------- *)
  PSuc a ↔ PSuc b

| CE_AbsAbs a b :
  a ⇔ b ->
  (* --------------------- *)
  PAbs a ↔ PAbs b

| CE_AbsNeu a u :
  ishne u ->
  a ⇔ PApp (ren_PTm shift u) (VarPTm var_zero) ->
  (* --------------------- *)
  PAbs a ↔ u

| CE_NeuAbs a u :
  ishne u ->
  PApp (ren_PTm shift u) (VarPTm var_zero) ⇔ a ->
  (* --------------------- *)
  u ↔ PAbs a

| CE_PairPair a0 a1 b0 b1 :
  a0 ⇔ a1 ->
  b0 ⇔ b1 ->
  (* ---------------------------- *)
  PPair a0 b0 ↔ PPair a1 b1

| CE_PairNeu a0 a1 u :
  ishne u ->
  a0 ⇔ PProj PL u ->
  a1 ⇔ PProj PR u ->
  (* ----------------------- *)
  PPair a0 a1 ↔ u

| CE_NeuPair a0 a1 u :
  ishne u ->
  PProj PL u ⇔ a0 ->
  PProj PR u ⇔ a1 ->
  (* ----------------------- *)
  u ↔ PPair a0 a1

| CE_UnivCong i :
  (* -------------------------- *)
  PUniv i ↔ PUniv i

| CE_BindCong p A0 A1 B0 B1 :
  A0 ⇔ A1 ->
  B0 ⇔ B1 ->
  (* ---------------------------- *)
  PBind p A0 B0 ↔ PBind p A1 B1

| CE_NatCong :
  (* ------------------ *)
  PNat ↔ PNat

| CE_NeuNeu a0 a1 :
  a0 ∼ a1 ->
  a0 ↔ a1

with CoqEq_Neu : PTm -> PTm -> Prop :=
| CE_VarCong i :
  (* -------------------------- *)
  VarPTm i ∼ VarPTm i

| CE_ProjCong p u0 u1 :
  ishne u0 ->
  ishne u1 ->
  u0 ∼ u1 ->
  (* ---------------------  *)
  PProj p u0 ∼ PProj p u1

| CE_AppCong u0 u1 a0 a1 :
  ishne u0 ->
  ishne u1 ->
  u0 ∼ u1 ->
  a0 ⇔ a1 ->
  (* ------------------------- *)
  PApp u0 a0 ∼ PApp u1 a1

| CE_IndCong P0 P1 u0 u1 b0 b1 c0 c1 :
  ishne u0 ->
  ishne u1 ->
  P0 ⇔ P1 ->
  u0 ∼ u1 ->
  b0 ⇔ b1 ->
  c0 ⇔ c1 ->
  (* ----------------------------------- *)
  PInd P0 u0 b0 c0 ∼ PInd P1 u1 b1 c1

with CoqEq_R : PTm -> PTm -> Prop :=
| CE_HRed a a' b b'  :
  rtc HRed.R a a' ->
  rtc HRed.R b b' ->
  a' ↔ b' ->
  (* ----------------------- *)
  a ⇔ b
where "a ↔ b" := (CoqEq a b) and "a ⇔ b" := (CoqEq_R a b) and "a ∼ b" := (CoqEq_Neu a b).

Lemma CE_HRedL (a a' b : PTm)  :
  HRed.R a a' ->
  a' ⇔ b ->
  a ⇔ b.
Proof.
  hauto lq:on ctrs:rtc, CoqEq_R inv:CoqEq_R.
Qed.

Lemma CE_Nf a b :
  a ↔ b -> a ⇔ b.
Proof. hauto l:on ctrs:rtc. Qed.

Scheme
  coqeq_neu_ind := Induction for CoqEq_Neu Sort Prop
  with coqeq_ind := Induction for CoqEq Sort Prop
  with coqeq_r_ind := Induction for CoqEq_R Sort Prop.

Combined Scheme coqeq_mutual from coqeq_neu_ind, coqeq_ind, coqeq_r_ind.

Lemma coqeq_symmetric_mutual :
    (forall (a b : PTm), a ∼ b -> b ∼ a) /\
    (forall (a b : PTm), a ↔ b -> b ↔ a) /\
    (forall (a b : PTm), a ⇔ b -> b ⇔ a).
Proof. apply coqeq_mutual; qauto l:on ctrs:CoqEq,CoqEq_R, CoqEq_Neu. Qed.

Lemma coqeq_sound_mutual :
    (forall (a b : PTm ), a ∼ b -> forall Γ A B, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> exists C,
       Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ≡ b ∈ C) /\
    (forall (a b : PTm ), a ↔ b -> forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> Γ ⊢ a ≡ b ∈ A) /\
    (forall (a b : PTm ), a ⇔ b -> forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> Γ ⊢ a ≡ b ∈ A).
Proof.
  move => [:hAppL hPairL].
  apply coqeq_mutual.
  - move => i Γ A B hi0 hi1.
    move /Var_Inv : hi0 => [hΓ [C [h00 h01]]].
    move /Var_Inv : hi1 => [_ [C0 [h10 h11]]].
    have ? : C0 = C by eauto using lookup_deter. subst.
    exists C.
    repeat split => //=.
    apply E_Refl. eauto using T_Var.
  - move => [] u0 u1 hu0 hu1 hu ihu Γ A B hu0' hu1'.
    + move /Proj1_Inv : hu0'.
      move => [A0][B0][hu0']hu0''.
      move /Proj1_Inv : hu1'.
      move => [A1][B1][hu1']hu1''.
      specialize ihu with (1 := hu0') (2 := hu1').
      move : ihu.
      move => [C][ih0][ih1]ih.
      have [i[A2[B2 h2]]] : exists i A2 B2, Γ ⊢ PBind PSig A2 B2 ≡ C ∈ PUniv i by sfirstorder use:Sub_Bind_InvL.
      exists  A2.
      have [h3 h4] : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0 /\ Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1 by qauto l:on use:Su_Eq, Su_Transitive.
      repeat split;
        eauto using Su_Sig_Proj1, Su_Transitive;[idtac].
      apply E_Proj1 with (B := B2); eauto using E_Conv_E.
    + move /Proj2_Inv : hu0'.
      move => [A0][B0][hu0']hu0''.
      move /Proj2_Inv : hu1'.
      move => [A1][B1][hu1']hu1''.
      specialize ihu with (1 := hu0') (2 := hu1').
      move : ihu.
      move => [C][ih0][ih1]ih.
      have [A2 [B2 [i hi]]] : exists A2 B2 i, Γ ⊢ PBind PSig A2 B2 ≡ C ∈ PUniv i by hauto q:on use:Sub_Bind_InvL.
      have [h3 h4] : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0 /\ Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1 by qauto l:on use:Su_Eq, Su_Transitive.
      have h5 : Γ ⊢ u0 ≡ u1 ∈ PBind PSig A2 B2 by eauto using E_Conv_E.
      exists (subst_PTm (scons (PProj PL u0) VarPTm) B2).
      have [? ?] : Γ ⊢ u0 ∈ PBind PSig A2 B2 /\ Γ ⊢ u1 ∈ PBind PSig A2 B2 by hauto l:on use:regularity.
      repeat split => //=.
      apply : Su_Transitive ;eauto.
      apply : Su_Sig_Proj2; eauto.
      apply E_Refl. eauto using T_Proj1.
      apply : Su_Transitive ;eauto.
      apply : Su_Sig_Proj2; eauto.
      apply : E_Proj1; eauto.
      apply : E_Proj2; eauto.
  - move => u0 u1 a0 a1 neu0 neu1 hu ihu ha iha Γ A B wta0 wta1.
    move /App_Inv : wta0 => [A0][B0][hu0][ha0]hU.
    move /App_Inv : wta1 => [A1][B1][hu1][ha1]hU1.
    move : ihu hu0 hu1. repeat move/[apply].
    move => [C][hC0][hC1]hu01.
    have [i [A2 [B2 hPi]]] : exists i A2 B2, Γ ⊢ PBind PPi A2 B2 ≡ C ∈ PUniv i by sfirstorder use:Sub_Bind_InvL.
    have ? : Γ ⊢ PBind PPi A2 B2 ≲ PBind PPi A0 B0 by eauto using Su_Eq, Su_Transitive.
    have h : Γ ⊢ PBind PPi A2 B2 ≲ PBind PPi A1 B1 by eauto using Su_Eq, Su_Transitive.
    have ha' : Γ ⊢ a0 ≡ a1 ∈ A2 by
      sauto lq:on use:Su_Transitive, Su_Pi_Proj1.
    have hwf : Γ ⊢ PBind PPi A2 B2 ∈ PUniv i by hauto l:on use:regularity.
    have [j hj'] : exists j,Γ ⊢ A2 ∈ PUniv j by hauto l:on use:regularity.
    have ? : ⊢ Γ by sfirstorder use:wff_mutual.
    exists (subst_PTm (scons a0 VarPTm) B2).
    repeat split. apply : Su_Transitive; eauto.
    apply : Su_Pi_Proj2';  eauto using E_Refl.
    apply : Su_Transitive; eauto.
    have ? : Γ ⊢ A1 ≲ A2 by eauto using Su_Pi_Proj1.
    apply Su_Transitive with (B := subst_PTm (scons a1 VarPTm) B2);
      first by sfirstorder use:bind_inst.
    apply : Su_Pi_Proj2';  eauto using E_Refl.
    apply E_App with (A := A2); eauto using E_Conv_E.
  - move {hAppL hPairL} => P0 P1 u0 u1 b0 b1 c0 c1 neu0 neu1 hP ihP hu ihu hb ihb hc ihc Γ A B.
    move /Ind_Inv => [i0][hP0][hu0][hb0][hc0]hSu0.
    move /Ind_Inv => [i1][hP1][hu1][hb1][hc1]hSu1.
    move : ihu hu0 hu1; do!move/[apply]. move => ihu.
    have {}ihu : Γ ⊢ u0 ≡ u1 ∈ PNat by hauto l:on use:E_Conv.
    have wfΓ : ⊢ Γ by hauto use:wff_mutual.
    have wfΓ' : ⊢ (cons PNat Γ) by hauto lq:on use:Wff_Cons', T_Nat'.
    move => [:sigeq].
    have sigeq' : Γ ⊢ PBind PSig PNat P0 ≡ PBind PSig PNat P1 ∈ PUniv (max i0 i1).
    apply E_Bind. by eauto using T_Nat, E_Refl.
    abstract : sigeq. hauto lq:on use:T_Univ_Raise solve+:lia.
    have sigleq : Γ ⊢ PBind PSig PNat P0 ≲ PBind PSig PNat P1.
    apply Su_Sig with (i := 0)=>//. by apply T_Nat'. by eauto using Su_Eq, T_Nat', E_Refl.
    apply Su_Eq with (i := max i0 i1).  apply sigeq.
    exists (subst_PTm (scons u0 VarPTm) P0). repeat split => //.
    suff : Γ ⊢ subst_PTm (scons u0 VarPTm) P0 ≲ subst_PTm (scons u1 VarPTm) P1 by eauto using Su_Transitive.
    by eauto using Su_Sig_Proj2.
    apply E_IndCong with (i := max i0 i1); eauto. move :sigeq; clear; hauto q:on use:regularity.
    apply ihb; eauto. apply : T_Conv; eauto. eapply morphing. apply : Su_Eq. apply E_Symmetric. apply sigeq.
    done. apply morphing_ext. apply morphing_id. done. by apply T_Zero.
    apply ihc; eauto.
    eapply T_Conv; eauto.
    eapply ctx_eq_subst_one; eauto. apply : Su_Eq; apply sigeq.
    eapply weakening_su; eauto.
    eapply morphing; eauto. apply : Su_Eq. apply E_Symmetric. apply sigeq.
    apply morphing_ext. set x := {1}(funcomp _ shift).
    have -> : x = funcomp (ren_PTm shift) VarPTm by asimpl.
    apply : morphing_ren; eauto. apply : renaming_shift; eauto. by apply morphing_id.
    apply T_Suc. apply T_Var; eauto using here.
  - hauto lq:on use:Zero_Inv db:wt.
  - hauto lq:on use:Suc_Inv db:wt.
  - move => a b ha iha Γ A h0 h1.
    move /Abs_Inv : h0 => [A0][B0][h0]h0'.
    move /Abs_Inv : h1 => [A1][B1][h1]h1'.
    have [i [A2 [B2 h]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PPi A2 B2 ∈ PUniv i by hauto l:on use:Sub_Bind_InvR.
    have hp0 : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
    have hp1 : Γ ⊢ PBind PPi A1 B1 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
    have [j ?] : exists j, Γ ⊢ A0 ∈ PUniv j by eapply wff_mutual in h0; inversion h0; subst; eauto.
    have [k ?] : exists j, Γ ⊢ A1 ∈ PUniv j by eapply wff_mutual in h1; inversion h1; subst; eauto.
    have [l ?] : exists j, Γ ⊢ A2 ∈ PUniv j by hauto lq:on rew:off use:regularity, Bind_Inv.
    have [h2 h3] : Γ ⊢ A2 ≲ A0 /\ Γ ⊢ A2 ≲ A1 by hauto l:on use:Su_Pi_Proj1.
    apply E_Conv with (A := PBind PPi A2 B2); cycle 1.
    eauto using E_Symmetric, Su_Eq.
    apply : E_Abs; eauto. hauto l:on use:regularity.
    apply iha.
    move /Su_Pi_Proj2_Var in hp0.
    apply : T_Conv; eauto.
    eapply ctx_eq_subst_one with (A0 := A0); eauto.
    move /Su_Pi_Proj2_Var in hp1.
    apply : T_Conv; eauto.
    eapply ctx_eq_subst_one with (A0 := A1); eauto.
  - abstract : hAppL.
    move => a u hneu ha iha Γ A wta wtu.
    move /Abs_Inv : wta => [A0][B0][wta]hPi.
    have [i [A2 [B2 h]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PPi A2 B2 ∈ PUniv i by hauto l:on use:Sub_Bind_InvR.
    have hPi'' : Γ ⊢ PBind PPi A2 B2 ≲ A by eauto using Su_Eq, Su_Transitive, E_Symmetric.
    have [j0 ?] : exists j0, Γ ⊢ A0 ∈ PUniv j0 by move /regularity_sub0 in hPi; hauto lq:on use:Bind_Inv.
    have [j2 ?] : exists j0, Γ ⊢ A2 ∈ PUniv j0 by move /regularity_sub0 in hPi''; hauto lq:on use:Bind_Inv.
    have hPi' : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Eq, Su_Transitive.
    have hPidup := hPi'.
    apply E_Conv with (A := PBind PPi A2 B2); eauto.
    have /regularity_sub0 [i' hPi0] := hPi.
    have : Γ ⊢ PAbs (PApp (ren_PTm shift u) (VarPTm var_zero)) ≡ u ∈ PBind PPi A2 B2.
    apply : E_AppEta; eauto.
    hauto l:on use:regularity.
    apply T_Conv with (A := A);eauto.
    eauto using Su_Eq.
    move => ?.
    suff : Γ ⊢ PAbs a ≡ PAbs (PApp (ren_PTm shift u) (VarPTm var_zero)) ∈ PBind PPi A2 B2
      by eauto using E_Transitive.
    apply : E_Abs; eauto. hauto l:on use:regularity.
    apply iha.
    move /Su_Pi_Proj2_Var in hPi'.
    apply : T_Conv; eauto.
    eapply ctx_eq_subst_one with (A0 := A0); eauto.
    sfirstorder use:Su_Pi_Proj1.
    eapply T_App' with (A := ren_PTm shift A2) (B := ren_PTm (upRen_PTm_PTm shift) B2).
    by asimpl; rewrite subst_scons_id.
    eapply weakening_wt' with (a := u) (A := PBind PPi A2 B2);eauto.
    by eauto using T_Conv_E. apply T_Var. apply : Wff_Cons'; eauto.
    apply here.
  (* Mirrors the last case *)
  - move => a u hu ha iha Γ A hu0 ha0.
    apply E_Symmetric.
    apply : hAppL; eauto.
    sfirstorder use:coqeq_symmetric_mutual.
    sfirstorder use:E_Symmetric.
  - move => {hAppL hPairL} a0 a1 b0 b1 ha iha hb ihb Γ A.
    move /Pair_Inv => [A0][B0][h00][h01]h02.
    move /Pair_Inv => [A1][B1][h10][h11]h12.
    have [i[A2[B2 h2]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PSig A2 B2 ∈ PUniv i by hauto l:on use:Sub_Bind_InvR.
    apply E_Conv with (A := PBind PSig A2 B2); last by eauto using E_Symmetric, Su_Eq.
    have h0 : Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A2 B2 by eauto using Su_Transitive, Su_Eq, E_Symmetric.
    have h1 : Γ ⊢ PBind PSig A1 B1 ≲ PBind PSig A2 B2 by eauto using Su_Transitive, Su_Eq, E_Symmetric.
    have /Su_Sig_Proj1 h0' := h0.
    have /Su_Sig_Proj1 h1' := h1.
    move => [:eqa].
    apply : E_Pair; eauto. hauto l:on use:regularity.
    abstract : eqa. apply iha; eauto using T_Conv.
    apply ihb.
    + apply T_Conv with (A := subst_PTm (scons a0 VarPTm) B0); eauto.
      have : Γ ⊢ a0 ≡ a0 ∈A0 by eauto using E_Refl.
      hauto l:on use:Su_Sig_Proj2.
    + apply T_Conv with (A := subst_PTm (scons a1 VarPTm) B2); eauto; cycle 1.
      move /E_Symmetric in eqa.
      have ? : Γ ⊢ PBind PSig A2 B2 ∈ PUniv i by hauto use:regularity.
      apply:bind_inst; eauto.
      apply : T_Conv; eauto.
      have : Γ ⊢ a1 ≡ a1 ∈ A1 by eauto using E_Refl.
      hauto l:on use:Su_Sig_Proj2.
  - move => {hAppL}.
    abstract : hPairL.
    move => {hAppL}.
    move => a0 a1 u neu h0 ih0 h1 ih1 Γ A ha hu.
    move /Pair_Inv : ha => [A0][B0][ha0][ha1]ha.
    have [i [A2 [B2 hA]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PSig A2 B2 ∈ PUniv i by hauto l:on use:Sub_Bind_InvR.
    have hA' : Γ ⊢ PBind PSig A2 B2 ≲ A by eauto using E_Symmetric, Su_Eq.
    move /E_Conv : (hA'). apply.
    have hSig : Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A2 B2 by eauto using E_Symmetric, Su_Eq, Su_Transitive.
    have hA02 : Γ ⊢ A0 ≲ A2 by sfirstorder use:Su_Sig_Proj1.
    have hu'  : Γ ⊢ u ∈ PBind PSig A2 B2 by eauto using T_Conv_E.
    move => [:ih0'].
    apply : E_Transitive; last (apply E_Symmetric; apply : E_PairEta).
    apply : E_Pair; eauto. hauto l:on use:regularity.
    abstract : ih0'.
    apply ih0. apply : T_Conv; eauto.
    by eauto using T_Proj1.
    apply ih1. apply : T_Conv; eauto.
    move /E_Refl in ha0.
    hauto l:on use:Su_Sig_Proj2.
    move /T_Proj2 in hu'.
    apply : T_Conv; eauto.
    move /E_Symmetric in ih0'.
    move /regularity_sub0 in hA'.
    hauto l:on use:bind_inst.
    hauto l:on use:regularity.
    eassumption.
  (* Same as before *)
  - move {hAppL}.
    move => *. apply E_Symmetric. apply : hPairL;
      sfirstorder use:coqeq_symmetric_mutual, E_Symmetric.
  - sfirstorder use:E_Refl.
  - move => {hAppL hPairL} p A0 A1 B0 B1 hA ihA hB ihB Γ A hA0 hA1.
    move /Bind_Inv : hA0 => [i][hA0][hB0]hU.
    move /Bind_Inv : hA1 => [j][hA1][hB1]hU1.
    have [l [k hk]] : exists l k, Γ ⊢ A ≡ PUniv k ∈ PUniv l
        by hauto lq:on use:Sub_Univ_InvR.
    have hjk : Γ ⊢ PUniv j ≲ PUniv k by eauto using Su_Eq, Su_Transitive.
    have hik : Γ ⊢ PUniv i ≲ PUniv k by eauto using Su_Eq, Su_Transitive.
    apply E_Conv with (A := PUniv k); last by eauto using Su_Eq, E_Symmetric.
    move => [:eqA].
    apply E_Bind. abstract : eqA. apply ihA.
    apply T_Conv with (A := PUniv i); eauto.
    apply T_Conv with (A := PUniv j); eauto.
    apply ihB.
    apply T_Conv with (A := PUniv i); eauto.
    move : weakening_su hik hA0. by repeat move/[apply].
    apply T_Conv with (A := PUniv j); eauto.
    apply : ctx_eq_subst_one; eauto. apply : Su_Eq; apply eqA.
    move : weakening_su hjk hA0. by repeat move/[apply].
  - hauto lq:on ctrs:Eq,LEq,Wt.
  - hauto lq:on ctrs:Eq,LEq,Wt.
  - move => a a' b b' ha hb hab ihab Γ A ha0 hb0.
    have [*] : Γ ⊢ a' ∈ A /\ Γ ⊢ b' ∈ A by eauto using HReds.preservation.
    hauto lq:on use:HReds.ToEq, E_Symmetric, E_Transitive.
Qed.

Definition term_metric k (a b : PTm) :=
  exists i j va vb, nsteps LoRed.R i a va /\ nsteps LoRed.R j b vb /\ nf va /\ nf vb /\ size_PTm va + size_PTm vb + i + j <= k.

Lemma term_metric_sym k (a b : PTm) :
  term_metric k a b -> term_metric k b a.
Proof. hauto lq:on unfold:term_metric solve+:lia. Qed.

Lemma ne_hne (a : PTm) : ne a -> ishne a.
Proof. elim : a => //=; sfirstorder b:on. Qed.

Lemma hf_hred_lored (a b : PTm) :
  ~~ ishf a ->
  LoRed.R a b ->
  HRed.R a b \/ ishne a.
Proof.
  move => + h. elim : a b/ h=>//=.
  - hauto l:on use:HRed.AppAbs.
  - hauto l:on use:HRed.ProjPair.
  - hauto lq:on ctrs:HRed.R.
  - hauto lq:on ctrs:HRed.R.
  - hauto lq:on ctrs:HRed.R.
  - sfirstorder use:ne_hne.
  - hauto lq:on ctrs:HRed.R.
  - sfirstorder use:ne_hne.
  - hauto q:on ctrs:HRed.R.
  - hauto lq:on use:ne_hne.
  - hauto lq:on use:ne_hne.
Qed.

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
  move => ?.
  apply A_NfNf.
  apply A_Conf; sfirstorder use:hf_no_hred, hne_no_hred.
Qed.

Lemma hne_nf_ne (a : PTm ) :
  ishne a -> nf a -> ne a.
Proof. case : a => //=. Qed.

Lemma lored_nsteps_renaming k (a b : PTm) (ξ : nat -> nat) :
  nsteps LoRed.R k a b ->
  nsteps LoRed.R k (ren_PTm ξ a) (ren_PTm ξ b).
Proof.
  induction 1; hauto lq:on ctrs:nsteps use:LoRed.renaming.
Qed.

Lemma hred_hne (a b : PTm) :
  HRed.R a b ->
  ishne a ->
  False.
Proof. induction 1; sfirstorder. Qed.

Lemma hf_not_hne (a : PTm) :
  ishf a -> ishne a -> False.
Proof. case : a => //=. Qed.

Lemma T_AbsPair_Imp Γ a (b0 b1 : PTm) A :
  Γ ⊢ PAbs a ∈ A ->
  Γ ⊢ PPair b0 b1 ∈ A ->
  False.
Proof.
  move /Abs_Inv => [A0][B0][_]haU.
  move /Pair_Inv => [A1][B1][_][_]hbU.
  move /Sub_Bind_InvR : haU => [i][A2][B2]h2.
  have : Γ ⊢ PBind PSig A1 B1 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_inj.
Qed.

Lemma T_AbsZero_Imp Γ a (A : PTm) :
  Γ ⊢ PAbs a ∈ A ->
  Γ ⊢ PZero ∈ A ->
  False.
Proof.
  move /Abs_Inv => [A0][B0][_]haU.
  move /Zero_Inv => hbU.
  move /Sub_Bind_InvR : haU => [i][A2][B2]h2.
  have : Γ ⊢ PNat ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
  clear. hauto lq:on use:synsub_to_usub, Sub.bind_nat_noconf.
Qed.

Lemma T_AbsSuc_Imp Γ a b (A : PTm) :
  Γ ⊢ PAbs a ∈ A ->
  Γ ⊢ PSuc b ∈ A ->
  False.
Proof.
  move /Abs_Inv => [A0][B0][_]haU.
  move /Suc_Inv => [_ hbU].
  move /Sub_Bind_InvR : haU => [i][A2][B2]h2.
  have {hbU h2} : Γ ⊢ PNat ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
  hauto lq:on use:Sub.bind_nat_noconf, synsub_to_usub.
Qed.

Lemma Nat_Inv Γ A:
  Γ ⊢ PNat ∈ A ->
  exists i, Γ ⊢ PUniv i ≲ A.
Proof.
  move E : PNat => u hu.
  move : E.
  elim : Γ u A / hu=>//=.
  - hauto lq:on use:E_Refl, T_Univ, Su_Eq.
  - hauto lq:on ctrs:LEq.
Qed.

Lemma T_AbsNat_Imp Γ a (A : PTm ) :
  Γ ⊢ PAbs a ∈ A ->
  Γ ⊢ PNat ∈ A ->
  False.
Proof.
  move /Abs_Inv => [A0][B0][_]haU.
  move /Nat_Inv => [i hA].
  move /Sub_Univ_InvR : hA => [j][k]hA.
  have : Γ ⊢ PBind PPi A0 B0 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  hauto lq:on use:Sub.bind_univ_noconf, synsub_to_usub.
Qed.

Lemma T_PairBind_Imp Γ (a0 a1 : PTm ) p A0 B0 U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PBind p A0 B0  ∈ U ->
  False.
Proof.
  move /Pair_Inv => [A1][B1][_][_]hbU.
  move /Bind_Inv => [i][_ [_ haU]].
  move /Sub_Univ_InvR : haU => [j][k]hU.
  have : Γ ⊢ PBind PSig A1 B1 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_univ_noconf.
Qed.

Lemma T_PairNat_Imp Γ (a0 a1 : PTm) U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PNat ∈ U ->
  False.
Proof.
  move/Pair_Inv => [A1][B1][_][_]hbU.
  move /Nat_Inv => [i]/Sub_Univ_InvR[j][k]hU.
  have : Γ ⊢ PBind PSig A1 B1 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_univ_noconf.
Qed.

Lemma T_PairZero_Imp Γ (a0 a1 : PTm ) U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PZero ∈ U ->
  False.
Proof.
  move/Pair_Inv=>[A1][B1][_][_]hbU.
  move/Zero_Inv. move/Sub_Bind_InvR : hbU=>[i][A0][B0]*.
  have : Γ ⊢ PNat ≲ PBind PSig A0 B0 by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_nat_noconf.
Qed.

Lemma T_PairSuc_Imp Γ (a0 a1 : PTm ) b U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PSuc b ∈ U ->
  False.
Proof.
  move/Pair_Inv=>[A1][B1][_][_]hbU.
  move/Suc_Inv=>[_ hU]. move/Sub_Bind_InvR : hbU=>[i][A0][B0]*.
  have : Γ ⊢ PNat ≲ PBind PSig A0 B0 by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_nat_noconf.
Qed.

Lemma Univ_Inv Γ i U :
  Γ ⊢ PUniv i ∈ U ->
  Γ ⊢ PUniv i ∈ PUniv (S i)  /\ Γ ⊢ PUniv (S i) ≲ U.
Proof.
  move E : (PUniv i) => u hu.
  move : i E. elim : Γ u U / hu => n //=.
  - hauto l:on use:E_Refl, Su_Eq, T_Univ.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma T_PairUniv_Imp Γ (a0 a1 : PTm) i U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PUniv i ∈ U ->
  False.
Proof.
  move /Pair_Inv => [A1][B1][_][_]hbU.
  move /Univ_Inv => [h0 h1].
  move /Sub_Univ_InvR : h1 => [j [k hU]].
  have : Γ ⊢ PBind PSig A1 B1 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub.
  hauto lq:on use:Sub.bind_univ_noconf.
Qed.

Lemma T_AbsUniv_Imp Γ a i (A : PTm) :
  Γ ⊢ PAbs a ∈ A ->
  Γ ⊢ PUniv i ∈ A ->
  False.
Proof.
  move /Abs_Inv => [A0][B0][_]haU.
  move /Univ_Inv => [h0 h1].
  move /Sub_Univ_InvR : h1 => [j [k hU]].
  have : Γ ⊢ PBind PPi A0 B0 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub.
  hauto lq:on use:Sub.bind_univ_noconf.
Qed.

Lemma T_AbsUniv_Imp' Γ (a : PTm) i  :
  Γ ⊢ PAbs a ∈ PUniv i -> False.
Proof.
  hauto lq:on use:synsub_to_usub, Sub.bind_univ_noconf, Abs_Inv.
Qed.

Lemma T_PairUniv_Imp' Γ (a b : PTm) i  :
  Γ ⊢ PPair a b ∈ PUniv i -> False.
Proof.
  hauto lq:on use:synsub_to_usub, Sub.bind_univ_noconf, Pair_Inv.
Qed.

Lemma T_AbsBind_Imp Γ a p A0 B0 (U : PTm ) :
  Γ ⊢ PAbs a ∈ U ->
  Γ ⊢ PBind p A0 B0 ∈ U ->
  False.
Proof.
  move /Abs_Inv => [A1][B1][_ ha].
  move /Bind_Inv => [i [_ [_ h]]].
  move /Sub_Univ_InvR : h => [j [k hU]].
  have : Γ ⊢ PBind PPi A1 B1 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub.
  hauto lq:on use:Sub.bind_univ_noconf.
Qed.

Lemma lored_nsteps_suc_inv k (a : PTm ) b :
  nsteps LoRed.R k (PSuc a) b -> exists b', nsteps LoRed.R k a b' /\ b = PSuc b'.
Proof.
  move E : (PSuc a) => u hu.
  move : a E.
  elim : u b /hu.
  - hauto l:on.
  - scrush ctrs:nsteps inv:LoRed.R.
Qed.

Lemma lored_nsteps_abs_inv k (a : PTm) b :
  nsteps LoRed.R k (PAbs a) b -> exists b', nsteps LoRed.R k a b' /\ b = PAbs b'.
Proof.
  move E : (PAbs a) => u hu.
  move : a E.
  elim : u b /hu.
  - hauto l:on.
  - scrush ctrs:nsteps inv:LoRed.R.
Qed.

Lemma lored_hne_preservation (a b : PTm) :
    LoRed.R a b -> ishne a -> ishne b.
Proof.  induction 1; sfirstorder. Qed.

Lemma loreds_hne_preservation (a b : PTm ) :
  rtc LoRed.R a b -> ishne a -> ishne b.
Proof. induction 1; hauto lq:on ctrs:rtc use:lored_hne_preservation. Qed.

Lemma lored_nsteps_bind_inv k p (a0 : PTm ) b0 C :
    nsteps LoRed.R k (PBind p a0 b0) C ->
    exists i j a1 b1,
      i <= k /\ j <= k /\
        C = PBind p a1 b1 /\
        nsteps LoRed.R i a0 a1 /\
        nsteps LoRed.R j b0 b1.
Proof.
  move E : (PBind p a0 b0) => u hu. move : p a0 b0 E.
  elim : k u C / hu.
  - sauto lq:on.
  - move => k a0 a1 a2 ha ha' ih p a3 b0 ?. subst.
    inversion ha; subst => //=;
    spec_refl.
    move : ih => [i][j][a1][b1][?][?][?][h0]h1. subst.
    exists (S i),j,a1,b1. sauto lq:on solve+:lia.
    move : ih => [i][j][a1][b1][?][?][?][h0]h1. subst.
    exists i,(S j),a1,b1. sauto lq:on solve+:lia.
Qed.

Lemma lored_nsteps_ind_inv k P0 (a0 : PTm) b0 c0 U :
  nsteps LoRed.R k (PInd P0 a0 b0 c0) U ->
  ishne a0 ->
  exists iP ia ib ic P1 a1 b1 c1,
    iP <= k /\ ia <= k /\ ib <= k /\ ic <= k /\
      U = PInd P1 a1 b1 c1 /\
      nsteps LoRed.R iP P0 P1 /\
      nsteps LoRed.R ia a0 a1 /\
      nsteps LoRed.R ib b0 b1 /\
      nsteps LoRed.R ic c0 c1.
Proof.
  move E : (PInd P0 a0 b0 c0) => u hu.
  move : P0 a0 b0 c0 E.
  elim : k u U / hu.
  - sauto lq:on.
  - move => k t0 t1 t2 ht01 ht12 ih P0 a0 b0 c0 ? nea0. subst.
    inversion ht01; subst => //=; spec_refl.
    * move /(_ ltac:(done)) : ih.
      move => [iP][ia][ib][ic].
      exists (S iP), ia, ib, ic. sauto lq:on solve+:lia.
    * move /(_ ltac:(sfirstorder use:lored_hne_preservation)) : ih.
      move => [iP][ia][ib][ic].
      exists iP, (S ia), ib, ic. sauto lq:on solve+:lia.
    * move /(_ ltac:(done)) : ih.
      move => [iP][ia][ib][ic].
      exists iP, ia, (S ib), ic. sauto lq:on solve+:lia.
    * move /(_ ltac:(done)) : ih.
      move => [iP][ia][ib][ic].
      exists iP, ia, ib, (S ic). sauto lq:on solve+:lia.
Qed.

Lemma lored_nsteps_app_inv k (a0 b0 C : PTm) :
    nsteps LoRed.R k (PApp a0 b0) C ->
    ishne a0 ->
    exists i j a1 b1,
      i <= k /\ j <= k /\
        C = PApp a1 b1 /\
        nsteps LoRed.R i a0 a1 /\
        nsteps LoRed.R j b0 b1.
Proof.
  move E : (PApp a0 b0) => u hu. move : a0 b0 E.
  elim : k u C / hu.
  - sauto lq:on.
  - move => k a0 a1 a2 ha01 ha12 ih a3 b0 ?.  subst.
    inversion ha01; subst => //=.
    spec_refl.
    move => h.
    have : ishne a4 by sfirstorder use:lored_hne_preservation.
    move : ih => /[apply]. move => [i][j][a1][b1][?][?][?][h0]h1.
    subst. exists (S i),j,a1,b1. sauto lq:on solve+:lia.
    spec_refl. move : ih => /[apply].
    move => [i][j][a1][b1][?][?][?][h0]h1. subst.
    exists i, (S j), a1, b1. sauto lq:on solve+:lia.
Qed.

Lemma lored_nsteps_proj_inv k p (a0 C : PTm) :
    nsteps LoRed.R k (PProj p a0) C ->
    ishne a0 ->
    exists i a1,
      i <= k /\
        C = PProj p a1 /\
        nsteps LoRed.R i a0 a1.
Proof.
  move E : (PProj p a0) => u hu. move : a0 E.
  elim : k u C / hu.
  - sauto lq:on.
  - move => k a0 a1 a2 ha01 ha12 ih a3 ?. subst.
    inversion ha01; subst => //=.
    spec_refl.
    move => h.
    have : ishne a4 by sfirstorder use:lored_hne_preservation.
    move : ih => /[apply]. move => [i][a1][?][?]h0. subst.
    exists (S i), a1. hauto lq:on ctrs:nsteps solve+:lia.
Qed.

Lemma lored_nsteps_app_cong k (a0 a1 b : PTm) :
  nsteps LoRed.R k a0 a1 ->
  ishne a0 ->
  nsteps LoRed.R k (PApp a0 b) (PApp a1 b).
  move => h. move : b.
  elim : k a0 a1 / h.
  - sauto.
  - move => m a0 a1 a2 h0 h1 ih.
    move => b hneu.
    apply : nsteps_l; eauto using LoRed.AppCong0.
    apply LoRed.AppCong0;eauto. move : hneu. clear. case : a0 => //=.
    apply ih. sfirstorder use:lored_hne_preservation.
Qed.

Lemma lored_nsteps_proj_cong k p (a0 a1 : PTm) :
  nsteps LoRed.R k a0 a1 ->
  ishne a0 ->
  nsteps LoRed.R k (PProj p a0) (PProj p a1).
  move => h. move : p.
  elim : k a0 a1 / h.
  - sauto.
  - move => m a0 a1 a2 h0 h1 ih p hneu.
    apply : nsteps_l; eauto using LoRed.ProjCong.
    apply LoRed.ProjCong;eauto. move : hneu. clear. case : a0 => //=.
    apply ih. sfirstorder use:lored_hne_preservation.
Qed.

Lemma lored_nsteps_pair_inv k (a0 b0 C : PTm ) :
    nsteps LoRed.R k (PPair a0 b0) C ->
    exists i j a1 b1,
      i <= k /\ j <= k /\
        C = PPair a1 b1 /\
        nsteps LoRed.R i a0 a1 /\
        nsteps LoRed.R j b0 b1.
  move E : (PPair a0 b0) => u hu. move : a0 b0 E.
  elim : k u C / hu.
  - sauto lq:on.
  - move => k a0 a1 a2 ha01 ha12 ih a3 b0 ?.  subst.
    inversion ha01; subst => //=.
    spec_refl.
    move : ih => [i][j][a1][b1][?][?][?][h0]h1.
    subst. exists (S i),j,a1,b1. sauto lq:on solve+:lia.
    spec_refl.
    move : ih => [i][j][a1][b1][?][?][?][h0]h1. subst.
    exists i, (S j), a1, b1. sauto lq:on solve+:lia.
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
  decompose record hva => {hva}.
  decompose record hvb => {hvb}. subst.
  simpl in *. exists (k - 1).
  hauto lqb:on solve+:lia.
Qed.

Lemma term_metric_bind : forall k p0 a0 b0 p1 a1 b1,
    term_metric k (PBind p0 a0 b0) (PBind p1 a1 b1) ->
    exists k', k' < k /\ term_metric k' a0 a1 /\ term_metric k' b0 b1.
Proof.
  move => k p0 a0 b0 p1 a1 b1 [i][j][va][vb][hva][hvb][nfa][nfb]h.
  apply lored_nsteps_bind_inv in hva, hvb.
  decompose record hva => {hva}.
  decompose record hvb => {hvb}. subst.
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
      apply A_NfNf.
      (* apply A_NfNf. apply A_NeuNeu. apply A_AppCong => //; eauto. *)
      have nfa0' : HRed.nf a0 by sfirstorder use:hne_no_hred.
      have nfb0' : HRed.nf a1 by sfirstorder use:hne_no_hred.
      have ha0 : algo_dom a0 a1 by eauto using algo_dom_r_algo_dom.
      constructor => //. eauto.
    + move => p0 A0 p1 A1 neA0 neA1.
      have {}nfa0 : HRed.nf A0 by sfirstorder use:hne_no_hred.
      have {}nfb0 : HRed.nf A1 by sfirstorder use:hne_no_hred.
      hauto lq:on use:term_metric_proj, algo_dom_r_algo_dom db:adom.
    + move => P0 a0 b0 c0 P1 a1 b1 c1 nea0 nea1.
      have {}nfa0 : HRed.nf a0 by sfirstorder use:hne_no_hred.
      have {}nfb0 : HRed.nf a1 by sfirstorder use:hne_no_hred.
      hauto lq:on use:term_metric_ind, algo_dom_r_algo_dom db:adom.
Qed.

Lemma ce_neu_neu_helper a b :
  ishne a -> ishne b ->
  (forall Γ A B, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ exists C, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ∈ C /\ Γ ⊢ b ∈ C) -> (forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> a ⇔ b) /\ (forall Γ A B, ishne a -> ishne b -> Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ exists C, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ∈ C /\ Γ ⊢ b ∈ C).
Proof. sauto lq:on. Qed.

Lemma hne_ind_inj P0 P1 u0 u1 b0 b1 c0 c1 :
  ishne u0 -> ishne u1 ->
  DJoin.R (PInd P0 u0 b0 c0) (PInd P1 u1 b1 c1) ->
  DJoin.R P0 P1 /\ DJoin.R u0 u1 /\ DJoin.R b0 b1 /\ DJoin.R c0 c1.
Proof. hauto q:on use:REReds.hne_ind_inv. Qed.

Lemma coqeq_complete' :
  (forall a b, algo_dom a b -> DJoin.R a b -> (forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> a ⇔ b) /\ (forall Γ A B, ishne a -> ishne b -> Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ exists C, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ∈ C /\ Γ ⊢ b ∈ C)) /\
    (forall a b, algo_dom_r a b -> DJoin.R a b -> forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> a ⇔ b).
  move => [:hhPairNeu hhAbsNeu].
  apply algo_dom_mutual.
  - move => a b h ih hj. split => //.
    move => Γ A. move : T_Abs_Inv; repeat move/[apply].
    move => [Δ][V][h0]h1.
    have [? ?] : SN a /\ SN b by hauto lq:on use:fundamental_theorem, logrel.SemWt_SN.
    apply CE_Nf. constructor. apply : ih; eauto using DJoin.abs_inj.
  - abstract : hhAbsNeu.
    move => a u hu ha iha hj => //.
    split => //= Γ A.
    move => + h. have ? : SN u  by hauto lq:on use:fundamental_theorem, logrel.SemWt_SN.
    move : T_Abs_Neu_Inv h; repeat move/[apply].
    move => [Δ][V][ha']hu'.
    apply CE_Nf. constructor => //. apply : iha; eauto.
    apply DJoin.abs_inj.
    hauto lq:on use:fundamental_theorem, logrel.SemWt_SN.
    hauto lq:on use:fundamental_theorem, logrel.SemWt_SN.
    apply : DJoin.transitive; eauto.
    apply DJoin.symmetric. apply DJoin.FromEJoin. eexists. split. apply relations.rtc_once.
    apply ERed.AppEta. apply rtc_refl.
  - hauto q:on use:coqeq_symmetric_mutual, DJoin.symmetric, algo_dom_sym.
  - move {hhAbsNeu hhPairNeu}.
    admit.
  - move {hhAbsNeu}. abstract : hhPairNeu.
    admit.
  - move {hhAbsNeu}.
    move => a0 a1 u hu  ha iha hb ihb /DJoin.symmetric hj. split => // *.
    eapply coqeq_symmetric_mutual.
    eapply algo_dom_sym in ha, hb.
    eapply hhPairNeu => //=; eauto; hauto lq:on use:DJoin.symmetric, coqeq_symmetric_mutual.
  - move {hhPairNeu hhAbsNeu}. hauto l:on.
  - move {hhPairNeu hhAbsNeu}.
    move => a0 a1 ha iha /DJoin.suc_inj hj. split => //.
    move => Γ A /Suc_Inv ? /Suc_Inv ?. apply CE_Nf. hauto lq:on ctrs:CoqEq.
  - move => i j /DJoin.univ_inj ?. subst.
    split => //. hauto l:on.
  - move => {hhPairNeu hhAbsNeu} p0 p1 A0 A1 B0 B1.
    move => hA ihA hB ihB /DJoin.bind_inj. move => [?][hjA]hjB. subst.
    split => // Γ A.
    move => hbd0 hbd1.
    have {hbd0} : exists i, Γ ⊢ PBind p1 A0 B0 ∈ PUniv i by move /Bind_Inv in hbd0; qauto use:T_Bind.
    move => [i] => hbd0.
    have {hbd1} : exists i, Γ ⊢ PBind p1 A1 B1 ∈ PUniv i by move /Bind_Inv in hbd1; qauto use:T_Bind.
    move => [j] => hbd1.
    have /Bind_Univ_Inv {hbd0} [? ?] : Γ ⊢ PBind p1 A0 B0 ∈ PUniv (max i j) by hauto lq:on use:T_Univ_Raise solve+:lia.
    have /Bind_Univ_Inv {hbd1} [? ?] : Γ ⊢ PBind p1 A1 B1 ∈ PUniv (max i j) by hauto lq:on use:T_Univ_Raise solve+:lia.
    move => [:eqa].
    apply CE_Nf. constructor; first by abstract : eqa; eauto.
    eapply ihB; eauto. apply : ctx_eq_subst_one; eauto.
    apply : Su_Eq; eauto. sfirstorder use:coqeq_sound_mutual.
  - hauto l:on.
  - move => {hhAbsNeu hhPairNeu} i j /DJoin.var_inj ?. subst. apply ce_neu_neu_helper => // Γ A B.
    move /Var_Inv => [h [A0 [h0 h1]]].
    move /Var_Inv => [h' [A1 [h0' h1']]].
    split. by constructor.
    suff : A0 = A1 by hauto lq:on db:wt.
    eauto using lookup_deter.
  - move => u0 u1 a0 a1 neu0 neu1 domu ihu doma iha. move /DJoin.hne_app_inj /(_ neu0 neu1) => [hju hja].
    apply ce_neu_neu_helper => //= Γ A B.
    move /App_Inv => [A0][B0][hb0][ha0]hS0.
    move /App_Inv => [A1][B1][hb1][ha1]hS1.
    move /(_ hju) : ihu.
    move => [_ ihb].
    move : ihb (neu0) (neu1) hb0 hb1. repeat move/[apply].
    move => [hb01][C][hT0][hT1][hT2]hT3.
    move /Sub_Bind_InvL : (hT0).
    move => [i][A2][B2]hE.
    have hSu20 : Γ ⊢ PBind PPi A2 B2 ≲ PBind PPi A0 B0 by
      eauto using Su_Eq, Su_Transitive.
    have hSu10 : Γ ⊢ PBind PPi A2 B2 ≲ PBind PPi A1 B1 by
      eauto using Su_Eq, Su_Transitive.
    have hSuA0 : Γ ⊢ A0 ≲ A2 by sfirstorder use:Su_Pi_Proj1.
    have hSuA1 : Γ ⊢ A1 ≲ A2 by sfirstorder use:Su_Pi_Proj1.
    have ha1' : Γ ⊢ a1 ∈ A2 by eauto using T_Conv.
    have ha0' : Γ ⊢ a0 ∈ A2 by eauto using T_Conv.
    move : iha hja. repeat move/[apply].
    move => iha.
    move : iha (ha0') (ha1'); repeat move/[apply].
    move => iha.
    split. sauto lq:on.
    exists (subst_PTm (scons a0 VarPTm) B2).
    split.
    apply : Su_Transitive; eauto.
    move /E_Refl in ha0.
    hauto l:on use:Su_Pi_Proj2.
    have h01 : Γ ⊢ a0 ≡ a1 ∈ A2 by sfirstorder use:coqeq_sound_mutual.
    split.
    apply Su_Transitive with (B := subst_PTm (scons a1 VarPTm) B2).
    move /regularity_sub0 : hSu10 => [i0].
    hauto l:on use:bind_inst.
    hauto lq:on rew:off use:Su_Pi_Proj2, Su_Transitive, E_Refl.
    split.
    by apply : T_App; eauto using T_Conv_E.
    apply : T_Conv; eauto.
    apply T_App with (A := A2) (B := B2); eauto.
    apply : T_Conv_E; eauto.
    move /E_Symmetric in h01.
    move /regularity_sub0 : hSu20 => [i0].
    sfirstorder use:bind_inst.
  - move => p0 p1 a0 a1 hne0 hne1 doma iha /DJoin.hne_proj_inj /(_ hne0 hne1) [? hja]. subst.
    move : iha hja; repeat move/[apply].
    move => [_ iha]. apply ce_neu_neu_helper => // Γ A B.
    move : iha (hne0) (hne1);repeat move/[apply].
    move => ih.
    case : p1.
    ** move => ha0 ha1.
       move /Proj1_Inv : ha0. move => [A0][B0][ha0]hSu0.
       move /Proj1_Inv : ha1. move => [A1][B1][ha1]hSu1.
       move : ih ha0 ha1 (hne0) (hne1); repeat move/[apply].
       move => [ha [C [hS0 [hS1 [wta0 wta1]]]]].
       split. sauto lq:on.
       move /Sub_Bind_InvL : (hS0) => [i][A2][B2]hS2.
       have hSu20 : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0
         by eauto using Su_Transitive, Su_Eq.
       have hSu21 : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1
         by eauto using Su_Transitive, Su_Eq.
       exists A2. split; eauto using Su_Sig_Proj1, Su_Transitive.
       repeat split => //=.
       hauto l:on use:Su_Sig_Proj1, Su_Transitive.
       apply T_Proj1 with (B := B2); eauto using T_Conv_E.
       apply T_Proj1 with (B := B2); eauto using T_Conv_E.
    ** move => ha0  ha1.
       move /Proj2_Inv : ha0. move => [A0][B0][ha0]hSu0.
       move /Proj2_Inv : ha1. move => [A1][B1][ha1]hSu1.
       move : ih (ha0) (ha1) (hne0) (hne1); repeat move/[apply].
       move => [ha [C [hS0 [hS1 [wta0 wta1]]]]].
       split. sauto lq:on.
       move /Sub_Bind_InvL : (hS0) => [i][A2][B2]hS2.
       have hSu20 : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0
         by eauto using Su_Transitive, Su_Eq.
       have hSu21 : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1
         by eauto using Su_Transitive, Su_Eq.
       have hA20 : Γ ⊢ A2 ≲ A0 by eauto using Su_Sig_Proj1.
       have hA21 : Γ ⊢ A2 ≲ A1 by eauto using Su_Sig_Proj1.
       have {}wta0 : Γ ⊢ a0 ∈ PBind PSig A2 B2 by eauto using T_Conv_E.
       have {}wta1 : Γ ⊢ a1 ∈ PBind PSig A2 B2 by eauto using T_Conv_E.
       have haE : Γ ⊢ PProj PL a0 ≡ PProj PL a1 ∈ A2
         by sauto lq:on use:coqeq_sound_mutual.
       exists (subst_PTm (scons (PProj PL a0) VarPTm) B2).
       repeat split.
       *** apply : Su_Transitive; eauto.
           have : Γ ⊢ PProj PL a0 ≡ PProj PL a0 ∈ A2
             by qauto use:regularity, E_Refl.
           sfirstorder use:Su_Sig_Proj2.
       *** apply : Su_Transitive; eauto.
           sfirstorder use:Su_Sig_Proj2.
       *** eauto using T_Proj2.
       *** apply : T_Conv.
           apply : T_Proj2; eauto.
           move /E_Symmetric in haE.
           move /regularity_sub0 in hSu21.
           sfirstorder use:bind_inst.
  - move {hhPairNeu hhAbsNeu}.
    move => P0 P1 u0 u1 b0 b1 c0 c1 neu0 neu1 domP ihP  domu ihu domb ihb domc ihc /hne_ind_inj.
    move => /(_ neu0 neu1)  [hjP][hju][hjb]hjc.
    apply ce_neu_neu_helper => // Γ A B.
    move /Ind_Inv => [iP0][wtP0][wta0][wtb0][wtc0]hSu0.
    move /Ind_Inv => [iP1][wtP1][wta1][wtb1][wtc1]hSu1.
    have {}iha : u0 ∼ u1 by qauto l:on.
    have []  : iP0 <= max iP0 iP1 /\ iP1 <= max iP0 iP1 by lia.
    move : T_Univ_Raise wtP0; repeat move/[apply]. move => wtP0.
    move : T_Univ_Raise wtP1; repeat move/[apply]. move => wtP1.
    have {}ihP : P0 ⇔ P1 by qauto l:on.
    set Δ := cons _ _ in wtP0, wtP1, wtc0, wtc1.
    have wfΔ :⊢ Δ by hauto l:on use:wff_mutual.
    have hPE : Δ ⊢ P0 ≡ P1 ∈ PUniv (max iP0 iP1)
      by hauto l:on use:coqeq_sound_mutual.
    have haE : Γ ⊢ u0 ≡ u1 ∈ PNat
      by hauto l:on use:coqeq_sound_mutual.
    have wtΓ : ⊢ Γ by hauto l:on use:wff_mutual.
    have hE : Γ ⊢ subst_PTm (scons PZero VarPTm) P0 ≡ subst_PTm (scons PZero VarPTm) P1 ∈ subst_PTm (scons PZero VarPTm) (PUniv (Nat.max iP0 iP1)).
    eapply morphing; eauto. apply morphing_ext. by apply morphing_id. by apply T_Zero.
    have {}wtb1 : Γ ⊢ b1 ∈ subst_PTm (scons PZero VarPTm) P0
      by eauto using T_Conv_E.
    have {}ihb : b0 ⇔ b1 by hauto l:on.
    have hPSig : Γ ⊢ PBind PSig PNat P0 ≡ PBind PSig PNat P1 ∈ PUniv (Nat.max iP0 iP1) by eauto with wt.
    set T := ren_PTm shift _ in wtc0.
    have : (cons P0 Δ) ⊢ c1 ∈ T.
    apply : T_Conv; eauto. apply : ctx_eq_subst_one; eauto with wt.
    apply : Su_Eq; eauto.
    subst T. apply : weakening_su; eauto.
    eapply morphing. apply : Su_Eq. apply E_Symmetric. by eauto.
    hauto l:on use:wff_mutual.
    apply morphing_ext. set x := funcomp _ _.
    have -> : x = funcomp (ren_PTm shift) VarPTm by asimpl.
    apply : morphing_ren; eauto using renaming_shift. by apply morphing_id.
    apply T_Suc. apply T_Var => //=. apply here. subst T => {}wtc1.
    have {}ihc : c0 ⇔ c1 by qauto l:on.
    move => [:ih].
    split. abstract : ih. move : neu0 neu1 ihP iha ihb ihc. clear. sauto lq:on.
    have hEInd : Γ ⊢ PInd P0 u0 b0 c0 ≡ PInd P1 u1 b1 c1 ∈ subst_PTm (scons u0 VarPTm) P0 by hfcrush use:coqeq_sound_mutual.
    exists (subst_PTm (scons u0 VarPTm) P0).
    repeat split => //=; eauto with wt.
    apply : Su_Transitive.
    apply : Su_Sig_Proj2; eauto. apply : Su_Sig; eauto using T_Nat' with wt.
    apply : Su_Eq. apply E_Refl. by apply T_Nat'.
    apply : Su_Eq. apply hPE. by eauto.
    move : hEInd. clear. hauto l:on use:regularity.
  - move => a b ha hb.
    move {hhPairNeu hhAbsNeu}.
Admitted.



(*   algo_metric k a b -> *)
(*   (forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> a ⇔ b) /\ *)
(*   (forall Γ A B, ishne a -> ishne b -> Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ exists C, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ∈ C /\ Γ ⊢ b ∈ C). *)
(* Proof. *)
(*   move : k a b. *)
(*   elim /Wf_nat.lt_wf_ind. *)
(*   move => n ih. *)
(*   move => a b /[dup] h /algo_metric_case. move : a b h => [:hstepL]. *)
(*   move => a b h. *)
(*   (* Cases where a and b can take steps *) *)
(*   case; cycle 1. *)
(*   move : ih a b h. *)
(*   abstract : hstepL. qauto l:on use:HRed.preservation, CE_HRedL, hred_hne. *)
(*   move  /algo_metric_sym /algo_metric_case : (h). *)
(*   case; cycle 1. *)
(*   move /algo_metric_sym : h. *)
(*   move : hstepL ih => /[apply]/[apply]. *)
(*   repeat move /[apply]. *)
(*   move => hstepL. *)
(*   hauto lq:on use:coqeq_symmetric_mutual, algo_metric_sym. *)
(*   (* Cases where a and b can't take wh steps *) *)
(*   move {hstepL}. *)
(*   move : a b h. move => [:hnfneu]. *)
(*   move => a b h. *)
(*   case => fb; case => fa. *)
(*   - split; last by sfirstorder use:hf_not_hne. *)
(*     move {hnfneu}. *)
(*     case : a h fb fa => //=. *)
(*     + case : b => //=; try qauto depth:1 use:T_AbsPair_Imp, T_AbsBind_Imp, T_AbsUniv_Imp, T_AbsZero_Imp, T_AbsSuc_Imp, T_AbsNat_Imp. *)
(*       move => a0 a1 ha0 _ _ Γ A wt0 wt1. *)
(*       move : T_Abs_Inv wt0 wt1; repeat move/[apply]. move  => [Δ [V [wt1 wt0]]]. *)
(*       apply : CE_HRed; eauto using rtc_refl. *)
(*       apply CE_AbsAbs. *)
(*       suff [l [h0 h1]] : exists l, l < n /\ algo_metric l a1 a0 by eapply ih; eauto. *)
(*       have ? : n > 0 by sauto solve+:lia. *)
(*       exists (n - 1). split; first by lia. *)
(*       move : (ha0). rewrite /algo_metric. *)
(*       move => [i][j][va][vb][hr0][hr1][nfva][nfvb][[v [hr0' hr1']]] har. *)
(*       apply lored_nsteps_abs_inv in hr0, hr1. *)
(*       move : hr0 => [va' [hr00 hr01]]. *)
(*       move : hr1 => [vb' [hr10 hr11]]. move {ih}. *)
(*       exists i,j,va',vb'. subst. *)
(*       suff [v0 [hv00 hv01]] : exists v0, rtc ERed.R va' v0 /\ rtc ERed.R vb' v0. *)
(*       repeat split =>//=. sfirstorder. *)
(*       simpl in *; by lia. *)
(*       move /algo_metric_join /DJoin.symmetric : ha0. *)
(*       have : SN a0 /\ SN a1 by qauto l:on use:fundamental_theorem, logrel.SemWt_SN. *)
(*       move => /[dup] [[ha00 ha10]] []. *)
(*       move : DJoin.abs_inj; repeat move/[apply]. *)
(*       move : DJoin.standardization ha00 ha10; repeat move/[apply]. *)
(*       (* this is awful *) *)
(*       move => [vb][va][h' [h'' [h''' [h'''' h'''''']]]]. *)
(*       have /LoReds.ToRReds {}hr00 : rtc LoRed.R a1 va' *)
(*         by hauto lq:on use:@relations.rtc_nsteps. *)
(*       have /LoReds.ToRReds {}hr10 : rtc LoRed.R a0 vb' *)
(*         by hauto lq:on use:@relations.rtc_nsteps. *)
(*       simpl in *. *)
(*       have [*] : va' = va /\ vb' = vb by eauto using red_uniquenf. subst. *)
(*       sfirstorder. *)
(*     + case : b => //=; try qauto depth:1 use:T_AbsPair_Imp, T_PairBind_Imp, T_PairUniv_Imp, T_PairNat_Imp, T_PairSuc_Imp, T_PairZero_Imp. *)
(*       move => a1 b1 a0 b0 h _ _ Γ A hu0 hu1. *)
(*       have [sn0 sn1] : SN (PPair a0 b0) /\ SN (PPair a1 b1) *)
(*         by qauto l:on use:fundamental_theorem, logrel.SemWt_SN. *)
(*       apply : CE_HRed; eauto using rtc_refl. *)
(*       move /Pair_Inv : hu0 => [A0][B0][ha0][hb0]hSu0. *)
(*       move /Pair_Inv : hu1 => [A1][B1][ha1][hb1]hSu1. *)
(*       move /Sub_Bind_InvR :  (hSu0). *)
(*       move => [i][A2][B2]hE. *)
(*       have hSu12 : Γ ⊢ PBind PSig A1 B1 ≲ PBind PSig A2 B2 *)
(*         by eauto using Su_Transitive, Su_Eq. *)
(*       have hSu02 : Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A2 B2 *)
(*         by eauto using Su_Transitive, Su_Eq. *)
(*       have hA02 : Γ ⊢ A0 ≲ A2 by eauto using Su_Sig_Proj1. *)
(*       have hA12 : Γ ⊢ A1 ≲ A2 by eauto using Su_Sig_Proj1. *)
(*       have ha0A2 : Γ ⊢ a0 ∈ A2 by eauto using T_Conv. *)
(*       have ha1A2 : Γ ⊢ a1 ∈ A2 by eauto using T_Conv. *)
(*       move /algo_metric_pair : h sn0 sn1; repeat move/[apply]. *)
(*       move => [j][hj][ih0 ih1]. *)
(*       have haE : a0 ⇔ a1 by hauto l:on. *)
(*       apply CE_PairPair => //. *)
(*       have {}haE : Γ ⊢ a0 ≡ a1 ∈ A2 *)
(*         by hauto l:on use:coqeq_sound_mutual. *)
(*       have {}hb1 : Γ ⊢ b1 ∈ subst_PTm (scons a1 VarPTm) B2. *)
(*       apply : T_Conv; eauto. *)
(*       move /E_Refl in ha1. hauto l:on use:Su_Sig_Proj2. *)
(*       eapply ih; cycle -1; eauto. *)
(*       apply : T_Conv; eauto. *)
(*       apply Su_Transitive with (B := subst_PTm (scons a0 VarPTm) B2). *)
(*       move /E_Refl in ha0. hauto l:on use:Su_Sig_Proj2. *)
(*       move : hE haE. clear. *)
(*       move => h. *)
(*       eapply regularity in h. *)
(*       move : h => [_ [hB _]]. *)
(*       eauto using bind_inst. *)
(*     + case : b => //=. *)
(*       * hauto lq:on use:T_AbsBind_Imp. *)
(*       * hauto lq:on rew:off use:T_PairBind_Imp. *)
(*       * move => p1 A1 B1 p0 A0 B0. *)
(*         move /algo_metric_bind. *)
(*         move => [?][j [ih0 [ih1 ih2]]]_ _. subst. *)
(*         move => Γ A hU0 hU1. *)
(*         move /Bind_Inv : hU0 => [i0 [hA0 [hB0 hS0]]]. *)
(*         move /Bind_Inv : hU1 => [i1 [hA1 [hB1 hS1]]]. *)
(*         have ? : Γ ⊢ PUniv i0 ≲ PUniv (max i0 i1) *)
(*           by hauto lq:on rew:off use:Su_Univ, wff_mutual solve+:lia. *)
(*         have ? : Γ ⊢ PUniv i1 ≲ PUniv (max i0 i1) *)
(*           by hauto lq:on rew:off use:Su_Univ, wff_mutual solve+:lia. *)
(*         have {}hA0 : Γ ⊢ A0 ∈ PUniv (max i0 i1) by eauto using T_Conv. *)
(*         have {}hA1 : Γ ⊢ A1 ∈ PUniv (max i0 i1) by eauto using T_Conv. *)
(*         have {}hB0 : (cons A0 Γ) ⊢ B0 ∈ PUniv (max i0 i1) *)
(*           by hauto lq:on use:T_Univ_Raise solve+:lia. *)
(*         have {}hB1 : (cons A1 Γ) ⊢ B1 ∈ PUniv (max i0 i1) *)
(*           by hauto lq:on use:T_Univ_Raise solve+:lia. *)

(*         have ihA : A0 ⇔ A1 by hauto l:on. *)
(*         have hAE : Γ ⊢ A0 ≡ A1 ∈ PUniv (Nat.max i0 i1) *)
(*           by hauto l:on use:coqeq_sound_mutual. *)
(*         apply : CE_HRed; eauto using rtc_refl. *)
(*         constructor => //. *)

(*         eapply ih; eauto. *)
(*         apply : ctx_eq_subst_one; eauto. *)
(*         eauto using Su_Eq. *)
(*       * move => > /algo_metric_join. *)
(*         hauto lq:on use:DJoin.bind_univ_noconf. *)
(*       * move => > /algo_metric_join. *)
(*         hauto lq:on use:Sub.nat_bind_noconf, Sub.FromJoin. *)
(*       * move => > /algo_metric_join. *)
(*         clear. hauto lq:on rew:off use:REReds.bind_inv, REReds.zero_inv. *)
(*       * move => > /algo_metric_join. clear. *)
(*         hauto lq:on rew:off use:REReds.bind_inv, REReds.suc_inv. *)
(*     + case : b => //=. *)
(*       * hauto lq:on use:T_AbsUniv_Imp. *)
(*       * hauto lq:on use:T_PairUniv_Imp. *)
(*       * qauto l:on use:algo_metric_join, DJoin.bind_univ_noconf, DJoin.symmetric. *)
(*       * move => i j /algo_metric_join /DJoin.univ_inj ? _ _ Γ A hi hj. *)
(*         subst. *)
(*         hauto l:on. *)
(*       * move => > /algo_metric_join. *)
(*         hauto lq:on use:Sub.nat_univ_noconf, Sub.FromJoin. *)
(*       * move => > /algo_metric_join. *)
(*         clear. hauto lq:on rew:off use:REReds.univ_inv, REReds.zero_inv. *)
(*       * move => > /algo_metric_join. *)
(*         clear. hauto lq:on rew:off use:REReds.univ_inv, REReds.suc_inv. *)
(*     + case : b => //=. *)
(*       * qauto l:on use:T_AbsNat_Imp. *)
(*       * qauto l:on use:T_PairNat_Imp. *)
(*       * move => > /algo_metric_join /Sub.FromJoin. hauto l:on use:Sub.bind_nat_noconf. *)
(*       * move => > /algo_metric_join /Sub.FromJoin. hauto lq:on use:Sub.univ_nat_noconf. *)
(*       * hauto l:on. *)
(*       * move /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.nat_inv, REReds.zero_inv. *)
(*       * move => > /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.nat_inv, REReds.suc_inv. *)
(*     (* Zero *) *)
(*     + case : b => //=. *)
(*       * hauto lq:on rew:off use:T_AbsZero_Imp. *)
(*       * hauto lq: on use: T_PairZero_Imp. *)
(*       * move =>> /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.zero_inv, REReds.bind_inv. *)
(*       * move =>> /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.zero_inv, REReds.univ_inv. *)
(*       * move =>> /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.zero_inv, REReds.nat_inv. *)
(*       * hauto l:on. *)
(*       * move =>> /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.zero_inv, REReds.suc_inv. *)
(*     (* Suc *) *)
(*     + case : b => //=. *)
(*       * hauto lq:on rew:off use:T_AbsSuc_Imp. *)
(*       * hauto lq:on use:T_PairSuc_Imp. *)
(*       * move => > /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.suc_inv, REReds.bind_inv. *)
(*       * move => > /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.suc_inv, REReds.univ_inv. *)
(*       * move => > /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.suc_inv, REReds.nat_inv. *)
(*       * move => > /algo_metric_join. *)
(*         hauto lq:on rew:off use:REReds.suc_inv, REReds.zero_inv. *)
(*       * move => a0 a1 h _ _. *)
(*         move /algo_metric_suc : h => [j [h4 h5]]. *)
(*         move => Γ A /Suc_Inv [h0 h1] /Suc_Inv [h2 h3]. *)
(*         move : ih h4 h5;do!move/[apply]. *)
(*         move => [ih _]. *)
(*         move : ih h0 h2;do!move/[apply]. *)
(*         move => h. apply : CE_HRed; eauto using rtc_refl. *)
(*         by constructor. *)
(*   - move : a b h fb fa. abstract : hnfneu. *)
(*     move => + b. *)
(*     case : b => //=. *)
(*     (* NeuAbs *) *)
(*     + move => a u halg _ nea. split => // Γ A hu /[dup] ha. *)
(*       move /Abs_Inv => [A0][B0][_]hSu. *)
(*       move /Sub_Bind_InvR : (hSu) => [i][A2][B2]hE. *)
(*       have {}hu : Γ ⊢ u ∈ PBind PPi A2 B2 by eauto using T_Conv_E. *)
(*       have {}ha : Γ ⊢ PAbs a ∈ PBind PPi A2 B2 by eauto using T_Conv_E. *)
(*       have {}hE : Γ ⊢ PBind PPi A2 B2 ∈ PUniv i *)
(*         by hauto l:on use:regularity. *)
(*       have {i} [j {}hE] : exists j, Γ ⊢ A2 ∈ PUniv j *)
(*           by qauto l:on use:Bind_Inv. *)
(*       have hΓ : ⊢ cons A2 Γ by eauto using Wff_Cons'. *)
(*       set Δ := cons _ _ in hΓ. *)
(*       have {}hu : Δ ⊢ PApp (ren_PTm shift u) (VarPTm var_zero) ∈ B2. *)
(*       apply : T_App'; cycle 1. apply : weakening_wt' => //=; eauto. *)
(*       reflexivity. *)
(*       rewrite -/ren_PTm. *)
(*       apply T_Var; eauto using here. *)
(*       rewrite -/ren_PTm. by asimpl; rewrite subst_scons_id. *)
(*       move /Abs_Pi_Inv in ha. *)
(*       move /algo_metric_neu_abs /(_ nea) : halg. *)
(*       move => [j0][hj0]halg. *)
(*       apply : CE_HRed; eauto using rtc_refl. *)
(*       eapply CE_NeuAbs => //=. *)
(*       eapply ih; eauto. *)
(*     (* NeuPair *) *)
(*     + move => a0 b0 u halg _ neu. *)
(*       split => // Γ A hu /[dup] wt. *)
(*       move /Pair_Inv => [A0][B0][ha0][hb0]hU. *)
(*       move /Sub_Bind_InvR : (hU) => [i][A2][B2]hE. *)
(*       have {}wt : Γ ⊢ PPair a0 b0 ∈ PBind PSig A2 B2 by sauto lq:on. *)
(*       have {}hu : Γ ⊢ u ∈ PBind PSig A2 B2 by eauto using T_Conv_E. *)
(*       move /Pair_Sig_Inv : wt => [{}ha0 {}hb0]. *)
(*       have /T_Proj1 huL := hu. *)
(*       have /T_Proj2 {hu} huR := hu. *)
(*       move /algo_metric_neu_pair /(_ neu) : halg => [j [hj [hL hR]]]. *)
(*       have heL : PProj PL u ⇔ a0 by hauto l:on. *)
(*       eapply CE_HRed; eauto using rtc_refl. *)
(*       apply CE_NeuPair; eauto. *)
(*       eapply ih; eauto. *)
(*       apply : T_Conv; eauto. *)
(*       have {}hE : Γ ⊢ PBind PSig A2 B2 ∈ PUniv i *)
(*         by hauto l:on use:regularity. *)
(*       have /E_Symmetric : Γ ⊢ PProj PL u  ≡ a0 ∈ A2 by *)
(*         hauto l:on use:coqeq_sound_mutual. *)
(*       hauto l:on use:bind_inst. *)
(*     (* NeuBind: Impossible *) *)
(*     + move => b p p0 a /algo_metric_join h _ h0. exfalso. *)
(*       move : h h0. clear. *)
(*       move /Sub.FromJoin. *)
(*       hauto l:on use:Sub.hne_bind_noconf. *)
(*     (* NeuUniv: Impossible *) *)
(*     + hauto lq:on rew:off use:DJoin.hne_univ_noconf, algo_metric_join. *)
(*     + hauto lq:on rew:off use:DJoin.hne_nat_noconf, algo_metric_join. *)
(*     (* Zero *) *)
(*     + case => //=. *)
(*       * move => i /algo_metric_join. clear. *)
(*         hauto lq:on rew:off use:REReds.var_inv, REReds.zero_inv. *)
(*       * move => >/algo_metric_join. clear. *)
(*         hauto lq:on rew:off use:REReds.hne_app_inv, REReds.zero_inv. *)
(*       * move => >/algo_metric_join. clear. *)
(*         hauto lq:on rew:off use:REReds.hne_proj_inv, REReds.zero_inv. *)
(*       * move => >/algo_metric_join. clear. *)
(*         move => h _ h2. exfalso. *)
(*         hauto q:on use:REReds.hne_ind_inv, REReds.zero_inv. *)
(*     (* Suc *) *)
(*     + move => a0. *)
(*       case => //=; move => >/algo_metric_join; clear. *)
(*       * hauto lq:on rew:off use:REReds.var_inv, REReds.suc_inv. *)
(*       * hauto lq:on rew:off use:REReds.hne_app_inv, REReds.suc_inv. *)
(*       * hauto lq:on rew:off use:REReds.hne_proj_inv, REReds.suc_inv. *)
(*       * hauto q:on use:REReds.hne_ind_inv, REReds.suc_inv. *)
(*   - move {ih}. *)
(*     move /algo_metric_sym in h. *)
(*     qauto l:on use:coqeq_symmetric_mutual. *)
(*   - move {hnfneu}. *)
(*     (* Clear out some trivial cases *) *)
(*     suff : (forall Γ A B, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ (exists C, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ∈ C /\ Γ ⊢ b ∈ C)). *)
(*     move => h0. *)
(*     split. move => *. apply : CE_HRed; eauto using rtc_refl. apply CE_NeuNeu. by firstorder. *)
(*     by firstorder. *)

(*     case : a h fb fa => //=. *)
(*     + case : b => //=; move => > /algo_metric_join. *)
(*       * move /DJoin.var_inj => i _ _. subst. *)
(*         move => Γ A B /Var_Inv [? [B0 [h0 h1]]]. *)
(*         move /Var_Inv => [_ [C0 [h2 h3]]]. *)
(*         have ? : B0 = C0 by eauto using lookup_deter. subst. *)
(*         sfirstorder use:T_Var. *)
(*       * clear => ? ? _. exfalso. *)
(*         hauto l:on use:REReds.var_inv, REReds.hne_app_inv. *)
(*       * clear => ? ? _. exfalso. *)
(*         hauto l:on use:REReds.var_inv, REReds.hne_proj_inv. *)
(*       * clear => ? ? _. exfalso. *)
(*         hauto q:on use:REReds.var_inv, REReds.hne_ind_inv. *)
(*     + case : b => //=; *)
(*                    lazymatch goal with *)
(*                    | [|- context[algo_metric _ (PApp _ _) (PApp _ _)]] => idtac *)
(*                    | _ => move => > /algo_metric_join *)
(*                    end. *)
(*       * clear => *. exfalso. *)
(*         hauto lq:on rew:off use:REReds.hne_app_inv, REReds.var_inv. *)
(*       (* real case *) *)
(*       * move => b1 a1 b0 a0 halg hne1 hne0 Γ A B wtA wtB. *)
(*         move /App_Inv : wtA => [A0][B0][hb0][ha0]hS0. *)
(*         move /App_Inv : wtB => [A1][B1][hb1][ha1]hS1. *)
(*         move : algo_metric_app (hne0) (hne1) halg. repeat move/[apply]. *)
(*         move => [j [hj [hal0 hal1]]]. *)
(*         have /ih := hal0. *)
(*         move /(_ hj). *)
(*         move => [_ ihb]. *)
(*         move : ihb (hne0) (hne1) hb0 hb1. repeat move/[apply]. *)
(*         move => [hb01][C][hT0][hT1][hT2]hT3. *)
(*         move /Sub_Bind_InvL : (hT0). *)
(*         move => [i][A2][B2]hE. *)
(*         have hSu20 : Γ ⊢ PBind PPi A2 B2 ≲ PBind PPi A0 B0 by *)
(*           eauto using Su_Eq, Su_Transitive. *)
(*         have hSu10 : Γ ⊢ PBind PPi A2 B2 ≲ PBind PPi A1 B1 by *)
(*           eauto using Su_Eq, Su_Transitive. *)
(*         have hSuA0 : Γ ⊢ A0 ≲ A2 by sfirstorder use:Su_Pi_Proj1. *)
(*         have hSuA1 : Γ ⊢ A1 ≲ A2 by sfirstorder use:Su_Pi_Proj1. *)
(*         have ha1' : Γ ⊢ a1 ∈ A2 by eauto using T_Conv. *)
(*         have ha0' : Γ ⊢ a0 ∈ A2 by eauto using T_Conv. *)
(*         move : ih (hj) hal1. repeat move/[apply]. *)
(*         move => [ih _]. *)
(*         move : ih (ha0') (ha1'); repeat move/[apply]. *)
(*         move => iha. *)
(*         split. qblast. *)
(*         exists (subst_PTm (scons a0 VarPTm) B2). *)
(*         split. *)
(*         apply : Su_Transitive; eauto. *)
(*         move /E_Refl in ha0. *)
(*         hauto l:on use:Su_Pi_Proj2. *)
(*         have h01 : Γ ⊢ a0 ≡ a1 ∈ A2 by sfirstorder use:coqeq_sound_mutual. *)
(*         split. *)
(*         apply Su_Transitive with (B := subst_PTm (scons a1 VarPTm) B2). *)
(*         move /regularity_sub0 : hSu10 => [i0]. *)
(*         hauto l:on use:bind_inst. *)
(*         hauto lq:on rew:off use:Su_Pi_Proj2, Su_Transitive, E_Refl. *)
(*         split. *)
(*         by apply : T_App; eauto using T_Conv_E. *)
(*         apply : T_Conv; eauto. *)
(*         apply T_App with (A := A2) (B := B2); eauto. *)
(*         apply : T_Conv_E; eauto. *)
(*         move /E_Symmetric in h01. *)
(*         move /regularity_sub0 : hSu20 => [i0]. *)
(*         sfirstorder use:bind_inst. *)
(*       * clear => ? ? ?. exfalso. *)
(*         hauto q:on use:REReds.hne_app_inv, REReds.hne_proj_inv. *)
(*       * clear => ? ? ?. exfalso. *)
(*         hauto q:on use:REReds.hne_app_inv, REReds.hne_ind_inv. *)
(*     + case : b => //=. *)
(*       * move => i p h /algo_metric_join. clear => ? _ ?. exfalso. *)
(*         hauto l:on use:REReds.hne_proj_inv, REReds.var_inv. *)
(*       * move => > /algo_metric_join. clear => ? ? ?. exfalso. *)
(*         hauto l:on use:REReds.hne_proj_inv, REReds.hne_app_inv. *)
(*       (* real case *) *)
(*       * move => p1 a1 p0 a0 /algo_metric_proj ha hne1 hne0. *)
(*         move : ha (hne0) (hne1); repeat move/[apply]. *)
(*         move => [? [j []]]. subst. *)
(*         move : ih; repeat move/[apply]. *)
(*         move => [_ ih]. *)
(*         case : p1. *)
(*         ** move => Γ A B ha0 ha1. *)
(*            move /Proj1_Inv : ha0. move => [A0][B0][ha0]hSu0. *)
(*            move /Proj1_Inv : ha1. move => [A1][B1][ha1]hSu1. *)
(*            move : ih ha0 ha1 (hne0) (hne1); repeat move/[apply]. *)
(*            move => [ha [C [hS0 [hS1 [wta0 wta1]]]]]. *)
(*            split. sauto lq:on. *)
(*            move /Sub_Bind_InvL : (hS0) => [i][A2][B2]hS2. *)
(*            have hSu20 : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0 *)
(*              by eauto using Su_Transitive, Su_Eq. *)
(*            have hSu21 : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1 *)
(*              by eauto using Su_Transitive, Su_Eq. *)
(*            exists A2. split; eauto using Su_Sig_Proj1, Su_Transitive. *)
(*            repeat split => //=. *)
(*            hauto l:on use:Su_Sig_Proj1, Su_Transitive. *)
(*            apply T_Proj1 with (B := B2); eauto using T_Conv_E. *)
(*            apply T_Proj1 with (B := B2); eauto using T_Conv_E. *)
(*         ** move => Γ A B  ha0  ha1. *)
(*            move /Proj2_Inv : ha0. move => [A0][B0][ha0]hSu0. *)
(*            move /Proj2_Inv : ha1. move => [A1][B1][ha1]hSu1. *)
(*            move : ih (ha0) (ha1) (hne0) (hne1); repeat move/[apply]. *)
(*            move => [ha [C [hS0 [hS1 [wta0 wta1]]]]]. *)
(*            split. sauto lq:on. *)
(*            move /Sub_Bind_InvL : (hS0) => [i][A2][B2]hS2. *)
(*            have hSu20 : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A0 B0 *)
(*              by eauto using Su_Transitive, Su_Eq. *)
(*            have hSu21 : Γ ⊢ PBind PSig A2 B2 ≲ PBind PSig A1 B1 *)
(*              by eauto using Su_Transitive, Su_Eq. *)
(*            have hA20 : Γ ⊢ A2 ≲ A0 by eauto using Su_Sig_Proj1. *)
(*            have hA21 : Γ ⊢ A2 ≲ A1 by eauto using Su_Sig_Proj1. *)
(*            have {}wta0 : Γ ⊢ a0 ∈ PBind PSig A2 B2 by eauto using T_Conv_E. *)
(*            have {}wta1 : Γ ⊢ a1 ∈ PBind PSig A2 B2 by eauto using T_Conv_E. *)
(*            have haE : Γ ⊢ PProj PL a0 ≡ PProj PL a1 ∈ A2 *)
(*              by sauto lq:on use:coqeq_sound_mutual. *)
(*            exists (subst_PTm (scons (PProj PL a0) VarPTm) B2). *)
(*            repeat split. *)
(*            *** apply : Su_Transitive; eauto. *)
(*                have : Γ ⊢ PProj PL a0 ≡ PProj PL a0 ∈ A2 *)
(*                  by qauto use:regularity, E_Refl. *)
(*                sfirstorder use:Su_Sig_Proj2. *)
(*            *** apply : Su_Transitive; eauto. *)
(*                sfirstorder use:Su_Sig_Proj2. *)
(*            *** eauto using T_Proj2. *)
(*            *** apply : T_Conv. *)
(*                apply : T_Proj2; eauto. *)
(*                move /E_Symmetric in haE. *)
(*                move /regularity_sub0 in hSu21. *)
(*                sfirstorder use:bind_inst. *)
(*       * move => > /algo_metric_join; clear => ? ? ?. exfalso. *)
(*         hauto q:on use:REReds.hne_proj_inv, REReds.hne_ind_inv. *)
(*     (* ind ind case *) *)
(*     + move => P a0 b0 c0. *)
(*       case : b => //=; *)
(*                    lazymatch goal with *)
(*                    | [|- context[algo_metric _ (PInd _ _ _ _) (PInd _ _ _ _)]] => idtac *)
(*                    | _ => move => > /algo_metric_join; clear => *; exfalso *)
(*                    end. *)
(*       * hauto q:on use:REReds.hne_ind_inv, REReds.var_inv. *)
(*       * hauto q:on use:REReds.hne_ind_inv, REReds.hne_app_inv. *)
(*       * hauto q:on use:REReds.hne_ind_inv, REReds.hne_proj_inv. *)
(*       * move => P1 a1 b1 c1 /[dup] halg /algo_metric_ind + h0 h1. *)
(*         move /(_ h1 h0). *)
(*         move => [j][hj][hP][ha][hb]hc Γ A B hL hR. *)
(*         move /Ind_Inv : hL => [iP0][wtP0][wta0][wtb0][wtc0]hSu0. *)
(*         move /Ind_Inv : hR => [iP1][wtP1][wta1][wtb1][wtc1]hSu1. *)
(*         have {}iha : a0 ∼ a1 by qauto l:on. *)
(*         have []  : iP0 <= max iP0 iP1 /\ iP1 <= max iP0 iP1 by lia. *)
(*         move : T_Univ_Raise wtP0; do!move/[apply]. move => wtP0. *)
(*         move : T_Univ_Raise wtP1; do!move/[apply]. move => wtP1. *)
(*         have {}ihP : P ⇔ P1 by qauto l:on. *)
(*         set Δ := cons _ _ in wtP0, wtP1, wtc0, wtc1. *)
(*         have wfΔ :⊢ Δ by hauto l:on use:wff_mutual. *)
(*         have hPE : Δ ⊢ P ≡ P1 ∈ PUniv (max iP0 iP1) *)
(*           by hauto l:on use:coqeq_sound_mutual. *)
(*         have haE : Γ ⊢ a0 ≡ a1 ∈ PNat *)
(*           by hauto l:on use:coqeq_sound_mutual. *)
(*         have wtΓ : ⊢ Γ by hauto l:on use:wff_mutual. *)
(*         have hE : Γ ⊢ subst_PTm (scons PZero VarPTm) P ≡ subst_PTm (scons PZero VarPTm) P1 ∈ subst_PTm (scons PZero VarPTm) (PUniv (Nat.max iP0 iP1)). *)
(*         eapply morphing; eauto. apply morphing_ext. by apply morphing_id. by apply T_Zero. *)
(*         have {}wtb1 : Γ ⊢ b1 ∈ subst_PTm (scons PZero VarPTm) P *)
(*           by eauto using T_Conv_E. *)
(*         have {}ihb : b0 ⇔ b1 by hauto l:on. *)
(*         have hPSig : Γ ⊢ PBind PSig PNat P ≡ PBind PSig PNat P1 ∈ PUniv (Nat.max iP0 iP1) by eauto with wt. *)
(*         set T := ren_PTm shift _ in wtc0. *)
(*         have : (cons P Δ) ⊢ c1 ∈ T. *)
(*         apply : T_Conv; eauto. apply : ctx_eq_subst_one; eauto with wt. *)
(*         apply : Su_Eq; eauto. *)
(*         subst T. apply : weakening_su; eauto. *)
(*         eapply morphing. apply : Su_Eq. apply E_Symmetric. by eauto. *)
(*         hauto l:on use:wff_mutual. *)
(*         apply morphing_ext. set x := funcomp _ _. *)
(*         have -> : x = funcomp (ren_PTm shift) VarPTm by asimpl. *)
(*         apply : morphing_ren; eauto using renaming_shift. by apply morphing_id. *)
(*         apply T_Suc. apply T_Var => //=. apply here. subst T => {}wtc1. *)
(*         have {}ihc : c0 ⇔ c1 by qauto l:on. *)
(*         move => [:ih]. *)
(*         split. abstract : ih. move : h0 h1 ihP iha ihb ihc. clear. sauto lq:on. *)
(*         have hEInd : Γ ⊢ PInd P a0 b0 c0 ≡ PInd P1 a1 b1 c1 ∈ subst_PTm (scons a0 VarPTm) P by hfcrush use:coqeq_sound_mutual. *)
(*         exists (subst_PTm (scons a0 VarPTm) P). *)
(*         repeat split => //=; eauto with wt. *)
(*         apply : Su_Transitive. *)
(*         apply : Su_Sig_Proj2; eauto. apply : Su_Sig; eauto using T_Nat' with wt. *)
(*         apply : Su_Eq. apply E_Refl. by apply T_Nat'. *)
(*         apply : Su_Eq. apply hPE. by eauto. *)
(*         move : hEInd. clear. hauto l:on use:regularity. *)
(* Qed. *)

Lemma coqeq_sound : forall Γ (a b : PTm) A,
    Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> a ⇔ b -> Γ ⊢ a ≡ b ∈ A.
Proof. sfirstorder use:coqeq_sound_mutual. Qed.

(* Lemma coqeq_complete Γ (a b A : PTm) : *)
(*   Γ ⊢ a ≡ b ∈ A -> a ⇔ b. *)
(* Proof. *)
(*   move => h. *)
(*   suff : exists k, algo_metric k a b by hauto lq:on use:coqeq_complete', regularity. *)
(*   eapply fundamental_theorem in h. *)
(*   move /logrel.SemEq_SN_Join : h. *)
(*   move => h. *)
(*   have : exists va vb : PTm, *)
(*          rtc LoRed.R a va /\ *)
(*          rtc LoRed.R b vb /\ nf va /\ nf vb /\ EJoin.R va vb *)
(*       by hauto l:on use:DJoin.standardization_lo. *)
(*   move => [va][vb][hva][hvb][nva][nvb]hj. *)
(*   move /relations.rtc_nsteps : hva => [i hva]. *)
(*   move /relations.rtc_nsteps : hvb => [j hvb]. *)
(*   exists (i + j + size_PTm va + size_PTm vb). *)
(*   hauto lq:on solve+:lia. *)
(* Qed. *)


Reserved Notation "a ≪ b" (at level 70).
Reserved Notation "a ⋖ b" (at level 70).
Inductive CoqLEq : PTm -> PTm -> Prop :=
| CLE_UnivCong i j :
  i <= j ->
  (* -------------------------- *)
  PUniv i ⋖ PUniv j

| CLE_PiCong A0 A1 B0 B1 :
  A1 ≪  A0 ->
  B0 ≪ B1 ->
  (* ---------------------------- *)
  PBind PPi A0 B0 ⋖ PBind PPi A1 B1

| CLE_SigCong A0 A1 B0 B1 :
  A0 ≪ A1 ->
  B0 ≪ B1 ->
  (* ---------------------------- *)
  PBind PSig A0 B0 ⋖ PBind PSig A1 B1

| CLE_NatCong :
  PNat ⋖ PNat

| CLE_NeuNeu a0 a1 :
  a0 ∼ a1 ->
  a0 ⋖ a1

with CoqLEq_R : PTm -> PTm -> Prop :=
| CLE_HRed a a' b b'  :
  rtc HRed.R a a' ->
  rtc HRed.R b b' ->
  a' ⋖ b' ->
  (* ----------------------- *)
  a ≪ b
where "a ≪ b" := (CoqLEq_R a b) and "a ⋖ b" := (CoqLEq a b).

Scheme coqleq_ind := Induction for CoqLEq Sort Prop
  with coqleq_r_ind := Induction for CoqLEq_R Sort Prop.

Combined Scheme coqleq_mutual from coqleq_ind, coqleq_r_ind.

(* Definition salgo_metric k (a b : PTm ) := *)
(*   exists i j va vb, nsteps LoRed.R i a va /\ nsteps LoRed.R j b vb /\ nf va /\ nf vb /\ ESub.R va vb /\ size_PTm va + size_PTm vb + i + j <= k. *)

(* Lemma salgo_metric_algo_metric k (a b : PTm) : *)
(*   ishne a \/ ishne b -> *)
(*   salgo_metric k a b -> *)
(*   algo_metric k a b. *)
(* Proof. *)
(*   move => h. *)
(*   move => [i][j][va][vb][hva][hvb][nva][nvb][hS]sz. *)
(*   rewrite/ESub.R in hS. *)
(*   move : hS => [va'][vb'][h0][h1]h2. *)
(*   suff : va' = vb' by sauto lq:on. *)
(*   have {}hva : rtc RERed.R a va by hauto lq:on use:@relations.rtc_nsteps, REReds.FromRReds, LoReds.ToRReds. *)
(*   have {}hvb : rtc RERed.R b vb by hauto lq:on use:@relations.rtc_nsteps, REReds.FromRReds, LoReds.ToRReds. *)
(*   apply REReds.FromEReds in h0, h1. *)
(*   have : ishne va' \/ ishne vb' by *)
(*     hauto lq:on rew:off use:@relations.rtc_transitive, REReds.hne_preservation. *)
(*   hauto lq:on use:Sub1.hne_refl. *)
(* Qed. *)

(* Lemma coqleq_sound_mutual : *)
(*     (forall (a b : PTm), a ⋖ b -> forall Γ i, Γ ⊢ a ∈ PUniv i -> Γ ⊢ b ∈ PUniv i -> Γ ⊢ a ≲ b ) /\ *)
(*     (forall (a b : PTm), a ≪ b -> forall Γ i, Γ ⊢ a ∈ PUniv i -> Γ ⊢ b ∈ PUniv i -> Γ ⊢ a ≲ b ). *)
(* Proof. *)
(*   apply coqleq_mutual. *)
(*   - hauto lq:on use:wff_mutual ctrs:LEq. *)
(*   - move => A0 A1 B0 B1 hA ihA hB ihB Γ i. *)
(*     move /Bind_Univ_Inv => [hA0]hB0 /Bind_Univ_Inv [hA1]hB1. *)
(*     have hlA  : Γ ⊢ A1 ≲ A0 by sfirstorder. *)
(*     have hΓ : ⊢ Γ by sfirstorder use:wff_mutual. *)
(*     apply Su_Transitive with (B := PBind PPi A1 B0). *)
(*     by apply : Su_Pi; eauto using E_Refl, Su_Eq. *)
(*     apply : Su_Pi; eauto using E_Refl, Su_Eq. *)
(*     apply : ihB; eauto using ctx_eq_subst_one. *)
(*   - move => A0 A1 B0 B1 hA ihA hB ihB Γ i. *)
(*     move /Bind_Univ_Inv => [hA0]hB0 /Bind_Univ_Inv [hA1]hB1. *)
(*     have hlA  : Γ ⊢ A0 ≲ A1 by sfirstorder. *)
(*     have hΓ : ⊢ Γ by sfirstorder use:wff_mutual. *)
(*     apply Su_Transitive with (B := PBind PSig A0 B1). *)
(*     apply : Su_Sig; eauto using E_Refl, Su_Eq. *)
(*     apply : ihB; by eauto using ctx_eq_subst_one. *)
(*     apply : Su_Sig; eauto using E_Refl, Su_Eq. *)
(*   - sauto lq:on use:coqeq_sound_mutual, Su_Eq. *)
(*   - sauto lq:on use:coqeq_sound_mutual, Su_Eq. *)
(*   - move => a a' b b' ? ? ? ih Γ i ha hb. *)
(*     have /Su_Eq ? : Γ ⊢ a ≡ a' ∈ PUniv i by sfirstorder use:HReds.ToEq. *)
(*     have /E_Symmetric /Su_Eq ? : Γ ⊢ b ≡ b' ∈ PUniv i by sfirstorder use:HReds.ToEq. *)
(*     suff : Γ ⊢ a' ≲ b' by eauto using Su_Transitive. *)
(*     eauto using HReds.preservation. *)
(* Qed. *)

(* Lemma salgo_metric_case k (a b : PTm ) : *)
(*   salgo_metric k a b -> *)
(*   (ishf a \/ ishne a) \/ exists k' a', HRed.R a a' /\ salgo_metric k' a' b /\ k' < k. *)
(* Proof. *)
(*   move=>[i][j][va][vb][h0] [h1][h2][h3][[v [h4 h5]]] h6. *)
(*   case : a h0 => //=; try firstorder. *)
(*   - inversion h0 as [|A B C D E F]; subst. *)
(*     hauto qb:on use:ne_hne. *)
(*     inversion E; subst => /=. *)
(*     + hauto lq:on use:HRed.AppAbs unfold:algo_metric solve+:lia. *)
(*     + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia. *)
(*     + sfirstorder qb:on use:ne_hne. *)
(*   - inversion h0 as [|A B C D E F]; subst. *)
(*     hauto qb:on use:ne_hne. *)
(*     inversion E; subst => /=. *)
(*     + hauto lq:on use:HRed.ProjPair unfold:algo_metric solve+:lia. *)
(*     + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia. *)
(*   - inversion h0 as [|A B C D E F]; subst. *)
(*     hauto qb:on use:ne_hne. *)
(*     inversion E; subst => /=. *)
(*     + hauto lq:on use:HRed.IndZero unfold:algo_metric solve+:lia. *)
(*     + hauto lq:on ctrs:HRed.R use:hf_hred_lored unfold:algo_metric solve+:lia. *)
(*     + sfirstorder use:ne_hne. *)
(*     + hauto lq:on ctrs:HRed.R use:hf_hred_lored unfold:algo_metric solve+:lia. *)
(*     + sfirstorder use:ne_hne. *)
(*     + sfirstorder use:ne_hne. *)
(* Qed. *)

(* Lemma CLE_HRedL (a a' b : PTm )  : *)
(*   HRed.R a a' -> *)
(*   a' ≪ b -> *)
(*   a ≪ b. *)
(* Proof. *)
(*   hauto lq:on ctrs:rtc, CoqLEq_R inv:CoqLEq_R. *)
(* Qed. *)

(* Lemma CLE_HRedR (a a' b : PTm)  : *)
(*   HRed.R a a' -> *)
(*   b ≪ a' -> *)
(*   b ≪ a. *)
(* Proof. *)
(*   hauto lq:on ctrs:rtc, CoqLEq_R inv:CoqLEq_R. *)
(* Qed. *)


(* Lemma algo_metric_caseR k (a b : PTm) : *)
(*   salgo_metric k a b -> *)
(*   (ishf b \/ ishne b) \/ exists k' b', HRed.R b b' /\ salgo_metric k' a b' /\ k' < k. *)
(* Proof. *)
(*   move=>[i][j][va][vb][h0] [h1][h2][h3][[v [h4 h5]]] h6. *)
(*   case : b h1 => //=; try by firstorder. *)
(*   - inversion 1 as [|A B C D E F]; subst. *)
(*     hauto qb:on use:ne_hne. *)
(*     inversion E; subst => /=. *)
(*     + hauto q:on use:HRed.AppAbs unfold:salgo_metric solve+:lia. *)
(*     + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:salgo_metric solve+:lia. *)
(*     + sfirstorder qb:on use:ne_hne. *)
(*   - inversion 1 as [|A B C D E F]; subst. *)
(*     hauto qb:on use:ne_hne. *)
(*     inversion E; subst => /=. *)
(*     + hauto lq:on use:HRed.ProjPair unfold:algo_metric solve+:lia. *)
(*     + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia. *)
(*   - inversion 1 as [|A B C D E F]; subst. *)
(*     hauto qb:on use:ne_hne. *)
(*     inversion E; subst => /=. *)
(*     + hauto lq:on use:HRed.IndZero unfold:algo_metric solve+:lia. *)
(*     + hauto lq:on ctrs:HRed.R use:hf_hred_lored unfold:algo_metric solve+:lia. *)
(*     + sfirstorder use:ne_hne. *)
(*     + hauto lq:on ctrs:HRed.R use:hf_hred_lored unfold:algo_metric solve+:lia. *)
(*     + sfirstorder use:ne_hne. *)
(*     + sfirstorder use:ne_hne. *)
(* Qed. *)

(* Lemma salgo_metric_sub k (a b : PTm) : *)
(*   salgo_metric k a b -> *)
(*   Sub.R a b. *)
(* Proof. *)
(*   rewrite /algo_metric. *)
(*   move => [i][j][va][vb][h0][h1][h2][h3][[va' [vb' [hva [hvb hS]]]]]h5. *)
(*   have {}h0 : rtc LoRed.R a va by hauto lq:on use:@relations.rtc_nsteps. *)
(*   have {}h1 : rtc LoRed.R b vb by hauto lq:on use:@relations.rtc_nsteps. *)
(*   apply REReds.FromEReds in hva,hvb. *)
(*   apply LoReds.ToRReds in h0,h1. *)
(*   apply REReds.FromRReds in h0,h1. *)
(*   rewrite /Sub.R. exists va', vb'. sfirstorder use:@relations.rtc_transitive. *)
(* Qed. *)

(* Lemma salgo_metric_pi k (A0 : PTm) B0 A1 B1  : *)
(*   salgo_metric k (PBind PPi A0 B0) (PBind PPi A1 B1) -> *)
(*   exists j, j < k /\ salgo_metric j A1 A0 /\ salgo_metric j B0 B1. *)
(* Proof. *)
(*   move => [i][j][va][vb][h0][h1][h2][h3][h4]h5. *)
(*   move : lored_nsteps_bind_inv h0 => /[apply]. *)
(*   move => [i0][i1][a2][b2][?][?][?][ha02]hb02. subst. *)
(*   move : lored_nsteps_bind_inv h1 => /[apply]. *)
(*   move => [j0][j1][a3][b3][?][?][?][ha13]hb13. subst. *)
(*   move /ESub.pi_inj : h4 => [? ?]. *)
(*   hauto qb:on solve+:lia. *)
(* Qed. *)

(* Lemma salgo_metric_sig k (A0 : PTm) B0 A1 B1  : *)
(*   salgo_metric k (PBind PSig A0 B0) (PBind PSig A1 B1) -> *)
(*   exists j, j < k /\ salgo_metric j A0 A1 /\ salgo_metric j B0 B1. *)
(* Proof. *)
(*   move => [i][j][va][vb][h0][h1][h2][h3][h4]h5. *)
(*   move : lored_nsteps_bind_inv h0 => /[apply]. *)
(*   move => [i0][i1][a2][b2][?][?][?][ha02]hb02. subst. *)
(*   move : lored_nsteps_bind_inv h1 => /[apply]. *)
(*   move => [j0][j1][a3][b3][?][?][?][ha13]hb13. subst. *)
(*   move /ESub.sig_inj : h4 => [? ?]. *)
(*   hauto qb:on solve+:lia. *)
(* Qed. *)

(* Lemma coqleq_complete' k (a b : PTm ) : *)
(*   salgo_metric k a b -> (forall Γ i, Γ ⊢ a ∈ PUniv i -> Γ ⊢ b ∈ PUniv i -> a ≪ b). *)
(* Proof. *)
(*   move : k a b. *)
(*   elim /Wf_nat.lt_wf_ind. *)
(*   move => n ih. *)
(*   move => a b /[dup] h /salgo_metric_case. *)
(*   (* Cases where a and b can take steps *) *)
(*   case; cycle 1. *)
(*   move : a b h. *)
(*   qauto l:on use:HRed.preservation, CLE_HRedL, hred_hne. *)
(*   case /algo_metric_caseR : (h); cycle 1. *)
(*   qauto l:on use:HRed.preservation, CLE_HRedR, hred_hne. *)
(*   (* Cases where neither a nor b can take steps *) *)
(*   case => fb; case => fa. *)
(*   - case : a fa h => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'. *)
(*     + case : b fb => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'. *)
(*       * move => p0 A0 B0 _ p1 A1 B1 _. *)
(*         move => h. *)
(*         have ? : p1 = p0 by *)
(*           hauto lq:on rew:off use:salgo_metric_sub, Sub.bind_inj. *)
(*         subst. *)
(*         case : p0 h => //=. *)
(*         ** move /salgo_metric_pi. *)
(*            move => [j [hj [hA hB]]] Γ i. *)
(*            move /Bind_Univ_Inv => [hA1 hB1] /Bind_Univ_Inv [hA0 hB0]. *)
(*            have ihA : A0 ≪ A1 by hauto l:on. *)
(*            econstructor; eauto using E_Refl; constructor=> //. *)
(*            have ihA' : Γ ⊢ A0 ≲ A1 by hauto l:on use:coqleq_sound_mutual. *)
(*            suff : (cons A0 Γ) ⊢ B1 ∈ PUniv i *)
(*              by hauto l:on. *)
(*            eauto using ctx_eq_subst_one. *)
(*         ** move /salgo_metric_sig. *)
(*            move => [j [hj [hA hB]]] Γ i. *)
(*            move /Bind_Univ_Inv => [hA1 hB1] /Bind_Univ_Inv [hA0 hB0]. *)
(*            have ihA : A1 ≪ A0 by hauto l:on. *)
(*            econstructor; eauto using E_Refl; constructor=> //. *)
(*            have ihA' : Γ ⊢ A1 ≲ A0 by hauto l:on use:coqleq_sound_mutual. *)
(*            suff : (cons A1 Γ) ⊢ B0 ∈ PUniv i *)
(*              by hauto l:on. *)
(*            eauto using ctx_eq_subst_one. *)
(*       * hauto lq:on use:salgo_metric_sub, Sub.bind_univ_noconf. *)
(*       * hauto lq:on use:salgo_metric_sub, Sub.nat_bind_noconf. *)
(*       * move => _ > _ /salgo_metric_sub. *)
(*         hauto lq:on rew:off use:REReds.bind_inv, REReds.zero_inv inv:Sub1.R. *)
(*       * hauto lq:on rew:off use:REReds.bind_inv, REReds.suc_inv, salgo_metric_sub inv:Sub1.R. *)
(*     + case : b fb => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'. *)
(*       * hauto lq:on use:salgo_metric_sub, Sub.univ_bind_noconf. *)
(*       * move => *. econstructor; eauto using rtc_refl. *)
(*         hauto lq:on use:salgo_metric_sub, Sub.univ_inj, CLE_UnivCong. *)
(*       * hauto lq:on rew:off use:REReds.univ_inv, REReds.nat_inv, salgo_metric_sub inv:Sub1.R. *)
(*       * hauto lq:on rew:off use:REReds.univ_inv, REReds.zero_inv, salgo_metric_sub inv:Sub1.R. *)
(*       * hauto lq:on rew:off use:REReds.suc_inv, REReds.univ_inv, salgo_metric_sub inv:Sub1.R. *)
(*   (* Both cases are impossible *) *)
(*     + case : b fb => //=. *)
(*       * hauto lq:on use:T_AbsNat_Imp. *)
(*       * hauto lq:on use:T_PairNat_Imp. *)
(*       * hauto lq:on rew:off use:REReds.nat_inv, REReds.bind_inv, salgo_metric_sub inv:Sub1.R. *)
(*       * hauto lq:on rew:off use:REReds.nat_inv, REReds.univ_inv, salgo_metric_sub inv:Sub1.R. *)
(*       * hauto l:on. *)
(*       * hauto lq:on rew:off use:REReds.nat_inv, REReds.zero_inv, salgo_metric_sub inv:Sub1.R. *)
(*       * hauto lq:on rew:off use:REReds.nat_inv, REReds.suc_inv, salgo_metric_sub inv:Sub1.R. *)
(*     + move => ? ? Γ i /Zero_Inv. *)
(*       clear. *)
(*       move /synsub_to_usub => [_ [_ ]]. *)
(*       hauto lq:on rew:off use:REReds.nat_inv, REReds.univ_inv inv:Sub1.R. *)
(*     + move => ? _ _ Γ i /Suc_Inv => [[_]]. *)
(*       move /synsub_to_usub. *)
(*       hauto lq:on rew:off use:REReds.nat_inv, REReds.univ_inv inv:Sub1.R. *)
(*   - have {}h : DJoin.R a b by *)
(*        hauto lq:on use:salgo_metric_algo_metric, algo_metric_join. *)
(*     case : b fb h => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'. *)
(*     + hauto lq:on use:DJoin.hne_bind_noconf. *)
(*     + hauto lq:on use:DJoin.hne_univ_noconf. *)
(*     + hauto lq:on use:DJoin.hne_nat_noconf. *)
(*     + move => _ _ Γ i _. *)
(*       move /Zero_Inv. *)
(*       hauto q:on use:REReds.nat_inv, REReds.univ_inv, synsub_to_usub inv:Sub1.R. *)
(*     + move => p _ _ Γ i _ /Suc_Inv. *)
(*       hauto q:on use:REReds.nat_inv, REReds.univ_inv, synsub_to_usub inv:Sub1.R. *)
(*   - have {}h : DJoin.R b a by *)
(*       hauto lq:on use:salgo_metric_algo_metric, algo_metric_join, DJoin.symmetric. *)
(*     case : a fa h => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'. *)
(*     + hauto lq:on use:DJoin.hne_bind_noconf. *)
(*     + hauto lq:on use:DJoin.hne_univ_noconf. *)
(*     + hauto lq:on use:DJoin.hne_nat_noconf. *)
(*     + move => _ _ Γ i. *)
(*       move /Zero_Inv. *)
(*       hauto q:on use:REReds.nat_inv, REReds.univ_inv, synsub_to_usub inv:Sub1.R. *)
(*     + move => p _ _ Γ i /Suc_Inv. *)
(*       hauto q:on use:REReds.nat_inv, REReds.univ_inv, synsub_to_usub inv:Sub1.R. *)
(*   - move => Γ i ha hb. *)
(*     econstructor; eauto using rtc_refl. *)
(*     apply CLE_NeuNeu. move {ih}. *)
(*     have {}h : algo_metric n a b by *)
(*       hauto lq:on use:salgo_metric_algo_metric. *)
(*     eapply coqeq_complete'; eauto. *)
(* Qed. *)

(* Lemma coqleq_complete Γ (a b : PTm) : *)
(*   Γ ⊢ a ≲ b -> a ≪ b. *)
(* Proof. *)
(*   move => h. *)
(*   suff : exists k, salgo_metric k a b by hauto lq:on use:coqleq_complete', regularity. *)
(*   eapply fundamental_theorem in h. *)
(*   move /logrel.SemLEq_SN_Sub : h. *)
(*   move => h. *)
(*   have : exists va vb : PTm , *)
(*          rtc LoRed.R a va /\ *)
(*          rtc LoRed.R b vb /\ nf va /\ nf vb /\ ESub.R va vb *)
(*       by hauto l:on use:Sub.standardization_lo. *)
(*   move => [va][vb][hva][hvb][nva][nvb]hj. *)
(*   move /relations.rtc_nsteps : hva => [i hva]. *)
(*   move /relations.rtc_nsteps : hvb => [j hvb]. *)
(*   exists (i + j + size_PTm va + size_PTm vb). *)
(*   hauto lq:on solve+:lia. *)
(* Qed. *)

(* Lemma coqleq_sound : forall Γ (a b : PTm) i j, *)
(*     Γ ⊢ a ∈ PUniv i -> Γ ⊢ b ∈ PUniv j -> a ≪ b -> Γ ⊢ a ≲ b. *)
(* Proof. *)
(*   move => Γ a b i j. *)
(*   have [*] : i <= i + j /\ j <= i + j by lia. *)
(*   have : Γ ⊢ a ∈ PUniv (i + j) /\ Γ ⊢ b ∈ PUniv (i + j) *)
(*     by sfirstorder use:T_Univ_Raise. *)
(*   sfirstorder use:coqleq_sound_mutual. *)
(* Qed. *)
