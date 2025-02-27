Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax
  common typing preservation admissible fp_red structural soundness.
From Hammer Require Import Tactics.
Require Import ssreflect ssrbool.
Require Import Psatz.
From stdpp Require Import relations (rtc(..), nsteps(..)).
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Cdcl.Itauto.

Module HRed.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a b :
    R (PApp (PAbs a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

  | IndZero P b c :
    R (PInd P PZero b c) b

  | IndSuc P a b c :
    R (PInd P (PSuc a) b c) (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c)

  (*************** Congruence ********************)
  | AppCong a0 a1 b :
    R a0 a1 ->
    R (PApp a0 b) (PApp a1 b)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1)
  | IndCong P a0 a1 b c :
    R a0 a1 ->
    R (PInd P a0 b c) (PInd P a1 b c).

  Lemma ToRRed n (a b : PTm n) : HRed.R a b -> RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:RRed.R. Qed.

  Lemma preservation n Γ (a b A : PTm n) : Γ ⊢ a ∈ A -> HRed.R a b -> Γ ⊢ b ∈ A.
  Proof.
    sfirstorder use:subject_reduction, ToRRed.
  Qed.

  Lemma ToEq n Γ (a b : PTm n) A : Γ ⊢ a ∈ A -> HRed.R a b -> Γ ⊢ a ≡ b ∈ A.
  Proof. sfirstorder use:ToRRed, RRed_Eq. Qed.

End HRed.

Module HReds.
  Lemma preservation n Γ (a b A : PTm n) : Γ ⊢ a ∈ A -> rtc HRed.R a b -> Γ ⊢ b ∈ A.
  Proof. induction 2; sfirstorder use:HRed.preservation. Qed.

  Lemma ToEq n Γ (a b : PTm n) A : Γ ⊢ a ∈ A -> rtc HRed.R a b -> Γ ⊢ a ≡ b ∈ A.
  Proof.
    induction 2; sauto lq:on use:HRed.ToEq, E_Transitive, HRed.preservation.
  Qed.
End HReds.

Lemma T_Conv_E n Γ (a : PTm n) A B i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ A ≡ B ∈ PUniv i \/ Γ ⊢ B ≡ A ∈ PUniv i ->
  Γ ⊢ a ∈ B.
Proof. qauto use:T_Conv, Su_Eq, E_Symmetric. Qed.

Lemma E_Conv_E n Γ (a b : PTm n) A B i :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ A ≡ B ∈ PUniv i \/ Γ ⊢ B ≡ A ∈ PUniv i ->
  Γ ⊢ a ≡ b ∈ B.
Proof. qauto use:E_Conv, Su_Eq, E_Symmetric. Qed.

Lemma lored_embed n Γ (a b : PTm n) A :
  Γ ⊢ a ∈ A -> LoRed.R a b -> Γ ⊢ a ≡ b ∈ A.
Proof. sfirstorder use:LoRed.ToRRed, RRed_Eq. Qed.

Lemma loreds_embed n Γ (a b : PTm n) A :
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

Lemma T_Bot_Imp n Γ (A : PTm n) :
  Γ ⊢ PBot ∈ A -> False.
  move E : PBot => u hu.
  move : E.
  induction hu => //=.
Qed.

Lemma Zero_Inv n Γ U :
  Γ ⊢ @PZero n ∈ U ->
  Γ ⊢ PNat ≲ U.
Proof.
  move E : PZero => u hu.
  move : E.
  elim : n Γ u U /hu=>//=.
  by eauto using Su_Eq, E_Refl, T_Nat'.
  hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma Sub_Bind_InvR n Γ p (A : PTm n) B C :
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
  - hauto lq:on use:regularity, T_Bot_Imp.
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

Lemma Sub_Univ_InvR n (Γ : fin n -> PTm n) i C :
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
  - hauto lq:on use:regularity, T_Bot_Imp.
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

Lemma Sub_Bind_InvL n Γ p (A : PTm n) B C :
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
  - hauto lq:on use:regularity, T_Bot_Imp.
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

Lemma T_Abs_Inv n Γ (a0 a1 : PTm (S n)) U :
  Γ ⊢ PAbs a0 ∈ U ->
  Γ ⊢ PAbs a1 ∈ U ->
  exists Δ V, Δ ⊢ a0 ∈ V /\ Δ ⊢ a1 ∈ V.
Proof.
  move /Abs_Inv => [A0][B0][wt0]hU0.
  move /Abs_Inv => [A1][B1][wt1]hU1.
  move /Sub_Bind_InvR : (hU0) => [i][A2][B2]hE.
  have hSu : Γ ⊢ PBind PPi A1 B1 ≲ PBind PPi A2 B2 by eauto using Su_Eq, Su_Transitive.
  have hSu' : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Eq, Su_Transitive.
  exists (funcomp (ren_PTm shift) (scons A2 Γ)), B2.
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

Lemma T_Univ_Raise n Γ (a : PTm n) i j :
  Γ ⊢ a ∈ PUniv i ->
  i <= j ->
  Γ ⊢ a ∈ PUniv j.
Proof. hauto lq:on rew:off use:T_Conv, Su_Univ, wff_mutual. Qed.

Lemma Bind_Univ_Inv n Γ p (A : PTm n) B i :
  Γ ⊢ PBind p A B ∈ PUniv i ->
  Γ ⊢ A ∈ PUniv i /\ funcomp (ren_PTm shift) (scons A Γ) ⊢ B ∈ PUniv i.
Proof.
  move /Bind_Inv.
  move => [i0][hA][hB]h.
  move /synsub_to_usub : h => [_ [_ /Sub.univ_inj ? ]].
  sfirstorder use:T_Univ_Raise.
Qed.

Lemma Abs_Pi_Inv n Γ (a : PTm (S n)) A B :
  Γ ⊢ PAbs a ∈ PBind PPi A B ->
  funcomp (ren_PTm shift) (scons A Γ) ⊢ a ∈ B.
Proof.
  move => h.
  have [i hi] : exists i, Γ ⊢ PBind PPi A B ∈ PUniv i by hauto use:regularity.
  have  [{}i {}hi] : exists i, Γ ⊢ A ∈ PUniv i by hauto use:Bind_Inv.
  apply : subject_reduction; last apply RRed.AppAbs'.
  apply : T_App'; cycle 1.
  apply : weakening_wt'; cycle 2. apply hi.
  apply h. reflexivity. reflexivity. rewrite -/ren_PTm.
  apply T_Var' with (i := var_zero).  by asimpl.
  by eauto using Wff_Cons'.
  rewrite -/ren_PTm.
  by asimpl.
  rewrite -/ren_PTm.
  by asimpl.
Qed.

Lemma Pair_Sig_Inv n Γ (a b : PTm n) A B :
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
Inductive CoqEq {n} : PTm n -> PTm n -> Prop :=
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

with CoqEq_Neu  {n} : PTm n -> PTm n -> Prop :=
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

with CoqEq_R {n} : PTm n -> PTm n -> Prop :=
| CE_HRed a a' b b'  :
  rtc HRed.R a a' ->
  rtc HRed.R b b' ->
  a' ↔ b' ->
  (* ----------------------- *)
  a ⇔ b
where "a ↔ b" := (CoqEq a b) and "a ⇔ b" := (CoqEq_R a b) and "a ∼ b" := (CoqEq_Neu a b).

Lemma CE_HRedL n (a a' b : PTm n)  :
  HRed.R a a' ->
  a' ⇔ b ->
  a ⇔ b.
Proof.
  hauto lq:on ctrs:rtc, CoqEq_R inv:CoqEq_R.
Qed.

Scheme
  coqeq_neu_ind := Induction for CoqEq_Neu Sort Prop
  with coqeq_ind := Induction for CoqEq Sort Prop
  with coqeq_r_ind := Induction for CoqEq_R Sort Prop.

Combined Scheme coqeq_mutual from coqeq_neu_ind, coqeq_ind, coqeq_r_ind.

Lemma coqeq_symmetric_mutual : forall n,
    (forall (a b : PTm n), a ∼ b -> b ∼ a) /\
    (forall (a b : PTm n), a ↔ b -> b ↔ a) /\
    (forall (a b : PTm n), a ⇔ b -> b ⇔ a).
Proof. apply coqeq_mutual; qauto l:on ctrs:CoqEq,CoqEq_R, CoqEq_Neu. Qed.

Lemma coqeq_sound_mutual : forall n,
    (forall (a b : PTm n), a ∼ b -> forall Γ A B, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> exists C,
       Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ≡ b ∈ C) /\
    (forall (a b : PTm n), a ↔ b -> forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> Γ ⊢ a ≡ b ∈ A) /\
    (forall (a b : PTm n), a ⇔ b -> forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> Γ ⊢ a ≡ b ∈ A).
Proof.
  move => [:hAppL hPairL].
  apply coqeq_mutual.
  - move => n i Γ A B hi0 hi1.
    move /Var_Inv : hi0 => [hΓ h0].
    move /Var_Inv : hi1 => [_ h1].
    exists (Γ i).
    repeat split => //=.
    apply E_Refl. eauto using T_Var.
  - move => n [] u0 u1 hu0 hu1 hu ihu Γ A B hu0' hu1'.
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
  - move => n u0 u1 a0 a1 neu0 neu1 hu ihu ha iha Γ A B wta0 wta1.
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
  - move {hAppL hPairL} => n P0 P1 u0 u1 b0 b1 c0 c1 neu0 neu1 hP ihP hu ihu hb ihb hc ihc Γ A B.
    move /Ind_Inv => [i0][hP0][hu0][hb0][hc0]hSu0.
    move /Ind_Inv => [i1][hP1][hu1][hb1][hc1]hSu1.
    move : ihu hu0 hu1; do!move/[apply]. move => ihu.
    have {}ihu : Γ ⊢ u0 ≡ u1 ∈ PNat by hauto l:on use:E_Conv.
    have wfΓ : ⊢ Γ by hauto use:wff_mutual.
    have wfΓ' : ⊢ funcomp (ren_PTm shift) (scons PNat Γ) by hauto lq:on use:Wff_Cons', T_Nat'.
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
    apply T_Suc. by apply T_Var.
  - hauto lq:on use:Zero_Inv db:wt.
  - hauto lq:on use:Suc_Inv db:wt.
  - move => n a b ha iha Γ A h0 h1.
    move /Abs_Inv : h0 => [A0][B0][h0]h0'.
    move /Abs_Inv : h1 => [A1][B1][h1]h1'.
    have [i [A2 [B2 h]]] : exists i A2 B2, Γ ⊢ A ≡ PBind PPi A2 B2 ∈ PUniv i by hauto l:on use:Sub_Bind_InvR.
    have hp0 : Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
    have hp1 : Γ ⊢ PBind PPi A1 B1 ≲ PBind PPi A2 B2 by eauto using Su_Transitive, Su_Eq.
    have [j ?] : exists j, Γ ⊢ A0 ∈ PUniv j by qauto l:on use:Wff_Cons_Inv, wff_mutual.
    have [k ?] : exists j, Γ ⊢ A1 ∈ PUniv j by qauto l:on use:Wff_Cons_Inv, wff_mutual.
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
    move => n a u hneu ha iha Γ A wta wtu.
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
    sfirstorder use:wff_mutual.
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

    (* move /Su_Pi_Proj2_Var in hPidup. *)
    (* apply : T_Conv; eauto. *)
    eapply T_App' with (A := ren_PTm shift A2) (B := ren_PTm (upRen_PTm_PTm shift) B2). by asimpl.
    eapply weakening_wt' with (a := u) (A := PBind PPi A2 B2);eauto.
    by eauto using T_Conv_E. apply T_Var. apply : Wff_Cons'; eauto.
  (* Mirrors the last case *)
  - move => n a u hu ha iha Γ A hu0 ha0.
    apply E_Symmetric.
    apply : hAppL; eauto.
    sfirstorder use:coqeq_symmetric_mutual.
    sfirstorder use:E_Symmetric.
  - move => {hAppL hPairL} n a0 a1 b0 b1 ha iha hb ihb Γ A.
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
    move => n a0 a1 u neu h0 ih0 h1 ih1 Γ A ha hu.
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
  - move => {hAppL hPairL} n p A0 A1 B0 B1 hA ihA hB ihB Γ A hA0 hA1.
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
  - move => n a a' b b' ha hb hab ihab Γ A ha0 hb0.
    have [*] : Γ ⊢ a' ∈ A /\ Γ ⊢ b' ∈ A by eauto using HReds.preservation.
    hauto lq:on use:HReds.ToEq, E_Symmetric, E_Transitive.
Qed.

Definition algo_metric {n} k (a b : PTm n) :=
  exists i j va vb, nsteps LoRed.R i a va /\ nsteps LoRed.R j b vb /\ nf va /\ nf vb /\ EJoin.R va vb /\ size_PTm va + size_PTm vb + i + j <= k.

Lemma ne_hne n (a : PTm n) : ne a -> ishne a.
Proof. elim : a => //=; sfirstorder b:on. Qed.

Lemma hf_hred_lored n (a b : PTm n) :
  ~~ ishf a ->
  LoRed.R a b ->
  HRed.R a b \/ ishne a.
Proof.
  move => + h. elim : n a b/ h=>//=.
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

Lemma algo_metric_case n k (a b : PTm n) :
  algo_metric k a b ->
  (ishf a \/ ishne a) \/ exists k' a', HRed.R a a' /\ algo_metric k' a' b /\ k' < k.
Proof.
  move=>[i][j][va][vb][h0] [h1][h2][h3][[v [h4 h5]]] h6.
  case : a h0 => //=; try firstorder.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.AppAbs unfold:algo_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia.
    + sfirstorder qb:on use:ne_hne.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.ProjPair unfold:algo_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.IndZero unfold:algo_metric solve+:lia.
    + hauto lq:on ctrs:HRed.R use:hf_hred_lored unfold:algo_metric solve+:lia.
    + sfirstorder use:ne_hne.
    + hauto lq:on ctrs:HRed.R use:hf_hred_lored unfold:algo_metric solve+:lia.
    + sfirstorder use:ne_hne.
    + sfirstorder use:ne_hne.
Qed.

Lemma algo_metric_sym n k (a b : PTm n) :
  algo_metric k a b -> algo_metric k b a.
Proof. hauto lq:on unfold:algo_metric solve+:lia. Qed.

Lemma hred_hne n (a b : PTm n) :
  HRed.R a b ->
  ishne a ->
  False.
Proof. induction 1; sfirstorder. Qed.

Lemma hf_not_hne n (a : PTm n) :
  ishf a -> ishne a -> False.
Proof. case : a => //=. Qed.

(* Lemma algo_metric_hf_case n Γ k a b (A : PTm n) : *)
(*   Γ ⊢ a ∈ A -> *)
(*   Γ ⊢ b ∈ A -> *)
(*   algo_metric k a b -> ishf a -> ishf b -> *)
(*   (exists a' b' k', a = PAbs a' /\ b = PAbs b' /\ algo_metric k' a' b' /\ k' < k) \/ *)
(*   (exists a0' a1' b0' b1' ka kb, a = PPair a0' a1' /\ b = PPair b0' b1' /\ algo_metric ka a0' b0' /\ algo_metric ) *)

Lemma T_AbsPair_Imp n Γ a (b0 b1 : PTm n) A :
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

Lemma T_AbsZero_Imp n Γ a (A : PTm n) :
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

Lemma T_AbsSuc_Imp n Γ a b (A : PTm n) :
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

Lemma Nat_Inv n Γ A:
  Γ ⊢ @PNat n ∈ A ->
  exists i, Γ ⊢ PUniv i ≲ A.
Proof.
  move E : PNat => u hu.
  move : E.
  elim : n Γ u A / hu=>//=.
  - hauto lq:on use:E_Refl, T_Univ, Su_Eq.
  - hauto lq:on ctrs:LEq.
Qed.

Lemma T_AbsNat_Imp n Γ a (A : PTm n) :
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

Lemma T_PairBind_Imp n Γ (a0 a1 : PTm n) p A0 B0 U :
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

Lemma T_PairNat_Imp n Γ (a0 a1 : PTm n) U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PNat ∈ U ->
  False.
Proof.
  move/Pair_Inv => [A1][B1][_][_]hbU.
  move /Nat_Inv => [i]/Sub_Univ_InvR[j][k]hU.
  have : Γ ⊢ PBind PSig A1 B1 ≲ PUniv j by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_univ_noconf.
Qed.

Lemma T_PairZero_Imp n Γ (a0 a1 : PTm n) U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PZero ∈ U ->
  False.
Proof.
  move/Pair_Inv=>[A1][B1][_][_]hbU.
  move/Zero_Inv. move/Sub_Bind_InvR : hbU=>[i][A0][B0]*.
  have : Γ ⊢ PNat ≲ PBind PSig A0 B0 by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_nat_noconf.
Qed.

Lemma T_PairSuc_Imp n Γ (a0 a1 : PTm n) b U :
  Γ ⊢ PPair a0 a1 ∈ U ->
  Γ ⊢ PSuc b ∈ U ->
  False.
Proof.
  move/Pair_Inv=>[A1][B1][_][_]hbU.
  move/Suc_Inv=>[_ hU]. move/Sub_Bind_InvR : hbU=>[i][A0][B0]*.
  have : Γ ⊢ PNat ≲ PBind PSig A0 B0 by eauto using Su_Transitive, Su_Eq.
  clear. move /synsub_to_usub. hauto l:on use:Sub.bind_nat_noconf.
Qed.

Lemma Univ_Inv n Γ i U :
  Γ ⊢ @PUniv n i ∈ U ->
  Γ ⊢ PUniv i ∈ PUniv (S i)  /\ Γ ⊢ PUniv (S i) ≲ U.
Proof.
  move E : (PUniv i) => u hu.
  move : i E. elim : n Γ u U / hu => n //=.
  - hauto l:on use:E_Refl, Su_Eq, T_Univ.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma T_PairUniv_Imp n Γ (a0 a1 : PTm n) i U :
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

Lemma T_AbsUniv_Imp n Γ a i (A : PTm n) :
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

Lemma T_AbsUniv_Imp' n Γ (a : PTm (S n)) i  :
  Γ ⊢ PAbs a ∈ PUniv i -> False.
Proof.
  hauto lq:on use:synsub_to_usub, Sub.bind_univ_noconf, Abs_Inv.
Qed.

Lemma T_PairUniv_Imp' n Γ (a b : PTm n) i  :
  Γ ⊢ PPair a b ∈ PUniv i -> False.
Proof.
  hauto lq:on use:synsub_to_usub, Sub.bind_univ_noconf, Pair_Inv.
Qed.

Lemma T_AbsBind_Imp n Γ a p A0 B0 (U : PTm n) :
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

Lemma lored_nsteps_suc_inv k n (a : PTm n) b :
  nsteps LoRed.R k (PSuc a) b -> exists b', nsteps LoRed.R k a b' /\ b = PSuc b'.
Proof.
  move E : (PSuc a) => u hu.
  move : a E.
  elim : u b /hu.
  - hauto l:on.
  - scrush ctrs:nsteps inv:LoRed.R.
Qed.

Lemma lored_nsteps_abs_inv k n (a : PTm (S n)) b :
  nsteps LoRed.R k (PAbs a) b -> exists b', nsteps LoRed.R k a b' /\ b = PAbs b'.
Proof.
  move E : (PAbs a) => u hu.
  move : a E.
  elim : u b /hu.
  - hauto l:on.
  - scrush ctrs:nsteps inv:LoRed.R.
Qed.

Lemma lored_hne_preservation n (a b : PTm n) :
    LoRed.R a b -> ishne a -> ishne b.
Proof.  induction 1; sfirstorder. Qed.

Lemma loreds_hne_preservation n (a b : PTm n) :
  rtc LoRed.R a b -> ishne a -> ishne b.
Proof. induction 1; hauto lq:on ctrs:rtc use:lored_hne_preservation. Qed.

Lemma lored_nsteps_bind_inv k n p (a0 : PTm n) b0 C :
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

Lemma lored_nsteps_app_inv k n (a0 b0 C : PTm n) :
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

Lemma lored_nsteps_proj_inv k n p (a0 C : PTm n) :
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

Lemma algo_metric_proj n k p0 p1 (a0 a1 : PTm n) :
  algo_metric k (PProj p0 a0) (PProj p1 a1) ->
  ishne a0 ->
  ishne a1 ->
  p0 = p1 /\ exists j, j < k /\ algo_metric j a0 a1.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3][h4]h5 hne0 hne1.
  move : lored_nsteps_proj_inv h0 (hne0);repeat move/[apply].
  move => [i0][a2][hi][?]ha02. subst.
  move : lored_nsteps_proj_inv h1 (hne1);repeat move/[apply].
  move => [i1][a3][hj][?]ha13. subst.
  simpl in *.
  move /EJoin.hne_proj_inj : h4 => [h40 h41]. subst.
  split => //.
  exists (k - 1). split. simpl in *; lia.
  rewrite/algo_metric.
  do 4 eexists. repeat split; eauto. sfirstorder use:ne_nf.
  sfirstorder use:ne_nf.
  lia.
Qed.

Lemma lored_nsteps_app_cong k n (a0 a1 b : PTm n) :
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

Lemma lored_nsteps_proj_cong k n p (a0 a1 : PTm n) :
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

Lemma lored_nsteps_pair_inv k n (a0 b0 C : PTm n) :
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

Lemma algo_metric_join n k (a b : PTm n) :
  algo_metric k a b ->
  DJoin.R a b.
  rewrite /algo_metric.
  move => [i][j][va][vb][h0][h1][h2][h3][[v [h40 h41]]]h5.
  have {}h0 : rtc LoRed.R a va by hauto lq:on use:@relations.rtc_nsteps.
  have {}h1 : rtc LoRed.R b vb by hauto lq:on use:@relations.rtc_nsteps.
  apply REReds.FromEReds in h40,h41.
  apply LoReds.ToRReds in h0,h1.
  apply REReds.FromRReds in h0,h1.
  rewrite /DJoin.R. exists v. sfirstorder use:@relations.rtc_transitive.
Qed.

Lemma algo_metric_pair n k (a0 b0 a1 b1 : PTm n) :
  SN (PPair a0 b0) ->
  SN (PPair a1 b1) ->
  algo_metric k (PPair a0 b0) (PPair a1 b1) ->
  exists j, j < k /\ algo_metric j a0 a1 /\ algo_metric j b0 b1.
  move => sn0 sn1 /[dup] /algo_metric_join hj.
  move => [i][j][va][vb][h0][h1][h2][h3][h4]h5.
  move : lored_nsteps_pair_inv h0;repeat move/[apply].
  move => [i0][i1][a2][b2][?][?][?][ha02]hb02. subst.
  move : lored_nsteps_pair_inv h1;repeat move/[apply].
  move => [j0][j1][a3][b3][?][?][?][ha13]hb13. subst.
  simpl in *. exists (k - 1).
  move /andP : h2 => [h20 h21].
  move /andP : h3 => [h30 h31].
  suff : EJoin.R a2 a3 /\ EJoin.R b2 b3 by hauto lq:on solve+:lia.
  hauto l:on use:DJoin.ejoin_pair_inj.
Qed.

Lemma hne_nf_ne n (a : PTm n) :
  ishne a -> nf a -> ne a.
Proof. case : a => //=. Qed.

Lemma lored_nsteps_renaming k n m (a b : PTm n) (ξ : fin n -> fin m) :
  nsteps LoRed.R k a b ->
  nsteps LoRed.R k (ren_PTm ξ a) (ren_PTm ξ b).
Proof.
  induction 1; hauto lq:on ctrs:nsteps use:LoRed.renaming.
Qed.

Lemma algo_metric_neu_abs n k (a0 : PTm (S n)) u :
  algo_metric k u (PAbs a0) ->
  ishne u ->
  exists j, j < k /\ algo_metric j (PApp (ren_PTm shift u) (VarPTm var_zero)) a0.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3][h4]h5 neu.
  have neva : ne va by hauto lq:on use:hne_nf_ne, loreds_hne_preservation, @relations.rtc_nsteps.
  move /lored_nsteps_abs_inv : h1 => [a1][h01]?. subst.
  exists (k - 1). simpl in *. split. lia.
  have {}h0 : nsteps LoRed.R i (ren_PTm shift u) (ren_PTm shift va)
    by eauto using lored_nsteps_renaming.
  have {}h0 : nsteps LoRed.R i (PApp (ren_PTm shift u) (VarPTm var_zero)) (PApp (ren_PTm shift va) (VarPTm var_zero)).
  apply lored_nsteps_app_cong => //=.
  scongruence use:ishne_ren.
  do 4 eexists. repeat split; eauto.
  hauto b:on use:ne_nf_ren.
  have h : EJoin.R (PAbs (PApp (ren_PTm shift va) (VarPTm var_zero))) (PAbs a1) by hauto q:on ctrs:rtc,ERed.R.
  apply DJoin.ejoin_abs_inj; eauto.
  hauto b:on drew:off use:ne_nf_ren.
  simpl in *.  rewrite size_PTm_ren. lia.
Qed.

Lemma algo_metric_neu_pair n k (a0 b0 : PTm n) u :
  algo_metric k u (PPair a0 b0) ->
  ishne u ->
  exists j, j < k /\ algo_metric j (PProj PL u) a0 /\ algo_metric j (PProj PR u) b0.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3][h4]h5 neu.
  move /lored_nsteps_pair_inv : h1.
  move => [i0][j0][a1][b1][hi][hj][?][ha01]hb01. subst.
  simpl in *.
  have ? : ishne va by
    hauto lq:on use:loreds_hne_preservation, @relations.rtc_nsteps.
  have ? : ne va by sfirstorder use:hne_nf_ne.
  exists (k - 1). split. lia.
  move :lored_nsteps_proj_cong (neu) h0; repeat move/[apply].
  move => h. have hL := h PL. have {h} hR := h PR.
  suff [? ?] : EJoin.R (PProj PL va) a1  /\ EJoin.R (PProj PR va) b1.
  rewrite /algo_metric.
  split; do 4 eexists; repeat split;eauto; sfirstorder b:on solve+:lia.
  eapply DJoin.ejoin_pair_inj; hauto qb:on ctrs:rtc, ERed.R.
Qed.

Lemma algo_metric_app n k (a0 b0 a1 b1 : PTm n) :
  algo_metric k (PApp a0 b0) (PApp a1 b1) ->
  ishne a0 ->
  ishne a1 ->
  exists j, j < k /\ algo_metric j a0 a1 /\ algo_metric j b0 b1.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3][h4]h5.
  move => hne0 hne1.
  move : lored_nsteps_app_inv h0 (hne0);repeat move/[apply].
  move => [i0][i1][a2][b2][?][?][?][ha02]hb02. subst.
  move : lored_nsteps_app_inv h1 (hne1);repeat move/[apply].
  move => [j0][j1][a3][b3][?][?][?][ha13]hb13. subst.
  simpl in *. exists (k - 1).
  move /andP : h2 => [h20 h21].
  move /andP : h3 => [h30 h31].
  move /EJoin.hne_app_inj : h4 => [h40 h41].
  split. lia.
  split.
  + rewrite /algo_metric.
    exists i0,j0,a2,a3.
    repeat split => //=.
    sfirstorder b:on use:ne_nf.
    sfirstorder b:on use:ne_nf.
    lia.
  + rewrite /algo_metric.
    exists i1,j1,b2,b3.
    repeat split => //=; sfirstorder b:on use:ne_nf.
Qed.

Lemma algo_metric_suc n k (a0 a1 : PTm n) :
  algo_metric k (PSuc a0) (PSuc a1) ->
  exists j, j < k /\ algo_metric j a0 a1.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3][h4]h5.
  exists (k - 1).
  move /lored_nsteps_suc_inv : h0.
  move => [a0'][ha0]?. subst.
  move /lored_nsteps_suc_inv : h1.
  move => [b0'][hb0]?. subst. simpl in *.
  split; first by lia.
  rewrite /algo_metric.
  hauto lq:on rew:off use:EJoin.suc_inj solve+:lia.
Qed.

Lemma algo_metric_bind n k p0 (A0 : PTm n) B0 p1 A1 B1  :
  algo_metric k (PBind p0 A0 B0) (PBind p1 A1 B1) ->
  p0 = p1 /\ exists j, j < k /\ algo_metric j A0 A1 /\ algo_metric j B0 B1.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3][h4]h5.
  move : lored_nsteps_bind_inv h0 => /[apply].
  move => [i0][i1][a2][b2][?][?][?][ha02]hb02. subst.
  move : lored_nsteps_bind_inv h1 => /[apply].
  move => [j0][j1][a3][b3][?][?][?][ha13]hb13. subst.
  move /EJoin.bind_inj : h4 => [?][hEa]hEb. subst.
  split => //.
  exists (k - 1). split. simpl in *; lia.
  simpl in *.
  split.
  - exists i0,j0,a2,a3.
    repeat split => //=; sfirstorder b:on solve+:lia.
  - exists i1,j1,b2,b3. sfirstorder b:on solve+:lia.
Qed.


Lemma coqeq_complete' n k (a b : PTm n) :
  algo_metric k a b ->
  (forall Γ A, Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> a ⇔ b) /\
  (forall Γ A B, ishne a -> ishne b -> Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ exists C, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ∈ C /\ Γ ⊢ b ∈ C).
Proof.
  move : k n a b.
  elim /Wf_nat.lt_wf_ind.
  move => n ih.
  move => k a b /[dup] h /algo_metric_case. move : k a b h => [:hstepL].
  move => k a b h.
  (* Cases where a and b can take steps *)
  case; cycle 1.
  move : k a b h.
  abstract : hstepL. qauto l:on use:HRed.preservation, CE_HRedL, hred_hne.
  move  /algo_metric_sym /algo_metric_case : (h).
  case; cycle 1.
  move {ih}. move /algo_metric_sym : h.
  move : hstepL => /[apply].
  hauto lq:on use:coqeq_symmetric_mutual, algo_metric_sym.
  (* Cases where a and b can't take wh steps *)
  move {hstepL}.
  move : k a b h. move => [:hnfneu].
  move => k a b h.
  case => fb; case => fa.
  - split; last by sfirstorder use:hf_not_hne.
    move {hnfneu}.
    case : a h fb fa => //=.
    + case : b => //=; try qauto depth:1 use:T_AbsPair_Imp, T_AbsBind_Imp, T_AbsUniv_Imp, T_AbsZero_Imp, T_AbsSuc_Imp, T_AbsNat_Imp.
      move => a0 a1 ha0 _ _ Γ A wt0 wt1.
      move : T_Abs_Inv wt0 wt1; repeat move/[apply]. move  => [Δ [V [wt1 wt0]]].
      apply : CE_HRed; eauto using rtc_refl.
      apply CE_AbsAbs.
      suff [l [h0 h1]] : exists l, l < n /\ algo_metric l a1 a0 by eapply ih; eauto.
      have ? : n > 0 by sauto solve+:lia.
      exists (n - 1). split; first by lia.
      move : (ha0). rewrite /algo_metric.
      move => [i][j][va][vb][hr0][hr1][nfva][nfvb][[v [hr0' hr1']]] har.
      apply lored_nsteps_abs_inv in hr0, hr1.
      move : hr0 => [va' [hr00 hr01]].
      move : hr1 => [vb' [hr10 hr11]]. move {ih}.
      exists i,j,va',vb'. subst.
      suff [v0 [hv00 hv01]] : exists v0, rtc ERed.R va' v0 /\ rtc ERed.R vb' v0.
      repeat split =>//=. sfirstorder.
      simpl in *; by lia.
      move /algo_metric_join /DJoin.symmetric : ha0.
      have : SN a0 /\ SN a1 by qauto l:on use:fundamental_theorem, logrel.SemWt_SN.
      move => /[dup] [[ha00 ha10]] [].
      move : DJoin.abs_inj; repeat move/[apply].
      move : DJoin.standardization ha00 ha10; repeat move/[apply].
      (* this is awful *)
      move => [vb][va][h' [h'' [h''' [h'''' h'''''']]]].
      have /LoReds.ToRReds {}hr00 : rtc LoRed.R a1 va'
        by hauto lq:on use:@relations.rtc_nsteps.
      have /LoReds.ToRReds {}hr10 : rtc LoRed.R a0 vb'
        by hauto lq:on use:@relations.rtc_nsteps.
      simpl in *.
      have [*] : va' = va /\ vb' = vb by eauto using red_uniquenf. subst.
      sfirstorder.
    + case : b => //=; try qauto depth:1 use:T_AbsPair_Imp, T_PairBind_Imp, T_PairUniv_Imp, T_PairNat_Imp, T_PairSuc_Imp, T_PairZero_Imp.
      move => a1 b1 a0 b0 h _ _ Γ A hu0 hu1.
      have [sn0 sn1] : SN (PPair a0 b0) /\ SN (PPair a1 b1)
        by qauto l:on use:fundamental_theorem, logrel.SemWt_SN.
      apply : CE_HRed; eauto using rtc_refl.
      move /Pair_Inv : hu0 => [A0][B0][ha0][hb0]hSu0.
      move /Pair_Inv : hu1 => [A1][B1][ha1][hb1]hSu1.
      move /Sub_Bind_InvR :  (hSu0).
      move => [i][A2][B2]hE.
      have hSu12 : Γ ⊢ PBind PSig A1 B1 ≲ PBind PSig A2 B2
        by eauto using Su_Transitive, Su_Eq.
      have hSu02 : Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A2 B2
        by eauto using Su_Transitive, Su_Eq.
      have hA02 : Γ ⊢ A0 ≲ A2 by eauto using Su_Sig_Proj1.
      have hA12 : Γ ⊢ A1 ≲ A2 by eauto using Su_Sig_Proj1.
      have ha0A2 : Γ ⊢ a0 ∈ A2 by eauto using T_Conv.
      have ha1A2 : Γ ⊢ a1 ∈ A2 by eauto using T_Conv.
      move /algo_metric_pair : h sn0 sn1; repeat move/[apply].
      move => [j][hj][ih0 ih1].
      have haE : a0 ⇔ a1 by hauto l:on.
      apply CE_PairPair => //.
      have {}haE : Γ ⊢ a0 ≡ a1 ∈ A2
        by hauto l:on use:coqeq_sound_mutual.
      have {}hb1 : Γ ⊢ b1 ∈ subst_PTm (scons a1 VarPTm) B2.
      apply : T_Conv; eauto.
      move /E_Refl in ha1. hauto l:on use:Su_Sig_Proj2.
      eapply ih; cycle -1; eauto.
      apply : T_Conv; eauto.
      apply Su_Transitive with (B := subst_PTm (scons a0 VarPTm) B2).
      move /E_Refl in ha0. hauto l:on use:Su_Sig_Proj2.
      move : hE haE. clear.
      move => h.
      eapply regularity in h.
      move : h => [_ [hB _]].
      eauto using bind_inst.
    + case : b => //=.
      * hauto lq:on use:T_AbsBind_Imp.
      * hauto lq:on rew:off use:T_PairBind_Imp.
      * move => p1 A1 B1 p0 A0 B0.
        move /algo_metric_bind.
        move => [?][j [ih0 [ih1 ih2]]]_ _. subst.
        move => Γ A hU0 hU1.
        move /Bind_Inv : hU0 => [i0 [hA0 [hB0 hS0]]].
        move /Bind_Inv : hU1 => [i1 [hA1 [hB1 hS1]]].
        have ? : Γ ⊢ PUniv i0 ≲ PUniv (max i0 i1)
          by hauto lq:on rew:off use:Su_Univ, wff_mutual solve+:lia.
        have ? : Γ ⊢ PUniv i1 ≲ PUniv (max i0 i1)
          by hauto lq:on rew:off use:Su_Univ, wff_mutual solve+:lia.
        have {}hA0 : Γ ⊢ A0 ∈ PUniv (max i0 i1) by eauto using T_Conv.
        have {}hA1 : Γ ⊢ A1 ∈ PUniv (max i0 i1) by eauto using T_Conv.
        have {}hB0 : funcomp (ren_PTm shift) (scons A0 Γ) ⊢
                       B0 ∈ PUniv (max i0 i1)
          by hauto lq:on use:T_Univ_Raise solve+:lia.
        have {}hB1 : funcomp (ren_PTm shift) (scons A1 Γ) ⊢
                       B1 ∈ PUniv (max i0 i1)
          by hauto lq:on use:T_Univ_Raise solve+:lia.

        have ihA : A0 ⇔ A1 by hauto l:on.
        have hAE : Γ ⊢ A0 ≡ A1 ∈ PUniv (Nat.max i0 i1)
          by hauto l:on use:coqeq_sound_mutual.
        apply : CE_HRed; eauto using rtc_refl.
        constructor => //.

        eapply ih; eauto.
        apply : ctx_eq_subst_one; eauto.
        eauto using Su_Eq.
      * move => > /algo_metric_join.
        hauto lq:on use:DJoin.bind_univ_noconf.
      * move => > /algo_metric_join.
        hauto lq:on use:Sub.nat_bind_noconf, Sub.FromJoin.
      * move => > /algo_metric_join.
        clear. hauto lq:on rew:off use:REReds.bind_inv, REReds.zero_inv.
      * move => > /algo_metric_join. clear.
        hauto lq:on rew:off use:REReds.bind_inv, REReds.suc_inv.
    + case : b => //=.
      * hauto lq:on use:T_AbsUniv_Imp.
      * hauto lq:on use:T_PairUniv_Imp.
      * qauto l:on use:algo_metric_join, DJoin.bind_univ_noconf, DJoin.symmetric.
      * move => i j /algo_metric_join /DJoin.univ_inj ? _ _ Γ A hi hj.
        subst.
        hauto l:on.
      * move => > /algo_metric_join.
        hauto lq:on use:Sub.nat_univ_noconf, Sub.FromJoin.
      * move => > /algo_metric_join.
        clear. hauto lq:on rew:off use:REReds.univ_inv, REReds.zero_inv.
      * move => > /algo_metric_join.
        clear. hauto lq:on rew:off use:REReds.univ_inv, REReds.suc_inv.
    + case : b => //=.
      * qauto l:on use:T_AbsNat_Imp.
      * qauto l:on use:T_PairNat_Imp.
      * move => > /algo_metric_join /Sub.FromJoin. hauto l:on use:Sub.bind_nat_noconf.
      * move => > /algo_metric_join /Sub.FromJoin. hauto lq:on use:Sub.univ_nat_noconf.
      * hauto l:on.
      * move /algo_metric_join.
        hauto lq:on rew:off use:REReds.nat_inv, REReds.zero_inv.
      * move => > /algo_metric_join.
        hauto lq:on rew:off use:REReds.nat_inv, REReds.suc_inv.
    (* Zero *)
    + case : b => //=.
      * hauto lq:on rew:off use:T_AbsZero_Imp.
      * hauto lq: on use: T_PairZero_Imp.
      * move =>> /algo_metric_join.
        hauto lq:on rew:off use:REReds.zero_inv, REReds.bind_inv.
      * move =>> /algo_metric_join.
        hauto lq:on rew:off use:REReds.zero_inv, REReds.univ_inv.
      * move =>> /algo_metric_join.
        hauto lq:on rew:off use:REReds.zero_inv, REReds.nat_inv.
      * hauto l:on.
      * move =>> /algo_metric_join.
        hauto lq:on rew:off use:REReds.zero_inv, REReds.suc_inv.
    (* Suc *)
    + case : b => //=.
      * hauto lq:on rew:off use:T_AbsSuc_Imp.
      * hauto lq:on use:T_PairSuc_Imp.
      * move => > /algo_metric_join.
        hauto lq:on rew:off use:REReds.suc_inv, REReds.bind_inv.
      * move => > /algo_metric_join.
        hauto lq:on rew:off use:REReds.suc_inv, REReds.univ_inv.
      * move => > /algo_metric_join.
        hauto lq:on rew:off use:REReds.suc_inv, REReds.nat_inv.
      * move => > /algo_metric_join.
        hauto lq:on rew:off use:REReds.suc_inv, REReds.zero_inv.
      * move => a0 a1 h _ _.
        move /algo_metric_suc : h => [j [h4 h5]].
        move => Γ A /Suc_Inv [h0 h1] /Suc_Inv [h2 h3].
        move : ih h4 h5;do!move/[apply].
        move => [ih _].
        move : ih h0 h2;do!move/[apply].
        move => h. apply : CE_HRed; eauto using rtc_refl.
        by constructor.
  - move : k a b h fb fa. abstract : hnfneu.
    move => k.
    move => + b.
    case : b => //=.
    (* NeuAbs *)
    + move => a u halg _ nea. split => // Γ A hu /[dup] ha.
      move /Abs_Inv => [A0][B0][_]hSu.
      move /Sub_Bind_InvR : (hSu) => [i][A2][B2]hE.
      have {}hu : Γ ⊢ u ∈ PBind PPi A2 B2 by eauto using T_Conv_E.
      have {}ha : Γ ⊢ PAbs a ∈ PBind PPi A2 B2 by eauto using T_Conv_E.
      have {}hE : Γ ⊢ PBind PPi A2 B2 ∈ PUniv i
        by hauto l:on use:regularity.
      have {i} [j {}hE] : exists j, Γ ⊢ A2 ∈ PUniv j
          by qauto l:on use:Bind_Inv.
      have hΓ : ⊢ funcomp (ren_PTm shift) (scons A2 Γ) by eauto using Wff_Cons'.
      set Δ := funcomp _ _ in hΓ.
      have {}hu : Δ ⊢ PApp (ren_PTm shift u) (VarPTm var_zero) ∈ B2.
      apply : T_App'; cycle 1. apply : weakening_wt' => //=; eauto.
      reflexivity.
      rewrite -/ren_PTm.
      by apply T_Var.
      rewrite -/ren_PTm. by asimpl.
      move /Abs_Pi_Inv in ha.
      move /algo_metric_neu_abs /(_ nea) : halg.
      move => [j0][hj0]halg.
      apply : CE_HRed; eauto using rtc_refl.
      eapply CE_NeuAbs => //=.
      eapply ih; eauto.
    (* NeuPair *)
    + move => a0 b0 u halg _ neu.
      split => // Γ A hu /[dup] wt.
      move /Pair_Inv => [A0][B0][ha0][hb0]hU.
      move /Sub_Bind_InvR : (hU) => [i][A2][B2]hE.
      have {}wt : Γ ⊢ PPair a0 b0 ∈ PBind PSig A2 B2 by sauto lq:on.
      have {}hu : Γ ⊢ u ∈ PBind PSig A2 B2 by eauto using T_Conv_E.
      move /Pair_Sig_Inv : wt => [{}ha0 {}hb0].
      have /T_Proj1 huL := hu.
      have /T_Proj2 {hu} huR := hu.
      move /algo_metric_neu_pair /(_ neu) : halg => [j [hj [hL hR]]].
      have heL : PProj PL u ⇔ a0 by hauto l:on.
      eapply CE_HRed; eauto using rtc_refl.
      apply CE_NeuPair; eauto.
      eapply ih; eauto.
      apply : T_Conv; eauto.
      have {}hE : Γ ⊢ PBind PSig A2 B2 ∈ PUniv i
        by hauto l:on use:regularity.
      have /E_Symmetric : Γ ⊢ PProj PL u  ≡ a0 ∈ A2 by
        hauto l:on use:coqeq_sound_mutual.
      hauto l:on use:bind_inst.
    (* NeuBind: Impossible *)
    + move => b p p0 a /algo_metric_join h _ h0. exfalso.
      move : h h0. clear.
      move /Sub.FromJoin.
      hauto l:on use:Sub.hne_bind_noconf.
    (* NeuUniv: Impossible *)
    + hauto lq:on rew:off use:DJoin.hne_univ_noconf, algo_metric_join.
    + hauto lq:on rew:off use:DJoin.hne_nat_noconf, algo_metric_join.
    (* Zero *)
    + case => //=.
      * move => i /algo_metric_join. clear.
        hauto lq:on rew:off use:REReds.var_inv, REReds.zero_inv.
      * move => >/algo_metric_join. clear.
        hauto lq:on rew:off use:REReds.hne_app_inv, REReds.zero_inv.
      * move => >/algo_metric_join. clear.
        hauto lq:on rew:off use:REReds.hne_proj_inv, REReds.zero_inv.
      * sfirstorder use:T_Bot_Imp.
      * move => >/algo_metric_join. clear.
        move => h _ h2. exfalso.
        hauto q:on use:REReds.hne_ind_inv, REReds.zero_inv.
    (* Suc *)
    + move => a0.
      case => //=; move => >/algo_metric_join; clear.
      * hauto lq:on rew:off use:REReds.var_inv, REReds.suc_inv.
      * hauto lq:on rew:off use:REReds.hne_app_inv, REReds.suc_inv.
      * hauto lq:on rew:off use:REReds.hne_proj_inv, REReds.suc_inv.
      *
  - move {ih}.
    move /algo_metric_sym in h.
    qauto l:on use:coqeq_symmetric_mutual.
  - move {hnfneu}.

    (* Clear out some trivial cases *)
    suff : (forall (Γ : fin k -> PTm k) (A B : PTm k), Γ ⊢ a ∈ A -> Γ ⊢ b ∈ B -> a ∼ b /\ (exists C : PTm k, Γ ⊢ C ≲ A /\ Γ ⊢ C ≲ B /\ Γ ⊢ a ∈ C /\ Γ ⊢ b ∈ C)).
    move => h0.
    split. move => *. apply : CE_HRed; eauto using rtc_refl. apply CE_NeuNeu. by firstorder.
    by firstorder.

    case : a h fb fa => //=.
    + case : b => //=.
      move => i j hi _ _.
      * have ? : j = i by hauto lq:on use:algo_metric_join, DJoin.var_inj. subst.
        move => Γ A B hA hB.
        split. apply CE_VarCong.
        exists (Γ i). hauto l:on use:Var_Inv, T_Var.
      * move => p p0 f /algo_metric_join. clear => ? ? _. exfalso.
        hauto l:on use:REReds.var_inv, REReds.hne_app_inv.
      * move => a0 a1 i /algo_metric_join. clear => ? ? _. exfalso.
        hauto l:on use:REReds.var_inv, REReds.hne_proj_inv.
      * sfirstorder use:T_Bot_Imp.
      * admit.
    + case : b => //=.
      * clear. move => i a a0 /algo_metric_join h _ ?. exfalso.
        hauto l:on use:REReds.hne_app_inv, REReds.var_inv.
      (* real case *)
      * move => b1 a1 b0 a0 halg hne1 hne0 Γ A B wtA wtB.
        move /App_Inv : wtA => [A0][B0][hb0][ha0]hS0.
        move /App_Inv : wtB => [A1][B1][hb1][ha1]hS1.
        move : algo_metric_app (hne0) (hne1) halg. repeat move/[apply].
        move => [j [hj [hal0 hal1]]].
        have /ih := hal0.
        move /(_ hj).
        move => [_ ihb].
        move : ihb (hne0) (hne1) hb0 hb1. repeat move/[apply].
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
        move : ih (hj) hal1. repeat move/[apply].
        move => [ih _].
        move : ih (ha0') (ha1'); repeat move/[apply].
        move => iha.
        split. qblast.
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
      * move => p p0 p1 p2 /algo_metric_join. clear => ? ? ?. exfalso.
        hauto q:on use:REReds.hne_app_inv, REReds.hne_proj_inv.
      * sfirstorder use:T_Bot_Imp.
      * admit.
    + case : b => //=.
      * move => i p h /algo_metric_join. clear => ? _ ?. exfalso.
        hauto l:on use:REReds.hne_proj_inv, REReds.var_inv.
      * move => > /algo_metric_join. clear => ? ? ?. exfalso.
        hauto l:on use:REReds.hne_proj_inv, REReds.hne_app_inv.
      (* real case *)
      * move => p1 a1 p0 a0 /algo_metric_proj ha hne1 hne0.
        move : ha (hne0) (hne1); repeat move/[apply].
        move => [? [j []]]. subst.
        move : ih; repeat move/[apply].
        move => [_ ih].
        case : p1.
        ** move => Γ A B ha0 ha1.
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
        ** move => Γ A B  ha0  ha1.
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
      * sfirstorder use:T_Bot_Imp.
      * admit.
    + sfirstorder use:T_Bot_Imp.
    (* ind ind case *)
    + admit.
Admitted.

Lemma coqeq_sound : forall n Γ (a b : PTm n) A,
    Γ ⊢ a ∈ A -> Γ ⊢ b ∈ A -> a ⇔ b -> Γ ⊢ a ≡ b ∈ A.
Proof. sfirstorder use:coqeq_sound_mutual. Qed.

Lemma coqeq_complete n Γ (a b A : PTm n) :
  Γ ⊢ a ≡ b ∈ A -> a ⇔ b.
Proof.
  move => h.
  suff : exists k, algo_metric k a b by hauto lq:on use:coqeq_complete', regularity.
  eapply fundamental_theorem in h.
  move /logrel.SemEq_SN_Join : h.
  move => h.
  have : exists va vb : PTm n,
         rtc LoRed.R a va /\
         rtc LoRed.R b vb /\ nf va /\ nf vb /\ EJoin.R va vb
      by hauto l:on use:DJoin.standardization_lo.
  move => [va][vb][hva][hvb][nva][nvb]hj.
  move /relations.rtc_nsteps : hva => [i hva].
  move /relations.rtc_nsteps : hvb => [j hvb].
  exists (i + j + size_PTm va + size_PTm vb).
  hauto lq:on solve+:lia.
Qed.


Reserved Notation "a ≪ b" (at level 70).
Reserved Notation "a ⋖ b" (at level 70).
Inductive CoqLEq {n} : PTm n -> PTm n -> Prop :=
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

| CLE_NeuNeu a0 a1 :
  a0 ∼ a1 ->
  a0 ⋖ a1

with CoqLEq_R {n} : PTm n -> PTm n -> Prop :=
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

Definition salgo_metric {n} k (a b : PTm n) :=
  exists i j va vb, nsteps LoRed.R i a va /\ nsteps LoRed.R j b vb /\ nf va /\ nf vb /\ ESub.R va vb /\ size_PTm va + size_PTm vb + i + j <= k.

Lemma salgo_metric_algo_metric n k (a b : PTm n) :
  ishne a \/ ishne b ->
  salgo_metric k a b ->
  algo_metric k a b.
Proof.
  move => h.
  move => [i][j][va][vb][hva][hvb][nva][nvb][hS]sz.
  rewrite/ESub.R in hS.
  move : hS => [va'][vb'][h0][h1]h2.
  suff : va' = vb' by sauto lq:on.
  have {}hva : rtc RERed.R a va by hauto lq:on use:@relations.rtc_nsteps, REReds.FromRReds, LoReds.ToRReds.
  have {}hvb : rtc RERed.R b vb by hauto lq:on use:@relations.rtc_nsteps, REReds.FromRReds, LoReds.ToRReds.
  apply REReds.FromEReds in h0, h1.
  have : ishne va' \/ ishne vb' by
    hauto lq:on rew:off use:@relations.rtc_transitive, REReds.hne_preservation.
  hauto lq:on use:Sub1.hne_refl.
Qed.

Lemma coqleq_sound_mutual : forall n,
    (forall (a b : PTm n), a ⋖ b -> forall Γ i, Γ ⊢ a ∈ PUniv i -> Γ ⊢ b ∈ PUniv i -> Γ ⊢ a ≲ b ) /\
    (forall (a b : PTm n), a ≪ b -> forall Γ i, Γ ⊢ a ∈ PUniv i -> Γ ⊢ b ∈ PUniv i -> Γ ⊢ a ≲ b ).
Proof.
  apply coqleq_mutual.
  - hauto lq:on use:wff_mutual ctrs:LEq.
  - move => n A0 A1 B0 B1 hA ihA hB ihB Γ i.
    move /Bind_Univ_Inv => [hA0]hB0 /Bind_Univ_Inv [hA1]hB1.
    have hlA  : Γ ⊢ A1 ≲ A0 by sfirstorder.
    have hΓ : ⊢ Γ by sfirstorder use:wff_mutual.
    apply Su_Transitive with (B := PBind PPi A1 B0).
    by apply : Su_Pi; eauto using E_Refl, Su_Eq.
    apply : Su_Pi; eauto using E_Refl, Su_Eq.
    apply : ihB; eauto using ctx_eq_subst_one.
  - move => n A0 A1 B0 B1 hA ihA hB ihB Γ i.
    move /Bind_Univ_Inv => [hA0]hB0 /Bind_Univ_Inv [hA1]hB1.
    have hlA  : Γ ⊢ A0 ≲ A1 by sfirstorder.
    have hΓ : ⊢ Γ by sfirstorder use:wff_mutual.
    apply Su_Transitive with (B := PBind PSig A0 B1).
    apply : Su_Sig; eauto using E_Refl, Su_Eq.
    apply : ihB; by eauto using ctx_eq_subst_one.
    apply : Su_Sig; eauto using E_Refl, Su_Eq.
  - sauto lq:on use:coqeq_sound_mutual, Su_Eq.
  - move => n a a' b b' ? ? ? ih Γ i ha hb.
    have /Su_Eq ? : Γ ⊢ a ≡ a' ∈ PUniv i by sfirstorder use:HReds.ToEq.
    have /E_Symmetric /Su_Eq ? : Γ ⊢ b ≡ b' ∈ PUniv i by sfirstorder use:HReds.ToEq.
    suff : Γ ⊢ a' ≲ b' by eauto using Su_Transitive.
    eauto using HReds.preservation.
Qed.

Lemma salgo_metric_case n k (a b : PTm n) :
  salgo_metric k a b ->
  (ishf a \/ ishne a) \/ exists k' a', HRed.R a a' /\ salgo_metric k' a' b /\ k' < k.
Proof.
  move=>[i][j][va][vb][h0] [h1][h2][h3][[v [h4 h5]]] h6.
  case : a h0 => //=; try firstorder.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.AppAbs unfold:algo_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia.
    + sfirstorder qb:on use:ne_hne.
  - inversion h0 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.ProjPair unfold:algo_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia.
      (* Copy paste from algo_metric_case *)
Admitted.

Lemma CLE_HRedL n (a a' b : PTm n)  :
  HRed.R a a' ->
  a' ≪ b ->
  a ≪ b.
Proof.
  hauto lq:on ctrs:rtc, CoqLEq_R inv:CoqLEq_R.
Qed.

Lemma CLE_HRedR n (a a' b : PTm n)  :
  HRed.R a a' ->
  b ≪ a' ->
  b ≪ a.
Proof.
  hauto lq:on ctrs:rtc, CoqLEq_R inv:CoqLEq_R.
Qed.


Lemma algo_metric_caseR n k (a b : PTm n) :
  salgo_metric k a b ->
  (ishf b \/ ishne b) \/ exists k' b', HRed.R b b' /\ salgo_metric k' a b' /\ k' < k.
Proof.
  move=>[i][j][va][vb][h0] [h1][h2][h3][[v [h4 h5]]] h6.
  case : b h1 => //=; try by firstorder.
  - inversion 1 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto q:on use:HRed.AppAbs unfold:salgo_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:salgo_metric solve+:lia.
    + sfirstorder qb:on use:ne_hne.
  - inversion 1 as [|A B C D E F]; subst.
    hauto qb:on use:ne_hne.
    inversion E; subst => /=.
    + hauto lq:on use:HRed.ProjPair unfold:algo_metric solve+:lia.
    + hauto q:on ctrs:HRed.R use: hf_hred_lored unfold:algo_metric solve+:lia.
Admitted.

Lemma salgo_metric_sub n k (a b : PTm n) :
  salgo_metric k a b ->
  Sub.R a b.
Proof.
  rewrite /algo_metric.
  move => [i][j][va][vb][h0][h1][h2][h3][[va' [vb' [hva [hvb hS]]]]]h5.
  have {}h0 : rtc LoRed.R a va by hauto lq:on use:@relations.rtc_nsteps.
  have {}h1 : rtc LoRed.R b vb by hauto lq:on use:@relations.rtc_nsteps.
  apply REReds.FromEReds in hva,hvb.
  apply LoReds.ToRReds in h0,h1.
  apply REReds.FromRReds in h0,h1.
  rewrite /Sub.R. exists va', vb'. sfirstorder use:@relations.rtc_transitive.
Qed.

Lemma salgo_metric_pi n k (A0 : PTm n) B0 A1 B1  :
  salgo_metric k (PBind PPi A0 B0) (PBind PPi A1 B1) ->
  exists j, j < k /\ salgo_metric j A1 A0 /\ salgo_metric j B0 B1.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3][h4]h5.
  move : lored_nsteps_bind_inv h0 => /[apply].
  move => [i0][i1][a2][b2][?][?][?][ha02]hb02. subst.
  move : lored_nsteps_bind_inv h1 => /[apply].
  move => [j0][j1][a3][b3][?][?][?][ha13]hb13. subst.
  move /ESub.pi_inj : h4 => [? ?].
  hauto qb:on solve+:lia.
Qed.

Lemma salgo_metric_sig n k (A0 : PTm n) B0 A1 B1  :
  salgo_metric k (PBind PSig A0 B0) (PBind PSig A1 B1) ->
  exists j, j < k /\ salgo_metric j A0 A1 /\ salgo_metric j B0 B1.
Proof.
  move => [i][j][va][vb][h0][h1][h2][h3][h4]h5.
  move : lored_nsteps_bind_inv h0 => /[apply].
  move => [i0][i1][a2][b2][?][?][?][ha02]hb02. subst.
  move : lored_nsteps_bind_inv h1 => /[apply].
  move => [j0][j1][a3][b3][?][?][?][ha13]hb13. subst.
  move /ESub.sig_inj : h4 => [? ?].
  hauto qb:on solve+:lia.
Qed.

Lemma coqleq_complete' n k (a b : PTm n) :
  salgo_metric k a b -> (forall Γ i, Γ ⊢ a ∈ PUniv i -> Γ ⊢ b ∈ PUniv i -> a ≪ b).
Proof.
  move : k n a b.
  elim /Wf_nat.lt_wf_ind.
  move => n ih.
  move => k a b /[dup] h /salgo_metric_case.
  (* Cases where a and b can take steps *)
  case; cycle 1.
  move : k a b h.
  qauto l:on use:HRed.preservation, CLE_HRedL, hred_hne.
  case /algo_metric_caseR : (h); cycle 1.
  qauto l:on use:HRed.preservation, CLE_HRedR, hred_hne.
  (* Cases where neither a nor b can take steps *)
  case => fb; case => fa.
  - case : a fa h => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'.
    + case : b fb => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'.
      * move => p0 A0 B0 _ p1 A1 B1 _.
        move => h.
        have ? : p1 = p0 by
          hauto lq:on rew:off use:salgo_metric_sub, Sub.bind_inj.
        subst.
        case : p0 h => //=.
        ** move /salgo_metric_pi.
           move => [j [hj [hA hB]]] Γ i.
           move /Bind_Univ_Inv => [hA1 hB1] /Bind_Univ_Inv [hA0 hB0].
           have ihA : A0 ≪ A1 by hauto l:on.
           econstructor; eauto using E_Refl; constructor=> //.
           have ihA' : Γ ⊢ A0 ≲ A1 by hauto l:on use:coqleq_sound_mutual.
           suff : funcomp (ren_PTm shift) (scons A0 Γ) ⊢ B1 ∈ PUniv i
             by hauto l:on.
           eauto using ctx_eq_subst_one.
        ** move /salgo_metric_sig.
           move => [j [hj [hA hB]]] Γ i.
           move /Bind_Univ_Inv => [hA1 hB1] /Bind_Univ_Inv [hA0 hB0].
           have ihA : A1 ≪ A0 by hauto l:on.
           econstructor; eauto using E_Refl; constructor=> //.
           have ihA' : Γ ⊢ A1 ≲ A0 by hauto l:on use:coqleq_sound_mutual.
           suff : funcomp (ren_PTm shift) (scons A1 Γ) ⊢ B0 ∈ PUniv i
             by hauto l:on.
           eauto using ctx_eq_subst_one.
      * hauto lq:on use:salgo_metric_sub, Sub.bind_univ_noconf.
      * hauto lq:on use:salgo_metric_sub, Sub.nat_bind_noconf.
      * admit.
      * admit.
    + case : b fb => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'.
      * hauto lq:on use:salgo_metric_sub, Sub.univ_bind_noconf.
      * move => *. econstructor; eauto using rtc_refl.
        hauto lq:on use:salgo_metric_sub, Sub.univ_inj, CLE_UnivCong.
  (* Both cases are impossible *)
  - have {}h : DJoin.R a b by
       hauto lq:on use:salgo_metric_algo_metric, algo_metric_join.
    case : b fb h => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'.
    + hauto lq:on use:DJoin.hne_bind_noconf.
    + hauto lq:on use:DJoin.hne_univ_noconf.
  - have {}h : DJoin.R b a by
      hauto lq:on use:salgo_metric_algo_metric, algo_metric_join, DJoin.symmetric.
    case : a fa h => //=; try hauto depth:1 lq:on use:T_AbsUniv_Imp', T_PairUniv_Imp'.
    + hauto lq:on use:DJoin.hne_bind_noconf.
    + hauto lq:on use:DJoin.hne_univ_noconf.
  - move => Γ i ha hb.
    econstructor; eauto using rtc_refl.
    apply CLE_NeuNeu. move {ih}.
    have {}h : algo_metric n a b by
      hauto lq:on use:salgo_metric_algo_metric.
    eapply coqeq_complete'; eauto.
Qed.

Lemma coqleq_complete n Γ (a b : PTm n) :
  Γ ⊢ a ≲ b -> a ≪ b.
Proof.
  move => h.
  suff : exists k, salgo_metric k a b by hauto lq:on use:coqleq_complete', regularity.
  eapply fundamental_theorem in h.
  move /logrel.SemLEq_SN_Sub : h.
  move => h.
  have : exists va vb : PTm n,
         rtc LoRed.R a va /\
         rtc LoRed.R b vb /\ nf va /\ nf vb /\ ESub.R va vb
      by hauto l:on use:Sub.standardization_lo.
  move => [va][vb][hva][hvb][nva][nvb]hj.
  move /relations.rtc_nsteps : hva => [i hva].
  move /relations.rtc_nsteps : hvb => [j hvb].
  exists (i + j + size_PTm va + size_PTm vb).
  hauto lq:on solve+:lia.
Qed.

Lemma coqleq_sound : forall n Γ (a b : PTm n) i j,
    Γ ⊢ a ∈ PUniv i -> Γ ⊢ b ∈ PUniv j -> a ≪ b -> Γ ⊢ a ≲ b.
Proof.
  move => n Γ a b i j.
  have [*] : i <= i + j /\ j <= i + j by lia.
  have : Γ ⊢ a ∈ PUniv (i + j) /\ Γ ⊢ b ∈ PUniv (i + j)
    by sfirstorder use:T_Univ_Raise.
  sfirstorder use:coqleq_sound_mutual.
Qed.
