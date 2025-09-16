Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common typing structural.
From Hammer Require Import Tactics.
Require Import ssreflect.
Require Import Psatz.

Derive Inversion wff_inv with (forall Γ, ⊢ Γ) Sort Prop.

Lemma T_Abs Γ (a : PTm ) A B :
  (cons A Γ) ⊢ a ∈ B ->
  Γ ⊢ PAbs a ∈ PBind PPi A B.
Proof.
  move => ha.
  have [i hB] : exists i, (cons A Γ) ⊢ B ∈ PUniv i by sfirstorder use:regularity.
  have hΓ : ⊢  (cons A Γ) by sfirstorder use:wff_mutual.
  hauto lq:on rew:off inv:Wff use:T_Bind', typing.T_Abs.
Qed.


Lemma App_Inv Γ (b a : PTm) U :
  Γ ⊢ PApp b a ∈ U ->
  exists A B, Γ ⊢ b ∈ PBind PPi A B /\ Γ ⊢ a ∈ A /\ Γ ⊢ subst_PTm (scons a VarPTm) B ≲ U.
Proof.
  move E : (PApp b a) => u hu.
  move : b a E. elim : Γ u U / hu => //=.
  - move => Γ b a A B hb _ ha _ b0 a0 [*]. subst.
    exists A,B.
    repeat split => //=.
    have [i] : exists i, Γ ⊢ PBind PPi A B ∈  PUniv i by sfirstorder use:regularity.
    hauto lq:on use:bind_inst, E_Refl.
  - hauto lq:on rew:off ctrs:LEq.
Qed.


Lemma Abs_Inv Γ (a : PTm) U :
  Γ ⊢ PAbs a ∈ U ->
  exists A B, (cons A Γ) ⊢ a ∈ B /\ Γ ⊢ PBind PPi A B ≲ U.
Proof.
  move E : (PAbs a) => u hu.
  move : a E. elim : Γ u U / hu => //=.
  - move => Γ a A B i hP _ ha _ a0 [*]. subst.
    exists A, B. repeat split => //=.
    hauto lq:on use:E_Refl, Su_Eq.
  - hauto lq:on rew:off ctrs:LEq.
Qed.



Lemma E_AppAbs : forall (a : PTm) (b : PTm) Γ (A : PTm),
  Γ ⊢ PApp (PAbs a) b ∈ A -> Γ ⊢ PApp (PAbs a) b ≡ subst_PTm (scons b VarPTm) a ∈ A.
Proof.
  move => a b Γ A ha.
  move /App_Inv : ha.
  move => [A0][B0][ha][hb]hS.
  move /Abs_Inv : ha => [A1][B1][ha]hS0.
  have hb' := hb.
  move /E_Refl in hb.
  have hS1 : Γ ⊢ A0 ≲ A1 by sfirstorder use:Su_Pi_Proj1.
  have [i hPi] : exists i, Γ ⊢ PBind PPi A1 B1 ∈ PUniv i by sfirstorder use:regularity_sub0.
  move : Su_Pi_Proj2 hS0 hb; repeat move/[apply].
  move : hS => /[swap]. move : Su_Transitive. repeat move/[apply].
  move => h.
  apply : E_Conv; eauto.
  apply : E_AppAbs; eauto.
  eauto using T_Conv.
Qed.

Lemma T_Eta Γ A a B :
  A :: Γ ⊢ a ∈ B ->
  A :: Γ ⊢ PApp (PAbs (ren_PTm (upRen_PTm_PTm shift) a)) (VarPTm var_zero) ∈ B.
Proof.
  move => ha.
  have hΓ' : ⊢ A :: Γ by sfirstorder use:wff_mutual.
  have [i hA] : exists i, Γ ⊢ A ∈ PUniv i by hauto lq:on inv:Wff.
  have hΓ : ⊢ Γ by hauto lq:on inv:Wff.
  eapply T_App' with (B  := ren_PTm (upRen_PTm_PTm shift) B). by asimpl; rewrite subst_scons_id.
  apply T_Abs. eapply renaming; eauto; cycle 1. apply renaming_up. apply renaming_shift.
  econstructor; eauto. sauto l:on use:renaming.
  apply T_Var => //.
  by constructor.
Qed.

Lemma E_Bind Γ i p (A0 A1 : PTm) B0 B1 :
  Γ ⊢ A0 ≡ A1 ∈ PUniv i ->
  (cons A0 Γ) ⊢ B0 ≡ B1 ∈ PUniv i ->
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i.
Proof.
  move => h0 h1.
  have : Γ ⊢ A0 ∈ PUniv i by hauto l:on use:regularity.
  have : ⊢ Γ by sfirstorder use:wff_mutual.
  move : E_Bind h0 h1; repeat move/[apply].
  firstorder.
Qed.

Lemma E_App Γ (b0 b1 a0 a1 : PTm ) A B :
  Γ ⊢ b0 ≡ b1 ∈ PBind PPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ PApp b0 a0 ≡ PApp b1 a1 ∈ subst_PTm (scons a0 VarPTm) B.
Proof.
  move => h.
  have [i] : exists i, Γ ⊢ PBind PPi A B ∈ PUniv i by hauto l:on use:regularity.
  move : E_App h. by repeat move/[apply].
Qed.

Lemma E_Proj2 Γ (a b : PTm) A B :
  Γ ⊢ a ≡ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ≡ PProj PR b ∈ subst_PTm (scons (PProj PL a) VarPTm) B.
Proof.
  move => h.
  have [i] : exists i, Γ ⊢ PBind PSig A B ∈ PUniv i by hauto l:on use:regularity.
  move : E_Proj2 h; by repeat move/[apply].
Qed.

Lemma E_FunExt Γ (a b : PTm) A B :
  Γ ⊢ a ∈ PBind PPi A B ->
  Γ ⊢ b ∈ PBind PPi A B ->
  A :: Γ ⊢ PApp (ren_PTm shift a) (VarPTm var_zero) ≡ PApp (ren_PTm shift b) (VarPTm var_zero) ∈ B ->
  Γ ⊢ a ≡ b ∈ PBind PPi A B.
Proof.
  hauto l:on use:regularity, E_FunExt.
Qed.

Lemma E_PairExt Γ (a b : PTm) A B :
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PL a ≡ PProj PL b ∈ A ->
  Γ ⊢ PProj PR a ≡ PProj PR b ∈ subst_PTm (scons (PProj PL a) VarPTm) B ->
  Γ ⊢ a ≡ b ∈ PBind PSig A B. hauto l:on use:regularity, E_PairExt. Qed.

Lemma renaming_comp Γ Δ Ξ ξ0 ξ1 :
  renaming_ok Γ Δ ξ0 -> renaming_ok Δ Ξ ξ1 ->
  renaming_ok Γ Ξ (funcomp ξ0 ξ1).
  rewrite /renaming_ok => h0 h1 i A.
  move => {}/h1 {}/h0.
  by asimpl.
Qed.

Lemma E_AppEta Γ (b : PTm) A B :
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ PAbs (PApp (ren_PTm shift b) (VarPTm var_zero)) ≡ b ∈ PBind PPi A B.
Proof.
  move => h.
  have [i hPi] : exists i, Γ ⊢ PBind PPi A B ∈ PUniv i by sfirstorder use:regularity.
  have [j [hA hB]] : exists i, Γ ⊢ A ∈ PUniv i /\ A :: Γ ⊢ B ∈ PUniv i by hauto lq:on use:Bind_Inv.
  have {i} {}hPi : Γ ⊢ PBind PPi A B ∈ PUniv j by sfirstorder use:T_Bind, wff_mutual.
  have hΓ : ⊢ A :: Γ by hauto lq:on use:Bind_Inv, Wff_Cons'.
  have hΓ' :  ⊢ ren_PTm shift A :: A :: Γ by sauto lq:on use:renaming, renaming_shift inv:Wff.
  apply E_FunExt; eauto.
  apply T_Abs.
  eapply T_App' with (A := ren_PTm shift A) (B := ren_PTm (upRen_PTm_PTm shift) B). by asimpl; rewrite subst_scons_id.
  change (PBind _ _ _) with (ren_PTm shift (PBind PPi A B)).

  eapply renaming; eauto.
  apply renaming_shift.
  constructor => //.
  by constructor.

  apply : E_Transitive. simpl.
  apply E_AppAbs' with (i := j)(A := ren_PTm shift A) (B := ren_PTm (upRen_PTm_PTm shift) B); eauto.
  by asimpl; rewrite subst_scons_id.
  hauto q:on use:renaming, renaming_shift.
  constructor => //.
  by constructor.
  asimpl.
  eapply T_App' with (A := ren_PTm shift (ren_PTm shift A)) (B := ren_PTm (upRen_PTm_PTm shift) (ren_PTm (upRen_PTm_PTm shift) B)); cycle 2.
  constructor. econstructor; eauto. sauto lq:on use:renaming, renaming_shift.
  by constructor. asimpl. substify. by asimpl.
  have -> : PBind PPi (ren_PTm shift (ren_PTm shift A)) (ren_PTm (upRen_PTm_PTm shift) (ren_PTm (upRen_PTm_PTm shift) B))=  (ren_PTm (funcomp shift shift) (PBind PPi A B)) by asimpl.
  eapply renaming; eauto. by eauto using renaming_shift, renaming_comp.
  asimpl. renamify.
  eapply E_App' with (A := ren_PTm shift A) (B := ren_PTm (upRen_PTm_PTm shift) B). by asimpl; rewrite subst_scons_id.
  hauto q:on use:renaming, renaming_shift.
  sauto lq:on use:renaming, renaming_shift, E_Refl.
  constructor. constructor=>//. constructor.
Qed.

Lemma Proj1_Inv Γ (a : PTm ) U :
  Γ ⊢ PProj PL a ∈ U ->
  exists A B, Γ ⊢ a ∈ PBind PSig A B /\ Γ ⊢ A ≲ U.
Proof.
  move E : (PProj PL a) => u hu.
  move :a E. elim : Γ u U / hu => //=.
  - move => Γ a A B ha _ a0 [*]. subst.
    exists A, B. split => //=.
    eapply regularity in ha.
    move : ha => [i].
    move /Bind_Inv => [j][h _].
    by move /E_Refl /Su_Eq in h.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma Proj2_Inv Γ (a : PTm) U :
  Γ ⊢ PProj PR a ∈ U ->
  exists A B, Γ ⊢ a ∈ PBind PSig A B /\ Γ ⊢ subst_PTm (scons (PProj PL a) VarPTm) B ≲ U.
Proof.
  move E : (PProj PR a) => u hu.
  move :a E. elim : Γ u U / hu => //=.
  - move => Γ a A B ha _ a0 [*]. subst.
    exists A, B. split => //=.
    have ha' := ha.
    eapply regularity in ha.
    move : ha => [i ha].
    move /T_Proj1 in ha'.
    apply : bind_inst; eauto.
    apply : E_Refl ha'.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma Pair_Inv Γ (a b : PTm ) U :
  Γ ⊢ PPair a b ∈ U ->
  exists A B, Γ ⊢ a ∈ A /\
         Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B /\
         Γ ⊢ PBind PSig A B ≲ U.
Proof.
  move E : (PPair a b) => u hu.
  move : a b E. elim : Γ u U / hu => //=.
  - move => Γ a b A B i hS _ ha _ hb _ a0 b0 [*]. subst.
    exists A,B. repeat split => //=.
    move /E_Refl /Su_Eq : hS. apply.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma E_ProjPair1 : forall (a b : PTm) Γ (A : PTm),
    Γ ⊢ PProj PL (PPair a b) ∈ A -> Γ ⊢ PProj PL (PPair a b) ≡ a ∈ A.
Proof.
  move => a b Γ A.
  move /Proj1_Inv. move => [A0][B0][hab]hA0.
  move /Pair_Inv : hab => [A1][B1][ha][hb]hS.
  have [i ?]  : exists i, Γ ⊢ PBind PSig A1 B1 ∈ PUniv i by sfirstorder use:regularity_sub0.
  move /Su_Sig_Proj1 in hS.
  have {hA0} {}hS : Γ ⊢ A1 ≲ A by eauto using Su_Transitive.
  apply : E_Conv; eauto.
  apply : E_ProjPair1; eauto.
Qed.

Lemma E_ProjPair2 : forall (a b : PTm) Γ (A : PTm),
    Γ ⊢ PProj PR (PPair a b) ∈ A -> Γ ⊢ PProj PR (PPair a b) ≡ b ∈ A.
Proof.
  move => a b Γ A. move /Proj2_Inv.
  move => [A0][B0][ha]h.
  have hr := ha.
  move /Pair_Inv : ha => [A1][B1][ha][hb]hU.
  have [i hSig] : exists i, Γ ⊢ PBind PSig A1 B1 ∈ PUniv i by sfirstorder use:regularity.
  have /E_Symmetric : Γ ⊢ (PProj PL (PPair a b)) ≡ a ∈ A1 by eauto using  E_ProjPair1 with wt.
  move /Su_Sig_Proj2 : hU. repeat move/[apply]. move => hB.
  apply : E_Conv; eauto.
  apply : E_Conv; eauto.
  apply : E_ProjPair2; eauto.
Qed.


Lemma E_PairEta Γ a A B :
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PPair (PProj PL a) (PProj PR a) ≡ a ∈ PBind PSig A B.
Proof.
  move => h.
  have [i hSig] : exists i, Γ ⊢ PBind PSig A B ∈ PUniv i by hauto use:regularity.
  apply E_PairExt => //.
  eapply T_Pair; eauto with wt.
  apply : E_Transitive. apply E_ProjPair1. by eauto with wt.
  by eauto with wt.
  apply E_ProjPair2.
  apply : T_Proj2; eauto with wt.
Qed.
