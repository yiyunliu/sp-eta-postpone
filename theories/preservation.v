Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common typing structural fp_red.
From Hammer Require Import Tactics.
Require Import ssreflect.
Require Import Psatz.
Require Import Coq.Logic.FunctionalExtensionality.

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

Lemma Ind_Inv Γ P (a : PTm) b c U :
  Γ ⊢ PInd P a b c ∈ U ->
  exists i, (cons PNat Γ) ⊢ P ∈ PUniv i /\
       Γ ⊢ a ∈ PNat /\
       Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P /\
          (cons P (cons PNat Γ)) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) /\
       Γ ⊢ subst_PTm (scons a VarPTm) P ≲ U.
Proof.
  move E : (PInd P a b c)=> u hu.
  move : P a b c E. elim : Γ u U / hu => //=.
  - move => Γ P a b c i hP _ ha _ hb _ hc _ P0 a0 b0 c0 [*]. subst.
    exists i. repeat split => //=.
    have : Γ ⊢ subst_PTm (scons a VarPTm) P ∈ subst_PTm (scons a VarPTm) (PUniv i) by hauto l:on use:substing_wt.
    eauto using E_Refl, Su_Eq.
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

Lemma Suc_Inv Γ (a : PTm) A :
  Γ ⊢ PSuc a ∈ A -> Γ ⊢ a ∈ PNat /\ Γ ⊢ PNat ≲ A.
Proof.
  move E : (PSuc a) => u hu.
  move : a E.
  elim : Γ u A /hu => //=.
  - move => Γ a ha iha a0 [*]. subst.
    split => //=. eapply wff_mutual in ha.
    apply : Su_Eq.
    apply E_Refl. by apply T_Nat'.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma RRed_Eq Γ (a b : PTm) A :
  Γ ⊢ a ∈ A ->
  RRed.R a b ->
  Γ ⊢ a ≡ b ∈ A.
Proof.
  move => + h. move : Γ A. elim : a b /h.
  - apply E_AppAbs.
  - move => p a b Γ A.
    case : p => //=.
    + apply E_ProjPair1.
    + move /Proj2_Inv. move => [A0][B0][hab]hA0.
      move /Pair_Inv : hab => [A1][B1][ha][hb]hS.
      have [i ?]  : exists i, Γ ⊢ PBind PSig A1 B1 ∈ PUniv i by sfirstorder use:regularity_sub0.
      have : Γ ⊢ PPair a b ∈ PBind PSig A1 B1 by hauto lq:on ctrs:Wt.
      move /T_Proj1.
      move /E_ProjPair1 /E_Symmetric => h.
      have /Su_Sig_Proj1 hSA := hS.
      have : Γ ⊢ subst_PTm (scons a VarPTm) B1 ≲ subst_PTm (scons (PProj PL (PPair a b)) VarPTm) B0 by
        apply : Su_Sig_Proj2; eauto.
      move : hA0 => /[swap]. move : Su_Transitive. repeat move/[apply].
      move {hS}.
      move => ?. apply : E_Conv; eauto. apply : E_ProjPair2; eauto.
  - hauto lq:on use:Ind_Inv, E_Conv, E_IndZero.
  - move => P a b c Γ A.
    move /Ind_Inv.
    move => [i][hP][ha][hb][hc]hSu.
    apply : E_Conv; eauto.
    apply : E_IndSuc'; eauto.
    hauto l:on use:Suc_Inv.
  - qauto l:on use:Abs_Inv, E_Conv, regularity_sub0, E_Abs.
  - move => a0 a1 b ha iha Γ A /App_Inv [A0][B0][ih0][ih1]hU.
    have {}/iha iha := ih0.
    have [i hP] : exists i, Γ ⊢ PBind PPi A0 B0 ∈ PUniv i by sfirstorder use:regularity.
    apply : E_Conv; eauto.
    apply : E_App; eauto using E_Refl.
  - move => a0 b0 b1 ha iha Γ A /App_Inv [A0][B0][ih0][ih1]hU.
    have {}/iha iha := ih1.
    have [i hP] : exists i, Γ ⊢ PBind PPi A0 B0 ∈ PUniv i by sfirstorder use:regularity.
    apply : E_Conv; eauto.
    apply : E_App; eauto.
    sfirstorder use:E_Refl.
  - move => a0 a1 b ha iha Γ A /Pair_Inv.
    move => [A0][B0][h0][h1]hU.
    have [i hP] : exists i, Γ ⊢ PBind PSig A0 B0 ∈ PUniv i by eauto using regularity_sub0.
    have {}/iha iha := h0.
    apply : E_Conv; eauto.
    apply : E_Pair; eauto using E_Refl.
  - move => a b0 b1 ha iha Γ A /Pair_Inv.
    move => [A0][B0][h0][h1]hU.
    have [i hP] : exists i, Γ ⊢ PBind PSig A0 B0 ∈ PUniv i by eauto using regularity_sub0.
    have {}/iha iha := h1.
    apply : E_Conv; eauto.
    apply : E_Pair; eauto using E_Refl.
  - case.
    + move => a0 a1 ha iha Γ A /Proj1_Inv [A0][B0][h0]hU.
      apply : E_Conv; eauto.
      qauto l:on ctrs:Eq,Wt.
    + move => a0 a1 ha iha Γ A /Proj2_Inv [A0][B0][h0]hU.
      have [i hP] : exists i, Γ ⊢ PBind PSig A0 B0 ∈ PUniv i by sfirstorder use:regularity.
      apply : E_Conv; eauto.
      apply : E_Proj2; eauto.
  - move => p A0 A1 B hA ihA Γ U /Bind_Inv [i][h0][h1]hU.
    have {}/ihA ihA := h0.
    apply : E_Conv; eauto.
    apply E_Bind'; eauto using E_Refl.
  - move => p A0 A1 B hA ihA Γ U /Bind_Inv [i][h0][h1]hU.
    have {}/ihA ihA := h1.
    apply : E_Conv; eauto.
    apply E_Bind'; eauto using E_Refl.
  - hauto lq:on rew:off use:Ind_Inv, E_Conv, E_IndCong db:wt.
  - hauto lq:on rew:off use:Ind_Inv, E_Conv, E_IndCong db:wt.
  - hauto lq:on rew:off use:Ind_Inv, E_Conv, E_IndCong db:wt.
  - hauto lq:on rew:off use:Ind_Inv, E_Conv, E_IndCong db:wt.
  - hauto lq:on use:Suc_Inv, E_Conv, E_SucCong.
Qed.

Theorem subject_reduction Γ (a b A : PTm) :
  Γ ⊢ a ∈ A ->
  RRed.R a b ->
  Γ ⊢ b ∈ A.
Proof. hauto lq:on use:RRed_Eq, regularity. Qed.
