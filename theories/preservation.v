Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax common typing structural fp_red.
From Hammer Require Import Tactics.
Require Import ssreflect.
Require Import Psatz.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma App_Inv n Γ (b a : PTm n) U :
  Γ ⊢ PApp b a ∈ U ->
  exists A B, Γ ⊢ b ∈ PBind PPi A B /\ Γ ⊢ a ∈ A /\ Γ ⊢ subst_PTm (scons a VarPTm) B ≲ U.
Proof.
  move E : (PApp b a) => u hu.
  move : b a E. elim : n Γ u U / hu => n //=.
  - move => Γ b a A B hb _ ha _ b0 a0 [*]. subst.
    exists A,B.
    repeat split => //=.
    have [i] : exists i, Γ ⊢ PBind PPi A B ∈  PUniv i by sfirstorder use:regularity.
    hauto lq:on use:bind_inst, E_Refl.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma Abs_Inv n Γ (a : PTm (S n)) U :
  Γ ⊢ PAbs a ∈ U ->
  exists A B, funcomp (ren_PTm shift) (scons A Γ) ⊢ a ∈ B /\ Γ ⊢ PBind PPi A B ≲ U.
Proof.
  move E : (PAbs a) => u hu.
  move : a E. elim : n Γ u U / hu => n //=.
  - move => Γ a A B i hP _ ha _ a0 [*]. subst.
    exists A, B. repeat split => //=.
    hauto lq:on use:E_Refl, Su_Eq.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma Proj1_Inv n Γ (a : PTm n) U :
  Γ ⊢ PProj PL a ∈ U ->
  exists A B, Γ ⊢ a ∈ PBind PSig A B /\ Γ ⊢ A ≲ U.
Proof.
  move E : (PProj PL a) => u hu.
  move :a E. elim : n Γ u U / hu => n //=.
  - move => Γ a A B ha _ a0 [*]. subst.
    exists A, B. split => //=.
    eapply regularity in ha.
    move : ha => [i].
    move /Bind_Inv => [j][h _].
    by move /E_Refl /Su_Eq in h.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma Proj2_Inv n Γ (a : PTm n) U :
  Γ ⊢ PProj PR a ∈ U ->
  exists A B, Γ ⊢ a ∈ PBind PSig A B /\ Γ ⊢ subst_PTm (scons (PProj PL a) VarPTm) B ≲ U.
Proof.
  move E : (PProj PR a) => u hu.
  move :a E. elim : n Γ u U / hu => n //=.
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

Lemma Pair_Inv n Γ (a b : PTm n) U :
  Γ ⊢ PPair a b ∈ U ->
  exists A B, Γ ⊢ a ∈ A /\
         Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B /\
         Γ ⊢ PBind PSig A B ≲ U.
Proof.
  move E : (PPair a b) => u hu.
  move : a b E. elim : n Γ u U / hu => n //=.
  - move => Γ a b A B i hS _ ha _ hb _ a0 b0 [*]. subst.
    exists A,B. repeat split => //=.
    move /E_Refl /Su_Eq : hS. apply.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma regularity_sub0 : forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> exists i, Γ ⊢ A ∈ PUniv i.
Proof. hauto lq:on use:regularity. Qed.

Lemma E_AppAbs : forall n (a : PTm (S n)) (b : PTm n) (Γ : fin n -> PTm n) (A : PTm n),
  Γ ⊢ PApp (PAbs a) b ∈ A -> Γ ⊢ PApp (PAbs a) b ≡ subst_PTm (scons b VarPTm) a ∈ A.
Proof.
  move => n a b Γ A ha.
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

Lemma E_ProjPair1 : forall n (a b : PTm n) (Γ : fin n -> PTm n) (A : PTm n),
    Γ ⊢ PProj PL (PPair a b) ∈ A -> Γ ⊢ PProj PL (PPair a b) ≡ a ∈ A.
Proof.
  move => n a b Γ A.
  move /Proj1_Inv. move => [A0][B0][hab]hA0.
  move /Pair_Inv : hab => [A1][B1][ha][hb]hS.
  have [i ?]  : exists i, Γ ⊢ PBind PSig A1 B1 ∈ PUniv i by sfirstorder use:regularity_sub0.
  move /Su_Sig_Proj1 in hS.
  have {hA0} {}hS : Γ ⊢ A1 ≲ A by eauto using Su_Transitive.
  apply : E_Conv; eauto.
  apply : E_ProjPair1; eauto.
Qed.

Lemma RRed_Eq n Γ (a b : PTm n) A :
  Γ ⊢ a ∈ A ->
  RRed.R a b ->
  Γ ⊢ a ≡ b ∈ A.
Proof.
  move => + h. move : Γ A. elim : n a b /h => n.
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
Qed.

Theorem subject_reduction n Γ (a b A : PTm n) :
  Γ ⊢ a ∈ A ->
  RRed.R a b ->
  Γ ⊢ b ∈ A.
Proof. hauto lq:on use:RRed_Eq, regularity. Qed.
