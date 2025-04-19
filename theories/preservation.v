Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common typing structural fp_red admissible.
From Hammer Require Import Tactics.
Require Import ssreflect.
Require Import Psatz.
Require Import Coq.Logic.FunctionalExtensionality.


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

Lemma E_Abs Γ a b A B :
  A :: Γ ⊢ a ≡ b ∈ B ->
  Γ ⊢ PAbs a ≡ PAbs b ∈ PBind PPi A B.
Proof.
  move => h.
  have [i hA] : exists i, Γ ⊢ A ∈ PUniv i by hauto l:on use:wff_mutual inv:Wff.
  have [j hB] : exists j, A :: Γ ⊢ B ∈ PUniv j by hauto l:on use:regularity.
  have hΓ : ⊢ Γ by sfirstorder use:wff_mutual.
  have hΓ' : ⊢ A::Γ by eauto with wt.
  set k := max i j.
  have [? ?] : i <= k /\ j <= k by lia.
  have {}hA : Γ ⊢ A ∈ PUniv k by hauto l:on use:T_Conv, Su_Univ.
  have {}hB : A :: Γ ⊢ B ∈ PUniv k by hauto lq:on use:T_Conv, Su_Univ.
  have hPi : Γ ⊢ PBind PPi A B ∈ PUniv k by eauto with wt.
  apply : E_FunExt; eauto with wt.
  hauto lq:on rew:off use:regularity, T_Abs.
  hauto lq:on rew:off use:regularity, T_Abs.
  apply : E_Transitive => /=. apply E_AppAbs.
  hauto lq:on use:T_Eta, regularity.
  apply /E_Symmetric /E_Transitive. apply E_AppAbs.
  hauto lq:on use:T_Eta, regularity.
  asimpl. rewrite !subst_scons_id. by apply E_Symmetric.
Qed.

Lemma E_Pair Γ a0 b0 a1 b1 A B i :
  Γ ⊢ PBind PSig A B ∈ PUniv i ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ b0 ≡ b1 ∈ subst_PTm (scons a0 VarPTm) B ->
  Γ ⊢ PPair a0 b0 ≡ PPair a1 b1 ∈ PBind PSig A B.
Proof.
  move => hSig ha hb.
  have [ha0 ha1] : Γ ⊢ a0 ∈ A /\ Γ ⊢ a1 ∈ A by hauto l:on use:regularity.
  have [hb0 hb1] : Γ ⊢ b0 ∈ subst_PTm (scons a0 VarPTm) B /\
                     Γ ⊢ b1 ∈ subst_PTm (scons a0 VarPTm) B by hauto l:on use:regularity.
  have hp : Γ ⊢ PPair a0 b0 ∈ PBind PSig A B by eauto with wt.
  have hp' : Γ ⊢ PPair a1 b1 ∈ PBind PSig A B. econstructor; eauto with wt; [idtac].
  apply : T_Conv; eauto. apply : Su_Sig_Proj2; by eauto using Su_Eq, E_Refl.
  have ea : Γ ⊢ PProj PL (PPair a0 b0) ≡ a0 ∈ A by eauto with wt.
  have : Γ ⊢ PProj PR (PPair a0 b0) ≡ b0 ∈ subst_PTm (scons a0 VarPTm) B by eauto with wt.
  have : Γ ⊢ PProj PL (PPair a1 b1) ≡ a1 ∈ A by eauto using E_ProjPair1 with wt.
  have : Γ ⊢ PProj PR (PPair a1 b1) ≡ b1 ∈ subst_PTm (scons a0 VarPTm) B.
  apply : E_Conv; eauto using E_ProjPair2 with wt.
  apply : Su_Sig_Proj2. apply /Su_Eq /E_Refl. eassumption.
  apply : E_Transitive. apply E_ProjPair1. by eauto with wt.
  by eauto using E_Symmetric.
  move => *.
  apply : E_PairExt; eauto using E_Symmetric, E_Transitive.
  apply : E_Conv. by eauto using E_Symmetric, E_Transitive.
  apply : Su_Sig_Proj2. apply /Su_Eq /E_Refl. eassumption.
  apply : E_Transitive. by eauto. apply /E_Symmetric /E_Transitive.
  by eauto using E_ProjPair1.
  eauto.
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
      move => ?. apply : E_Conv; eauto. apply : typing.E_ProjPair2; eauto.
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
