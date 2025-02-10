Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax common typing.
From Hammer Require Import Tactics.
Require Import ssreflect.
Require Import Psatz.

Lemma wff_mutual :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> True) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> ⊢ Γ)  /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> ⊢ Γ) /\
  (forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> ⊢ Γ).
Proof. apply wt_mutual; eauto. Qed.

#[export]Hint Constructors Wt Wff Eq : wt.

Lemma renaming_up n m (ξ : fin n -> fin m) Δ Γ A :
  renaming_ok Δ Γ ξ ->
  renaming_ok (funcomp (ren_PTm shift) (scons (ren_PTm ξ A) Δ)) (funcomp (ren_PTm shift) (scons A Γ)) (upRen_PTm_PTm ξ) .
Proof.
  move => h i.
  destruct i as [i|].
  asimpl. rewrite /renaming_ok in h.
  rewrite /funcomp. rewrite -h.
  by asimpl.
  by asimpl.
Qed.

Lemma Su_Wt n Γ a i :
  Γ ⊢ a ∈ @PUniv n i ->
  Γ ⊢ a ≲ a.
Proof. hauto lq:on ctrs:LEq, Eq. Qed.

Lemma Wt_Univ n Γ a A i
  (h : Γ ⊢ a ∈ A) :
  Γ ⊢ @PUniv n i ∈ PUniv (S i).
Proof.
  hauto lq:on ctrs:Wt use:wff_mutual.
Qed.


Lemma Pi_Inv n Γ (A : PTm n) B U :
  Γ ⊢ PBind PPi A B ∈ U ->
  exists i, Γ ⊢ A ∈ PUniv i /\
  funcomp (ren_PTm shift) (scons A Γ) ⊢ B ∈ PUniv i /\
  Γ ⊢ PUniv i ≲ U.
Proof.
  move E :(PBind PPi A B) => T h.
  move : A B E.
  elim : n Γ T U / h => //=.
  - hauto lq:on ctrs:Wt,LEq,Eq use:Wt_Univ.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma Sig_Inv n Γ (A : PTm n) B U :
  Γ ⊢ PBind PSig A B ∈ U ->
  exists i, Γ ⊢ A ∈ PUniv i /\
  funcomp (ren_PTm shift) (scons A Γ) ⊢ B ∈ PUniv i /\
  Γ ⊢ PUniv i ≲ U.
Proof.
  move E :(PBind PSig A B) => T h.
  move : A B E.
  elim : n Γ T U / h => //=.
  - hauto lq:on ctrs:Wt,LEq,Eq use:Wt_Univ.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma T_App' n Γ (b a : PTm n) A B U :
  U = subst_PTm (scons a VarPTm) B ->
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ PApp b a ∈ U.
Proof. move => ->. apply T_App. Qed.

Lemma T_Pair' n Γ (a b : PTm n) A B i U :
  U = subst_PTm (scons a VarPTm) B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ U ->
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ PPair a b ∈ PBind PSig A B.
Proof.
  move => ->. eauto using T_Pair.
Qed.

Lemma T_Proj2' n Γ (a : PTm n) A B U :
  U = subst_PTm (scons (PProj PL a) VarPTm) B ->
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ∈ U.
Proof. move => ->. apply T_Proj2. Qed.

Lemma E_Proj2' n Γ i (a b : PTm n) A B U :
  U = subst_PTm (scons (PProj PL a) VarPTm) B ->
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ≡ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ≡ PProj PR b ∈ U.
Proof.
  move => ->. apply E_Proj2.
Qed.

Lemma E_Bind' n Γ i p (A0 A1 : PTm n) B0 B1 :
  Γ ⊢ A0 ∈ PUniv i ->
  Γ ⊢ A0 ≡ A1 ∈ PUniv i ->
  funcomp (ren_PTm shift) (scons A0 Γ) ⊢ B0 ≡ B1 ∈ PUniv i ->
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i.
Proof. hauto lq:on use:E_Bind, wff_mutual. Qed.

Lemma E_App' n Γ i (b0 b1 a0 a1 : PTm n) A B U :
  U = subst_PTm (scons a0 VarPTm) B ->
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  Γ ⊢ b0 ≡ b1 ∈ PBind PPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ PApp b0 a0 ≡ PApp b1 a1 ∈ U.
Proof. move => ->. apply E_App. Qed.

Lemma E_AppAbs' n Γ (a : PTm (S n)) b A B i u U :
  u = subst_PTm (scons b VarPTm) a ->
  U = subst_PTm (scons b VarPTm ) B ->
  Γ ⊢ PBind PPi A B ∈ PUniv i ->
  Γ ⊢ b ∈ A ->
  funcomp (ren_PTm shift) (scons A Γ) ⊢ a ∈ B ->
  Γ ⊢ PApp (PAbs a) b ≡ u ∈ U.
  move => -> ->. apply E_AppAbs. Qed.

Lemma E_ProjPair2' n Γ (a b : PTm n) A B i U :
  U = subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PProj PR (PPair a b) ≡ b ∈ U.
Proof. move => ->. apply E_ProjPair2. Qed.

Lemma E_AppEta' n Γ (b : PTm n) A B i u :
  u = (PApp (ren_PTm shift b) (VarPTm var_zero)) ->
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ PAbs u ≡ b ∈ PBind PPi A B.
Proof. qauto l:on use:wff_mutual, E_AppEta. Qed.

Lemma Su_Pi_Proj2' n Γ (a0 a1 A0 A1 : PTm n) B0 B1 U T :
  U = subst_PTm (scons a0 VarPTm) B0 ->
  T = subst_PTm (scons a1 VarPTm) B1 ->
  Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A1 B1 ->
  Γ ⊢ a0 ≡ a1 ∈ A1 ->
  Γ ⊢ U ≲ T.
Proof. move => -> ->. apply Su_Pi_Proj2. Qed.

Lemma Su_Sig_Proj2' n Γ (a0 a1 A0 A1 : PTm n) B0 B1 U T :
  U = subst_PTm (scons a0 VarPTm) B0 ->
  T = subst_PTm (scons a1 VarPTm) B1 ->
  Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A1 B1 ->
  Γ ⊢ a0 ≡ a1 ∈ A0 ->
  Γ ⊢ U ≲ T.
Proof. move => -> ->. apply Su_Sig_Proj2. Qed.

Lemma renaming :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> True) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> forall m Δ (ξ : fin n -> fin m), ⊢ Δ -> renaming_ok Δ Γ ξ ->
     Δ ⊢ ren_PTm ξ a ∈ ren_PTm ξ A) /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> forall m Δ (ξ : fin n -> fin m), ⊢ Δ -> renaming_ok Δ Γ ξ ->
     Δ ⊢ ren_PTm ξ a ≡ ren_PTm ξ b ∈ ren_PTm ξ A) /\
  (forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> forall  m Δ (ξ : fin n -> fin m), ⊢ Δ -> renaming_ok Δ Γ ξ ->
    Δ ⊢ ren_PTm ξ A ≲ ren_PTm ξ B).
Proof.
  apply wt_mutual => //=; eauto 3 with wt.
  - move => n Γ i hΓ _ m Δ ξ hΔ hξ.
    rewrite hξ.
    by apply T_Var.
  - hauto lq:on rew:off ctrs:Wt, Wff  use:renaming_up.
  - move => n Γ a A B i hP ihP ha iha m Δ ξ hΔ hξ.
    apply : T_Abs; eauto.
    move : ihP(hΔ) (hξ); repeat move/[apply]. move/Pi_Inv.
    hauto lq:on rew:off ctrs:Wff,Wt use:renaming_up.
  - move => *. apply : T_App'; eauto. by asimpl.
  - move => n Γ a A b B i hA ihA hB ihB hS ihS m Δ ξ hξ hΔ.
    eapply T_Pair' with (U := ren_PTm ξ (subst_PTm (scons a VarPTm) B));eauto. by asimpl.
  - move => n Γ a A B ha iha m Δ ξ hΔ hξ. apply : T_Proj2'; eauto. by asimpl.
  - hauto lq:on ctrs:Wt,LEq.
  - hauto lq:on ctrs:Eq.
  - hauto lq:on rew:off use:E_Bind', Wff_Cons, renaming_up.
  - move => n Γ a b A B i hPi ihPi ha iha m Δ ξ hΔ hξ.
    move : ihPi (hΔ) (hξ). repeat move/[apply].
    move => /Pi_Inv [j][h0][h1]h2.
    have ? : Δ ⊢ PBind PPi (ren_PTm ξ A) (ren_PTm (upRen_PTm_PTm ξ) B) ∈ PUniv j by qauto l:on ctrs:Wt.
    move {hPi}.
    apply : E_Abs; eauto. qauto l:on ctrs:Wff use:renaming_up.
  - move => *. apply : E_App'; eauto. by asimpl.
  - move => n Γ a0 a1 b0 b1 A B i hA ihA ha iha hb ihb m Δ ξ hΔ hξ.
    apply : E_Pair; eauto.
    move : ihb hΔ hξ. repeat move/[apply].
    by asimpl.
  - move => *. apply : E_Proj2'; eauto. by asimpl.
  - qauto l:on ctrs:Eq, LEq.
  - move => n Γ a b A B i hP ihP hb ihb ha iha m Δ ξ hΔ hξ.
    move : ihP (hξ) (hΔ). repeat move/[apply].
    move /Pi_Inv.
    move => [j][h0][h1]h2.
    have ? : Δ ⊢ PBind PPi (ren_PTm ξ A) (ren_PTm (upRen_PTm_PTm ξ) B) ∈ PUniv j by qauto l:on ctrs:Wt.
    apply : E_AppAbs'; eauto. by asimpl. by asimpl.
    hauto lq:on ctrs:Wff use:renaming_up.
  - move => n Γ a b A B i hP ihP ha iha hb ihb m Δ ξ hΔ hξ.
    move : {hP} ihP (hξ) (hΔ). repeat move/[apply].
    move /Sig_Inv => [i0][h0][h1]h2.
    have ? : Δ ⊢ PBind PSig (ren_PTm ξ A) (ren_PTm (upRen_PTm_PTm ξ) B) ∈ PUniv i0 by qauto l:on ctrs:Wt.
    apply : E_ProjPair1; eauto.
    move : ihb hξ hΔ. repeat move/[apply]. by asimpl.
  - move => n Γ a b A B i hP ihP ha iha hb ihb m Δ ξ hΔ hξ.
    apply : E_ProjPair2'; eauto. by asimpl.
    move : ihb hξ hΔ; repeat move/[apply]. by asimpl.
  - move => *.
    apply : E_AppEta'; eauto. by asimpl.
  - qauto l:on use:E_PairEta.
  - hauto lq:on ctrs:LEq.
  - qauto l:on ctrs:LEq.
  - hauto lq:on ctrs:Wff use:renaming_up, Su_Pi.
  - hauto lq:on ctrs:Wff use:Su_Sig, renaming_up.
  - hauto q:on ctrs:LEq.
  - hauto lq:on ctrs:LEq.
  - qauto l:on ctrs:LEq.
  - move => *; apply : Su_Pi_Proj2'; eauto; by asimpl.
  - move => *. apply : Su_Sig_Proj2'; eauto; by asimpl.
Qed.

Definition morphing_ok {n m} Δ Γ (ρ : fin n -> PTm m) :=
  forall i, Δ ⊢ ρ i ∈ subst_PTm ρ (Γ i).

Lemma morphing_ren n m p Ξ Δ Γ
  (ρ : fin n -> PTm m) (ξ : fin m -> fin p) :
  ⊢ Ξ ->
  renaming_ok Ξ Δ ξ -> morphing_ok Δ Γ ρ ->
  morphing_ok Ξ Γ (funcomp (ren_PTm ξ) ρ).
Proof.
  move => hΞ hξ hρ.
  move => i.
  rewrite {1}/funcomp.
  have -> :
    subst_PTm (funcomp (ren_PTm ξ) ρ) (Γ i) =
    ren_PTm ξ (subst_PTm ρ (Γ i)) by asimpl.
  eapply renaming; eauto.
Qed.

Lemma morphing_ext n m Δ Γ (ρ : fin n -> PTm m) (a : PTm m) (A : PTm n)  :
  morphing_ok Δ Γ ρ ->
  Δ ⊢ a ∈ subst_PTm ρ A ->
  morphing_ok
  Δ (funcomp (ren_PTm shift) (scons A Γ)) (scons a ρ).
Proof.
  move => h ha i. destruct i as [i|]; by asimpl.
Qed.

Lemma T_Var' n Γ (i : fin n) U :
  U = Γ i ->
  ⊢ Γ ->
  Γ ⊢ VarPTm i ∈ U.
Proof. move => ->. apply T_Var. Qed.

Lemma renaming_wt : forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> forall m Δ (ξ : fin n -> fin m), ⊢ Δ -> renaming_ok Δ Γ ξ -> Δ ⊢ ren_PTm ξ a ∈ ren_PTm ξ A.
Proof. sfirstorder use:renaming. Qed.

Lemma renaming_wt' : forall n m Δ Γ a A (ξ : fin n -> fin m) u U,
    u = ren_PTm ξ a -> U = ren_PTm ξ A ->
    Γ ⊢ a ∈ A -> ⊢ Δ ->
    renaming_ok Δ Γ ξ -> Δ ⊢ u ∈ U.
Proof. hauto use:renaming_wt. Qed.

Lemma renaming_shift n m Γ (ρ : fin n -> PTm m) A :
  renaming_ok (funcomp (ren_PTm shift) (scons (subst_PTm ρ A) Γ)) Γ shift.
Proof. sfirstorder. Qed.

Lemma morphing_up n m Γ Δ (ρ : fin n -> PTm m) (A : PTm n) k :
  morphing_ok Γ Δ ρ ->
  Γ ⊢ subst_PTm ρ A ∈ PUniv k ->
  morphing_ok (funcomp (ren_PTm shift) (scons (subst_PTm ρ A) Γ)) (funcomp (ren_PTm shift) (scons A Δ)) (up_PTm_PTm ρ).
Proof.
  move => h h1 [:hp]. apply morphing_ext.
  rewrite /morphing_ok.
  move => i.
  rewrite {2}/funcomp.
  apply : renaming_wt'; eauto. by asimpl.
  abstract : hp. qauto l:on ctrs:Wff use:wff_mutual.
  eauto using renaming_shift.
  apply : T_Var';eauto. rewrite /funcomp. by asimpl.
Qed.

Lemma Wff_Cons' n Γ (A : PTm n) i :
  Γ ⊢ A ∈ PUniv i ->
  (* -------------------------------- *)
  ⊢ funcomp (ren_PTm shift) (scons A Γ).
Proof. hauto lq:on rew:off use:Wff_Cons, wff_mutual. Qed.

Lemma weakening_wt : forall n Γ (a A B : PTm n) i,
    Γ ⊢ B ∈ PUniv i ->
    Γ ⊢ a ∈ A ->
    funcomp (ren_PTm shift) (scons B Γ) ⊢ ren_PTm shift a ∈ ren_PTm shift A.
Proof.
  move => n Γ a A B i hB ha.
  apply : renaming_wt'; eauto.
  apply : Wff_Cons'; eauto.
  apply : renaming_shift; eauto.
Qed.

Lemma weakening_wt' : forall n Γ (a A B : PTm n) i U u,
    u = ren_PTm shift a ->
    U = ren_PTm shift A ->
    Γ ⊢ B ∈ PUniv i ->
    Γ ⊢ a ∈ A ->
    funcomp (ren_PTm shift) (scons B Γ) ⊢ u ∈ U.
Proof. move => > -> ->. apply weakening_wt. Qed.

Lemma morphing :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> True) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> forall m Δ (ρ : fin n -> PTm m), ⊢ Δ -> morphing_ok Δ Γ ρ ->
     Δ ⊢ subst_PTm ρ a ∈ subst_PTm ρ A) /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> forall m Δ (ρ : fin n -> PTm m), ⊢ Δ -> morphing_ok Δ Γ ρ ->
     Δ ⊢ subst_PTm ρ a ≡ subst_PTm ρ b ∈ subst_PTm ρ A) /\
  (forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> forall  m Δ (ρ : fin n -> PTm m), ⊢ Δ -> morphing_ok Δ Γ ρ ->
    Δ ⊢ subst_PTm ρ A ≲ subst_PTm ρ B).
Proof.
  apply wt_mutual => //=.
  - hauto lq:on use:morphing_up, Wff_Cons', T_Bind.
  - move => n Γ a A B i hP ihP ha iha m Δ ρ hΔ hρ.
    move : ihP (hΔ) (hρ); repeat move/[apply].
    move /Pi_Inv => [j][h0][h1]h2. move {hP}.
    have ? : Δ ⊢ PBind PPi (subst_PTm ρ A) (subst_PTm (up_PTm_PTm ρ) B) ∈ PUniv i by hauto lq:on ctrs:Wt.
    apply : T_Abs; eauto.
    apply : iha.
    hauto lq:on use:Wff_Cons', Pi_Inv.
    apply : morphing_up; eauto.
  - move => *; apply : T_App'; eauto; by asimpl.
  - move => n Γ a A b B i hA ihA hB ihB hS ihS m Δ ρ hρ hΔ.
    eapply T_Pair' with (U := subst_PTm ρ (subst_PTm (scons a VarPTm) B));eauto. by asimpl.
  - hauto lq:on use:T_Proj1.
  - move => *. apply : T_Proj2'; eauto. by asimpl.
  - hauto lq:on ctrs:Wt,LEq.
  - qauto l:on ctrs:Wt.
  - hauto lq:on ctrs:Eq.
  - hauto lq:on ctrs:Eq.
  - hauto lq:on ctrs:Eq.
  - hauto lq:on rew:off use:E_Bind', Wff_Cons, morphing_up.
  - move => n Γ a b A B i hPi ihPi ha iha m Δ ρ hΔ hρ.
    move : ihPi (hΔ) (hρ). repeat move/[apply].
    move => /Pi_Inv [j][h0][h1]h2.
    have ? : Δ ⊢ PBind PPi (subst_PTm ρ A) (subst_PTm (up_PTm_PTm ρ) B) ∈ PUniv j by qauto l:on ctrs:Wt.
    move {hPi}.
    apply : E_Abs; eauto. qauto l:on ctrs:Wff use:morphing_up.
  - move => *. apply : E_App'; eauto. by asimpl.
  - move => n Γ a0 a1 b0 b1 A B i hA ihA ha iha hb ihb m Δ ρ hΔ hρ.
    apply : E_Pair; eauto.
    move : ihb hΔ hρ. repeat move/[apply].
    by asimpl.
  - hauto q:on ctrs:Eq.
  - move => *. apply : E_Proj2'; eauto. by asimpl.
  - qauto l:on ctrs:Eq, LEq.
  - move => n Γ a b A B i hP ihP hb ihb ha iha m Δ ρ hΔ hρ.
    move : ihP (hρ) (hΔ). repeat move/[apply].
    move /Pi_Inv.
    move => [j][h0][h1]h2.
    have ? : Δ ⊢ PBind PPi (subst_PTm ρ A) (subst_PTm (up_PTm_PTm ρ) B) ∈ PUniv j by qauto l:on ctrs:Wt.
    apply : E_AppAbs'; eauto. by asimpl. by asimpl.
    hauto lq:on ctrs:Wff use:morphing_up.
  - move => n Γ a b A B i hP ihP ha iha hb ihb m Δ ρ hΔ hρ.
    move : {hP} ihP (hρ) (hΔ). repeat move/[apply].
    move /Sig_Inv => [i0][h0][h1]h2.
    have ? : Δ ⊢ PBind PSig (subst_PTm ρ A) (subst_PTm (up_PTm_PTm ρ) B) ∈ PUniv i0 by qauto l:on ctrs:Wt.
    apply : E_ProjPair1; eauto.
    move : ihb hρ hΔ. repeat move/[apply]. by asimpl.
  - move => n Γ a b A B i hP ihP ha iha hb ihb m Δ ρ hΔ hρ.
    apply : E_ProjPair2'; eauto. by asimpl.
    move : ihb hρ hΔ; repeat move/[apply]. by asimpl.
  - move => *.
    apply : E_AppEta'; eauto. by asimpl.
  - qauto l:on use:E_PairEta.
  - hauto lq:on ctrs:LEq.
  - qauto l:on ctrs:LEq.
  - hauto lq:on ctrs:Wff use:morphing_up, Su_Pi.
  - hauto lq:on ctrs:Wff use:Su_Sig, morphing_up.
  - hauto q:on ctrs:LEq.
  - hauto lq:on ctrs:LEq.
  - qauto l:on ctrs:LEq.
  - move => *; apply : Su_Pi_Proj2'; eauto; by asimpl.
  - move => *. apply : Su_Sig_Proj2'; eauto; by asimpl.
Qed.

Lemma morphing_wt : forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> forall m Δ (ρ : fin n -> PTm m), ⊢ Δ -> morphing_ok Δ Γ ρ -> Δ ⊢ subst_PTm ρ a ∈ subst_PTm ρ A.
Proof. sfirstorder use:morphing. Qed.

Lemma morphing_wt' : forall n m Δ Γ a A (ρ : fin n -> PTm m) u U,
    u = subst_PTm ρ a -> U = subst_PTm ρ A ->
    Γ ⊢ a ∈ A -> ⊢ Δ ->
    morphing_ok Δ Γ ρ -> Δ ⊢ u ∈ U.
Proof. hauto use:morphing_wt. Qed.

Lemma morphing_id : forall n (Γ : fin n -> PTm n), ⊢ Γ -> morphing_ok Γ Γ VarPTm.
Proof.
  move => n Γ hΓ.
  rewrite /morphing_ok.
  move => i. asimpl. by apply T_Var.
Qed.

Lemma substing_wt : forall n Γ (a : PTm (S n)) (b A : PTm n) B,
    funcomp (ren_PTm shift) (scons A Γ) ⊢ a ∈ B ->
    Γ ⊢ b ∈ A ->
    Γ ⊢ subst_PTm (scons b VarPTm) a ∈ subst_PTm (scons b VarPTm) B.
Proof.
  move => n Γ a b A B ha hb [:hΓ]. apply : morphing_wt; eauto.
  abstract : hΓ. sfirstorder use:wff_mutual.
  apply morphing_ext; last by asimpl.
  by apply morphing_id.
Qed.

Lemma regularity :
  (forall n (Γ : fin n -> PTm n), ⊢ Γ -> forall i, exists j, Γ ⊢ Γ i ∈ PUniv j) /\
  (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> exists i, Γ ⊢ A ∈ PUniv i)  /\
  (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A /\ exists i, Γ ⊢ A ∈ PUniv i) /\
  (forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> exists i, Γ ⊢ A ∈ PUniv i /\ Γ ⊢ B ∈ PUniv i).
Proof.
  apply wt_mutual => //=; eauto with wt.
  - move => n Γ A i hΓ ihΓ hA _ j.
    destruct j as [j|].
    have := ihΓ j.
    move => [j0 hj].
    exists j0. apply : renaming_wt' => //=; eauto using renaming_shift.
    reflexivity. econstructor; eauto.
    exists i. rewrite {2}/funcomp. simpl.
    apply : renaming_wt'; eauto. reflexivity.
    econstructor; eauto.
    apply : renaming_shift; eauto.
  - move => n Γ b a A B hb [i ihb] ha [j iha].
    move /Pi_Inv : ihb => [k][h0][h1]h2.
    move : substing_wt ha h1; repeat move/[apply].
    move => h. exists k.
    move : h. by asimpl.
  - hauto lq:on use:Sig_Inv.
  - move => n Γ a A B ha [i /Sig_Inv[j][h0][h1]h2].
    exists j. have : Γ ⊢ PProj PL a ∈ A by qauto use:T_Proj1.
    move : substing_wt h1; repeat move/[apply].
    by asimpl.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - move => n Γ i p A0 A1 B0 B1 hΓ ihΓ hA0
             [i0 ihA0] hA [ihA [ihA' [i1 ihA'']]].
    move => hB [ihB0 [ihB1 [i2 ihB2]]].
    repeat split => //=.
    qauto use:T_Bind.
    admit.
    eauto using T_Univ.
  - hauto lq:on ctrs:Wt,Eq.
  - move => n Γ i b0 b1 a0 a1 A B hP _ hb [ihb0 [ihb1 [i0 ihb2]]]
             ha [iha0 [iha1 [i1 iha2]]].
    repeat split.
    qauto use:T_App.
    apply : T_Conv; eauto.
    qauto use:T_App.
    apply Su_Pi_Proj2 with (A0 := A) (A1 := A).
    apply : Su_Eq; apply E_Refl; eauto.
    by apply E_Symmetric.
    sauto lq:on use:Pi_Inv, substing_wt.
  - admit.
  - admit.
  - admit.
  - hauto lq:on ctrs:Wt.
  - admit.
  - admit.
  - admit.
  - hauto lq:on ctrs:Wt.
  - move => n Γ A B C hA [i [ihA0 ihA1]] hC [j [ihC0 ihC1]].
    have ? : ⊢ Γ by sfirstorder use:wff_mutual.
    exists (max i j).
    have [? ?] : i <= Nat.max i j /\ j <= Nat.max i j by lia.
    qauto l:on use:T_Conv, Su_Univ.
  - move => n Γ i j hΓ *. exists (S (max i j)).
    have [? ?] : S i <= S (Nat.max i j) /\ S j <= S (Nat.max i j) by lia.
    hauto lq:on ctrs:Wt,LEq.
  - admit.
  - admit.
  - sfirstorder.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
