Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax common typing.
From Hammer Require Import Tactics.
Require Import ssreflect.


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

(* Lemma regularity : *)
(*   (forall n (Γ : fin n -> PTm n), ⊢ Γ -> forall i, exists j, Γ ⊢ Γ i ∈ PUniv j) /\ *)
(*   (forall n Γ (a A : PTm n), Γ ⊢ a ∈ A -> exists i, Γ ⊢ A ∈ PUniv i)  /\ *)
(*   (forall n Γ (a b A : PTm n), Γ ⊢ a ≡ b ∈ A -> Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A /\ exists i, Γ ⊢ A ∈ PUniv i) /\ *)
(*   (forall n Γ (A B : PTm n), Γ ⊢ A ≲ B -> exists i, Γ ⊢ A ∈ PUniv i /\ Γ ⊢ A ∈ PUniv i). *)
(* Proof. *)
(*   apply wt_mutual => //=. *)
(*   - admit. *)
(*   - admit. *)

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
