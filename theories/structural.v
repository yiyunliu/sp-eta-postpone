Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common typing.
From Hammer Require Import Tactics.
Require Import ssreflect.
Require Import Psatz.

Lemma wff_mutual :
  (forall Γ, ⊢ Γ -> True) /\
  (forall Γ (a A : PTm), Γ ⊢ a ∈ A -> ⊢ Γ)  /\
  (forall Γ (a b A : PTm), Γ ⊢ a ≡ b ∈ A -> ⊢ Γ) /\
  (forall Γ (A B : PTm), Γ ⊢ A ≲ B -> ⊢ Γ).
Proof. apply wt_mutual; eauto. Qed.

#[export]Hint Constructors Wt Wff Eq : wt.

Lemma T_Nat' Γ :
  ⊢ Γ ->
  Γ ⊢ PNat ∈ PUniv 0.
Proof. apply T_Nat. Qed.

Lemma renaming_up (ξ : nat -> nat) Δ Γ A :
  renaming_ok Δ Γ ξ ->
  renaming_ok (cons (ren_PTm ξ A) Δ) (cons A Γ) (upRen_PTm_PTm ξ) .
Proof.
  move => h i A0.
  elim /lookup_inv => //=_.
  - move => A1 Γ0 ? [*]. subst. apply here'. by asimpl.
  - move => i0 Γ0 A1 B h' ? [*]. subst.
    apply : there'; eauto. by asimpl.
Qed.

Lemma Su_Wt Γ a i :
  Γ ⊢ a ∈ PUniv i ->
  Γ ⊢ a ≲ a.
Proof. hauto lq:on ctrs:LEq, Eq. Qed.

Lemma Wt_Univ Γ a A i
  (h : Γ ⊢ a ∈ A) :
  Γ ⊢ @PUniv i ∈ PUniv (S i).
Proof.
  hauto lq:on ctrs:Wt use:wff_mutual.
Qed.

Lemma Bind_Inv Γ p (A : PTm) B U :
  Γ ⊢ PBind p A B ∈ U ->
  exists i, Γ ⊢ A ∈ PUniv i /\
  (cons A Γ) ⊢ B ∈ PUniv i /\
  Γ ⊢ PUniv i ≲ U.
Proof.
  move E :(PBind p A B) => T h.
  move : p A B E.
  elim : Γ T U / h => //=.
  - move => Γ i p A B hA _ hB _ p0 A0 B0 [*]. subst.
    exists i. repeat split => //=.
    eapply wff_mutual in hA.
    apply Su_Univ; eauto.
  - hauto lq:on rew:off ctrs:LEq.
Qed.

Lemma T_App' Γ (b a : PTm) A B U :
  U = subst_PTm (scons a VarPTm) B ->
  Γ ⊢ b ∈ PBind PPi A B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ PApp b a ∈ U.
Proof. move => ->. apply T_App. Qed.

Lemma T_Pair' Γ (a b : PTm ) A B i U :
  U = subst_PTm (scons a VarPTm) B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ U ->
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ PPair a b ∈ PBind PSig A B.
Proof.
  move => ->. eauto using T_Pair.
Qed.

Lemma E_IndCong' Γ P0 P1 (a0 a1 : PTm ) b0 b1 c0 c1 i U :
  U = subst_PTm (scons a0 VarPTm) P0 ->
  (cons PNat Γ) ⊢ P0 ∈ PUniv i ->
  (cons PNat Γ) ⊢ P0 ≡ P1 ∈ PUniv i ->
  Γ ⊢ a0 ≡ a1 ∈ PNat ->
  Γ ⊢ b0 ≡ b1 ∈ subst_PTm (scons PZero VarPTm) P0 ->
  (cons P0 (cons PNat Γ)) ⊢ c0 ≡ c1 ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P0) ->
  Γ ⊢ PInd P0 a0 b0 c0 ≡ PInd P1 a1 b1 c1 ∈ U.
Proof. move => ->. apply E_IndCong. Qed.

Lemma T_Ind' Γ P (a : PTm) b c i U :
  U = subst_PTm (scons a VarPTm) P ->
  cons PNat Γ ⊢ P ∈ PUniv i ->
  Γ ⊢ a ∈ PNat ->
  Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P ->
  cons P (cons PNat Γ) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊢ PInd P a b c ∈ U.
Proof. move =>->. apply T_Ind. Qed.

Lemma T_Proj2' Γ (a : PTm) A B U :
  U = subst_PTm (scons (PProj PL a) VarPTm) B ->
  Γ ⊢ a ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ∈ U.
Proof. move => ->. apply T_Proj2. Qed.

Lemma E_Proj2' Γ i (a b : PTm) A B U :
  U = subst_PTm (scons (PProj PL a) VarPTm) B ->
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ≡ b ∈ PBind PSig A B ->
  Γ ⊢ PProj PR a ≡ PProj PR b ∈ U.
Proof. move => ->. apply E_Proj2. Qed.

Lemma E_Bind' Γ i p (A0 A1 : PTm) B0 B1 :
  Γ ⊢ A0 ∈ PUniv i ->
  Γ ⊢ A0 ≡ A1 ∈ PUniv i ->
  cons A0 Γ ⊢ B0 ≡ B1 ∈ PUniv i ->
  Γ ⊢ PBind p A0 B0 ≡ PBind p A1 B1 ∈ PUniv i.
Proof. hauto lq:on use:E_Bind, wff_mutual. Qed.

Lemma E_App' Γ i (b0 b1 a0 a1 : PTm) A B U :
  U = subst_PTm (scons a0 VarPTm) B ->
  Γ ⊢ PBind PPi A B ∈ (PUniv i) ->
  Γ ⊢ b0 ≡ b1 ∈ PBind PPi A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ PApp b0 a0 ≡ PApp b1 a1 ∈ U.
Proof. move => ->. apply E_App. Qed.

Lemma E_AppAbs' Γ (a : PTm) b A B i u U :
  u = subst_PTm (scons b VarPTm) a ->
  U = subst_PTm (scons b VarPTm ) B ->
  Γ ⊢ PBind PPi A B ∈ PUniv i ->
  Γ ⊢ b ∈ A ->
  cons A Γ ⊢ a ∈ B ->
  Γ ⊢ PApp (PAbs a) b ≡ u ∈ U.
  move => -> ->. apply E_AppAbs. Qed.

Lemma E_ProjPair2' Γ (a b : PTm) A B i U :
  U = subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PBind PSig A B ∈ (PUniv i) ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ subst_PTm (scons a VarPTm) B ->
  Γ ⊢ PProj PR (PPair a b) ≡ b ∈ U.
Proof. move => ->. apply E_ProjPair2. Qed.

(* Lemma E_AppEta' Γ (b : PTm ) A B i u : *)
(*   u = (PApp (ren_PTm shift b) (VarPTm var_zero)) -> *)
(*   Γ ⊢ PBind PPi A B ∈ (PUniv i) -> *)
(*   Γ ⊢ b ∈ PBind PPi A B -> *)
(*   Γ ⊢ PAbs u ≡ b ∈ PBind PPi A B. *)
(* Proof. qauto l:on use:wff_mutual, E_AppEta. Qed. *)

Lemma Su_Pi_Proj2' Γ (a0 a1 A0 A1 : PTm ) B0 B1 U T :
  U = subst_PTm (scons a0 VarPTm) B0 ->
  T = subst_PTm (scons a1 VarPTm) B1 ->
  Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A1 B1 ->
  Γ ⊢ a0 ≡ a1 ∈ A1 ->
  Γ ⊢ U ≲ T.
Proof. move => -> ->. apply Su_Pi_Proj2. Qed.

Lemma Su_Sig_Proj2' Γ (a0 a1 A0 A1 : PTm) B0 B1 U T :
  U = subst_PTm (scons a0 VarPTm) B0 ->
  T = subst_PTm (scons a1 VarPTm) B1 ->
  Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A1 B1 ->
  Γ ⊢ a0 ≡ a1 ∈ A0 ->
  Γ ⊢ U ≲ T.
Proof. move => -> ->. apply Su_Sig_Proj2. Qed.

Lemma E_IndZero' Γ P i (b : PTm) c U :
  U = subst_PTm (scons PZero VarPTm) P ->
  cons PNat Γ ⊢ P ∈ PUniv i ->
  Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P ->
  cons P (cons PNat Γ) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊢ PInd P PZero b c ≡ b ∈ U.
Proof. move => ->. apply E_IndZero. Qed.

Lemma Wff_Cons' Γ (A : PTm) i :
  Γ ⊢ A ∈ PUniv i ->
  (* -------------------------------- *)
  ⊢ cons A Γ.
Proof. hauto lq:on rew:off use:Wff_Cons, wff_mutual. Qed.

Lemma E_IndSuc' Γ P (a : PTm) b c i u U :
  u = subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c ->
  U = subst_PTm (scons (PSuc a) VarPTm) P ->
  cons PNat Γ ⊢ P ∈ PUniv i ->
  Γ ⊢ a ∈ PNat ->
  Γ ⊢ b ∈ subst_PTm (scons PZero VarPTm) P ->
  (cons P (cons PNat Γ)) ⊢ c ∈ ren_PTm shift (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift) ) P) ->
  Γ ⊢ PInd P (PSuc a) b c ≡ u ∈ U.
Proof. move => ->->. apply E_IndSuc. Qed.

Lemma renaming :
  (forall Γ, ⊢ Γ -> True) /\
  (forall Γ (a A : PTm), Γ ⊢ a ∈ A -> forall Δ (ξ : nat -> nat), ⊢ Δ -> renaming_ok Δ Γ ξ ->
     Δ ⊢ ren_PTm ξ a ∈ ren_PTm ξ A) /\
  (forall Γ (a b A : PTm), Γ ⊢ a ≡ b ∈ A -> forall Δ (ξ : nat -> nat), ⊢ Δ -> renaming_ok Δ Γ ξ ->
     Δ ⊢ ren_PTm ξ a ≡ ren_PTm ξ b ∈ ren_PTm ξ A) /\
  (forall Γ (A B : PTm), Γ ⊢ A ≲ B -> forall  Δ (ξ : nat -> nat), ⊢ Δ -> renaming_ok Δ Γ ξ ->
    Δ ⊢ ren_PTm ξ A ≲ ren_PTm ξ B).
Proof.
  apply wt_mutual => //=; eauto 3 with wt.
  - hauto lq:on rew:off ctrs:Wt, Wff  use:renaming_up.
  - move => Γ a A B i hP ihP ha iha Δ ξ hΔ hξ.
    apply : T_Abs; eauto.
    move : ihP(hΔ) (hξ); repeat move/[apply]. move/Bind_Inv.
    hauto lq:on rew:off ctrs:Wff,Wt use:renaming_up.
  - move => *. apply : T_App'; eauto. by asimpl.
  - move => Γ a A b B i hA ihA hB ihB hS ihS Δ ξ hξ hΔ.
    eapply T_Pair' with (U := ren_PTm ξ (subst_PTm (scons a VarPTm) B));eauto. by asimpl.
  - move => Γ a A B ha iha Δ ξ hΔ hξ. apply : T_Proj2'; eauto. by asimpl.
  - move => Γ P a b c i hP ihP ha iha hb ihb hc ihc Δ ξ hΔ hξ.
    move => [:hP].
    apply : T_Ind'; eauto. by asimpl.
    abstract :hP. apply ihP. by eauto using Wff_Cons', T_Nat'.
    hauto l:on use:renaming_up.
    set x := subst_PTm _ _. have -> : x = ren_PTm ξ (subst_PTm (scons PZero VarPTm) P) by subst x; asimpl.
    by subst x; eauto.
    set Ξ := cons _ _.
    have  hΞ : ⊢ Ξ. subst Ξ.
    apply : Wff_Cons'; eauto. apply hP.
    move /(_ Ξ (upRen_PTm_PTm (upRen_PTm_PTm ξ)) hΞ) : ihc.
    set Ξ' := (cons _ _) .
    have : renaming_ok Ξ Ξ' (upRen_PTm_PTm (upRen_PTm_PTm ξ)).
    by do 2 apply renaming_up.
    move /[swap] /[apply].
    by asimpl.
  - hauto lq:on ctrs:Wt,LEq.
  - hauto lq:on ctrs:Eq.
  - hauto lq:on rew:off use:E_Bind', Wff_Cons, renaming_up.
  - move => *. apply : E_App'; eauto. by asimpl.
  - move => *. apply : E_Proj2'; eauto. by asimpl.
  - move => Γ P0 P1 a0 a1 b0 b1 c0 c1 i hP0 ihP0 hP ihP ha iha hb ihb hc ihc.
    move => Δ ξ hΔ hξ [:hP' hren].
    apply E_IndCong' with (i := i); eauto with wt.
    by asimpl.
    apply ihP0.
    abstract : hP'.
    qauto l:on use:renaming_up, Wff_Cons', T_Nat'.
    abstract : hren.
    qauto l:on use:renaming_up, Wff_Cons', T_Nat'.
    apply ihP; eauto with wt.
    move : ihb (hΔ) (hξ); do! move/[apply]. by asimpl.
    set Ξ := cons _ _.
    have hΞ : ⊢ Ξ.
    subst Ξ. apply :Wff_Cons'; eauto.
    move /(_ Ξ  (upRen_PTm_PTm (upRen_PTm_PTm ξ)) hΞ) : ihc.
    move /(_ ltac:(qauto l:on use:renaming_up)).
    suff : ren_PTm (upRen_PTm_PTm (upRen_PTm_PTm ξ))
      (ren_PTm shift
         (subst_PTm
            (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift)) P0)) = ren_PTm shift
      (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift))
         (ren_PTm (upRen_PTm_PTm ξ) P0)) by scongruence.
    by asimpl.
  - qauto l:on ctrs:Eq, LEq.
  - move => Γ a b A B i hP ihP hb ihb ha iha Δ ξ hΔ hξ.
    move : ihP (hξ) (hΔ). repeat move/[apply].
    move /Bind_Inv.
    move => [j][h0][h1]h2.
    have ? : Δ ⊢ PBind PPi (ren_PTm ξ A) (ren_PTm (upRen_PTm_PTm ξ) B) ∈ PUniv j by qauto l:on ctrs:Wt.
    apply : E_AppAbs'; eauto. by asimpl. by asimpl.
    hauto lq:on ctrs:Wff use:renaming_up.
  - move => Γ a b A B i hP ihP ha iha hb ihb Δ ξ hΔ hξ.
    move : {hP} ihP (hξ) (hΔ). repeat move/[apply].
    move /Bind_Inv => [i0][h0][h1]h2.
    have ? : Δ ⊢ PBind PSig (ren_PTm ξ A) (ren_PTm (upRen_PTm_PTm ξ) B) ∈ PUniv i0 by qauto l:on ctrs:Wt.
    apply : E_ProjPair1; eauto.
    move : ihb hξ hΔ. repeat move/[apply]. by asimpl.
  - move => Γ a b A B i hP ihP ha iha hb ihb Δ ξ hΔ hξ.
    apply : E_ProjPair2'; eauto. by asimpl.
    move : ihb hξ hΔ; repeat move/[apply]. by asimpl.
  - move => Γ P i b c hP ihP hb ihb hc ihc Δ ξ hΔ hξ.
    apply E_IndZero' with (i := i); eauto. by asimpl.
    sauto lq:on use:Wff_Cons', T_Nat', renaming_up.
    move  /(_ Δ ξ hΔ) : ihb.
    asimpl. by apply.
    set Ξ := cons _ _.
    have hΞ : ⊢ Ξ by  sauto lq:on use:Wff_Cons', T_Nat', renaming_up.
    move /(_ Ξ  (upRen_PTm_PTm (upRen_PTm_PTm ξ)) hΞ) : ihc.
    set p := renaming_ok _ _ _.
    have : p. by do 2 apply renaming_up.
    move => /[swap]/[apply].
    suff : ren_PTm (upRen_PTm_PTm (upRen_PTm_PTm ξ))
      (ren_PTm shift
         (subst_PTm
            (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift)) P))= ren_PTm shift
      (subst_PTm (scons (PSuc (VarPTm var_zero)) (funcomp VarPTm shift))
         (ren_PTm (upRen_PTm_PTm ξ) P)) by scongruence.
    by asimpl.
  - move => Γ P a b c i hP ihP ha iha hb ihb hc ihc Δ ξ hΔ hξ.
    apply E_IndSuc' with (i := i). by asimpl. by asimpl.
    sauto lq:on use:Wff_Cons', T_Nat', renaming_up.
    by eauto with wt.
    move  /(_ Δ ξ hΔ) : ihb. asimpl. by apply.
    set Ξ := cons _ _.
    have hΞ : ⊢ Ξ by  sauto lq:on use:Wff_Cons', T_Nat', renaming_up.
    move /(_ Ξ  (upRen_PTm_PTm (upRen_PTm_PTm ξ)) hΞ) : ihc.
    move /(_ ltac:(by eauto using renaming_up)).
    by asimpl.
  - move => Γ a b A B i hPi ihPi ha iha hb ihb he0 ihe1 Δ ξ hΔ hξ.
    apply : E_FunExt; eauto. move : ihe1. asimpl. apply.
    hfcrush use:Bind_Inv.
    by apply renaming_up.
  - move => Γ a b A B i hPi ihPi ha iha hb ihb hL ihL hR ihR Δ ξ hΔ hξ.
    apply : E_PairExt; eauto. move : ihR. asimpl. by apply.
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

Definition morphing_ok Δ Γ (ρ : nat -> PTm) :=
  forall i A, lookup i Γ A -> Δ ⊢ ρ i ∈ subst_PTm ρ A.

Lemma morphing_ren Ξ Δ Γ
  (ρ : nat -> PTm) (ξ : nat -> nat) :
  ⊢ Ξ ->
  renaming_ok Ξ Δ ξ -> morphing_ok Δ Γ ρ ->
  morphing_ok Ξ Γ (funcomp (ren_PTm ξ) ρ).
Proof.
  move => hΞ hξ hρ i A.
  rewrite {1}/funcomp.
  have -> :
    subst_PTm (funcomp (ren_PTm ξ) ρ) A =
    ren_PTm ξ (subst_PTm ρ A) by asimpl.
  move => ?.  eapply renaming; eauto.
Qed.

Lemma morphing_ext Δ Γ (ρ : nat -> PTm) (a : PTm) (A : PTm)  :
  morphing_ok Δ Γ ρ ->
  Δ ⊢ a ∈ subst_PTm ρ A ->
  morphing_ok
    Δ (cons A Γ) (scons a ρ).
Proof.
  move => h ha i B.
  elim /lookup_inv => //=_.
  - move => A0 Γ0 ? [*]. subst.
    by asimpl.
  - move => i0 Γ0 A0 B0 h0 ? [*]. subst.
    asimpl. by apply h.
Qed.

Lemma renaming_wt : forall Γ (a A : PTm), Γ ⊢ a ∈ A -> forall Δ (ξ : nat -> nat), ⊢ Δ -> renaming_ok Δ Γ ξ -> Δ ⊢ ren_PTm ξ a ∈ ren_PTm ξ A.
Proof. sfirstorder use:renaming. Qed.

Lemma renaming_wt' : forall Δ Γ a A (ξ : nat -> nat) u U,
    u = ren_PTm ξ a -> U = ren_PTm ξ A ->
    Γ ⊢ a ∈ A -> ⊢ Δ ->
    renaming_ok Δ Γ ξ -> Δ ⊢ u ∈ U.
Proof. hauto use:renaming_wt. Qed.

Lemma morphing_up Γ Δ (ρ : nat -> PTm) (A : PTm) k :
  morphing_ok Γ Δ ρ ->
  Γ ⊢ subst_PTm ρ A ∈ PUniv k ->
  morphing_ok (cons (subst_PTm ρ A) Γ) (cons A Δ) (up_PTm_PTm ρ).
Proof.
  move => h h1 [:hp]. apply morphing_ext.
  rewrite /morphing_ok.
  move => i A0 hA0.
  apply : renaming_wt'; last by apply renaming_shift.
  rewrite /funcomp. reflexivity.
  2 : { eauto. }
  by asimpl.
  abstract : hp. qauto l:on ctrs:Wff use:wff_mutual.
  apply : T_Var;eauto. apply here'. by asimpl.
Qed.

Lemma weakening_wt : forall Γ (a A B : PTm) i,
    Γ ⊢ B ∈ PUniv i ->
    Γ ⊢ a ∈ A ->
    cons B Γ ⊢ ren_PTm shift a ∈ ren_PTm shift A.
Proof.
  move => Γ a A B i hB ha.
  apply : renaming_wt'; eauto.
  apply : Wff_Cons'; eauto.
  apply : renaming_shift; eauto.
Qed.

Lemma weakening_wt' : forall Γ (a A B : PTm) i U u,
    u = ren_PTm shift a ->
    U = ren_PTm shift A ->
    Γ ⊢ B ∈ PUniv i ->
    Γ ⊢ a ∈ A ->
    cons B Γ ⊢ u ∈ U.
Proof. move => > -> ->. apply weakening_wt. Qed.

Lemma morphing :
  (forall Γ, ⊢ Γ -> True) /\
    (forall Γ a A, Γ ⊢ a ∈ A -> forall Δ ρ, ⊢ Δ -> morphing_ok Δ Γ ρ ->
     Δ ⊢ subst_PTm ρ a ∈ subst_PTm ρ A) /\
    (forall Γ a b A, Γ ⊢ a ≡ b ∈ A -> forall Δ ρ, ⊢ Δ -> morphing_ok Δ Γ ρ ->
     Δ ⊢ subst_PTm ρ a ≡ subst_PTm ρ b ∈ subst_PTm ρ A) /\
    (forall Γ A B, Γ ⊢ A ≲ B -> forall Δ ρ, ⊢ Δ -> morphing_ok Δ Γ ρ ->
    Δ ⊢ subst_PTm ρ A ≲ subst_PTm ρ B).
Proof.
  apply wt_mutual => //=.
  - hauto l:on unfold:morphing_ok.
  - hauto lq:on use:morphing_up, Wff_Cons', T_Bind.
  - move => Γ a A B i hP ihP ha iha Δ ρ hΔ hρ.
    move : ihP (hΔ) (hρ); repeat move/[apply].
    move /Bind_Inv => [j][h0][h1]h2. move {hP}.
    have ? : Δ ⊢ PBind PPi (subst_PTm ρ A) (subst_PTm (up_PTm_PTm ρ) B) ∈ PUniv i by hauto lq:on ctrs:Wt.
    apply : T_Abs; eauto.
    apply : iha.
    hauto lq:on use:Wff_Cons', Bind_Inv.
    apply : morphing_up; eauto.
  - move => *; apply : T_App'; eauto; by asimpl.
  - move => Γ a A b B i hA ihA hB ihB hS ihS Δ ρ hρ hΔ.
    eapply T_Pair' with (U := subst_PTm ρ (subst_PTm (scons a VarPTm) B));eauto. by asimpl.
  - hauto lq:on use:T_Proj1.
  - move => *. apply : T_Proj2'; eauto. by asimpl.
  - hauto lq:on ctrs:Wt,LEq.
  - qauto l:on ctrs:Wt.
  - qauto l:on ctrs:Wt.
  - qauto l:on ctrs:Wt.
  - move => Γ P a b c i hP ihP ha iha hb ihb hc ihc Δ ξ hΔ hξ.
    have  hξ' : morphing_ok (cons PNat Δ) (cons PNat Γ) (up_PTm_PTm ξ).
    move /morphing_up : hξ.  move /(_ PNat 0).
    apply. by apply T_Nat.
    move => [:hP].
    apply : T_Ind'; eauto. by asimpl.
    abstract :hP. apply ihP. by eauto using Wff_Cons', T_Nat'.
    move /morphing_up : hξ.  move /(_ PNat 0).
    apply. by apply T_Nat.
    move : ihb hξ hΔ; do!move/[apply]. by asimpl.
    set Ξ := cons _ _.
    have  hΞ : ⊢ Ξ. subst Ξ.
    apply : Wff_Cons'; eauto. apply hP.
    move /(_ Ξ (up_PTm_PTm (up_PTm_PTm ξ)) hΞ) : ihc.
    set Ξ' := (cons _ _) .
    have : morphing_ok Ξ Ξ' (up_PTm_PTm (up_PTm_PTm ξ)).
    eapply morphing_up; eauto. apply hP.
    move /[swap]/[apply].
    set x := (x in _ ⊢ _ ∈ x).
    set y := (y in _ -> _ ⊢ _ ∈ y).
    suff : x = y by scongruence.
    subst x y. asimpl. substify. by asimpl.
  - qauto l:on ctrs:Wt.
  - hauto lq:on ctrs:Eq.
  - hauto lq:on ctrs:Eq.
  - hauto lq:on ctrs:Eq.
  - hauto lq:on rew:off use:E_Bind', Wff_Cons, morphing_up.
  - move => *. apply : E_App'; eauto. by asimpl.
  - hauto q:on ctrs:Eq.
  - move => *. apply : E_Proj2'; eauto. by asimpl.
  - move => Γ P0 P1 a0 a1 b0 b1 c0 c1 i hP0 ihP0 hP ihP ha iha hb ihb hc ihc.
    move => Δ ξ hΔ hξ.
    have  hξ' : morphing_ok (cons PNat Δ)
                   (cons PNat Γ) (up_PTm_PTm ξ).
    move /morphing_up : hξ.  move /(_ PNat 0).
    apply. by apply T_Nat.
    move => [:hP'].
    apply E_IndCong' with (i := i).
    by asimpl.
    abstract : hP'.
    qauto l:on use:morphing_up, Wff_Cons', T_Nat'.
    qauto l:on use:renaming_up, Wff_Cons', T_Nat'.
    by eauto with wt.
    move : ihb (hΔ) (hξ); do! move/[apply]. by asimpl.
    set Ξ := cons _ _.
    have hΞ : ⊢ Ξ.
    subst Ξ. apply :Wff_Cons'; eauto. apply hP'.
    move /(_ Ξ  (up_PTm_PTm (up_PTm_PTm ξ)) hΞ) : ihc.
    move /(_ ltac:(qauto l:on use:morphing_up)).
    asimpl. substify. by asimpl.
  - eauto with wt.
  - qauto l:on ctrs:Eq, LEq.
  - move => Γ a b A B i hP ihP hb ihb ha iha Δ ρ hΔ hρ.
    move : ihP (hρ) (hΔ). repeat move/[apply].
    move /Bind_Inv.
    move => [j][h0][h1]h2.
    have ? : Δ ⊢ PBind PPi (subst_PTm ρ A) (subst_PTm (up_PTm_PTm ρ) B) ∈ PUniv j by qauto l:on ctrs:Wt.
    apply : E_AppAbs'; eauto. by asimpl. by asimpl.
    hauto lq:on ctrs:Wff use:morphing_up.
  - move => Γ a b A B i hP ihP ha iha hb ihb Δ ρ hΔ hρ.
    move : {hP} ihP (hρ) (hΔ). repeat move/[apply].
    move /Bind_Inv => [i0][h0][h1]h2.
    have ? : Δ ⊢ PBind PSig (subst_PTm ρ A) (subst_PTm (up_PTm_PTm ρ) B) ∈ PUniv i0 by qauto l:on ctrs:Wt.
    apply : E_ProjPair1; eauto.
    move : ihb hρ hΔ. repeat move/[apply]. by asimpl.
  - move => Γ a b A B i hP ihP ha iha hb ihb Δ ρ hΔ hρ.
    apply : E_ProjPair2'; eauto. by asimpl.
    move : ihb hρ hΔ; repeat move/[apply]. by asimpl.
  - move => Γ P i b c hP ihP hb ihb hc ihc Δ ξ hΔ hξ.
    have  hξ' : morphing_ok (cons PNat Δ)(cons PNat Γ) (up_PTm_PTm ξ).
    move /morphing_up : hξ.  move /(_ PNat 0).
    apply. by apply T_Nat.
    apply E_IndZero' with (i := i); eauto. by asimpl.
    qauto l:on use:Wff_Cons', T_Nat', renaming_up.
    move  /(_ Δ ξ hΔ) : ihb.
    asimpl. by apply.
    set Ξ := cons _ _.
    have hΞ : ⊢ Ξ by  qauto l:on use:Wff_Cons', T_Nat', renaming_up.
    move /(_ Ξ  (up_PTm_PTm (up_PTm_PTm ξ)) hΞ) : ihc.
    move /(_ ltac:(sauto lq:on use:morphing_up)).
    asimpl. substify. by asimpl.
  - move => Γ P a b c i hP ihP ha iha hb ihb hc ihc Δ ξ hΔ hξ.
    have  hξ' : morphing_ok (cons PNat Δ) (cons PNat Γ) (up_PTm_PTm ξ).
    move /morphing_up : hξ.  move /(_ PNat 0).
    apply. by apply T_Nat'.
    apply E_IndSuc' with (i := i). by asimpl. by asimpl.
    qauto l:on use:Wff_Cons', T_Nat', renaming_up.
    by eauto with wt.
    move  /(_ Δ ξ hΔ) : ihb. asimpl. by apply.
    set Ξ := cons _ _.
    have hΞ : ⊢ Ξ by  qauto l:on use:Wff_Cons', T_Nat', renaming_up.
    move /(_ Ξ  (up_PTm_PTm (up_PTm_PTm ξ)) hΞ) : ihc.
    move /(_ ltac:(sauto l:on use:morphing_up)).
    asimpl. substify. by asimpl.
  - move => Γ a b A B i hPi ihPi ha iha hb ihb he0 ihe1 Δ ξ hΔ hξ.
    move  : ihPi (hΔ) (hξ); repeat move/[apply]. move /[dup] /Bind_Inv => ihPi ?.
    decompose [and ex] ihPi.
    apply : E_FunExt; eauto. move : ihe1. asimpl. apply.
    by eauto with wt.
    by eauto using morphing_up with wt.
  - move => Γ a b A B i hPi ihPi ha iha hb ihb hL ihL hR ihR Δ ξ hΔ hξ.
    apply : E_PairExt; eauto. move : ihR. asimpl. by apply.
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

Lemma morphing_wt : forall Γ (a A : PTm ), Γ ⊢ a ∈ A -> forall Δ (ρ : nat -> PTm), ⊢ Δ -> morphing_ok Δ Γ ρ -> Δ ⊢ subst_PTm ρ a ∈ subst_PTm ρ A.
Proof. sfirstorder use:morphing. Qed.

Lemma morphing_wt' : forall Δ Γ a A (ρ : nat -> PTm) u U,
    u = subst_PTm ρ a -> U = subst_PTm ρ A ->
    Γ ⊢ a ∈ A -> ⊢ Δ ->
    morphing_ok Δ Γ ρ -> Δ ⊢ u ∈ U.
Proof. hauto use:morphing_wt. Qed.

Lemma morphing_id : forall Γ, ⊢ Γ -> morphing_ok Γ Γ VarPTm.
Proof.
  rewrite /morphing_ok => Γ hΓ i. asimpl.
  eauto using T_Var.
Qed.

Lemma substing_wt : forall Γ (a : PTm) (b A : PTm) B,
    (cons A Γ) ⊢ a ∈ B ->
    Γ ⊢ b ∈ A ->
    Γ ⊢ subst_PTm (scons b VarPTm) a ∈ subst_PTm (scons b VarPTm) B.
Proof.
  move => Γ a b A B ha hb [:hΓ]. apply : morphing_wt; eauto.
  abstract : hΓ. sfirstorder use:wff_mutual.
  apply morphing_ext; last by asimpl.
  by apply morphing_id.
Qed.

(* Could generalize to all equal contexts *)
Lemma ctx_eq_subst_one (A0 A1 : PTm) i j Γ a A :
  (cons A0 Γ) ⊢ a ∈ A ->
  Γ ⊢ A0 ∈ PUniv i ->
  Γ ⊢ A1 ∈ PUniv j ->
  Γ ⊢ A1 ≲ A0 ->
  (cons A1 Γ) ⊢ a ∈ A.
Proof.
  move => h0 h1 h2 h3.
  replace a with (subst_PTm VarPTm a); last by asimpl.
  replace A with (subst_PTm VarPTm A); last by asimpl.
  have ? : ⊢ Γ by sfirstorder use:wff_mutual.
  apply : morphing_wt; eauto.
  apply : Wff_Cons'; eauto.
  move => k A2. elim/lookup_inv => //=_; cycle 1.
  - move => i0 Γ0 A3 B hi ? [*]. subst.
    asimpl.
    eapply weakening_wt' with (a := VarPTm i0);eauto using T_Var.
    by substify.
  - move => A3 Γ0 ? [*]. subst.
    move => [:hΓ'].
    apply : T_Conv.
    apply T_Var.
    abstract : hΓ'.
    eauto using Wff_Cons'. apply here.
    asimpl. renamify.
    eapply renaming; eauto.
    apply : renaming_shift; eauto.
Qed.

Lemma bind_inst Γ p (A : PTm) B i a0 a1 :
  Γ ⊢ PBind p A B ∈ PUniv i ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ subst_PTm (scons a0 VarPTm) B ≲ subst_PTm (scons a1 VarPTm) B.
Proof.
  move => h h0.
  have {}h : Γ ⊢ PBind p A B ≲ PBind p A B by eauto using E_Refl, Su_Eq.
  case : p h => //=; hauto l:on use:Su_Pi_Proj2, Su_Sig_Proj2.
Qed.

Lemma Cumulativity Γ (a : PTm ) i j :
  i <= j ->
  Γ ⊢ a ∈ PUniv i ->
  Γ ⊢ a ∈ PUniv j.
Proof.
  move => h0 h1. apply : T_Conv; eauto.
  apply Su_Univ => //=.
  sfirstorder use:wff_mutual.
Qed.

Lemma T_Bind' Γ i j p (A : PTm ) (B : PTm) :
  Γ ⊢ A ∈ PUniv i ->
  (cons A Γ) ⊢ B ∈ PUniv j ->
  Γ ⊢ PBind p A B ∈ PUniv (max i j).
Proof.
  move => h0 h1.
  have [*] : i <= max i j /\ j <= max i j by lia.
  qauto l:on ctrs:Wt use:Cumulativity.
Qed.

Hint Resolve T_Bind' : wt.

Lemma regularity :
  (forall Γ, ⊢ Γ -> forall i A, lookup i Γ A -> exists j, Γ ⊢ A ∈ PUniv j) /\
    (forall Γ a A, Γ ⊢ a ∈ A -> exists i, Γ ⊢ A ∈ PUniv i)  /\
    (forall Γ a b A, Γ ⊢ a ≡ b ∈ A -> Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A /\ exists i, Γ ⊢ A ∈ PUniv i) /\
    (forall Γ A B, Γ ⊢ A ≲ B -> exists i, Γ ⊢ A ∈ PUniv i /\ Γ ⊢ B ∈ PUniv i).
Proof.
  apply wt_mutual => //=; eauto with wt.
  - move => i A. elim/lookup_inv => //=_.
  - move => Γ A i hΓ ihΓ hA _ j A0.
    elim /lookup_inv => //=_; cycle 1.
    + move => i0 Γ0 A1 B + ? [*]. subst.
      move : ihΓ => /[apply]. move => [j hA1].
      exists j. apply : renaming_wt' => //=; eauto using renaming_shift. done.
      apply : Wff_Cons'; eauto.
    + move => A1 Γ0 ? [*]. subst.
      exists i. apply : renaming_wt'; eauto. reflexivity.
      econstructor; eauto.
      apply : renaming_shift; eauto.
  - move => Γ b a A B hb [i ihb] ha [j iha].
    move /Bind_Inv : ihb => [k][h0][h1]h2.
    move : substing_wt ha h1; repeat move/[apply].
    move => h. exists k.
    move : h. by asimpl.
  - hauto lq:on use:Bind_Inv.
  - move => Γ a A B ha [i /Bind_Inv[j][h0][h1]h2].
    exists j. have : Γ ⊢ PProj PL a ∈ A by qauto use:T_Proj1.
    move : substing_wt h1; repeat move/[apply].
    by asimpl.
  - move => Γ P a b c i + ? + *. clear. move => h ha. exists i.
    hauto lq:on use:substing_wt.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - move => Γ i p A0 A1 B0 B1 hΓ ihΓ hA0
             [i0 ihA0] hA [ihA [ihA' [i1 ihA'']]].
    repeat split => //=.
    qauto use:T_Bind.
    apply T_Bind; eauto.
    sfirstorder.
    apply : ctx_eq_subst_one; eauto using Su_Eq, E_Symmetric.
    hauto lq:on.
  - move => n i b0 b1 a0 a1 A B hP _ hb [ihb0 [ihb1 [i0 ihb2]]]
             ha [iha0 [iha1 [i1 iha2]]].
    repeat split.
    qauto use:T_App.
    apply : T_Conv; eauto.
    qauto use:T_App.
    move /E_Symmetric in ha.
    by eauto using bind_inst.
    hauto lq:on ctrs:Wt,Eq,LEq lq:on use:Bind_Inv, substing_wt.
  - hauto lq:on use:Bind_Inv db:wt.
  - move => Γ i a b A B hS _ hab [iha][ihb][j]ihs.
    repeat split => //=; eauto with wt.
    apply : T_Conv; eauto with wt.
    move /E_Symmetric /E_Proj1 in hab.
    eauto using bind_inst.
    move /T_Proj1 in iha.
    hauto lq:on ctrs:Wt,Eq,LEq use:Bind_Inv, substing_wt.
  - move => Γ P0 P1 a0 a1 b0 b1 c0 c1 i _ _ hPE [hP0 [hP1 _]] hae [ha0 [ha1 _]] _ [hb0 [hb1 hb2]] _ [hc0 [hc1 [j hc2]]].
    have wfΓ : ⊢ Γ by hauto use:wff_mutual.
    have wfΓ' : ⊢ (PNat :: Γ) by qauto use:Wff_Cons', T_Nat'.
    repeat split. by eauto using T_Ind.
    apply : T_Conv. apply : T_Ind; eauto.
    apply : T_Conv; eauto.
    eapply morphing; by eauto using Su_Eq, morphing_ext, morphing_id with wt.
    apply : T_Conv.  apply : ctx_eq_subst_one; eauto.
    by eauto using Su_Eq, E_Symmetric.
    eapply renaming; eauto.
    eapply morphing. apply : Su_Eq. apply hPE. apply wfΓ'.
    apply morphing_ext.
    replace (funcomp VarPTm shift) with (funcomp (@ren_PTm shift) VarPTm); last by asimpl.
    apply : morphing_ren; eauto using morphing_id, renaming_shift.
    apply T_Suc. apply T_Var=>//. apply here. apply : Wff_Cons'; eauto using T_Nat'.
    apply renaming_shift.
    have /E_Symmetric /Su_Eq : Γ ⊢ PBind PSig PNat P0 ≡ PBind PSig PNat P1 ∈ PUniv i by eauto with wt.
    move /E_Symmetric in hae.
    by eauto using Su_Sig_Proj2.
    sauto lq:on use:substing_wt.
  - hauto lq:on ctrs:Wt.
  - hauto lq:on ctrs:Wt.
  - hauto q:on use:substing_wt db:wt.
  - hauto l:on use:bind_inst db:wt.
  - move => Γ P i b c hP _ hb _ hc _.
    have ? : ⊢ Γ by hauto use:wff_mutual.
    repeat split=>//.
    by eauto with wt.
    sauto lq:on use:substing_wt.
  - move => Γ P a b c i hP _ ha _ hb _ hc _.
    have ? : ⊢ Γ by hauto use:wff_mutual.
    repeat split=>//.
    apply : T_Ind; eauto with wt.
    set Ξ := (X in X ⊢ _ ∈ _) in hc.
    have : morphing_ok Γ Ξ (scons (PInd P a b c) (scons a VarPTm)).
    apply morphing_ext. apply morphing_ext. by apply morphing_id.
    by eauto. by eauto with wt.
    subst Ξ.
    move : morphing_wt hc; repeat move/[apply]. asimpl. by apply.
    sauto lq:on use:substing_wt.
  - move => Γ A B C hA [i [ihA0 ihA1]] hC [j [ihC0 ihC1]].
    have ? : ⊢ Γ by sfirstorder use:wff_mutual.
    exists (max i j).
    have [? ?] : i <= Nat.max i j /\ j <= Nat.max i j by lia.
    qauto l:on use:T_Conv, Su_Univ.
  - move => Γ i j hΓ *. exists (S (max i j)).
    have [? ?] : S i <= S (Nat.max i j) /\ S j <= S (Nat.max i j) by lia.
    hauto lq:on ctrs:Wt,LEq.
  - move => Γ A0 A1 B0 B1 i hA0 _ hA1 [i0][ih0]ih1 hB[j0][ihB0]ihB1.
    exists (max i0 j0).
    split; eauto with wt.
    apply T_Bind'; eauto.
    sfirstorder use:ctx_eq_subst_one.
  - move => n A0 A1 B0 B1 i hA1 _ hA0 [i0][ihA0]ihA1 hB[i1][ihB0]ihB1.
    exists (max i0 i1). repeat split; eauto with wt.
    apply T_Bind'; eauto.
    sfirstorder use:ctx_eq_subst_one.
  - sfirstorder.
  - move => Γ A0 A1 B0 B1 _ [i][ih0 ih1].
    move /Bind_Inv : ih0 => [i0][h _].
    move /Bind_Inv : ih1 => [i1][h' _].
    exists (max i0 i1).
    have [? ?] : i0 <= Nat.max i0 i1 /\ i1 <= Nat.max i0 i1 by lia.
    eauto using Cumulativity.
  - move => Γ A0 A1 B0 B1 _ [i][ih0 ih1].
    move /Bind_Inv : ih0 => [i0][h _].
    move /Bind_Inv : ih1 => [i1][h' _].
    exists (max i0 i1).
    have [? ?] : i0 <= Nat.max i0 i1 /\ i1 <= Nat.max i0 i1 by lia.
    eauto using Cumulativity.
  - move => Γ a0 a1 A0 A1 B0 B1 /Su_Pi_Proj1 hA1.
    move => [i][ihP0]ihP1.
    move => ha [iha0][iha1][j]ihA1.
    move /Bind_Inv :ihP0 => [i0][ih0][ih0' _].
    move /Bind_Inv :ihP1 => [i1][ih1][ih1' _].
    have [*] : i0 <= max i0 i1 /\ i1 <= max i0 i1 by lia.
    exists (max i0 i1).
    split.
    + apply Cumulativity with (i := i0); eauto.
      have : Γ ⊢ a0 ∈ A0 by eauto using T_Conv.
      move : substing_wt ih0';repeat move/[apply]. by asimpl.
    + apply Cumulativity with (i := i1); eauto.
      move : substing_wt ih1' iha1;repeat move/[apply]. by asimpl.
  - move => Γ a0 a1 A0 A1 B0 B1 /Su_Sig_Proj1 hA1.
    move => [i][ihP0]ihP1.
    move => ha [iha0][iha1][j]ihA1.
    move /Bind_Inv :ihP0 => [i0][ih0][ih0' _].
    move /Bind_Inv :ihP1 => [i1][ih1][ih1' _].
    have [*] : i0 <= max i0 i1 /\ i1 <= max i0 i1 by lia.
    exists (max i0 i1).
    split.
    + apply Cumulativity with (i := i0); eauto.
      move : substing_wt iha0 ih0';repeat move/[apply]. by asimpl.
    + apply Cumulativity with (i := i1); eauto.
      have : Γ ⊢ a1 ∈ A1 by eauto using T_Conv.
      move : substing_wt ih1';repeat move/[apply]. by asimpl.
      Unshelve. all: exact 0.
Qed.

Lemma Var_Inv Γ (i : nat) A :
  Γ ⊢ VarPTm i ∈ A ->
  ⊢ Γ /\ exists B, lookup i Γ B /\ Γ ⊢ B ≲ A.
Proof.
  move E : (VarPTm i) => u hu.
  move : i E.
  elim : Γ u A / hu=>//=.
  - move => i Γ A hΓ hi i0 [*]. subst.
    split => //.
    exists A. split => //.
    have h : Γ ⊢ VarPTm i ∈ A by eauto using T_Var.
    eapply regularity in h.
    move : h => [i0]?.
    apply : Su_Eq. apply E_Refl; eassumption.
  - sfirstorder use:Su_Transitive.
Qed.

Lemma renaming_su' : forall Δ Γ ξ (A B : PTm) u U ,
    u = ren_PTm ξ A ->
    U = ren_PTm ξ B ->
    Γ ⊢ A ≲ B ->
    ⊢ Δ -> renaming_ok Δ Γ ξ ->
    Δ ⊢ u ≲ U.
Proof. move => > -> ->. hauto l:on use:renaming. Qed.

Lemma weakening_su : forall Γ (A0 A1 B : PTm) i,
    Γ ⊢ B ∈ PUniv i ->
    Γ ⊢ A0 ≲ A1 ->
    (cons B Γ) ⊢ ren_PTm shift A0 ≲ ren_PTm shift A1.
Proof.
  move => Γ A0 A1 B i hB hlt.
  apply : renaming_su'; eauto.
  apply : Wff_Cons'; eauto.
  apply : renaming_shift; eauto.
Qed.

Lemma regularity_sub0 : forall Γ (A B : PTm), Γ ⊢ A ≲ B -> exists i, Γ ⊢ A ∈ PUniv i.
Proof. hauto lq:on use:regularity. Qed.

Lemma Su_Pi_Proj2_Var Γ (A0 A1 : PTm) B0 B1 :
  Γ ⊢ PBind PPi A0 B0 ≲ PBind PPi A1 B1 ->
  cons A1 Γ ⊢ B0 ≲ B1.
Proof.
  move => h.
  have /Su_Pi_Proj1 h1 := h.
  have /regularity_sub0 [i h2] := h1.
  move /weakening_su : (h) h2. move => /[apply].
  move => h2.
  apply : Su_Pi_Proj2'; try eassumption; rewrite -?/ren_PTm; cycle 2.
  apply E_Refl. apply T_Var with (i := var_zero); eauto.
  sfirstorder use:wff_mutual.
  apply here.
  by asimpl; rewrite subst_scons_id.
  by asimpl; rewrite subst_scons_id.
Qed.

Lemma Su_Sig_Proj2_Var Γ (A0 A1 : PTm) B0 B1 :
  Γ ⊢ PBind PSig A0 B0 ≲ PBind PSig A1 B1 ->
  (cons A0 Γ) ⊢ B0 ≲ B1.
Proof.
  move => h.
  have /Su_Sig_Proj1 h1 := h.
  have /regularity_sub0 [i h2] := h1.
  move /weakening_su : (h) h2. move => /[apply].
  move => h2.
  apply : Su_Sig_Proj2'; try eassumption; rewrite -?/ren_PTm; cycle 2.
  apply E_Refl. apply T_Var with (i := var_zero); eauto.
  sfirstorder use:wff_mutual.
  apply here.
  by asimpl; rewrite subst_scons_id.
  by asimpl; rewrite subst_scons_id.
Qed.
