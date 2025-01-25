From Ltac2 Require Ltac2.
Import Ltac2.Notations.
Import Ltac2.Control.
Require Import ssreflect ssrbool.
Require Import FunInd.
Require Import Arith.Wf_nat.
Require Import Psatz.
From stdpp Require Import relations (rtc (..), rtc_once, rtc_r).
From Hammer Require Import Tactics.
Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.

Ltac2 spec_refl () :=
  List.iter
    (fun a => match a with
           | (i, _, _) =>
               let h := Control.hyp i in
               try (specialize $h with (1 := eq_refl))
           end)  (Control.hyps ()).

Ltac spec_refl := ltac2:(spec_refl ()).

Module ERed.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Eta ***********************)
  | AppEta A a :
    R (PAbs A (PApp (ren_PTm shift a) (VarPTm var_zero))) a
  | PairEta a :
    R (PPair (PProj PL a) (PProj PR a)) a

  (*************** Congruence ********************)
  | AbsCong A a0 a1 :
    R a0 a1 ->
    R (PAbs A a0) (PAbs A a1)
  | AppCong0 a0 a1 b :
    R a0 a1 ->
    R (PApp a0 b) (PApp a1 b)
  | AppCong1 a b0 b1 :
    R b0 b1 ->
    R (PApp a b0) (PApp a b1)
  | PairCong0 a0 a1 b :
    R a0 a1 ->
    R (PPair a0 b) (PPair a1 b)
  | PairCong1 a b0 b1 :
    R b0 b1 ->
    R (PPair a b0) (PPair a b1)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1).

  Derive Dependent Inversion inv with (forall n (a b : PTm n), R a b) Sort Prop.

  Lemma AppEta' n A a (u : PTm n) :
    u = (PAbs A (PApp (ren_PTm shift a) (VarPTm var_zero))) ->
    R u a.
  Proof. move => ->. apply AppEta. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n A a m ξ /=.
    apply AppEta' with (A := A). by asimpl.
    all : qauto ctrs:R.
  Qed.

  Lemma substing n m (a : PTm n) b (ρ : fin n -> PTm m) :
    R a b ->
    R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    move => h. move : m ρ. elim : n a b / h => n.
    move => A a m ρ /=.
    apply AppEta' with (A := A); eauto. by asimpl.
    all : hauto ctrs:R inv:option use:renaming.
  Qed.

End ERed.

Module RRed.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Eta ***********************)
  | AppAbs A a b :
    R (PApp (PAbs A a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

  (*************** Congruence ********************)
  | AbsCong A a0 a1 :
    R a0 a1 ->
    R (PAbs A a0) (PAbs A a1)
  | AppCong0 a0 a1 b :
    R a0 a1 ->
    R (PApp a0 b) (PApp a1 b)
  | AppCong1 a b0 b1 :
    R b0 b1 ->
    R (PApp a b0) (PApp a b1)
  | PairCong0 a0 a1 b :
    R a0 a1 ->
    R (PPair a0 b) (PPair a1 b)
  | PairCong1 a b0 b1 :
    R b0 b1 ->
    R (PPair a b0) (PPair a b1)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1).

  Derive Dependent Inversion inv with (forall n (a b : PTm n), R a b) Sort Prop.
End RRed.

Inductive Wt {n} (Γ : fin n -> Ty) : PTm n -> Ty -> Prop :=
| T_Var i :
  Wt Γ (VarPTm i) (Γ i)
| T_Abs a A B :
  Wt (scons A Γ) a B ->
  Wt Γ (PAbs A a) (Fun A B)
| T_App b a A B :
  Wt Γ b (Fun A B) ->
  Wt Γ a A ->
  Wt Γ (PApp b a) B
| T_Pair a b A B :
  Wt Γ a A ->
  Wt Γ b B ->
  Wt Γ (PPair a b) (Prod A B)
| T_Proj p a A B :
  Wt Γ a (Prod A B) ->
  Wt Γ (PProj p a) (if p is PL then A else B).

Module Wt.
  Lemma renaming n m (Γ : fin n -> Ty) Δ (ξ : fin n -> fin m) a A :
    (forall i,  Γ i = Δ (ξ i)) ->
    Wt Γ a A ->
    Wt Δ (ren_PTm ξ a) A.
  Proof.
    move => + h. move : m Δ ξ. elim : n Γ a A / h; try hauto inv:option lq:on ctrs:Wt.
  Qed.

  Lemma antirenaming n m (Γ : fin n -> Ty) Δ (ξ : fin n -> fin m) a A :
    (forall i,  Γ i = Δ (ξ i)) ->
    Wt Δ (ren_PTm ξ a) A ->
    Wt Γ a A.
  Proof.
    move E : (ren_PTm ξ a) => u + h.
    move : n a ξ Γ E.
    elim : m Δ u A / h=> n /=.
    - hauto q:on ctrs:Wt inv:PTm.
    - move => Γ a A B ha iha m  []//= A0 p ξ Δ [? ?]. subst.
      hauto q:on inv:option ctrs:Wt.
    - move => Γ b a A B hb ihb ha iha m [] //=.
      move => p p0 ξ Δ [*]. subst.
      hauto lq:on rew:off ctrs:Wt.
    - move => Γ a b A B ha iha hb ihb m []//=.
      hauto lq:on ctrs:Wt.
    - move => Γ p a A B ha iha m []//=.
      move => p0 p1 ξ Δ [*]. subst.
      hauto lq:on rew:off ctrs:Wt.
  Qed.

  Local Lemma morphing_upren n m (Γ : fin n -> Ty) Δ
    (ρ : fin n -> PTm m) A :
    (forall i, Wt Δ (ρ i) (Γ i)) ->
    (forall i, Wt (scons A Δ) ((up_PTm_PTm ρ) i) ((scons A Γ) i)).
  Proof.
    sblast inv:option use:renaming.
  Qed.


  Lemma morphing n m (Γ : fin n -> Ty) Δ (ρ : fin n -> PTm m) a A:
    (forall i, Wt Δ (ρ i) (Γ i)) ->  Wt Γ a A -> Wt Δ (subst_PTm ρ a) A.
  Proof.
    move => + h. move : m Δ ρ;
      elim : n Γ a A /h;
    hauto lq:on use:morphing_upren ctrs:Wt.
  Qed.

  Lemma substing n (Γ : fin n -> Ty) a b A B:
    Wt (scons B Γ) a A ->
    Wt Γ b B ->
    Wt Γ (subst_PTm (scons b VarPTm) a) A.
  Proof.
    move => h0 h1. apply : morphing; eauto.
    hauto lq:on ctrs:Wt inv:option.
  Qed.

  Lemma preservation_beta n Γ a b A :
    @Wt n Γ a A ->
    RRed.R a b ->
    Wt Γ b A.
  Proof.
    move => + h0. move : Γ A.
    elim : n a b /h0=> n //=; hauto lq:on inv:Wt ctrs:Wt use:substing.
  Qed.

  Lemma typing_unique n Γ a A B :
    @Wt n Γ a A ->
    Wt Γ a B ->
    A = B.
  Proof.
    move => h. move : B.
    elim : n Γ a A /h=>//=; hauto lq:on rew:off ctrs:Wt inv:Wt.
  Qed.

  Lemma preservation_eta n Γ a b A :
    @Wt n Γ a A ->
    ERed.R a b ->
    Wt Γ b A.
  Proof.
    move => + h0. move : Γ A.
    elim : n a b /h0=> n //=; try qauto inv:Wt ctrs:Wt use:substing.
    - move => A a Γ ξ hA.
      inversion hA; subst.
      inversion H2; subst.
      inversion H4; subst.
      apply antirenaming with (Γ := Γ) in H1;
        sfirstorder use:typing_unique.
    - move => a Γ U.
      inversion 1; subst.
      inversion H2; subst.
      inversion H4; subst.
      suff : Prod A B0 = Prod A0 B by congruence.
      eauto using typing_unique.
    - hauto lq:on inv:Wt ctrs:Wt.
  Qed.
End Wt.


Lemma eta_postponement n Γ a b c A :
  @Wt n Γ a A ->
  ERed.R a b ->
  RRed.R b c ->
  exists d, rtc RRed.R a d /\ ERed.R d c.
Proof.
  move => + h.
  move : Γ c A.
  elim : n a b /h => //=.
  - move => n A a Γ c A0 hA0 ha.
    exists (PAbs A (PApp (ren_PTm shift c) (VarPTm var_zero))).
    split. admit.
    apply ERed.AppEta.
  - move => n a Γ c A ha ha0.
    exists (PPair (PProj PL c) (PProj PR c)).
    split. admit.
    apply ERed.PairEta.
  - move => n A a0 a1 ha iha Γ c A0 ha0.
    elim /RRed.inv => //= _.
    move => A1 a2 a3 ha' [*]. subst.
    inversion ha0; subst.
    move : iha H2 ha'. repeat move/[apply].
    move => [d [h0 h1]].
    exists (PAbs A d).
    split. admit.
    hauto lq:on ctrs:ERed.R.
  - move => n a0 a1 b ha iha Γ c A hab hab0.
    elim /RRed.inv : hab0 => //= _.
    move => A0 a2 b0 [*]. subst.
    + inversion ha; subst.
      * exists (subst_PTm (scons b VarPTm) a2).
        split.
        apply : rtc_l.
        apply RRed.AppAbs.
        asimpl.
        apply rtc_once. apply RRed.AppAbs.
        admit.
      * exfalso.
        move : hab. clear.
        hauto lq:on inv:Wt.
      * inversion hab; subst.
        exists (subst_PTm (scons b VarPTm) a1).
        split.
        apply rtc_once.
        apply RRed.AppAbs.
        admit.
    + move => a2 a3 b0 ha0 [*]. subst.
      have : exists Γ  A, @Wt n Γ a0 A by hauto lq:on inv:Wt.
      move => [Γ0 [A0] hA0].
      move : iha hA0 ha0. repeat move /[apply].
      move => [d [h0 h1]].
      exists (PApp d b).
      split. admit.
      hauto lq:on ctrs:ERed.R.
    + move => a2 b0 b1 hb [*]. subst.
      sauto lq:on.
  - move => n a b0 b1 hb ihb Γ c A hu hu'.
    elim /RRed.inv : hu' => //=_.
    + move => A0 a0 b2 [*]. subst.
      admit.
    + sauto lq:on.
    + move => a0 b2 b3 hb0 [*]. subst.
      have [? [? ]] : exists Γ  A, @Wt n Γ b0 A by hauto lq:on inv:Wt.
      move : ihb hb0. repeat move/[apply].
      move => [d [h0 h1]].
      exists (PApp a d).
      split. admit.
      sauto lq:on.
  - move => n a0 a1 b ha iha Γ u A hu.
    elim / RRed.inv => //= _.
    + move => a2 a3 b0 h [*]. subst.
      have [? [? ]] : exists Γ  A, @Wt n Γ a0 A by hauto lq:on inv:Wt.
      move : iha h. repeat move/[apply].
      move => [d [h0 h1]].
      exists (PPair d b).
      split. admit.
      sauto lq:on.
    + move => a2 b0 b1 h [*]. subst.
      sauto lq:on.
  - move => n a b0 b1 hb ihb Γ c A hu.
    elim / RRed.inv => //=_.
    move => a0 a1 b2 ha [*]. subst.
    + sauto lq:on.
    + move => a0 b2 b3 hb0 [*]. subst.
      have [? [? ]] : exists Γ  A, @Wt n Γ b0 A by hauto lq:on inv:Wt.
      move : ihb hb0. repeat move/[apply].
      move => [d [h0 h1]].
      exists (PPair a d).
      split. admit.
      sauto lq:on.
  - move => n p a0 a1 ha iha Γ u A hu.
    elim / RRed.inv => //=_.
    + move => p0 a2 b0 [*]. subst.
      inversion ha; subst.
      * exfalso.
        move : hu. clear. hauto q:on inv:Wt.
      * exists (match p with
                    | PL => a2
                    | PR => b0
           end).
        split. apply : rtc_l.
        apply RRed.ProjPair.
        apply rtc_once. clear.
        hauto lq:on use:RRed.ProjPair.
        admit.
      * eexists.
        split. apply rtc_once.
        apply RRed.ProjPair.
        admit.
      * eexists.
        split. apply rtc_once.
        apply RRed.ProjPair.
        admit.
    + move => p0 a2 a3 ha0 [*]. subst.
      have [? [? ]] : exists Γ  A, @Wt n Γ a0 A by hauto lq:on inv:Wt.
      move : iha ha0; repeat move/[apply].
      move => [d [h0 h1]].
      exists (PProj p d).
      split.
      admit.
      sauto lq:on.
Admitted.

(* Trying my best to not write C style module_funcname *)
Module Par.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (***************** Beta ***********************)
  | AppAbs a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0)  (subst_PTm (scons b1 VarPTm) a1)
  | AppPair a0 a1 b0 b1 c0 c1:
    R a0 a1 ->
    R b0 b1 ->
    R c0 c1 ->
    R (PApp (PPair a0 b0) c0) (PPair (PApp a1 c1) (PApp b1 c1))
  | ProjAbs p a0 a1 :
    R a0 a1 ->
    R (PProj p (PAbs a0)) (PAbs (PProj p a1))
  | ProjPair p a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) (if p is PL then a1 else b1)

  (****************** Eta ***********************)
  | AppEta a0 a1 :
    R a0 a1 ->
    R a0 (PAbs (PApp (ren_PTm shift a1) (VarPTm var_zero)))
  | PairEta a0 a1 :
    R a0 a1 ->
    R a0 (PPair (PProj PL a1) (PProj PR a1))

  (*************** Congruence ********************)
  | Var i : R (VarPTm i) (VarPTm i)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (PAbs a0) (PAbs a1)
  | AppCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp a0 b0) (PApp a1 b1)
  | PairCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PPair a0 b0) (PPair a1 b1)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1)
  | ConstCong k :
    R (PConst k) (PConst k)
  | Univ i :
    R (PUniv i) (PUniv i)
  | Bot :
    R PBot PBot.

  Lemma refl n (a : PTm n) : R a a.
    elim : n /a; hauto ctrs:R.
  Qed.

  Lemma AppAbs' n a0 a1 (b0 b1 t : PTm n) :
    t = subst_PTm (scons b1 VarPTm) a1 ->
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0) t.
  Proof. move => ->. apply AppAbs. Qed.

  Lemma ProjPair' n p (a0 a1 b0 b1 : PTm n) t :
    t = (if p is PL then a1 else b1) ->
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) t.
  Proof.  move => > ->. apply ProjPair. Qed.

  Lemma AppEta' n (a0 a1 b : PTm n) :
    b = (PAbs (PApp (ren_PTm shift a1) (VarPTm var_zero))) ->
    R a0 a1 ->
    R a0 b.
  Proof. move => ->; apply AppEta. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.
    move => *; apply : AppAbs'; eauto; by asimpl.
    all : match goal with
          | [ |- context[var_zero]] => move => *; apply : AppEta'; eauto; by asimpl
          | _ => qauto ctrs:R use:ProjPair'
          end.
  Qed.


  Lemma morphing n m (a b : PTm n) (ρ0 ρ1 : fin n -> PTm m) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    R a b -> R (subst_PTm ρ0 a) (subst_PTm ρ1 b).
  Proof.
    move => + h. move : m ρ0 ρ1. elim : n a b/h.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ρ0 ρ1 hρ /=.
      eapply AppAbs' with (a1 := subst_PTm (up_PTm_PTm ρ1) a1); eauto.
      by asimpl.
      hauto l:on use:renaming inv:option.
    - hauto lq:on rew:off ctrs:R.
    - hauto l:on inv:option use:renaming ctrs:R.
    - hauto lq:on use:ProjPair'.
    - move => n a0 a1 ha iha m ρ0 ρ1 hρ /=.
      apply : AppEta'; eauto. by asimpl.
    - hauto lq:on ctrs:R.
    - sfirstorder.
    - hauto l:on inv:option ctrs:R use:renaming.
    - hauto q:on ctrs:R.
    - qauto l:on ctrs:R.
    - qauto l:on ctrs:R.
    - hauto l:on inv:option ctrs:R use:renaming.
    - qauto l:on ctrs:R.
    - qauto l:on ctrs:R.
  Qed.

  Lemma substing n m (a b : PTm n) (ρ : fin n -> PTm m) :
    R a b -> R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof. hauto l:on use:morphing, refl. Qed.

  Lemma antirenaming n m (a : PTm n) (b : PTm m) (ξ : fin n -> fin m) :
    R (ren_PTm ξ a) b -> exists b0, R a b0 /\ ren_PTm ξ b0 = b.
  Proof.
    move E : (ren_PTm ξ a) => u h.
    move : n ξ a E. elim : m u b/h.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ξ []//=.
      move => c c0 [+ ?]. subst.
      case : c => //=.
      move => c [?]. subst.
      spec_refl.
      move : iha => [c1][ih0]?. subst.
      move : ihb => [c2][ih1]?. subst.
      eexists. split.
      apply AppAbs; eauto.
      by asimpl.
    - move => n a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc m ξ []//=.
      move => []//= t t0 t1 [*]. subst.
      spec_refl.
      move : iha => [? [*]].
      move : ihb => [? [*]].
      move : ihc => [? [*]].
      eexists. split.
      apply AppPair; hauto. subst.
      by asimpl.
    - move => n p a0 a1 ha iha m ξ []//= p0 []//= t [*]. subst.
      spec_refl. move : iha => [b0 [? ?]]. subst.
      eexists. split. apply ProjAbs; eauto. by asimpl.
    - move => n p a0 a1 b0 b1 ha iha hb ihb m ξ []//= p0 []//= t t0[*].
      subst. spec_refl.
      move : iha => [b0 [? ?]].
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by eauto using ProjPair.
      hauto q:on.
    - move => n a0 a1 ha iha m ξ a ?. subst.
      spec_refl. move : iha => [a0 [? ?]]. subst.
      eexists. split. apply AppEta; eauto.
      by asimpl.
    - move => n a0 a1 ha iha m ξ a ?. subst.
      spec_refl. move : iha => [b0 [? ?]]. subst.
      eexists. split. apply PairEta; eauto.
      by asimpl.
    - move => n i m ξ []//=.
      hauto l:on.
    - move => n a0 a1 ha iha m ξ []//= t [*]. subst.
      spec_refl.
      move  :iha => [b0 [? ?]]. subst.
      eexists. split. by apply AbsCong; eauto.
      done.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ξ []//= t t0 [*]. subst.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by apply AppCong; eauto.
      done.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ξ []//= t t0[*]. subst.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      move : ihb => [c0 [? ?]]. subst.
      eexists. split=>/=. by apply PairCong; eauto.
      done.
    - move => n p a0 a1 ha iha m ξ []//= p0 t [*]. subst.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      eexists. split. by apply ProjCong; eauto.
      done.
    - hauto q:on inv:PTm ctrs:R.
    - hauto q:on inv:PTm ctrs:R.
    - hauto q:on inv:PTm ctrs:R.
  Qed.

End Par.

Module Pars.
  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    rtc Par.R a b -> rtc Par.R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    induction 1; hauto lq:on ctrs:rtc use:Par.renaming.
  Qed.

  Lemma substing n m (a b : PTm n) (ρ : fin n -> PTm m) :
    rtc Par.R a b ->
    rtc Par.R (subst_PTm ρ a) (subst_PTm ρ b).
    induction 1; hauto l:on ctrs:rtc use:Par.substing.
  Qed.

  Lemma antirenaming n m (a : PTm n) (b : PTm m) (ξ : fin n -> fin m) :
    rtc Par.R (ren_PTm ξ a) b -> exists b0, rtc Par.R a b0 /\ ren_PTm ξ b0 = b.
  Proof.
    move E  :(ren_PTm ξ a) => u h.
    move : a E.
    elim : u b /h.
    - sfirstorder.
    - move => a b c h0 h1 ih1 a0 ?. subst.
      move /Par.antirenaming : h0.
      move => [b0 [h2 ?]]. subst.
      hauto lq:on rew:off ctrs:rtc.
  Qed.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:Par.R use:Par.refl.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma ProjCong n p (a0 a1 : PTm n) :
    rtc Par.R a0 a1 ->
    rtc Par.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    rtc Par.R a0 a1 ->
    rtc Par.R b0 b1 ->
    rtc Par.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    rtc Par.R a0 a1 ->
    rtc Par.R b0 b1 ->
    rtc Par.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma AbsCong n (a b : PTm (S n)) :
    rtc Par.R a b ->
    rtc Par.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

End Pars.

Definition var_or_const {n} (a : PTm n) :=
  match a with
  | VarPTm _ => true
  | PBot => true
  | _ => false
  end.


(***************** Beta rules only ***********************)
Module RPar.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (***************** Beta ***********************)
  | AppAbs a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0)  (subst_PTm (scons b1 VarPTm) a1)
  | AppPair a0 a1 b0 b1 c0 c1:
    R a0 a1 ->
    R b0 b1 ->
    R c0 c1 ->
    R (PApp (PPair a0 b0) c0) (PPair (PApp a1 c1) (PApp b1 c1))
  | ProjAbs p a0 a1 :
    R a0 a1 ->
    R (PProj p (PAbs a0)) (PAbs (PProj p a1))
  | ProjPair p a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) (if p is PL then a1 else b1)


  (*************** Congruence ********************)
  | Var i : R (VarPTm i) (VarPTm i)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (PAbs a0) (PAbs a1)
  | AppCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp a0 b0) (PApp a1 b1)
  | PairCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PPair a0 b0) (PPair a1 b1)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1)
  | ConstCong k :
    R (PConst k) (PConst k)
  | Univ i :
    R (PUniv i) (PUniv i)
  | Bot :
    R PBot PBot.

  Derive Dependent Inversion inv with (forall n (a b : PTm n), R a b) Sort Prop.

  Lemma refl n (a : PTm n) : R a a.
  Proof.
    induction a; hauto lq:on ctrs:R.
  Qed.

  Lemma AppAbs' n a0 a1 (b0 b1 t : PTm n) :
    t = subst_PTm (scons b1 VarPTm) a1 ->
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0) t.
  Proof. move => ->. apply AppAbs. Qed.

  Lemma ProjPair' n p (a0 a1 b0 b1 : PTm n) t :
    t = (if p is PL then a1 else b1) ->
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) t.
  Proof.  move => > ->. apply ProjPair. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.
    move => *; apply : AppAbs'; eauto; by asimpl.
    all : qauto ctrs:R use:ProjPair'.
  Qed.

  Lemma morphing_ren n m p (ρ0 ρ1 : fin n -> PTm m) (ξ : fin m -> fin p) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((funcomp (ren_PTm ξ) ρ0) i) ((funcomp (ren_PTm ξ) ρ1) i)).
  Proof. eauto using renaming. Qed.

  Lemma morphing_ext n m (ρ0 ρ1 : fin n -> PTm m) a b  :
    R a b ->
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((scons a ρ0) i) ((scons b ρ1) i)).
  Proof. hauto q:on inv:option. Qed.

  Lemma morphing_up n m (ρ0 ρ1 : fin n -> PTm m) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R (up_PTm_PTm ρ0 i) (up_PTm_PTm ρ1 i)).
  Proof. hauto l:on ctrs:R use:morphing_ext, morphing_ren unfold:up_PTm_PTm. Qed.

  Lemma morphing n m (a b : PTm n) (ρ0 ρ1 : fin n -> PTm m) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    R a b -> R (subst_PTm ρ0 a) (subst_PTm ρ1 b).
  Proof.
    move => + h. move : m ρ0 ρ1.
    elim : n a b /h.
    - move => *.
      apply : AppAbs'; eauto using morphing_up.
      by asimpl.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R use:ProjPair' use:morphing_up.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R.
  Qed.

  Lemma substing n m (a b : PTm n) (ρ : fin n -> PTm m) :
    R a b ->
    R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof. hauto l:on use:morphing, refl. Qed.

  Lemma cong n (a b : PTm (S n)) c d :
    R a b ->
    R c d ->
    R (subst_PTm (scons c VarPTm) a) (subst_PTm (scons d VarPTm) b).
  Proof.
    move => h0 h1. apply morphing => //=.
    qauto l:on ctrs:R inv:option.
  Qed.

  Lemma var_or_const_imp {n} (a b : PTm n) :
    var_or_const a ->
    a = b -> ~~ var_or_const b -> False.
  Proof.
    hauto lq:on inv:PTm.
  Qed.

  Lemma var_or_const_up n m (ρ : fin n -> PTm m) :
    (forall i, var_or_const (ρ i)) ->
    (forall i, var_or_const (up_PTm_PTm ρ i)).
  Proof.
    move => h /= [i|].
    - asimpl.
      move /(_ i) in h.
      rewrite /funcomp.
      move : (ρ i) h.
      case => //=.
    - sfirstorder.
  Qed.

  Local Ltac antiimp := qauto l:on use:var_or_const_imp.

  Lemma antirenaming n m (a : PTm n) (b : PTm m) (ρ : fin n -> PTm m) :
    (forall i, var_or_const (ρ i)) ->
    R (subst_PTm ρ a) b -> exists b0, R a b0 /\ subst_PTm ρ b0 = b.
  Proof.
    move E : (subst_PTm ρ a) => u hρ h.
    move : n ρ hρ a E. elim : m u b/h.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ρ hρ []//=;
               first by antiimp.
      move => c c0 [+ ?]. subst.
      case : c => //=; first by antiimp.
      move => c [?]. subst.
      spec_refl.
      have /var_or_const_up hρ' := hρ.
      move : iha hρ' => /[apply] iha.
      move : ihb hρ => /[apply] ihb.
      spec_refl.
      move : iha => [c1][ih0]?. subst.
      move : ihb => [c2][ih1]?. subst.
      eexists. split.
      apply AppAbs; eauto.
      by asimpl.
    - move => n a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc m ρ hρ.
      move => []//=;
               first by antiimp.
      move => []//=; first by antiimp.
      move => t t0 t1 [*]. subst.
      have  {}/iha := hρ => iha.
      have  {}/ihb := hρ => ihb.
      have  {}/ihc := hρ => ihc.
      spec_refl.
      move : iha => [? [*]].
      move : ihb => [? [*]].
      move : ihc => [? [*]].
      eexists. split.
      apply AppPair; hauto. subst.
      by asimpl.
    - move => n p a0 a1 ha iha m ρ hρ []//=;
               first by antiimp.
      move => p0 []//= t [*]; first by antiimp. subst.
      have  /var_or_const_up {}/iha  := hρ => iha.
      spec_refl. move : iha => [b0 [? ?]]. subst.
      eexists. split. apply ProjAbs; eauto. by asimpl.
    - move => n p a0 a1 b0 b1 ha iha hb ihb m ρ hρ []//=;
               first by antiimp.
      move => p0 []//=; first by antiimp. move => t t0[*].
      subst.
      have {}/iha := (hρ) => iha.
      have {}/ihb := (hρ) => ihb.
      spec_refl.
      move : iha => [b0 [? ?]].
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by eauto using ProjPair.
      hauto q:on.
    - move => n i m ρ hρ []//=.
      hauto l:on.
    - move => n a0 a1 ha iha m ρ hρ []//=; first by antiimp.
      move => t [*]. subst.
      have /var_or_const_up {}/iha := hρ => iha.
      spec_refl.
      move  :iha => [b0 [? ?]]. subst.
      eexists. split. by apply AbsCong; eauto.
      by asimpl.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ρ hρ []//=;
               first by antiimp.
      move => t t0 [*]. subst.
      have {}/iha := (hρ) => iha.
      have {}/ihb := (hρ) => ihb.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by apply AppCong; eauto.
      done.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ρ hρ []//=;
               first by antiimp.
      move => t t0[*]. subst.
      have {}/iha := (hρ) => iha.
      have {}/ihb := (hρ) => ihb.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by apply PairCong; eauto.
      by asimpl.
    - move => n p a0 a1 ha iha m ρ hρ []//=;
               first by antiimp.
      move => p0 t [*]. subst.
      have {}/iha := (hρ) => iha.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      eexists. split. apply ProjCong; eauto. reflexivity.
    - hauto q:on ctrs:R inv:PTm.
    - hauto q:on ctrs:R inv:PTm.
    - hauto q:on ctrs:R inv:PTm.
  Qed.
End RPar.

(***************** Beta rules only ***********************)
Module RPar'.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (***************** Beta ***********************)
  | AppAbs a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0)  (subst_PTm (scons b1 VarPTm) a1)
  | ProjPair p a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) (if p is PL then a1 else b1)


  (*************** Congruence ********************)
  | Var i : R (VarPTm i) (VarPTm i)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (PAbs a0) (PAbs a1)
  | AppCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp a0 b0) (PApp a1 b1)
  | PairCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PPair a0 b0) (PPair a1 b1)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1)
  | ConstCong k :
    R (PConst k) (PConst k)
  | UnivCong i :
    R (PUniv i) (PUniv i)
  | BotCong :
    R PBot PBot.

  Derive Dependent Inversion inv with (forall n (a b : PTm n), R a b) Sort Prop.

  Lemma refl n (a : PTm n) : R a a.
  Proof.
    induction a; hauto lq:on ctrs:R.
  Qed.

  Lemma AppAbs' n a0 a1 (b0 b1 t : PTm n) :
    t = subst_PTm (scons b1 VarPTm) a1 ->
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0) t.
  Proof. move => ->. apply AppAbs. Qed.

  Lemma ProjPair' n p (a0 a1 b0 b1 : PTm n) t :
    t = (if p is PL then a1 else b1) ->
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) t.
  Proof.  move => > ->. apply ProjPair. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.
    move => *; apply : AppAbs'; eauto; by asimpl.
    all : qauto ctrs:R use:ProjPair'.
  Qed.

  Lemma morphing_ren n m p (ρ0 ρ1 : fin n -> PTm m) (ξ : fin m -> fin p) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((funcomp (ren_PTm ξ) ρ0) i) ((funcomp (ren_PTm ξ) ρ1) i)).
  Proof. eauto using renaming. Qed.

  Lemma morphing_ext n m (ρ0 ρ1 : fin n -> PTm m) a b  :
    R a b ->
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((scons a ρ0) i) ((scons b ρ1) i)).
  Proof. hauto q:on inv:option. Qed.

  Lemma morphing_up n m (ρ0 ρ1 : fin n -> PTm m) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R (up_PTm_PTm ρ0 i) (up_PTm_PTm ρ1 i)).
  Proof. hauto l:on ctrs:R use:morphing_ext, morphing_ren unfold:up_PTm_PTm. Qed.

  Lemma morphing n m (a b : PTm n) (ρ0 ρ1 : fin n -> PTm m) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    R a b -> R (subst_PTm ρ0 a) (subst_PTm ρ1 b).
  Proof.
    move => + h. move : m ρ0 ρ1.
    elim : n a b /h.
    - move => *.
      apply : AppAbs'; eauto using morphing_up.
      by asimpl.
    - hauto lq:on ctrs:R use:ProjPair' use:morphing_up.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R.
    - hauto l:on ctrs:R use:morphing_up.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R.
  Qed.

  Lemma substing n m (a b : PTm n) (ρ : fin n -> PTm m) :
    R a b ->
    R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof. hauto l:on use:morphing, refl. Qed.

  Lemma cong n (a b : PTm (S n)) c d :
    R a b ->
    R c d ->
    R (subst_PTm (scons c VarPTm) a) (subst_PTm (scons d VarPTm) b).
  Proof.
    move => h0 h1. apply morphing => //=.
    qauto l:on ctrs:R inv:option.
  Qed.

  Lemma var_or_const_imp {n} (a b : PTm n) :
    var_or_const a ->
    a = b -> ~~ var_or_const b -> False.
  Proof.
    hauto lq:on inv:PTm.
  Qed.

  Lemma var_or_const_up n m (ρ : fin n -> PTm m) :
    (forall i, var_or_const (ρ i)) ->
    (forall i, var_or_const (up_PTm_PTm ρ i)).
  Proof.
    move => h /= [i|].
    - asimpl.
      move /(_ i) in h.
      rewrite /funcomp.
      move : (ρ i) h.
      case => //=.
    - sfirstorder.
  Qed.

  Local Ltac antiimp := qauto l:on use:var_or_const_imp.

  Lemma antirenaming n m (a : PTm n) (b : PTm m) (ρ : fin n -> PTm m) :
    (forall i, var_or_const (ρ i)) ->
    R (subst_PTm ρ a) b -> exists b0, R a b0 /\ subst_PTm ρ b0 = b.
  Proof.
    move E : (subst_PTm ρ a) => u hρ h.
    move : n ρ hρ a E. elim : m u b/h.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ρ hρ []//=;
               first by antiimp.
      move => c c0 [+ ?]. subst.
      case : c => //=; first by antiimp.
      move => c [?]. subst.
      spec_refl.
      have /var_or_const_up hρ' := hρ.
      move : iha hρ' => /[apply] iha.
      move : ihb hρ => /[apply] ihb.
      spec_refl.
      move : iha => [c1][ih0]?. subst.
      move : ihb => [c2][ih1]?. subst.
      eexists. split.
      apply AppAbs; eauto.
      by asimpl.
    - move => n p a0 a1 b0 b1 ha iha hb ihb m ρ hρ []//=;
               first by antiimp.
      move => p0 []//=; first by antiimp. move => t t0[*].
      subst.
      have {}/iha := (hρ) => iha.
      have {}/ihb := (hρ) => ihb.
      spec_refl.
      move : iha => [b0 [? ?]].
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by eauto using ProjPair.
      hauto q:on.
    - move => n i m ρ hρ []//=.
      hauto l:on.
    - move => n a0 a1 ha iha m ρ hρ []//=; first by antiimp.
      move => t [*]. subst.
      have /var_or_const_up {}/iha := hρ => iha.
      spec_refl.
      move  :iha => [b0 [? ?]]. subst.
      eexists. split. by apply AbsCong; eauto.
      by asimpl.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ρ hρ []//=;
               first by antiimp.
      move => t t0 [*]. subst.
      have {}/iha := (hρ) => iha.
      have {}/ihb := (hρ) => ihb.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by apply AppCong; eauto.
      done.
    - move => n a0 a1 b0 b1 ha iha hb ihb m ρ hρ []//=;
               first by antiimp.
      move => t t0[*]. subst.
      have {}/iha := (hρ) => iha.
      have {}/ihb := (hρ) => ihb.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      move : ihb => [c0 [? ?]]. subst.
      eexists. split. by apply PairCong; eauto.
      by asimpl.
    - move => n p a0 a1 ha iha m ρ hρ []//=;
               first by antiimp.
      move => p0 t [*]. subst.
      have {}/iha := (hρ) => iha.
      spec_refl.
      move : iha => [b0 [? ?]]. subst.
      eexists. split. apply ProjCong; eauto. reflexivity.
    - hauto q:on ctrs:R inv:PTm.
    - move => n i n0 ρ hρ []//=; first by antiimp.
      hauto l:on.
    - hauto q:on inv:PTm ctrs:R.
  Qed.
End RPar'.


Module EReds.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:ERed.R.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong n (a b : PTm (S n)) :
    rtc ERed.R a b ->
    rtc ERed.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R b0 b1 ->
    rtc ERed.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R b0 b1 ->
    rtc ERed.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1  : PTm n) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.
End EReds.

Module EPar.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Eta ***********************)
  | AppEta a0 a1 :
    R a0 a1 ->
    R a0 (PAbs (PApp (ren_PTm shift a1) (VarPTm var_zero)))
  | PairEta a0 a1 :
    R a0 a1 ->
    R a0 (PPair (PProj PL a1) (PProj PR a1))

  (*************** Congruence ********************)
  | Var i : R (VarPTm i) (VarPTm i)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (PAbs a0) (PAbs a1)
  | AppCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp a0 b0) (PApp a1 b1)
  | PairCong a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PPair a0 b0) (PPair a1 b1)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1)
  | ConstCong k :
    R (PConst k) (PConst k)
  | UnivCong i :
    R (PUniv i) (PUniv i)
  | BotCong :
    R PBot PBot.

  Lemma refl n (a : PTm n) : EPar.R a a.
  Proof.
    induction a; hauto lq:on ctrs:EPar.R.
  Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n a0 a1 ha iha m ξ /=.
    move /(_ _ ξ) /AppEta : iha.
    by asimpl.

    all : qauto ctrs:R.
  Qed.

  Derive Dependent Inversion inv with (forall n (a b : PTm n), R a b) Sort Prop.

  Lemma AppEta' n (a0 a1 b : PTm n) :
    b = (PAbs (PApp (ren_PTm shift a1) (VarPTm var_zero))) ->
    R a0 a1 ->
    R a0 b.
  Proof. move => ->; apply AppEta. Qed.

  Lemma morphing n m (a b : PTm n) (ρ0 ρ1 : fin n -> PTm m) :
    R a b ->
    (forall i, R (ρ0 i) (ρ1 i)) ->
    R (subst_PTm ρ0 a) (subst_PTm ρ1 b).
  Proof.
    move => h. move : m ρ0 ρ1. elim : n a b / h => n.
    - move => a0 a1 ha iha m ρ0 ρ1 hρ /=.
      apply : AppEta'; eauto. by asimpl.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R.
    - hauto l:on ctrs:R use:renaming inv:option.
    - hauto q:on ctrs:R.
    - hauto q:on ctrs:R.
    - hauto q:on ctrs:R.
    - hauto l:on ctrs:R use:renaming inv:option.
    - hauto lq:on ctrs:R.
    - hauto lq:on ctrs:R.
  Qed.

  Lemma substing n a0 a1 (b0 b1 : PTm n) :
    R a0 a1 ->
    R b0 b1 ->
    R (subst_PTm (scons b0 VarPTm) a0) (subst_PTm (scons b1 VarPTm) a1).
  Proof.
    move => h0 h1. apply morphing => //.
    hauto lq:on ctrs:R inv:option.
  Qed.

End EPar.


Module OExp.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Eta ***********************)
  | AppEta a :
    R a (PAbs (PApp (ren_PTm shift a) (VarPTm var_zero)))
  | PairEta a :
    R a (PPair (PProj PL a) (PProj PR a)).

  Lemma merge n (t a b : PTm n) :
    rtc R a b ->
    EPar.R t a ->
    EPar.R t b.
  Proof.
    move => h. move : t. elim : a b /h.
    - eauto using EPar.refl.
    - hauto q:on ctrs:EPar.R inv:R.
  Qed.

  Lemma commutativity n (a b c : PTm n) :
    EPar.R a b -> R a c -> exists d, R b d /\ EPar.R c d.
  Proof.
    move => h.
    inversion 1; subst.
    - hauto q:on ctrs:EPar.R, R use:EPar.renaming, EPar.refl.
    - hauto lq:on ctrs:EPar.R, R.
  Qed.

  Lemma commutativity0 n (a b c : PTm n) :
    EPar.R a b -> rtc R a c -> exists d, rtc R b d /\ EPar.R c d.
  Proof.
    move => + h. move : b.
    elim : a c / h.
    - sfirstorder.
    - hauto lq:on rew:off ctrs:rtc use:commutativity.
  Qed.

End OExp.


Local Ltac com_helper :=
  split; [hauto lq:on ctrs:RPar.R use: RPar.refl, RPar.renaming
         |hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming].

Module RPars.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:RPar.R use:RPar.refl.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong n (a b : PTm (S n)) :
    rtc RPar.R a b ->
    rtc RPar.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R b0 b1 ->
    rtc RPar.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R b0 b1 ->
    rtc RPar.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1  : PTm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma renaming n (a0 a1 : PTm n) m (ξ : fin n -> fin m) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R (ren_PTm ξ a0) (ren_PTm ξ a1).
  Proof.
    induction 1.
    - apply rtc_refl.
    - eauto using RPar.renaming, rtc_l.
  Qed.

  Lemma weakening n (a0 a1 : PTm n) :
    rtc RPar.R a0 a1 ->
    rtc RPar.R (ren_PTm shift a0) (ren_PTm shift a1).
  Proof. apply renaming. Qed.

  Lemma Abs_inv n (a : PTm (S n)) b :
    rtc RPar.R (PAbs a) b -> exists a', b = PAbs a' /\ rtc RPar.R a a'.
  Proof.
    move E : (PAbs a) => b0 h. move : a E.
    elim : b0 b / h.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on ctrs:rtc inv:RPar.R, rtc.
  Qed.

  Lemma morphing n m (a b : PTm n) (ρ : fin n -> PTm m) :
    rtc RPar.R a b ->
    rtc RPar.R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof. induction 1; qauto l:on ctrs:rtc use:RPar.substing. Qed.

  Lemma substing n (a b : PTm (S n)) c :
    rtc RPar.R a b ->
    rtc RPar.R (subst_PTm (scons c VarPTm) a) (subst_PTm (scons c VarPTm) b).
  Proof. hauto lq:on use:morphing inv:option. Qed.

  Lemma antirenaming n m (a : PTm n) (b : PTm m) (ρ : fin n -> PTm m) :
    (forall i, var_or_const (ρ i)) ->
    rtc RPar.R (subst_PTm ρ a) b -> exists b0, rtc RPar.R a b0 /\ subst_PTm ρ b0 = b.
  Proof.
    move E  :(subst_PTm ρ a) => u hρ h.
    move : a E.
    elim : u b /h.
    - sfirstorder.
    - move => a b c h0 h1 ih1 a0 ?. subst.
      move /RPar.antirenaming : h0.
      move /(_ hρ).
      move => [b0 [h2 ?]]. subst.
      hauto lq:on rew:off ctrs:rtc.
  Qed.

End RPars.

Module RPars'.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:RPar'.R use:RPar'.refl.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong n (a b : PTm (S n)) :
    rtc RPar'.R a b ->
    rtc RPar'.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    rtc RPar'.R a0 a1 ->
    rtc RPar'.R b0 b1 ->
    rtc RPar'.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    rtc RPar'.R a0 a1 ->
    rtc RPar'.R b0 b1 ->
    rtc RPar'.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1  : PTm n) :
    rtc RPar'.R a0 a1 ->
    rtc RPar'.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma renaming n (a0 a1 : PTm n) m (ξ : fin n -> fin m) :
    rtc RPar'.R a0 a1 ->
    rtc RPar'.R (ren_PTm ξ a0) (ren_PTm ξ a1).
  Proof.
    induction 1.
    - apply rtc_refl.
    - eauto using RPar'.renaming, rtc_l.
  Qed.

  Lemma weakening n (a0 a1 : PTm n) :
    rtc RPar'.R a0 a1 ->
    rtc RPar'.R (ren_PTm shift a0) (ren_PTm shift a1).
  Proof. apply renaming. Qed.

  Lemma Abs_inv n (a : PTm (S n)) b :
    rtc RPar'.R (PAbs a) b -> exists a', b = PAbs a' /\ rtc RPar'.R a a'.
  Proof.
    move E : (PAbs a) => b0 h. move : a E.
    elim : b0 b / h.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on ctrs:rtc inv:RPar'.R, rtc.
  Qed.

  Lemma morphing n m (a b : PTm n) (ρ : fin n -> PTm m) :
    rtc RPar'.R a b ->
    rtc RPar'.R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof. induction 1; qauto l:on ctrs:rtc use:RPar'.substing. Qed.

  Lemma substing n (a b : PTm (S n)) c :
    rtc RPar'.R a b ->
    rtc RPar'.R (subst_PTm (scons c VarPTm) a) (subst_PTm (scons c VarPTm) b).
  Proof. hauto lq:on use:morphing inv:option. Qed.

  Lemma antirenaming n m (a : PTm n) (b : PTm m) (ρ : fin n -> PTm m) :
    (forall i, var_or_const (ρ i)) ->
    rtc RPar'.R (subst_PTm ρ a) b -> exists b0, rtc RPar'.R a b0 /\ subst_PTm ρ b0 = b.
  Proof.
    move E  :(subst_PTm ρ a) => u hρ h.
    move : a E.
    elim : u b /h.
    - sfirstorder.
    - move => a b c h0 h1 ih1 a0 ?. subst.
      move /RPar'.antirenaming : h0.
      move /(_ hρ).
      move => [b0 [h2 ?]]. subst.
      hauto lq:on rew:off ctrs:rtc.
  Qed.

End RPars'.

Lemma Abs_EPar n a (b : PTm n) :
  EPar.R (PAbs a) b ->
  (exists d, EPar.R a d /\
     rtc RPar.R (PApp (ren_PTm shift b) (VarPTm var_zero)) d) /\
         (exists d,
         EPar.R a d /\ forall p,
         rtc RPar.R (PProj p b) (PAbs (PProj p d))).
Proof.
  move E : (PAbs a) => u h.
  move : a E.
  elim : n u b /h => //=.
  - move => n a0 a1 ha iha b ?. subst.
    specialize iha with (1 := eq_refl).
    move : iha => [[d [ih0 ih1]] _].
    split; exists d.
    + split => //.
      apply : rtc_l.
      apply RPar.AppAbs; eauto => //=.
      apply RPar.refl.
      by apply RPar.refl.
      move :ih1; substify; by asimpl.
    + split => // p.
      apply : rtc_l.
      apply : RPar.ProjAbs.
      by apply RPar.refl.
      eauto using RPars.ProjCong, RPars.AbsCong.
  - move => n ? a1 ha iha a0 ?. subst. specialize iha with (1 := eq_refl).
    move : iha => [_ [d [ih0 ih1]]].
    split.
    + exists (PPair (PProj PL d) (PProj PR d)).
      split; first by apply EPar.PairEta.
      apply : rtc_l.
      apply RPar.AppPair; eauto using RPar.refl.
      suff h : forall p, rtc RPar.R (PApp (PProj p (ren_PTm shift a1)) (VarPTm var_zero)) (PProj p d) by
          sfirstorder use:RPars.PairCong.
      move => p. move /(_ p) /RPars.weakening in ih1.
      apply relations.rtc_transitive with (y := PApp (ren_PTm shift (PAbs (PProj p d))) (VarPTm var_zero)).
      by eauto using RPars.AppCong, rtc_refl.
      apply relations.rtc_once => /=.
      apply : RPar.AppAbs'; eauto using RPar.refl.
      by asimpl.
    + exists d. repeat split => //. move => p.
      apply : rtc_l; eauto.
      hauto q:on use:RPar.ProjPair', RPar.refl.
  - move => n a0 a1 ha _ ? [*]. subst.
    split.
    + exists a1. split => //.
      apply rtc_once. apply : RPar.AppAbs'; eauto using RPar.refl. by asimpl.
    + exists a1. split => // p.
      apply rtc_once. apply : RPar.ProjAbs; eauto using RPar.refl.
Qed.

Lemma Pair_EPar n (a b c : PTm n) :
  EPar.R (PPair a b) c ->
  (forall p, exists d, rtc RPar.R (PProj p c) d /\ EPar.R (if p is PL then a else b) d) /\
    (exists d0 d1, rtc RPar.R (PApp (ren_PTm shift c) (VarPTm var_zero))
                (PPair (PApp (ren_PTm shift d0) (VarPTm var_zero))(PApp (ren_PTm shift d1) (VarPTm var_zero))) /\
    EPar.R a d0 /\ EPar.R b d1).
Proof.
  move E : (PPair a b) => u h. move : a b E.
  elim : n u c /h => //=.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    move : iha => [_ [d0 [d1 [ih0 [ih1 ih2]]]]].
    split.
    + move => p.
      exists (PAbs (PApp (ren_PTm shift (if p is PL then d0 else d1)) (VarPTm var_zero))).
      split.
      * apply : relations.rtc_transitive.
        ** apply RPars.ProjCong. apply RPars.AbsCong. eassumption.
        ** apply : rtc_l. apply RPar.ProjAbs; eauto using RPar.refl. apply RPars.AbsCong.
           apply : rtc_l. apply RPar.ProjPair; eauto using RPar.refl.
           hauto l:on.
      * hauto lq:on use:EPar.AppEta'.
    + exists d0, d1.
      repeat split => //.
      apply : rtc_l. apply : RPar.AppAbs'; eauto using RPar.refl => //=.
      by asimpl; renamify.
  - move => n a0 a1 ha iha a b ?. subst. specialize iha with (1 := eq_refl).
    split => [p|].
    + move : iha => [/(_ p) [d [ih0 ih1]] _].
      exists d. split=>//.
      apply : rtc_l. apply RPar.ProjPair; eauto using RPar.refl.
      set q := (X in rtc RPar.R X d).
      by have -> : q = PProj p a1 by hauto lq:on.
    + move  :iha => [iha _].
      move : (iha PL) => [d0 [ih0 ih0']].
      move : (iha PR) => [d1 [ih1 ih1']] {iha}.
      exists d0, d1.
      apply RPars.weakening in ih0, ih1.
      repeat split => //=.
      apply : rtc_l. apply RPar.AppPair; eauto using RPar.refl.
      apply RPars.PairCong; apply RPars.AppCong; eauto using rtc_refl.
  - move => n a0 a1 b0 b1 ha _ hb _ a b [*]. subst.
    split.
    + move => p.
      exists (if p is PL then a1 else b1).
      split.
      * apply rtc_once. apply : RPar.ProjPair'; eauto using RPar.refl.
      * hauto lq:on rew:off.
    + exists a1, b1.
      split. apply rtc_once. apply RPar.AppPair; eauto using RPar.refl.
      split => //.
Qed.

Lemma commutativity0 n (a b0 b1 : PTm n) :
  EPar.R a b0 -> RPar.R a b1 -> exists c, rtc RPar.R b0 c /\ EPar.R b1 c.
Proof.
  move => h. move : b1.
  elim : n a b0 / h.
  - move => n a b0 ha iha b1 hb.
    move : iha (hb) => /[apply].
    move => [c [ih0 ih1]].
    exists (PAbs (PApp (ren_PTm shift c) (VarPTm var_zero))).
    split.
    + hauto lq:on ctrs:rtc use:RPars.AbsCong, RPars.AppCong, RPars.renaming.
    + hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming.
  - move => n a b0 hb0 ihb0 b1 /[dup] hb1 {}/ihb0.
    move => [c [ih0 ih1]].
    exists (PPair (PProj PL c) (PProj PR c)). split.
    + apply RPars.PairCong;
      by apply RPars.ProjCong.
    + hauto lq:on ctrs:EPar.R use:EPar.refl, EPar.renaming.
  - hauto l:on ctrs:rtc inv:RPar.R.
  - move => n a0 a1 h ih b1.
    elim /RPar.inv => //= _.
    move => a2 a3 ? [*]. subst.
    hauto lq:on ctrs:rtc, RPar.R, EPar.R use:RPars.AbsCong.
  - move => n a0 a1 b0 b1 ha iha hb ihb b2.
    elim /RPar.inv => //= _.
    + move =>  a2 a3 b3 b4 h0 h1 [*]. subst.
      move /(_ _ ltac:(by eauto)) : ihb => [b [ihb0 ihb1]].
      have {}/iha : RPar.R (PAbs a2) (PAbs a3) by hauto lq:on ctrs:RPar.R.
      move => [c [ih0 /Abs_EPar [[d [ih1 ih2]] _]]].
      exists (subst_PTm (scons b VarPTm) d).
      split.
      (* By substitution *)
      * move /RPars.substing  : ih2.
        move /(_ b).
        asimpl.
        eauto using relations.rtc_transitive, RPars.AppCong.
      (* By EPar morphing *)
      * by apply EPar.substing.
    + move => a2 a3 b3 b4 c0 c1 h0 h1 h2 [*]. subst.
      move /(_ _ ltac:(by eauto using RPar.PairCong)) : iha
           => [c [ihc0 ihc1]].
      move /(_ _ ltac:(by eauto)) : ihb => [d [ihd0 ihd1]].
      move /Pair_EPar  : ihc1 => [_ [d0 [d1 [ih0 [ih1 ih2]]]]].
      move /RPars.substing : ih0. move /(_ d).
      asimpl => h.
      exists (PPair (PApp d0 d) (PApp d1 d)).
      split.
      hauto lq:on use:relations.rtc_transitive, RPars.AppCong.
      apply EPar.PairCong; by apply EPar.AppCong.
    + hauto lq:on ctrs:EPar.R use:RPars.AppCong.
  - hauto lq:on ctrs:EPar.R inv:RPar.R use:RPars.PairCong.
  - move => n p a b0 h0 ih0 b1.
    elim /RPar.inv => //= _.
    + move => ? a0 a1 h [*]. subst.
      move /(_ _ ltac:(by eauto using RPar.AbsCong)) : ih0 => [c [ih0 ih1]].
      move /Abs_EPar : ih1 => [_ [d [ih1 ih2]]].
      exists (PAbs (PProj p d)).
      qauto l:on ctrs:EPar.R use:RPars.ProjCong, @relations.rtc_transitive.
    + move => p0 a0 a1 b2 b3 h1 h2 [*]. subst.
      move /(_ _ ltac:(by eauto using RPar.PairCong)) : ih0 => [c [ih0 ih1]].
      move /Pair_EPar : ih1 => [/(_ p)[d [ihd ihd']] _].
      exists d. split => //.
      hauto lq:on use:RPars.ProjCong, relations.rtc_transitive.
    + hauto lq:on ctrs:EPar.R use:RPars.ProjCong.
  - hauto l:on ctrs:EPar.R inv:RPar.R.
  - hauto l:on ctrs:EPar.R inv:RPar.R.
  - hauto l:on ctrs:EPar.R inv:RPar.R.
Qed.

Lemma commutativity1 n (a b0 b1 : PTm n) :
  EPar.R a b0 -> rtc RPar.R a b1 -> exists c, rtc RPar.R b0 c /\ EPar.R b1 c.
Proof.
  move => + h. move : b0.
  elim : a b1 / h.
  - sfirstorder.
  - qauto l:on use:relations.rtc_transitive, commutativity0.
Qed.

Lemma commutativity n (a b0 b1 : PTm n) :
  rtc EPar.R a b0 -> rtc RPar.R a b1 -> exists c, rtc RPar.R b0 c /\ rtc EPar.R b1 c.
  move => h. move : b1. elim : a b0 /h.
  - sfirstorder.
  - move => a0 a1 a2 + ha1 ih b1 +.
    move : commutativity1; repeat move/[apply].
    hauto q:on ctrs:rtc.
Qed.

Lemma Abs_EPar' n a (b : PTm n) :
  EPar.R (PAbs a) b ->
  (exists d, EPar.R a d /\
          rtc OExp.R (PAbs d) b).
Proof.
  move E : (PAbs a) => u h.
  move : a E.
  elim : n u b /h => //=.
  - move => n a0 a1 ha iha a ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 ha iha a ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma Proj_EPar' n p a (b : PTm n) :
  EPar.R (PProj p a) b ->
  (exists d, EPar.R a d /\
          rtc OExp.R (PProj p d) b).
Proof.
  move E : (PProj p a) => u h.
  move : p a E.
  elim : n u b /h => //=.
  - move => n a0 a1 ha iha a p ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 ha iha a p ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma App_EPar' n (a b u : PTm n)  :
  EPar.R (PApp a b) u ->
  (exists a0 b0, EPar.R a a0 /\ EPar.R b b0 /\ rtc OExp.R (PApp a0 b0) u).
Proof.
  move E : (PApp a b) => t h.
  move : a b E. elim : n t u /h => //=.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma Pair_EPar' n (a b u : PTm n) :
  EPar.R (PPair a b) u ->
  exists a0 b0, EPar.R a a0 /\ EPar.R b b0 /\ rtc OExp.R (PPair a0 b0) u.
Proof.
  move E : (PPair a b) => t h.
  move : a b E. elim : n t u /h => //=.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 ha iha a b ?. subst.
    specialize iha with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma Const_EPar' n k (u : PTm n) :
  EPar.R (PConst k) u ->
  rtc OExp.R (PConst k) u.
  move E : (PConst k) => t h.
  move : k E. elim : n t u /h => //=.
  - move => n a0 a1 h ih k ?. subst.
    specialize ih with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 h ih k ?. subst.
    specialize ih with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma Bot_EPar' n (u : PTm n) :
  EPar.R (PBot) u ->
  rtc OExp.R (PBot) u.
  move E : (PBot) => t h.
  move : E. elim : n t u /h => //=.
  - move => n a0 a1 h ih ?. subst.
    specialize ih with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 h ih ?. subst.
    specialize ih with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma Univ_EPar' n i (u : PTm n) :
  EPar.R (PUniv i) u ->
  rtc OExp.R (PUniv i) u.
  move E : (PUniv i) => t h.
  move : E. elim : n t u /h => //=.
  - move => n a0 a1 h ih ?. subst.
    specialize ih with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - move => n a0 a1 h ih ?. subst.
    specialize ih with (1 := eq_refl).
    hauto lq:on ctrs:OExp.R use:rtc_r.
  - hauto l:on ctrs:OExp.R.
Qed.

Lemma EPar_diamond n (c a1 b1 : PTm n) :
  EPar.R c a1 ->
  EPar.R c b1 ->
  exists d2, EPar.R a1 d2 /\ EPar.R b1 d2.
Proof.
  move => h. move : b1. elim : n c a1 / h.
  - move => n c a1 ha iha b1 /iha [d2 [hd0 hd1]].
    exists(PAbs (PApp (ren_PTm shift d2) (VarPTm var_zero))).
    hauto lq:on ctrs:EPar.R use:EPar.renaming.
  - hauto lq:on rew:off ctrs:EPar.R.
  - hauto lq:on use:EPar.refl.
  - move => n a0 a1 ha iha a2.
    move /Abs_EPar' => [d [hd0 hd1]].
    move : iha hd0; repeat move/[apply].
    move => [d2 [h0 h1]].
    have : EPar.R (PAbs d) (PAbs d2) by eauto using EPar.AbsCong.
    move : OExp.commutativity0 hd1; repeat move/[apply].
    move => [d1 [hd1 hd2]].
    exists d1. hauto lq:on ctrs:EPar.R use:OExp.merge.
  - move => n a0 a1 b0 b1 ha iha hb ihb c.
    move /App_EPar' => [a2][b2][/iha [a3 h0]][/ihb [b3 h1]]h2 {iha ihb}.
    have : EPar.R (PApp a2 b2)(PApp a3 b3)
      by hauto l:on use:EPar.AppCong.
    move : OExp.commutativity0 h2; repeat move/[apply].
    move => [d h].
    exists d. hauto lq:on rew:off ctrs:EPar.R use:OExp.merge.
  - move => n a0 a1 b0 b1 ha iha hb ihb c.
    move /Pair_EPar' => [a2][b2][/iha [a3 h0]][/ihb [b3 h1]]h2 {iha ihb}.
    have : EPar.R (PPair a2 b2)(PPair a3 b3)
      by hauto l:on use:EPar.PairCong.
    move : OExp.commutativity0 h2; repeat move/[apply].
    move => [d h].
    exists d. hauto lq:on rew:off ctrs:EPar.R use:OExp.merge.
  - move => n p a0 a1 ha iha b.
    move /Proj_EPar' => [d [/iha [d2 h] h1]] {iha}.
    have : EPar.R (PProj p d) (PProj p d2)
      by hauto l:on use:EPar.ProjCong.
    move : OExp.commutativity0 h1; repeat move/[apply].
    move => [d1 h1].
    exists d1. hauto lq:on rew:off ctrs:EPar.R use:OExp.merge.
  - qauto use:Const_EPar', EPar.refl.
  - qauto use:Univ_EPar', EPar.refl.
  - qauto use:Bot_EPar', EPar.refl.
Qed.

Function tstar {n} (a : PTm n) :=
  match a with
  | VarPTm i => a
  | PAbs a => PAbs (tstar a)
  | PApp (PAbs a) b => subst_PTm (scons (tstar b) VarPTm) (tstar a)
  | PApp (PPair a b) c =>
      PPair (PApp (tstar a) (tstar c)) (PApp (tstar b) (tstar c))
  | PApp a b => PApp (tstar a) (tstar b)
  | PPair a b => PPair (tstar a) (tstar b)
  | PProj p (PPair a b) => if p is PL then (tstar a) else (tstar b)
  | PProj p (PAbs a) => (PAbs (PProj p (tstar a)))
  | PProj p a => PProj p (tstar a)
  | PConst k => PConst k
  | PUniv i => PUniv i
  | PBot => PBot
  end.

Lemma RPar_triangle n (a : PTm n) : forall b, RPar.R a b -> RPar.R b (tstar a).
Proof.
  apply tstar_ind => {n a}.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on use:RPar.cong, RPar.refl ctrs:RPar.R inv:RPar.R.
  - hauto lq:on rew:off ctrs:RPar.R inv:RPar.R.
  - hauto lq:on rew:off inv:RPar.R ctrs:RPar.R.
  - hauto lq:on rew:off inv:RPar.R ctrs:RPar.R.
  - hauto drew:off inv:RPar.R use:RPar.refl, RPar.ProjPair'.
  - hauto drew:off inv:RPar.R use:RPar.refl, RPar.ProjPair'.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
  - hauto lq:on inv:RPar.R ctrs:RPar.R.
Qed.

Function tstar' {n} (a : PTm n) :=
  match a with
  | VarPTm i => a
  | PAbs a => PAbs (tstar' a)
  | PApp (PAbs a) b => subst_PTm (scons (tstar' b) VarPTm) (tstar' a)
  | PApp a b => PApp (tstar' a) (tstar' b)
  | PPair a b => PPair (tstar' a) (tstar' b)
  | PProj p (PPair a b) => if p is PL then (tstar' a) else (tstar' b)
  | PProj p a => PProj p (tstar' a)
  | PConst k => PConst k
  | PUniv i => PUniv i
  | PBot => PBot
  end.

Lemma RPar'_triangle n (a : PTm n) : forall b, RPar'.R a b -> RPar'.R b (tstar' a).
Proof.
  apply tstar'_ind => {n a}.
  - hauto lq:on inv:RPar'.R ctrs:RPar'.R.
  - hauto lq:on inv:RPar'.R ctrs:RPar'.R.
  - hauto lq:on use:RPar'.cong, RPar'.refl ctrs:RPar'.R inv:RPar'.R.
  - hauto lq:on rew:off ctrs:RPar'.R inv:RPar'.R.
  - hauto lq:on rew:off inv:RPar'.R ctrs:RPar'.R.
  - hauto drew:off inv:RPar'.R use:RPar'.refl, RPar'.ProjPair'.
  - hauto drew:off inv:RPar'.R use:RPar'.refl, RPar'.ProjPair'.
  - hauto lq:on inv:RPar'.R ctrs:RPar'.R.
  - hauto lq:on inv:RPar'.R ctrs:RPar'.R.
  - hauto lq:on inv:RPar'.R ctrs:RPar'.R.
  - hauto lq:on inv:RPar'.R ctrs:RPar'.R.
Qed.

Lemma RPar_diamond n (c a1 b1 : PTm n) :
  RPar.R c a1 ->
  RPar.R c b1 ->
  exists d2, RPar.R a1 d2 /\ RPar.R b1 d2.
Proof. hauto l:on use:RPar_triangle. Qed.

Lemma RPar'_diamond n (c a1 b1 : PTm n) :
  RPar'.R c a1 ->
  RPar'.R c b1 ->
  exists d2, RPar'.R a1 d2 /\ RPar'.R b1 d2.
Proof. hauto l:on use:RPar'_triangle. Qed.

Lemma RPar_confluent n (c a1 b1 : PTm n) :
  rtc RPar.R c a1 ->
  rtc RPar.R c b1 ->
  exists d2, rtc RPar.R a1 d2 /\ rtc RPar.R b1 d2.
Proof.
  sfirstorder use:relations.diamond_confluent, RPar_diamond.
Qed.

Lemma RPar'_confluent n (c a1 b1 : PTm n) :
  rtc RPar'.R c a1 ->
  rtc RPar'.R c b1 ->
  exists d2, rtc RPar'.R a1 d2 /\ rtc RPar'.R b1 d2.
Proof.
  sfirstorder use:relations.diamond_confluent, RPar'_diamond.
Qed.

Lemma EPar_confluent n (c a1 b1 : PTm n) :
  rtc EPar.R c a1 ->
  rtc EPar.R c b1 ->
  exists d2, rtc EPar.R a1 d2 /\ rtc EPar.R b1 d2.
Proof.
  sfirstorder use:relations.diamond_confluent, EPar_diamond.
Qed.

Inductive prov {n} : PTm n -> PTm n -> Prop :=
| P_Abs h a :
  (forall b, prov h (subst_PTm (scons b VarPTm) a)) ->
  prov h (PAbs a)
| P_App h a b  :
  prov h a ->
  prov h (PApp a b)
| P_Pair h a b :
  prov h a ->
  prov h b ->
  prov h (PPair a b)
| P_Proj h p a :
  prov h a ->
  prov h (PProj p a)
| P_Const k  :
  prov (PConst k) (PConst k)
| P_Var i :
  prov (VarPTm i) (VarPTm i)
| P_Univ i :
  prov (PUniv i) (PUniv i)
| P_Bot :
  prov PBot PBot.

Lemma ERed_EPar n (a b : PTm n) : ERed.R a b -> EPar.R a b.
Proof.
  induction 1; hauto lq:on ctrs:EPar.R use:EPar.refl.
Qed.

Lemma EPar_ERed n (a b : PTm n) : EPar.R a b -> rtc ERed.R a b.
Proof.
  move => h. elim : n a b /h.
  - eauto using rtc_r, ERed.AppEta.
  - eauto using rtc_r, ERed.PairEta.
  - auto using rtc_refl.
  - eauto using EReds.AbsCong.
  - eauto using EReds.AppCong.
  - eauto using EReds.PairCong.
  - eauto using EReds.ProjCong.
  - auto using rtc_refl.
  - auto using rtc_refl.
  - auto using rtc_refl.
Qed.

Lemma EPar_Par n (a b : PTm n) : EPar.R a b -> Par.R a b.
Proof.
  move => h. elim : n a b /h; qauto ctrs:Par.R.
Qed.

Lemma RPar_Par n (a b : PTm n) : RPar.R a b -> Par.R a b.
Proof.
  move => h. elim : n a b /h; hauto lq:on ctrs:Par.R.
Qed.

Lemma rtc_idem n (R : PTm n -> PTm n -> Prop) (a b : PTm n) : rtc (rtc R) a b -> rtc R a b.
Proof.
  induction 1; hauto l:on use:@relations.rtc_transitive, @rtc_r.
Qed.

Lemma EPars_EReds {n} (a b : PTm n) : rtc EPar.R a b <-> rtc ERed.R a b.
Proof.
  sfirstorder use:@relations.rtc_subrel, EPar_ERed, rtc_idem, ERed_EPar.
Qed.

Lemma prov_rpar n (u : PTm n) a b : prov u a -> RPar.R a b -> prov u b.
Proof.
  move => h.
  move : b.
  elim : u a / h.
  (* - qauto l:on ctrs:prov inv:RPar.R use:@rtc_r, RPar_Par. *)
  - hauto lq:on ctrs:prov inv:RPar.R use:RPar.substing.
  - move => h a b ha iha b0.
    elim /RPar.inv => //= _.
    + move => a0 a1 b1 b2 h0 h1 [*]. subst.
      have {}iha :  prov h (PAbs a1) by hauto lq:on ctrs:RPar.R.
      hauto lq:on inv:prov use:RPar.substing.
    + move => a0 a1 b1 b2 c0 c1.
      move => h0 h1 h2 [*]. subst.
      have {}iha : prov h (PPair a1 b2) by hauto lq:on ctrs:RPar.R.
      hauto lq:on inv:prov ctrs:prov.
    + hauto lq:on ctrs:prov.
  - hauto lq:on ctrs:prov inv:RPar.R.
  - move => h p a ha iha b.
    elim /RPar.inv => //= _.
    + move => p0 a0 a1 h0 [*]. subst.
      have {iha} :  prov h (PAbs a1) by hauto lq:on ctrs:RPar.R.
      hauto lq:on ctrs:prov inv:prov use:RPar.substing.
    + move => p0 a0 a1 b0 b1 h0 h1 [*]. subst.
      have {iha} : prov h (PPair a1 b1) by hauto lq:on ctrs:RPar.R.
      qauto l:on inv:prov.
    + hauto lq:on ctrs:prov.
  - hauto lq:on ctrs:prov inv:RPar.R.
  - hauto l:on ctrs:RPar.R inv:RPar.R.
  - hauto l:on ctrs:RPar.R inv:RPar.R.
  - hauto l:on ctrs:RPar.R inv:RPar.R.
Qed.


Lemma prov_lam n (u : PTm n) a : prov u a <-> prov u (PAbs (PApp (ren_PTm shift a) (VarPTm var_zero))).
Proof.
  split.
  move => h. constructor. move => b. asimpl. by constructor.
  inversion 1; subst.
  specialize H2 with (b := PBot).
  move : H2. asimpl. inversion 1; subst. done.
Qed.

Lemma prov_pair n (u : PTm n) a : prov u a <-> prov u (PPair (PProj PL a) (PProj PR a)).
Proof. hauto lq:on inv:prov ctrs:prov. Qed.

Lemma prov_ered n (u : PTm n) a b : prov u a -> ERed.R a b -> prov u b.
Proof.
  move => h.
  move : b.
  elim : u a / h.
  - move => h a ha iha b.
    elim /ERed.inv => // _.
    + move => a0 *. subst.
      rewrite -prov_lam.
      by constructor.
    + move => a0 *. subst.
      rewrite -prov_pair.
      by constructor.
    + hauto lq:on ctrs:prov use:ERed.substing.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
  - move => h a b ha iha hb ihb b0.
    elim /ERed.inv => //_.
    + move => a0 *. subst.
      rewrite -prov_lam.
      by constructor.
    + move => a0 *. subst.
      rewrite -prov_pair.
      by constructor.
    + hauto lq:on ctrs:prov.
    + hauto lq:on ctrs:prov.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
  - hauto lq:on inv:ERed.R, prov ctrs:prov.
Qed.

Lemma prov_ereds n (u : PTm n) a b : prov u a -> rtc ERed.R a b -> prov u b.
Proof.
  induction 2; sfirstorder use:prov_ered.
Qed.

Fixpoint extract {n} (a : PTm n) : PTm n :=
  match a with
  | PAbs a => subst_PTm (scons PBot VarPTm) (extract a)
  | PApp a b => extract a
  | PPair a b => extract a
  | PProj p a => extract a
  | PConst k => PConst k
  | VarPTm i => VarPTm i
  | PUniv i => PUniv i
  | PBot => PBot
  end.

Lemma ren_extract n m (a : PTm n) (ξ : fin n -> fin m) :
  extract (ren_PTm ξ a) = ren_PTm ξ (extract a).
Proof.
  move : m ξ. elim : n/a.
  - sfirstorder.
  - move => n a ih m ξ /=.
    rewrite ih.
    by asimpl.
  - hauto q:on.
  - hauto q:on.
  - hauto q:on.
  - hauto q:on.
  - sfirstorder.
  - sfirstorder.
Qed.

Lemma ren_morphing n m (a : PTm n) (ρ : fin n -> PTm m) :
  (forall i, ρ i = extract (ρ i)) ->
  extract (subst_PTm ρ a) = subst_PTm ρ (extract a).
Proof.
  move : m ρ.
  elim : n /a => n //=.
  move => a ha m ρ hi.
  rewrite ha.
  - destruct i as [i|] => //.
    rewrite ren_extract.
    rewrite -hi.
    by asimpl.
  - by asimpl.
Qed.

Lemma ren_subst_bot n (a : PTm (S n)) :
  extract (subst_PTm (scons PBot VarPTm) a) = subst_PTm (scons PBot VarPTm) (extract a).
Proof.
  apply ren_morphing. destruct i as [i|] => //=.
Qed.

Definition prov_extract_spec {n} u (a : PTm n) :=
  match u with
  | PUniv i => extract a = PUniv i
  | VarPTm i => extract a = VarPTm i
  | (PConst i) => extract a = (PConst i)
  | PBot => extract a = PBot
  | _ => True
  end.

Lemma prov_extract n u (a : PTm n) :
  prov u a -> prov_extract_spec u a.
Proof.
  move => h.
  elim : u a /h.
  - move => h a ha ih.
    case : h ha ih => //=.
    + move => i ha ih.
      move /(_ PBot) in ih.
      rewrite -ih.
      by rewrite ren_subst_bot.
    + move => p _ /(_ PBot).
      by rewrite ren_subst_bot.
    + move => i h /(_ PBot).
      by rewrite ren_subst_bot => ->.
    + move /(_ PBot).
      move => h /(_ PBot).
      by rewrite ren_subst_bot.
  - hauto lq:on.
  - hauto lq:on.
  - hauto lq:on.
  - case => //=.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
Qed.

Definition union {A : Type} (R0 R1 : A -> A -> Prop) a b :=
  R0 a b \/ R1 a b.

Module ERPar.
  Definition R {n} (a b : PTm n) := union RPar.R EPar.R a b.
  Lemma RPar {n} (a b : PTm n) : RPar.R a b -> R a b.
  Proof. sfirstorder. Qed.

  Lemma EPar {n} (a b : PTm n) : EPar.R a b -> R a b.
  Proof. sfirstorder. Qed.

  Lemma refl {n} ( a : PTm n) : ERPar.R a a.
  Proof.
    sfirstorder use:RPar.refl, EPar.refl.
  Qed.

  Lemma ProjCong n p (a0 a1 : PTm n) :
    R a0 a1 ->
    rtc R (PProj p a0) (PProj p a1).
  Proof.
    move => [].
    - move => h.
      apply rtc_once.
      left.
      by apply RPar.ProjCong.
    - move => h.
      apply rtc_once.
      right.
      by apply EPar.ProjCong.
  Qed.

  Lemma AbsCong n (a0 a1 : PTm (S n)) :
    R a0 a1 ->
    rtc R (PAbs a0) (PAbs a1).
  Proof.
    move => [].
    - move => h.
      apply rtc_once.
      left.
      by apply RPar.AbsCong.
    - move => h.
      apply rtc_once.
      right.
      by apply EPar.AbsCong.
  Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    R a0 a1 ->
    R b0 b1 ->
    rtc R (PApp a0 b0) (PApp a1 b1).
  Proof.
    move => [] + [].
    - sfirstorder use:RPar.AppCong, @rtc_once.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.AppCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.AppCong, EPar.refl.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.AppCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.AppCong, EPar.refl.
    - sfirstorder use:EPar.AppCong, @rtc_once.
  Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    R a0 a1 ->
    R b0 b1 ->
    rtc R (PPair a0 b0) (PPair a1 b1).
  Proof.
    move => [] + [].
    - sfirstorder use:RPar.PairCong, @rtc_once.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.PairCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.PairCong, EPar.refl.
    - move => h0 h1.
      apply : rtc_l.
      left. apply RPar.PairCong; eauto; apply RPar.refl.
      apply rtc_once.
      hauto l:on use:EPar.PairCong, EPar.refl.
    - sfirstorder use:EPar.PairCong, @rtc_once.
  Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    sfirstorder use:EPar.renaming, RPar.renaming.
  Qed.

End ERPar.

Hint Resolve ERPar.AppCong ERPar.refl ERPar.AbsCong ERPar.PairCong ERPar.ProjCong : erpar.

Module ERPars.
  #[local]Ltac solve_s_rec :=
  move => *; eapply relations.rtc_transitive; eauto;
         hauto lq:on db:erpar.
  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R b0 b1 ->
    rtc ERPar.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma AbsCong n (a0 a1 : PTm (S n)) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R (PAbs a0) (PAbs a1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R b0 b1 ->
    rtc ERPar.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1 : PTm n) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma renaming n (a0 a1 : PTm n) m (ξ : fin n -> fin m) :
    rtc ERPar.R a0 a1 ->
    rtc ERPar.R (ren_PTm ξ a0) (ren_PTm ξ a1).
  Proof.
    induction 1.
    - apply rtc_refl.
    - eauto using ERPar.renaming, rtc_l.
  Qed.

End ERPars.

Lemma ERPar_Par n (a b : PTm n) : ERPar.R a b -> Par.R a b.
Proof.
  sfirstorder use:EPar_Par, RPar_Par.
Qed.

Lemma Par_ERPar n (a b : PTm n) : Par.R a b -> rtc ERPar.R a b.
Proof.
  move => h. elim : n a b /h.
  - move => n a0 a1 b0 b1 ha iha hb ihb.
    suff ? : rtc ERPar.R (PApp (PAbs a0) b0) (PApp (PAbs a1) b1).
    apply : relations.rtc_transitive; eauto.
    apply rtc_once. apply ERPar.RPar.
    by apply RPar.AppAbs; eauto using RPar.refl.
    eauto using ERPars.AppCong,ERPars.AbsCong.
  - move => n a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc.
    apply : rtc_l. apply ERPar.RPar.
    apply RPar.AppPair; eauto using RPar.refl.
    sfirstorder use:ERPars.AppCong, ERPars.PairCong.
  - move => n p a0 a1 ha iha.
    apply : rtc_l. apply ERPar.RPar. apply RPar.ProjAbs; eauto using RPar.refl.
    sfirstorder use:ERPars.AbsCong, ERPars.ProjCong.
  - move => n p a0 a1 b0 b1 ha iha hb ihb.
    apply : rtc_l. apply ERPar.RPar. apply RPar.ProjPair; eauto using RPar.refl.
    hauto lq:on.
  - move => n a0 a1 ha iha.
    apply : rtc_l. apply ERPar.EPar. apply EPar.AppEta; eauto using EPar.refl.
    hauto lq:on ctrs:rtc
      use:ERPars.AppCong, ERPars.AbsCong, ERPars.renaming.
  - move => n a0 a1 ha iha.
    apply : rtc_l. apply ERPar.EPar. apply EPar.PairEta; eauto using EPar.refl.
    sfirstorder use:ERPars.PairCong, ERPars.ProjCong.
  - sfirstorder.
  - sfirstorder use:ERPars.AbsCong.
  - sfirstorder use:ERPars.AppCong.
  - sfirstorder use:ERPars.PairCong.
  - sfirstorder use:ERPars.ProjCong.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
Qed.

Lemma Pars_ERPar n (a b : PTm n) : rtc Par.R a b -> rtc ERPar.R a b.
Proof.
  induction 1; hauto l:on use:Par_ERPar, @relations.rtc_transitive.
Qed.

Lemma Par_ERPar_iff n (a b : PTm n) : rtc Par.R a b <-> rtc ERPar.R a b.
Proof.
  split.
  sfirstorder use:Pars_ERPar, @relations.rtc_subrel.
  sfirstorder use:ERPar_Par, @relations.rtc_subrel.
Qed.

Lemma RPar_ERPar n (a b : PTm n) : rtc RPar.R a b -> rtc ERPar.R a b.
Proof.
  sfirstorder use:@relations.rtc_subrel.
Qed.

Lemma EPar_ERPar n (a b : PTm n) : rtc EPar.R a b -> rtc ERPar.R a b.
Proof.
  sfirstorder use:@relations.rtc_subrel.
Qed.

Module Type HindleyRosen.
  Parameter A : nat -> Type.
  Parameter R0 R1 : forall n, A n -> A n -> Prop.
  Axiom diamond_R0 : forall n, relations.diamond (R0 n).
  Axiom diamond_R1 : forall n, relations.diamond (R1 n).
  Axiom commutativity : forall n,
    forall a b c, R0 n a b -> R1 n a c -> exists d, R1 n b d /\ R0 n c d.
End HindleyRosen.

Module HindleyRosenFacts (M : HindleyRosen).
  Import M.
  Lemma R0_comm :
    forall n a b c, R0 n a b -> rtc (union (R0 n) (R1 n)) a c ->
             exists d, rtc (union (R0 n) (R1 n)) b d /\ R0 n c d.
  Proof.
    move => n a + c + h.
    elim : a c /h.
    - sfirstorder.
    - move => a0 a1 a2 ha ha0 ih b h.
      case : ha.
      + move : diamond_R0 h; repeat move/[apply].
        hauto lq:on ctrs:rtc.
      + move : commutativity h; repeat move/[apply].
        hauto lq:on ctrs:rtc.
  Qed.

  Lemma R1_comm :
    forall n a b c, R1 n a b -> rtc (union (R0 n) (R1 n)) a c ->
             exists d, rtc (union (R0 n) (R1 n)) b d /\ R1 n c d.
  Proof.
    move => n a + c + h.
    elim : a c /h.
    - sfirstorder.
    - move => a0 a1 a2 ha ha0 ih b h.
      case : ha.
      + move : commutativity h; repeat move/[apply].
        hauto lq:on ctrs:rtc.
      + move : diamond_R1 h; repeat move/[apply].
        hauto lq:on ctrs:rtc.
  Qed.

  Lemma U_comm :
    forall n a b c, (union (R0 n) (R1 n)) a b -> rtc (union (R0 n) (R1 n)) a c ->
             exists d, rtc (union (R0 n) (R1 n)) b d /\ (union (R0 n) (R1 n)) c d.
  Proof.
    hauto lq:on use:R0_comm, R1_comm.
  Qed.

  Lemma U_comms :
    forall n a b c, rtc (union (R0 n) (R1 n)) a b -> rtc (union (R0 n) (R1 n)) a c ->
             exists d, rtc (union (R0 n) (R1 n)) b d /\ rtc (union (R0 n) (R1 n)) c d.
  Proof.
    move => n a b + h.
    elim : a b /h.
    - sfirstorder.
    - hecrush ctrs:rtc use:U_comm.
  Qed.

End HindleyRosenFacts.

Module HindleyRosenER <: HindleyRosen.
  Definition A := PTm.
  Definition R0 n := rtc (@RPar.R n).
  Definition R1 n := rtc (@EPar.R n).
  Lemma diamond_R0 : forall n, relations.diamond (R0 n).
    sfirstorder use:RPar_confluent.
  Qed.
  Lemma diamond_R1 : forall n, relations.diamond (R1 n).
    sfirstorder use:EPar_confluent.
  Qed.
  Lemma commutativity : forall n,
    forall a b c, R0 n a b -> R1 n a c -> exists d, R1 n b d /\ R0 n c d.
  Proof.
    hauto l:on use:commutativity.
  Qed.
End HindleyRosenER.

Module ERFacts := HindleyRosenFacts HindleyRosenER.

Lemma rtc_union n (a b : PTm n) :
  rtc (union RPar.R EPar.R) a b <->
    rtc (union (rtc RPar.R) (rtc EPar.R)) a b.
Proof.
  split; first by induction 1; hauto lq:on ctrs:rtc.
  move => h.
  elim  :a b /h.
  - sfirstorder.
  - move => a0 a1 a2.
    case.
    + move => h0 h1 ih.
      apply : relations.rtc_transitive; eauto.
      move : h0.
      apply relations.rtc_subrel.
      sfirstorder.
    + move => h0 h1 ih.
      apply : relations.rtc_transitive; eauto.
      move : h0.
      apply relations.rtc_subrel.
      sfirstorder.
Qed.

Lemma prov_erpar n (u : PTm n) a b : prov u a -> ERPar.R a b -> prov u b.
Proof.
  move => h [].
  - sfirstorder use:prov_rpar.
  - move /EPar_ERed.
    sfirstorder use:prov_ereds.
Qed.

Lemma prov_pars n (u : PTm n) a b : prov u a -> rtc Par.R a b -> prov u b.
Proof.
  move => h /Pars_ERPar.
  move => h0.
  move  : h.
  elim : a b /h0.
  - done.
  - hauto lq:on use:prov_erpar.
Qed.

Lemma Par_confluent n (a b c : PTm n) :
  rtc Par.R a b ->
  rtc Par.R a c ->
  exists d, rtc Par.R b d /\ rtc Par.R c d.
Proof.
  move : n a b c.
  suff : forall (n : nat) (a b c : PTm n),
      rtc ERPar.R a b ->
      rtc ERPar.R a c -> exists d : PTm n, rtc ERPar.R b d /\ rtc ERPar.R c d.
  move => h n a b c h0 h1.
  apply Par_ERPar_iff in h0, h1.
  move : h h0 h1; repeat move/[apply].
  hauto lq:on use:Par_ERPar_iff.
  have h := ERFacts.U_comms.
  move => n a b c.
  rewrite /HindleyRosenER.R0 /HindleyRosenER.R1 in h.
  specialize h with (n := n).
  rewrite /HindleyRosenER.A in h.
  rewrite /ERPar.R.
  have eq : (fun a0 b0 : PTm n => union RPar.R EPar.R a0 b0) = union RPar.R EPar.R by reflexivity.
  rewrite !{}eq.
  move /rtc_union => + /rtc_union.
  move : h; repeat move/[apply].
  hauto lq:on use:rtc_union.
Qed.

Lemma pars_univ_inv n i (c : PTm n) :
  rtc Par.R (PUniv i) c ->
  extract c = PUniv i.
Proof.
  have : prov (PUniv i) (PUniv i : PTm n) by sfirstorder.
  move : prov_pars. repeat move/[apply].
  apply prov_extract.
Qed.

Lemma pars_const_inv n i (c : PTm n) :
  rtc Par.R (PConst i) c ->
  extract c = PConst i.
Proof.
  have : prov (PConst i) (PConst i : PTm n) by sfirstorder.
  move : prov_pars. repeat move/[apply].
  apply prov_extract.
Qed.

Lemma pars_var_inv n (i : fin n) C :
  rtc Par.R (VarPTm i) C ->
  extract C = VarPTm i.
Proof.
  have : prov (VarPTm i) (VarPTm i) by hauto lq:on ctrs:prov, rtc.
  move : prov_pars. repeat move/[apply].
  apply prov_extract.
Qed.

Lemma pars_univ_inj n i j (C : PTm n) :
  rtc Par.R (PUniv i) C ->
  rtc Par.R (PUniv j) C ->
  i = j.
Proof.
  sauto l:on use:pars_univ_inv.
Qed.

Lemma pars_const_inj n i j (C : PTm n) :
  rtc Par.R (PConst i) C ->
  rtc Par.R (PConst j) C ->
  i = j.
Proof.
  sauto l:on use:pars_const_inv.
Qed.

Definition join {n} (a b : PTm n) :=
  exists c, rtc Par.R a c /\ rtc Par.R b c.

Lemma join_transitive n (a b c : PTm n) :
  join a b -> join b c -> join a c.
Proof.
  rewrite /join.
  move => [ab [h0 h1]] [bc [h2 h3]].
  move : Par_confluent h1 h2; repeat move/[apply].
  move => [abc [h4 h5]].
  eauto using relations.rtc_transitive.
Qed.

Lemma join_symmetric n (a b : PTm n) :
  join a b -> join b a.
Proof. sfirstorder unfold:join. Qed.

Lemma join_refl n (a : PTm n) : join a a.
Proof. hauto lq:on ctrs:rtc unfold:join. Qed.

Lemma join_univ_inj n i j :
  join (PUniv i : PTm n) (PUniv j) -> i = j.
Proof.
  sfirstorder use:pars_univ_inj.
Qed.

Lemma join_const_inj n i j :
  join (PConst i : PTm n) (PConst j) -> i = j.
Proof.
  sfirstorder use:pars_const_inj.
Qed.

Lemma join_substing n m (a b : PTm n) (ρ : fin n -> PTm m) :
  join a b ->
  join (subst_PTm ρ a) (subst_PTm ρ b).
Proof. hauto lq:on unfold:join use:Pars.substing. Qed.

Fixpoint ne {n} (a : PTm n) :=
  match a with
  | VarPTm i => true
  | PApp a b => ne a && nf b
  | PAbs a => false
  | PUniv _ => false
  | PProj _ a => ne a
  | PPair _ _ => false
  | PConst _ => false
  | PBot => true
  end
with nf {n} (a : PTm n) :=
  match a with
  | VarPTm i => true
  | PApp a b => ne a && nf b
  | PAbs a => nf a
  | PUniv _ => true
  | PProj _ a => ne a
  | PPair a b => nf a && nf b
  | PConst _ => true
  | PBot => true
end.

Lemma ne_nf n a : @ne n a -> nf a.
Proof. elim : a => //=. Qed.

Definition wn {n} (a : PTm n) := exists b, rtc RPar'.R a b /\ nf b.
Definition wne {n} (a : PTm n) := exists b, rtc RPar'.R a b /\ ne b.

(* Weakly neutral implies weakly normal *)
Lemma wne_wn n a : @wne n a -> wn a.
Proof. sfirstorder use:ne_nf. Qed.

(* Normal implies weakly normal *)
Lemma nf_wn n v : @nf n v -> wn v.
Proof. sfirstorder ctrs:rtc. Qed.

Lemma nf_refl n (a b : PTm n) (h : RPar'.R a b) : (nf a -> b = a) /\ (ne a -> b = a).
Proof.
  elim : a b /h => //=; solve [hauto b:on].
Qed.

Lemma nf_refls n (a b : PTm n) (h : rtc RPar'.R a b) : (nf a -> b = a) /\ (ne a -> b = a).
Proof.
  induction h; sauto lq:on rew:off ctrs:rtc use:nf_refl.
Qed.

Lemma ne_nf_ren n m (a : PTm n) (ξ : fin n -> fin m) :
  (ne a <-> ne (ren_PTm ξ a)) /\ (nf a <-> nf (ren_PTm ξ a)).
Proof.
  move : m ξ. elim : n / a => //=; solve [hauto b:on].
Qed.

Lemma wne_app n (a b : PTm n) :
  wne a -> wn b -> wne (PApp a b).
Proof.
  move => [a0 [? ?]] [b0 [? ?]].
  exists (PApp a0 b0). hauto b:on drew:off use:RPars'.AppCong.
Qed.

Lemma wn_abs n a (h : wn a) : @wn n (PAbs a).
Proof.
  move : h => [v [? ?]].
  exists (PAbs v).
  eauto using RPars'.AbsCong.
Qed.

Require Import Coq.Program.Equality.

Lemma wn_abs' n a (h : @wn n (PAbs a)) : wn a.
Proof.
  move : h. move => [a0 [h0 h1]].
  dependent induction h0; sauto q:on.
Qed.

Lemma wn_pair n (a b : PTm n) : wn a -> wn b -> wn (PPair a b).
Proof.
  move => [a0 [? ?]] [b0 [? ?]].
  exists (PPair a0 b0).
  hauto lqb:on use:RPars'.PairCong.
Qed.

Lemma wne_proj n p (a : PTm n) : wne a -> wne (PProj p a).
Proof.
  move => [a0 [? ?]].
  exists (PProj p a0). hauto lqb:on use:RPars'.ProjCong.
Qed.

Create HintDb nfne.
#[export]Hint Resolve nf_wn ne_nf wne_wn nf_refl : nfne.

Lemma ne_nf_antiren n m (a : PTm n) (ρ : fin n -> PTm m) :
  (forall i, var_or_const (ρ i)) ->
  (ne (subst_PTm ρ a) -> ne a) /\ (nf (subst_PTm ρ a) -> nf a).
Proof.
  move : m ρ. elim : n / a => //;
   hauto b:on drew:off use:RPar.var_or_const_up.
Qed.

Lemma wn_antirenaming n m a (ρ : fin n -> PTm m) :
  (forall i, var_or_const (ρ i)) ->
  wn (subst_PTm ρ a) -> wn a.
Proof.
  rewrite /wn => hρ.
  move => [v [rv nfv]].
  move /RPars'.antirenaming : rv.
  move /(_ hρ) => [b [hb ?]]. subst.
  exists b. split => //=.
  move : nfv.
  by eapply ne_nf_antiren.
Qed.

Lemma ext_wn n (a : PTm n) :
    wn (PApp a PBot) ->
    wn a.
Proof.
  move E : (PApp a (PBot)) => a0 [v [hr hv]].
  move : a E.
  move : hv.
  elim : a0 v / hr.
  - hauto q:on inv:PTm ctrs:rtc b:on db: nfne.
  - move => a0 a1 a2 hr0 hr1 ih hnfa2.
    move /(_ hnfa2) in ih.
    move => a.
    case : a0 hr0=>// => b0 b1.
    elim /RPar'.inv=>// _.
    + move => a0 a3 b2 b3 ? ? [? ?] ? [? ?]. subst.
      have ? : b3 = (PBot) by hauto lq:on inv:RPar'.R. subst.
      suff : wn (PAbs a3) by hauto lq:on ctrs:RPar'.R, rtc unfold:wn.
      have : wn (subst_PTm (scons (PBot) VarPTm) a3) by sfirstorder.
      move => h. apply wn_abs.
      move : h. apply wn_antirenaming.
      hauto lq:on rew:off inv:option.
    + hauto q:on inv:RPar'.R ctrs:rtc b:on.
Qed.

Module Join.
  Lemma ProjCong p n (a0 a1 : PTm n) :
    join a0 a1 ->
    join (PProj p a0) (PProj p a1).
  Proof. hauto lq:on use:Pars.ProjCong unfold:join. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    join a0 a1 ->
    join b0 b1 ->
    join (PPair a0 b0) (PPair a1 b1).
  Proof. hauto lq:on use:Pars.PairCong unfold:join. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    join a0 a1 ->
    join b0 b1 ->
    join (PApp a0 b0) (PApp a1 b1).
  Proof. hauto lq:on use:Pars.AppCong. Qed.

  Lemma AbsCong n (a b : PTm (S n)) :
    join a b ->
    join (PAbs a) (PAbs b).
  Proof. hauto lq:on use:Pars.AbsCong. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    join a b -> join (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    induction 1; hauto lq:on use:Pars.renaming.
  Qed.

  Lemma weakening n (a b : PTm n)  :
    join a b -> join (ren_PTm shift a) (ren_PTm shift b).
  Proof.
    apply renaming.
  Qed.

  Lemma FromPar n (a b : PTm n) :
    Par.R a b ->
    join a b.
  Proof.
    hauto lq:on ctrs:rtc use:rtc_once.
  Qed.
End Join.

Lemma abs_eq n a (b : PTm n) :
  join (PAbs a) b <-> join a (PApp (ren_PTm shift b) (VarPTm var_zero)).
Proof.
  split.
  - move => /Join.weakening h.
    have {h} : join (PApp (ren_PTm shift (PAbs a)) (VarPTm var_zero)) (PApp (ren_PTm shift b) (VarPTm var_zero))
      by hauto l:on use:Join.AppCong, join_refl.
    simpl.
    move => ?. apply : join_transitive; eauto.
    apply join_symmetric. apply Join.FromPar.
    apply : Par.AppAbs'; eauto using Par.refl. by asimpl.
  - move /Join.AbsCong.
    move /join_transitive. apply.
    apply join_symmetric. apply Join.FromPar. apply Par.AppEta. apply Par.refl.
Qed.

Lemma pair_eq n (a0 a1 b : PTm n) :
  join (PPair a0 a1) b <-> join a0 (PProj PL b) /\ join a1 (PProj PR b).
Proof.
  split.
  - move => h.
    have /Join.ProjCong {}h := h.
    have h0 : forall p, join (if p is PL then a0 else a1) (PProj p (PPair a0 a1))
                     by hauto lq:on use:join_symmetric, Join.FromPar, Par.ProjPair', Par.refl.
    hauto lq:on rew:off use:join_transitive, join_symmetric.
  - move => [h0 h1].
    move : h0 h1.
    move : Join.PairCong; repeat move/[apply].
    move /join_transitive. apply. apply join_symmetric.
    apply Join.FromPar. hauto lq:on ctrs:Par.R use:Par.refl.
Qed.

Lemma join_pair_inj n (a0 a1 b0 b1 : PTm n) :
  join (PPair a0 a1) (PPair b0 b1) <-> join a0 b0 /\ join a1 b1.
Proof.
  split; last by hauto lq:on use:Join.PairCong.
  move /pair_eq => [h0 h1].
  have : join (PProj PL (PPair b0 b1)) b0 by hauto lq:on use:Join.FromPar, Par.refl, Par.ProjPair'.
  have : join (PProj PR (PPair b0 b1)) b1 by hauto lq:on use:Join.FromPar, Par.refl, Par.ProjPair'.
  eauto using join_transitive.
Qed.

Lemma rpars_wn n (a b : PTm n) :
  rtc RPar'.R a b -> wn a -> wn b.
Proof.
  move => h [b0 [h0 h1]].
  have : exists c, rtc RPar'.R b c /\ rtc RPar'.R b0 c by
      eauto using RPar'_confluent.
  move => [c [h2 h3]].
  have ? : c = b0 by sfirstorder use:nf_refls. subst.
  sfirstorder use:@relations.rtc_transitive.
Qed.

Lemma rpar_wn n (a b : PTm n) :
  RPar'.R a b -> wn a -> wn b.
Proof. hauto lq:on use:rpars_wn ctrs:rtc. Qed.

Definition norm {n} (a b : PTm n) := rtc RPar'.R a b /\ nf b.


Lemma epar_wn n (a b : PTm n) :
  ERed.R b a -> wn a -> wn b.
Proof.
  move => h.
  move => [v [h0 h1]].
  move : b h1 h.
  elim : a v /h0 .
  - admit.
  - move => a b v ha iha hb b0 hv hr.
    specialize hb with (1 := hv).


  - move => a h.
    apply wn_abs' in h.
    have {h} : wn (PApp a PBot) by admit.
    apply ext_wn.
  - move => a ha.
    have [h0 h1] : wn (PProj PL a) /\ wn (PProj PR a) by admit.
    admit.
  - hauto q:on use:wn_abs, wn_abs'.
  - move => a0 a1 b ha iha hb.
