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
  | AppEta A a0 a1 :
    R a0 a1 ->
    R (PAbs A (PApp (ren_PTm shift a0) (VarPTm var_zero))) a1
  | PairEta a0 a1 :
    R a0 a1 ->
    R (PPair (PProj PL a0) (PProj PR a0)) a1
  (*************** Congruence ********************)
  | AbsCong A a0 a1 :
    R a0 a1 ->
    R (PAbs A a0) (PAbs A a1)
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
  | VarTm i :
    R (VarPTm i) (VarPTm i).

  Lemma refl n (a : PTm n) : R a a.
  Proof.
    elim : n / a; hauto lq:on ctrs:R.
  Qed.

  Derive Dependent Inversion inv with (forall n (a b : PTm n), R a b) Sort Prop.

  Lemma AppEta' n A a0 a1 (u : PTm n) :
    u = (PAbs A (PApp (ren_PTm shift a0) (VarPTm var_zero))) ->
    R a0 a1 ->
    R u a1.
  Proof. move => ->. apply AppEta. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n A a0 a1 ha iha m ξ /=.
    eapply AppEta' with (A := A); eauto. by asimpl.
    all : qauto ctrs:R.
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
    move => + h. move : m ρ0 ρ1. elim : n a b / h => n.
    move => A a0 a1 ha iha m ρ0 ρ1 hρ /=.
    eapply AppEta' with (A := A); eauto. by asimpl.
    all : hauto lq:on ctrs:R use:morphing_up.
  Qed.

  Lemma substing n m (a : PTm n) b (ρ : fin n -> PTm m) :
    R a b ->
    R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    hauto l:on use:morphing, refl.
  Qed.

End ERed.

Inductive SNe {n} : PTm n -> Prop :=
| N_Var i :
  SNe (VarPTm i)
| N_App a b :
  SNe a ->
  SN b ->
  SNe (PApp a b)
| N_Proj p a :
  SNe a ->
  SNe (PProj p a)
with SN  {n} : PTm n -> Prop :=
| N_Pair a b :
  SN a ->
  SN b ->
  SN (PPair a b)
| N_Abs A a :
  SN a ->
  SN (PAbs A a)
| N_SNe a :
  SNe a ->
  SN a
| N_Exp a b :
  TRedSN a b ->
  SN b ->
  SN a
with TRedSN {n} : PTm n -> PTm n -> Prop :=
| N_β A a b :
  SN b ->
  TRedSN (PApp (PAbs A a) b) (subst_PTm (scons b VarPTm) a)
| N_AppL a0 a1 b :
  TRedSN a0 a1 ->
  TRedSN (PApp a0 b) (PApp a1 b)
| N_ProjPairL a b  :
  SN b ->
  TRedSN (PProj PL (PPair a b)) a
| N_ProjPairR a b  :
  SN a ->
  TRedSN (PProj PR (PPair a b)) b
| N_ProjCong p a b :
  TRedSN a b ->
  TRedSN (PProj p a) (PProj p b).

Scheme sne_ind := Induction for SNe Sort Prop
  with sn_ind := Induction for SN Sort Prop
  with sred_ind := Induction for TRedSN Sort Prop.

Combined Scheme sn_mutual from sne_ind, sn_ind, sred_ind.

Inductive TRedSN' {n} (a : PTm n) : PTm n -> Prop :=
| T_Refl :
  TRedSN' a a
| T_Once b :
  TRedSN a b ->
  TRedSN' a b.

Lemma SN_Proj n p (a : PTm n) :
  SN (PProj p a) -> SN a.
Proof.
  move E : (PProj p a) => u h.
  move : a E.
  elim : n u / h => n //=; sauto.
Qed.

Lemma ered_sn_preservation n :
  (forall (a : PTm n) (s : SNe a), forall b, ERed.R a b -> SNe b) /\
  (forall (a : PTm n) (s : SN a), forall b, ERed.R a b -> SN b) /\
  (forall (a b : PTm n) (_ : TRedSN a b), forall c, ERed.R a c -> exists d, TRedSN' c d /\ ERed.R b d).
Proof.
  move : n. apply sn_mutual => n.
  - sauto lq:on.
  - sauto lq:on.
  - sauto lq:on.
  - move => a b ha iha hb ihb b0.
    inversion 1; subst.
    + have /iha : (ERed.R (PProj PL a0) (PProj PL b0)) by sauto lq:on.
      sfirstorder use:SN_Proj.
    + sauto lq:on.
  - move => A a ha iha b.
    inversion 1; subst.
    + have : ERed.R (PApp (ren_PTm shift a0) (VarPTm var_zero))  (PApp (ren_PTm shift b) (VarPTm var_zero)).
      apply ERed.AppCong; eauto using ERed.refl.
      sfirstorder use:ERed.renaming.
      move /iha.
      admit.
    + sauto lq:on.
  - sauto lq:on.
  - sauto lq:on.
  - move => A a b ha iha c h0.
    inversion h0; subst.
    inversion H1; subst.
    + exists (PApp a1 b1). split. sfirstorder.
      asimpl.
      sauto lq:on.
    + have  {}/iha := H3 => iha.
      exists (subst_PTm (scons b1 VarPTm) a2).
      split.
      sauto lq:on.
      hauto lq:on use:ERed.morphing, ERed.refl inv:option.
  - sauto.
  - move => a b hb ihb c.
    elim /ERed.inv => //= _.
    move => p a0 a1 ha [*]. subst.
    elim  /ERed.inv :  ha => //= _.
    + move => a0 a2 ha [*]. subst.
      exists (PProj PL a1).
      split. sauto.
      sauto lq:on.
    + sauto lq:on rew:off.
  - move => a b ha iha c.
    elim /ERed.inv => //=_.
    move => p a0 a1 + [*]. subst.
    elim /ERed.inv => //=_.
    + move => a0 a2 h [*]. subst.
      exists (PProj PR a1).
      split. sauto.
      sauto lq:on.
    + sauto lq:on.
  - sauto.
Admitted.

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
