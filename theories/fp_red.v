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
  | AppEta a0 a1 :
    R a0 a1 ->
    R (PAbs (PApp (ren_PTm shift a0) (VarPTm var_zero))) a1
  | PairEta a0 a1 :
    R a0 a1 ->
    R (PPair (PProj PL a0) (PProj PR a0)) a1
  (*************** Congruence ********************)
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
  | VarTm i :
    R (VarPTm i) (VarPTm i).

  Lemma refl n (a : PTm n) : R a a.
  Proof.
    elim : n / a; hauto lq:on ctrs:R.
  Qed.

  Derive Dependent Inversion inv with (forall n (a b : PTm n), R a b) Sort Prop.

  Lemma AppEta' n a0 a1 (u : PTm n) :
    u = (PAbs (PApp (ren_PTm shift a0) (VarPTm var_zero))) ->
    R a0 a1 ->
    R u a1.
  Proof. move => ->. apply AppEta. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n a0 a1 ha iha m ξ /=.
    eapply AppEta'; eauto. by asimpl.
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
    move => a0 a1 ha iha m ρ0 ρ1 hρ /=.
    eapply AppEta'; eauto. by asimpl.
    all : hauto lq:on ctrs:R use:morphing_up.
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
| N_Abs a :
  SN a ->
  SN (PAbs a)
| N_SNe a :
  SNe a ->
  SN a
| N_Exp a b :
  TRedSN a b ->
  SN b ->
  SN a
with TRedSN {n} : PTm n -> PTm n -> Prop :=
| N_β a b :
  SN b ->
  TRedSN (PApp (PAbs a) b) (subst_PTm (scons b VarPTm) a)
| N_AppL a0 a1 b :
  SN b ->
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

Derive Dependent Inversion tred_inv with (forall n (a b : PTm n), TRedSN a b) Sort Prop.

Lemma PProjAbs_imp n p (a : PTm (S n)) :
  ~ SN (PProj p (PAbs a)).
Proof.
  move E : (PProj p (PAbs a)) => u hu.
  move : p a E.
  elim : n u / hu=>//=.
  hauto lq:on inv:SNe.
  hauto lq:on inv:TRedSN.
Qed.

Lemma PProjPair_imp n (a b0 b1 : PTm n ) :
  ~ SN (PApp (PPair b0 b1) a).
Proof.
  move E : (PApp (PPair b0 b1) a) => u hu.
  move : a b0 b1 E.
  elim : n u / hu=>//=.
  hauto lq:on inv:SNe.
  hauto lq:on inv:TRedSN.
Qed.

Scheme sne_ind := Induction for SNe Sort Prop
  with sn_ind := Induction for SN Sort Prop
  with sred_ind := Induction for TRedSN Sort Prop.

Combined Scheme sn_mutual from sne_ind, sn_ind, sred_ind.

Fixpoint ne {n} (a : PTm n) :=
  match a with
  | VarPTm i => true
  | PApp a b => ne a && nf b
  | PAbs a => false
  | PPair _ _ => false
  | PProj _ a => ne a
  end
with nf {n} (a : PTm n) :=
  match a with
  | VarPTm i => true
  | PApp a b => ne a && nf b
  | PAbs a => nf a
  | PPair a b => nf a && nf b
  | PProj _ a => ne a
end.

Lemma ne_nf n a : @ne n a -> nf a.
Proof. elim : a => //=. Qed.

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

Lemma N_β' n a (b : PTm n) u :
  u = (subst_PTm (scons b VarPTm) a) ->
  SN b ->
  TRedSN (PApp (PAbs a) b) u.
Proof. move => ->. apply N_β. Qed.

Lemma sn_renaming n :
  (forall (a : PTm n) (s : SNe a), forall m (ξ : fin n -> fin m), SNe (ren_PTm ξ a)) /\
  (forall (a : PTm n) (s : SN a), forall m (ξ : fin n -> fin m), SN (ren_PTm ξ a)) /\
  (forall (a b : PTm n) (_ : TRedSN a b), forall m (ξ : fin n -> fin m), TRedSN (ren_PTm ξ a) (ren_PTm ξ b)).
Proof.
  move : n. apply sn_mutual => n; try qauto ctrs:SN, SNe, TRedSN depth:1.
  move => a b ha iha m ξ /=.
  apply N_β'. by asimpl. eauto.
Qed.

#[export]Hint Constructors SN SNe TRedSN : sn.

Ltac2 rec solve_anti_ren () :=
  let x := Fresh.in_goal (Option.get (Ident.of_string "x")) in
  intro $x;
  lazy_match! Constr.type (Control.hyp x) with
  | fin ?x -> _ ?y => (ltac1:(case;qauto depth:2 db:sn))
  | _ => solve_anti_ren ()
  end.

Ltac solve_anti_ren := ltac2:(Control.enter solve_anti_ren).

Lemma sn_antirenaming n :
  (forall (a : PTm n) (s : SNe a), forall m (ξ : fin m -> fin n) b, a = ren_PTm ξ b -> SNe b) /\
  (forall (a : PTm n) (s : SN a), forall m (ξ : fin m -> fin n) b, a = ren_PTm ξ b -> SN b) /\
  (forall (a b : PTm n) (_ : TRedSN a b), forall m (ξ : fin m -> fin n) a0,
      a = ren_PTm ξ a0 -> exists b0, TRedSN a0 b0 /\ b = ren_PTm ξ b0).
Proof.
  move : n. apply sn_mutual => n; try solve_anti_ren.

  move => a b ha iha m ξ []//= u u0 [+ ?]. subst.
  case : u => //= => u [*]. subst.
  spec_refl. eexists. split. apply N_β=>//. by asimpl.

  move => a b hb ihb m ξ[]//= p p0 [? +]. subst.
  case : p0 => //= p p0 [*]. subst.
  spec_refl. by eauto with sn.

  move => a b ha iha m ξ[]//= u u0 [? ]. subst.
  case : u0 => //=. move => p p0 [*]. subst.
  spec_refl. by eauto with sn.
Qed.

Lemma sn_unmorphing n :
  (forall (a : PTm n) (s : SNe a), forall m (ρ : fin m -> PTm n) b, a = subst_PTm ρ b -> SNe b) /\
  (forall (a : PTm n) (s : SN a), forall m (ρ : fin m -> PTm n) b, a = subst_PTm ρ b -> SN b) /\
  (forall (a b : PTm n) (_ : TRedSN a b), forall m (ρ : fin m -> PTm n) a0,
      a = subst_PTm ρ a0 -> (exists b0, b = subst_PTm ρ b0 /\ TRedSN a0 b0) \/ SNe a0).
Proof.
  move : n. apply sn_mutual => n; try solve_anti_ren.
  - move => a b ha iha  m ξ b0.
    case : b0 => //=.
    + hauto lq:on rew:off db:sn.
    + move => p p0 [+ ?]. subst.
      case : p => //=.
      hauto lq:on db:sn.
      move => p [?]. subst.
      asimpl. left.
      spec_refl.
      eexists. split; last by eauto using N_β.
      by asimpl.
  - move => a0 a1 b hb ihb ha iha m ρ []//=.
    + hauto lq:on rew:off db:sn.
    + move => t0  t1 [*]. subst.
      spec_refl.
      case : iha.
      * move => [u [? hu]]. subst.
        left. eexists. split; eauto using N_AppL.
        reflexivity.
      * move => h.
        right.
        apply N_App => //.
  - move => a b hb ihb m ρ []//=.
    + hauto l:on ctrs:TRedSN.
    + move => p p0 [?]. subst.
      case : p0 => //=.
      * hauto lq:on rew:off db:sn.
      * move => p p0 [*]. subst.
        hauto lq:on db:sn.
  - move => a b ha iha m ρ []//=; first by hauto l:on db:sn.
    hauto q:on inv:PTm db:sn.
  - move => p a b ha iha m ρ []//=; first by hauto l:on db:sn.
    move => t0 t1 [*]. subst.
    spec_refl.
    case : iha.
    + move => [b0 [? h]]. subst.
      left. eexists. split; last by eauto with sn.
      reflexivity.
    + hauto lq:on db:sn.
Qed.

Lemma SN_AppInv : forall n (a b : PTm n), SN (PApp a b) -> SN a /\ SN b.
Proof.
  move => n a b. move E : (PApp a b) => u hu. move : a b E.
  elim : n u /hu=>//=.
  hauto lq:on rew:off inv:SNe db:sn.
  move => n a b ha hb ihb a0 b0 ?. subst.
  inversion ha; subst.
  move {ihb}.
  hecrush use:sn_unmorphing.
  hauto lq:on db:sn.
Qed.

Lemma SN_ProjInv : forall n p (a : PTm n), SN (PProj p a) -> SN a.
Proof.
  move => n p a. move E : (PProj p a) => u hu.
  move : p a E.
  elim : n u / hu => //=.
  hauto lq:on rew:off inv:SNe db:sn.
  hauto lq:on rew:off inv:TRedSN db:sn.
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
  - move => a ha iha b.
    inversion 1; subst.
    + have : ERed.R (PApp (ren_PTm shift a0) (VarPTm var_zero))  (PApp (ren_PTm shift b) (VarPTm var_zero)).
      apply ERed.AppCong; eauto using ERed.refl.
      sfirstorder use:ERed.renaming.
      move /iha.
      move /SN_AppInv => [+ _].
      hauto l:on use:sn_antirenaming.
    + sauto lq:on.
  - sauto lq:on.
  - sauto lq:on.
  - move => a b ha iha c h0.
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
    + move => a0 a2 ha' [*]. subst.
      exists (PProj PL a1).
      split. sauto.
      sauto lq:on.
    + sauto lq:on rew:off.
  - move => a b ha iha c.
    elim /ERed.inv => //=_.
    move => p a0 a1 + [*]. subst.
    elim /ERed.inv => //=_.
    + move => a0  a2 h1 [*]. subst.
      exists (PProj PR a1).
      split. sauto.
      sauto lq:on.
    + sauto lq:on.
  - sauto.
Qed.

Module RRed.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Eta ***********************)
  | AppAbs a b :
    R (PApp (PAbs a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

  (*************** Congruence ********************)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (PAbs a0) (PAbs a1)
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

  Lemma AppAbs' n a (b : PTm n) u :
    u = (subst_PTm (scons b VarPTm) a) ->
    R (PApp (PAbs a) b)  u.
  Proof.
    move => ->. by apply AppAbs. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n a b m ξ /=.
    apply AppAbs'. by asimpl.
    all : qauto ctrs:R.
  Qed.


  Lemma antirenaming n m (a : PTm n) (b : PTm m) (ξ : fin n -> fin m) :
    R (ren_PTm ξ a) b -> exists b0, R a b0 /\ ren_PTm ξ b0 = b.
  Proof.
    move E : (ren_PTm ξ a) => u h.
    move : n ξ a E. elim : m u b/h.
    - move => n a b m ξ []//=. move => []//= t t0 [*]. subst.
      eexists. split. apply AppAbs. by asimpl.
    - move => n p a b m ξ []//=.
      move => p0 []//=. hauto q:on ctrs:R.
    - move => n a0 a1 ha iha m ξ []//=.
      move => p [*]. subst.
      spec_refl.
      move : iha => [t [h0 h1]]. subst.
      eexists. split. eauto using AbsCong.
      by asimpl.
    - move => n a0 a1 b ha iha m ξ []//=.
      hauto lq:on ctrs:R.
    - move => n a b0 b1 h ih m ξ []//=.
      hauto lq:on ctrs:R.
    - move => n a0 a1 b ha iha m ξ []//=.
      hauto lq:on ctrs:R.
    - move => n a b0 b1 h ih m ξ []//=.
      hauto lq:on ctrs:R.
    - move => n p a0 a1 ha iha m ξ []//=.
      hauto lq:on ctrs:R.
  Qed.

End RRed.

Module RPar.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0)  (subst_PTm (scons b1 VarPTm) a1)

  | ProjPair p a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) (if p is PL then a1 else b1)

  (*************** Congruence ********************)
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
  | VarTm i :
    R (VarPTm i) (VarPTm i).

  Lemma refl n (a : PTm n) : R a a.
  Proof.
    elim : n / a; hauto lq:on ctrs:R.
  Qed.

  Derive Dependent Inversion inv with (forall n (a b : PTm n), R a b) Sort Prop.

  Lemma AppAbs' n a0 a1 (b0 b1 : PTm n) u :
    u = (subst_PTm (scons b1 VarPTm) a1) ->
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0)  u.
  Proof. move => ->. apply AppAbs. Qed.

  Lemma ProjPair' n p u (a0 a1 b0 b1 : PTm n) :
    u = (if p is PL then a1 else b1) ->
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) u.
  Proof. move => ->. apply ProjPair. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n a0 a1 b0 b1 ha iha hb ihb m ξ /=.
    eapply AppAbs'; eauto. by asimpl.
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
    move => + h. move : m ρ0 ρ1. elim : n a b / h => n.
    move => a0 a1 b0 b1 ha iha hb ihb m ρ0 ρ1 hρ /=.
    eapply AppAbs'; eauto; cycle 1. sfirstorder use:morphing_up.
    by asimpl.
    all : hauto lq:on ctrs:R use:morphing_up, ProjPair'.
  Qed.

  Lemma substing n m (a : PTm n) b (ρ : fin n -> PTm m) :
    R a b ->
    R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    hauto l:on use:morphing, refl.
  Qed.


  Lemma cong n (a0 a1 : PTm (S n)) b0 b1  :
    R a0 a1 ->
    R b0 b1 ->
    R (subst_PTm (scons b0 VarPTm) a0) (subst_PTm (scons b1 VarPTm) a1).
  Proof.
    move => h0 h1. apply morphing=>//.
    hauto q:on inv:option ctrs:R.
  Qed.

  Lemma FromRRed n (a b : PTm n) :
    RRed.R a b -> RPar.R a b.
  Proof.
    induction 1; qauto l:on use:RPar.refl ctrs:RPar.R.
  Qed.

End RPar.

Lemma red_sn_preservation n :
  (forall (a : PTm n) (s : SNe a), forall b, RPar.R a b -> SNe b) /\
  (forall (a : PTm n) (s : SN a), forall b, RPar.R a b -> SN b) /\
  (forall (a b : PTm n) (_ : TRedSN a b), forall c, RPar.R a c -> exists d, TRedSN' c d /\ RPar.R b d).
Proof.
  move : n. apply sn_mutual => n.
  - hauto l:on inv:RPar.R.
  - qauto l:on inv:RPar.R,SNe,SN ctrs:SNe.
  - hauto lq:on inv:RPar.R, SNe ctrs:SNe.
  - qauto l:on ctrs:SN inv:RPar.R.
  - hauto lq:on ctrs:SN inv:RPar.R.
  - hauto lq:on ctrs:SN.
  - hauto q:on ctrs:SN inv:SN, TRedSN'.
  - move => a b ha iha hb ihb.
    elim /RPar.inv : ihb => //=_.
    + move => a0 a1 b0 b1 ha0 hb0 [*]. subst.
      eauto using RPar.cong, T_Refl.
    + move => a0 a1 b0 b1 h0 h1 [*]. subst.
      elim /RPar.inv : h0 => //=_.
      move => a0 a2 h [*]. subst.
      eexists. split. apply T_Once. hauto lq:on ctrs:TRedSN.
      eauto using RPar.cong.
  - move => a0 a1 b hb ihb ha iha c.
    elim /RPar.inv => //=_.
    + qauto l:on inv:TRedSN.
    + move => a2 a3 b0 b1 h0 h1 [*]. subst.
      have {}/iha := h0.
      move => [d [iha0 iha1]].
      hauto lq:on rew:off inv:TRedSN' ctrs:TRedSN, RPar.R, TRedSN'.
  - hauto lq:on inv:RPar.R ctrs:RPar.R, TRedSN', TRedSN.
  - hauto lq:on inv:RPar.R ctrs:RPar.R, TRedSN', TRedSN.
  - sauto.
Qed.

Function tstar {n} (a : PTm n) :=
  match a with
  | VarPTm i => a
  | PAbs a => PAbs (tstar a)
  | PApp (PAbs a) b => subst_PTm (scons (tstar b) VarPTm) (tstar a)
  | PApp a b => PApp (tstar a) (tstar b)
  | PPair a b => PPair (tstar a) (tstar b)
  | PProj p (PPair a b) => if p is PL then (tstar a) else (tstar b)
  | PProj p a => PProj p (tstar a)
  end.

Module TStar.
  Lemma renaming n m (ξ : fin n -> fin m) (a : PTm n) :
    tstar (ren_PTm ξ a) = ren_PTm ξ (tstar a).
  Proof.
    move : m ξ.
    apply tstar_ind => {}n {}a => //=.
    - hauto lq:on.
    - scongruence.
    - move => a0 b ? h ih m ξ.
      rewrite ih.
      asimpl; congruence.
    - qauto l:on.
    - scongruence.
    - hauto q:on.
    - qauto l:on.
  Qed.

  Lemma pair n (a b : PTm n) :
    tstar (PPair a b) = PPair (tstar a) (tstar b).
    reflexivity. Qed.
End TStar.

Definition isPair {n} (a : PTm n) := if a is PPair _ _ then true else false.

Lemma tstar_proj n (a : PTm n) :
  ((~~ isPair a) /\ forall p, tstar (PProj p a) = PProj p (tstar a)) \/
    exists a0 b0, a = PPair a0 b0 /\ forall p, tstar (PProj p a) = (if p is PL then (tstar a0) else (tstar b0)).
Proof. sauto lq:on. Qed.

Module ERed'.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Eta ***********************)
  | AppEta a :
    R (PAbs (PApp (ren_PTm shift a) (VarPTm var_zero))) a
  | PairEta a :
    R (PPair (PProj PL a) (PProj PR a)) a
  (*************** Congruence ********************)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (PAbs a0) (PAbs a1)
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

  Lemma AppEta' n a (u : PTm n) :
    u = (PAbs (PApp (ren_PTm shift a) (VarPTm var_zero))) ->
    R u a.
  Proof. move => ->. apply AppEta. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n a m ξ /=.
    eapply AppEta'; eauto. by asimpl.
    all : qauto ctrs:R.
  Qed.

  Lemma morphing_ren n m p (ρ0 ρ1 : fin n -> PTm m) (ξ : fin m -> fin p) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((funcomp (ren_PTm ξ) ρ0) i) ((funcomp (ren_PTm ξ) ρ1) i)).
  Proof. eauto using renaming. Qed.

End ERed'.

Module EReds.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:ERed'.R.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong n (a b : PTm (S n)) :
    rtc ERed'.R a b ->
    rtc ERed'.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    rtc ERed'.R a0 a1 ->
    rtc ERed'.R b0 b1 ->
    rtc ERed'.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    rtc ERed'.R a0 a1 ->
    rtc ERed'.R b0 b1 ->
    rtc ERed'.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1  : PTm n) :
    rtc ERed'.R a0 a1 ->
    rtc ERed'.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.
End EReds.

Module RReds.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:RRed.R.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong n (a b : PTm (S n)) :
    rtc RRed.R a b ->
    rtc RRed.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    rtc RRed.R a0 a1 ->
    rtc RRed.R b0 b1 ->
    rtc RRed.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    rtc RRed.R a0 a1 ->
    rtc RRed.R b0 b1 ->
    rtc RRed.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1  : PTm n) :
    rtc RRed.R a0 a1 ->
    rtc RRed.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    rtc RRed.R a b -> rtc RRed.R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ. elim : a b /h; hauto lq:on ctrs:rtc use:RRed.renaming.
  Qed.

End RReds.


Lemma ne_nf_ren n m (a : PTm n) (ξ : fin n -> fin m) :
  (ne a <-> ne (ren_PTm ξ a)) /\ (nf a <-> nf (ren_PTm ξ a)).
Proof.
  move : m ξ. elim : n / a => //=; solve [hauto b:on].
Qed.

Lemma ne_ered n (a b : PTm n) (h : ERed'.R a b ) :
  (ne a -> ne b) /\ (nf a -> nf b).
Proof.
  elim : n a b /h=>//=; hauto qb:on use:ne_nf_ren, ne_nf.
Qed.

Definition ishf {n} (a : PTm n) :=
  match a with
  | PPair _ _ => true
  | PAbs _ => true
  | _ => false
  end.

Module NeERed.
  Inductive R_nonelim {n} : PTm n -> PTm n ->  Prop :=
  (****************** Eta ***********************)
  | AppEta a0 a1 :
    ~~ ishf a0 ->
    R_elim a0 a1 ->
    R_nonelim (PAbs (PApp (ren_PTm shift a0) (VarPTm var_zero))) a1
  | PairEta a0 a1 :
    ~~ ishf a0 ->
    R_elim a0 a1 ->
    R_nonelim (PPair (PProj PL a0) (PProj PR a0)) a1
  (*************** Congruence ********************)
  | AbsCong a0 a1 :
    R_nonelim a0 a1 ->
    R_nonelim (PAbs a0) (PAbs a1)
  | AppCong a0 a1 b0 b1 :
    R_elim a0 a1 ->
    R_nonelim b0 b1 ->
    R_nonelim (PApp a0 b0) (PApp a1 b1)
  | PairCong a0 a1 b0 b1 :
    R_nonelim a0 a1 ->
    R_nonelim b0 b1 ->
    R_nonelim (PPair a0 b0) (PPair a1 b1)
  | ProjCong p a0 a1 :
    R_elim a0 a1 ->
    R_nonelim (PProj p a0) (PProj p a1)
  | VarTm i :
    R_nonelim (VarPTm i) (VarPTm i)
  with R_elim {n} : PTm n -> PTm n -> Prop :=
  | NAbsCong a0 a1 :
    R_nonelim a0 a1 ->
    R_elim (PAbs a0) (PAbs a1)
  | NAppCong a0 a1 b0 b1 :
    R_elim a0 a1 ->
    R_nonelim b0 b1 ->
    R_elim (PApp a0 b0) (PApp a1 b1)
  | NPairCong a0 a1 b0 b1 :
    R_nonelim a0 a1 ->
    R_nonelim b0 b1 ->
    R_elim (PPair a0 b0) (PPair a1 b1)
  | NProjCong p a0 a1 :
    R_elim a0 a1 ->
    R_elim (PProj p a0) (PProj p a1)
  | NVarTm i :
    R_elim (VarPTm i) (VarPTm i).

  Scheme ered_elim_ind := Induction for R_elim Sort Prop
      with ered_nonelim_ind := Induction for R_nonelim Sort Prop.

  Combined Scheme ered_mutual from ered_elim_ind, ered_nonelim_ind.

  Lemma R_elim_nf n :
    (forall (a b : PTm n), R_elim a b -> nf b -> nf a) /\
      (forall (a b : PTm n), R_nonelim a b -> nf b -> nf a).
  Proof.
    move : n. apply ered_mutual => n //=.
    - move => a0 a1 b0 b1 h ih h' ih' /andP [h0 h1].
      have hb0 : nf b0 by eauto.
      suff : ne a0 by qauto b:on.
      qauto l:on inv:R_elim.
    - hauto lb:on.
    - hauto lq:on inv:R_elim.
    - move => a0 a1 /negP ha' ha ih ha1.
      have {ih} := ih ha1.
      move => ha0.
      suff : ne a0 by hauto lb:on drew:off use:ne_nf_ren.
      inversion ha; subst => //=.
    - move => a0 a1 /negP ha' ha ih ha1.
      have {}ih := ih ha1.
      have : ne a0 by hauto lq:on inv:PTm.
      qauto lb:on.
    - move => a0 a1 b0 b1 ha iha hb ihb /andP [h0 h1].
      have {}ihb := ihb h1.
      have {}iha := iha ltac:(eauto using ne_nf).
      suff : ne a0 by hauto lb:on.
      move : ha h0. hauto lq:on inv:R_elim.
    - hauto lb: on drew: off.
    - hauto lq:on rew:off inv:R_elim.
  Qed.

  Lemma R_nonelim_nothf n (a b : PTm n) :
    R_nonelim a b ->
    ~~ ishf a ->
    R_elim a b.
  Proof.
    move => h. elim : n a b /h=>//=; hauto lq:on ctrs:R_elim.
  Qed.

  Lemma R_elim_nonelim n (a b : PTm n) :
    R_elim a b ->
    R_nonelim a b.
    move => h. elim : n a b /h=>//=; hauto lq:on ctrs:R_nonelim.
  Qed.

End NeERed.

Module Type NoForbid.
  Parameter P : forall n, PTm n -> Prop.
  Arguments P {n}.

  Axiom P_ERed : forall n (a b : PTm n), ERed.R a b -> P a -> P b.
  Axiom P_RRed : forall n (a b : PTm n), RRed.R a b -> P a -> P b.
  Axiom P_AppPair : forall n (a b c : PTm n), ~ P (PApp (PPair a b) c).
  Axiom P_ProjAbs : forall n p (a : PTm (S n)), ~ P (PProj p (PAbs a)).

  Axiom P_AppInv : forall n (a b : PTm n), P (PApp a b) -> P a /\ P b.
  Axiom P_AbsInv : forall n (a : PTm (S n)), P (PAbs a) -> P a.
  Axiom P_PairInv : forall n (a b : PTm n), P (PPair a b) -> P a /\ P b.
  Axiom P_ProjInv : forall n p (a : PTm n), P (PProj p a) -> P a.
  Axiom P_renaming : forall n m (ξ : fin n -> fin m) a , P (ren_PTm ξ a) <-> P a.

End NoForbid.

Module Type NoForbid_FactSig (M : NoForbid).

  Axiom P_EReds : forall n (a b : PTm n), rtc ERed.R a b -> M.P a -> M.P b.

  Axiom P_RReds : forall n (a b : PTm n), rtc RRed.R a b -> M.P a -> M.P b.

End NoForbid_FactSig.

Module NoForbid_Fact (M : NoForbid) : NoForbid_FactSig M.
  Import M.

  Lemma P_EReds : forall n (a b : PTm n), rtc ERed.R a b -> P a -> P b.
  Proof.
    induction 1; eauto using P_ERed, rtc_l, rtc_refl.
  Qed.

  Lemma P_RReds : forall n (a b : PTm n), rtc RRed.R a b -> P a -> P b.
  Proof.
    induction 1; eauto using P_RRed, rtc_l, rtc_refl.
  Qed.
End NoForbid_Fact.

Module SN_NoForbid : NoForbid.
  Definition P := @SN.
  Arguments P {n}.

  Lemma P_ERed : forall n (a b : PTm n), ERed.R a b -> P a -> P b.
  Proof. sfirstorder use:ered_sn_preservation. Qed.

  Lemma P_RRed : forall n (a b : PTm n), RRed.R a b -> P a -> P b.
  Proof. hauto q:on use:red_sn_preservation, RPar.FromRRed. Qed.

  Lemma P_AppPair : forall n (a b c : PTm n), ~ P (PApp (PPair a b) c).
  Proof. sfirstorder use:PProjPair_imp. Qed.

  Lemma P_ProjAbs : forall n p (a : PTm (S n)), ~ P (PProj p (PAbs a)).
  Proof. sfirstorder use:PProjAbs_imp. Qed.

  Lemma P_AppInv : forall n (a b : PTm n), P (PApp a b) -> P a /\ P b.
  Proof. sfirstorder use:SN_AppInv. Qed.

  Lemma P_PairInv : forall n (a b : PTm n), P (PPair a b) -> P a /\ P b.
    move => n a b. move E : (PPair a b) => u h.
    move : a b E. elim : n u / h; sauto lq:on rew:off. Qed.

  Lemma P_ProjInv : forall n p (a : PTm n), P (PProj p a) -> P a.
  Proof. sfirstorder use:SN_ProjInv. Qed.

  Lemma P_AbsInv : forall n (a : PTm (S n)), P (PAbs a) -> P a.
  Proof.
    move => n a. move E : (PAbs a) => u h.
    move : E. move : a.
    induction h; sauto lq:on rew:off.
  Qed.

  Lemma P_renaming : forall n m (ξ : fin n -> fin m) a , P (ren_PTm ξ a) <-> P  a.
  Proof. hauto lq:on use:sn_antirenaming, sn_renaming. Qed.

End SN_NoForbid.

Module UniqueNF (M : NoForbid) (MFacts : NoForbid_FactSig M).
  Import M MFacts.
  #[local]Hint Resolve P_ERed P_RRed P_AppPair P_ProjAbs : forbid.

  Lemma η_split n (a0 a1 : PTm n) :
    ERed.R a0 a1 ->
    P a0 ->
    exists b, rtc RRed.R a0 b /\ NeERed.R_nonelim b a1.
  Proof.
    move => h. elim : n a0 a1 /h .
    - move => n a0 a1 ha ih /[dup] hP.
      move /P_AbsInv /P_AppInv => [/P_renaming ha0 _].
      have {ih} := ih ha0.
      move => [b [ih0 ih1]].
      case /orP : (orNb (ishf b)).
      exists (PAbs (PApp (ren_PTm shift b) (VarPTm var_zero))).
      split. apply RReds.AbsCong. apply RReds.AppCong; auto using rtc_refl.
      by eauto using RReds.renaming.
      apply NeERed.AppEta=>//.
      sfirstorder use:NeERed.R_nonelim_nothf.

      case : b ih0 ih1 => //=.
      + move => p ih0 ih1 _.
        set q := PAbs _.
        suff : rtc RRed.R q (PAbs p) by sfirstorder.
        subst q.
        apply : rtc_r.
        apply RReds.AbsCong. apply RReds.AppCong.
        by eauto using RReds.renaming.
        apply rtc_refl.
        apply : RRed.AbsCong => /=.
        apply RRed.AppAbs'. by asimpl.
      (* violates SN *)
      + move => p p0 h. exfalso.
        have : P (PApp (ren_PTm shift a0) (VarPTm var_zero))
          by sfirstorder use:P_AbsInv.

        have : rtc RRed.R (PApp (ren_PTm shift a0) (VarPTm var_zero))
                 (PApp (ren_PTm shift (PPair p p0)) (VarPTm var_zero))
          by hauto lq:on use:RReds.AppCong, RReds.renaming, rtc_refl.

        move : P_RReds. repeat move/[apply] => /=.
        hauto l:on use:P_AppPair.
    - move => n a0 a1 h ih /[dup] hP.
      move /P_PairInv => [/P_ProjInv + _].
      move : ih => /[apply].
      move => [b [ih0 ih1]].
      case /orP : (orNb (ishf b)).
      exists (PPair (PProj PL b) (PProj PR b)).
      split. sfirstorder use:RReds.PairCong,RReds.ProjCong.
      hauto lq:on ctrs:NeERed.R_nonelim use:NeERed.R_nonelim_nothf.

      case : b ih0 ih1 => //=.
      (* violates SN *)
      + move => p ?. exfalso.
        have {}hP : P (PProj PL a0) by sfirstorder use:P_PairInv.
        have : rtc RRed.R (PProj PL a0) (PProj PL (PAbs p))
          by eauto using RReds.ProjCong.
        move : P_RReds hP. repeat move/[apply] => /=.
        sfirstorder use:P_ProjAbs.
      + move => t0 t1 ih0 h1 _.
        exists (PPair t0 t1).
        split => //=.
        apply RReds.PairCong.
        apply : rtc_r; eauto using RReds.ProjCong.
        apply RRed.ProjPair.
        apply : rtc_r; eauto using RReds.ProjCong.
        apply RRed.ProjPair.
    - hauto lq:on ctrs:NeERed.R_nonelim use:RReds.AbsCong, P_AbsInv.
    - move => n a0 a1 b0 b1 ha iha hb ihb.
      move => /[dup] hP /P_AppInv [hP0 hP1].
      have {iha} [a2 [iha0 iha1]]  := iha hP0.
      have {ihb} [b2 [ihb0 ihb1]]  := ihb hP1.
      case /orP : (orNb (ishf a2)) => [h|].
      + exists (PApp a2 b2). split; first by eauto using RReds.AppCong.
        hauto lq:on ctrs:NeERed.R_nonelim use:NeERed.R_nonelim_nothf.
      + case : a2 iha0 iha1 => //=.
        * move => p h0 h1 _.
          inversion h1; subst.
          ** exists (PApp a2 b2).
             split.
             apply : rtc_r.
             apply RReds.AppCong; eauto.
             apply RRed.AppAbs'. by asimpl.
             hauto lq:on ctrs:NeERed.R_nonelim.
          ** hauto lq:on ctrs:NeERed.R_nonelim,NeERed.R_elim use:RReds.AppCong.
        (* Impossible *)
        * move => u0 u1 h. exfalso.
          have : rtc RRed.R (PApp a0 b0) (PApp (PPair u0 u1) b0)
            by hauto lq:on ctrs:rtc use:RReds.AppCong.
          move : P_RReds hP; repeat move/[apply].
          sfirstorder use:P_AppPair.
    - hauto lq:on ctrs:NeERed.R_nonelim use:RReds.PairCong, P_PairInv.
    - move => n p a0 a1 ha ih /[dup] hP /P_ProjInv.
      move : ih => /[apply]. move => [a2 [iha0 iha1]].
      case /orP : (orNb (ishf a2)) => [h|].
      exists (PProj p a2).
      split.  eauto using RReds.ProjCong.
      qauto l:on ctrs:NeERed.R_nonelim, NeERed.R_elim use:NeERed.R_nonelim_nothf.

      case : a2 iha0 iha1 => //=.
      + move => u iha0. exfalso.
        have : rtc RRed.R (PProj p a0) (PProj p (PAbs u))
          by sfirstorder use:RReds.ProjCong ctrs:rtc.
        move : P_RReds hP. repeat move/[apply].
        sfirstorder use:P_ProjAbs.
      + move => u0 u1 iha0 iha1 _.
        inversion iha1; subst.
        * exists (PProj p a2). split.
          apply : rtc_r.
          apply RReds.ProjCong; eauto.
          clear. hauto l:on inv:PTag.
          hauto lq:on ctrs:NeERed.R_nonelim.
        * hauto lq:on ctrs:NeERed.R_nonelim,NeERed.R_elim use:RReds.ProjCong.
    - hauto lq:on ctrs:rtc, NeERed.R_nonelim.
  Qed.

End UniqueNF.

Lemma η_nf_to_ne n (a0 a1 : PTm n) :
  ERed'.R a0 a1 -> nf a0 -> ~~ ne a0 -> ne a1 ->
  (a0 = PAbs (PApp (ren_PTm shift a1) (VarPTm var_zero))) \/
    (a0 = PPair (PProj PL a1) (PProj PR a1)).
Proof.
  move => h.
  elim : n a0 a1 /h => n /=.
  - sfirstorder use:ne_ered.
  - hauto l:on use:ne_ered.
  - scongruence use:ne_ered.
  - hauto qb:on use:ne_ered, ne_nf.
  - move => a b0 b1 h0 ih0 /andP [h1 h2] h3 /andP [h4 h5].
    have {h3} : ~~ ne a by sfirstorder b:on.
    by move /negP.
  - hauto lqb:on.
  - sfirstorder b:on.
  - scongruence b:on.
Qed.
