From Ltac2 Require Ltac2.
Import Ltac2.Notations.

Import Ltac2.Control.
Require Import ssreflect ssrbool.
Require Import FunInd.
Require Import Arith.Wf_nat (well_founded_lt_compat).
Require Import Psatz.
From stdpp Require Import relations (rtc (..), rtc_once, rtc_r, sn).
From Hammer Require Import Tactics.
Require Import Autosubst2.core Autosubst2.fintype Autosubst2.syntax.
Require Import Btauto.
Require Import Cdcl.Itauto.

Ltac2 spec_refl () :=
  List.iter
    (fun a => match a with
           | (i, _, _) =>
               let h := Control.hyp i in
               try (specialize $h with (1 := eq_refl))
           end)  (Control.hyps ()).

Ltac spec_refl := ltac2:(spec_refl ()).

Module EPar.
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
    R (VarPTm i) (VarPTm i)
  | Univ i :
    R (PUniv i) (PUniv i)
  | BindCong p A0 A1 B0 B1 :
    R A0 A1 ->
    R B0 B1 ->
    R (PBind p A0 B0) (PBind p A1 B1)
  | BotCong :
    R PBot PBot.

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

End EPar.

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
| N_Bot :
  SNe PBot
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
| N_Bind p A B :
  SN A ->
  SN B ->
  SN (PBind p A B)
| N_Univ i :
  SN (PUniv i)
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

Definition ishf {n} (a : PTm n) :=
  match a with
  | PPair _ _ => true
  | PAbs _ => true
  | PUniv _ => true
  | PBind _ _ _ => true
  | _ => false
  end.
Definition isbind {n} (a : PTm n) := if a is PBind _ _ _ then true else false.

Definition isuniv {n} (a : PTm n) := if a is PUniv _ then true else false.

Definition ispair {n} (a : PTm n) :=
  match a with
  | PPair _ _ => true
  | _ => false
  end.

Definition isabs {n} (a : PTm n) :=
  match a with
  | PAbs _ => true
  | _ => false
  end.

Definition ishf_ren n m (a : PTm n)  (ξ : fin n -> fin m) :
  ishf (ren_PTm ξ a) = ishf a.
Proof. case : a => //=. Qed.

Definition isabs_ren n m (a : PTm n)  (ξ : fin n -> fin m) :
  isabs (ren_PTm ξ a) = isabs a.
Proof. case : a => //=. Qed.

Definition ispair_ren n m (a : PTm n)  (ξ : fin n -> fin m) :
  ispair (ren_PTm ξ a) = ispair a.
Proof. case : a => //=. Qed.

Lemma PProj_imp n p a :
  @ishf n a ->
  ~~ ispair a ->
  ~ SN (PProj p a).
Proof.
  move => + + h. move E  : (PProj p a) h => u h.
  move : p a E.
  elim : n u / h => //=.
  hauto lq:on inv:SNe,PTm.
  hauto lq:on inv:TRedSN.
Qed.

Lemma PAbs_imp n a b :
  @ishf n a ->
  ~~ isabs a ->
  ~ SN (PApp a b).
Proof.
  move => + + h. move E : (PApp a b) h => u h.
  move : a b E. elim  : n u /h=>//=.
  hauto lq:on inv:SNe,PTm.
  hauto lq:on inv:TRedSN.
Qed.

Lemma PProjAbs_imp n p (a : PTm (S n)) :
  ~ SN (PProj p (PAbs a)).
Proof.
  move E : (PProj p (PAbs a)) => u hu.
  move : p a E.
  elim : n u / hu=>//=.
  hauto lq:on inv:SNe.
  hauto lq:on inv:TRedSN.
Qed.

Lemma PAppPair_imp n (a b0 b1 : PTm n ) :
  ~ SN (PApp (PPair b0 b1) a).
Proof.
  move E : (PApp (PPair b0 b1) a) => u hu.
  move : a b0 b1 E.
  elim : n u / hu=>//=.
  hauto lq:on inv:SNe.
  hauto lq:on inv:TRedSN.
Qed.

Lemma PAppBind_imp n p (A : PTm n) B b :
  ~ SN (PApp (PBind p A B) b).
Proof.
  move E :(PApp (PBind p A B) b) => u hu.
  move : p A B b E.
  elim : n u /hu=> //=.
  hauto lq:on inv:SNe.
  hauto lq:on inv:TRedSN.
Qed.

Lemma PProjBind_imp n p p' (A : PTm n) B :
  ~ SN (PProj p (PBind p' A B)).
Proof.
  move E :(PProj p (PBind p' A B)) => u hu.
  move : p p' A B E.
  elim : n u /hu=>//=.
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
  | PUniv _ => false
  | PBind _ _ _ => false
  | PBot => true
  end
with nf {n} (a : PTm n) :=
  match a with
  | VarPTm i => true
  | PApp a b => ne a && nf b
  | PAbs a => nf a
  | PPair a b => nf a && nf b
  | PProj _ a => ne a
  | PUniv _ => true
  | PBind _ A B => nf A && nf B
  | PBot => true
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
  | fin _ -> _ _ => (ltac1:(case;qauto depth:2 db:sn))
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

Lemma epar_sn_preservation n :
  (forall (a : PTm n) (s : SNe a), forall b, EPar.R a b -> SNe b) /\
  (forall (a : PTm n) (s : SN a), forall b, EPar.R a b -> SN b) /\
  (forall (a b : PTm n) (_ : TRedSN a b), forall c, EPar.R a c -> exists d, TRedSN' c d /\ EPar.R b d).
Proof.
  move : n. apply sn_mutual => n.
  - sauto lq:on.
  - sauto lq:on.
  - sauto lq:on.
  - sauto lq:on.
  - move => a b ha iha hb ihb b0.
    inversion 1; subst.
    + have /iha : (EPar.R (PProj PL a0) (PProj PL b0)) by sauto lq:on.
      sfirstorder use:SN_Proj.
    + sauto lq:on.
  - move => a ha iha b.
    inversion 1; subst.
    + have : EPar.R (PApp (ren_PTm shift a0) (VarPTm var_zero))  (PApp (ren_PTm shift b) (VarPTm var_zero)).
      apply EPar.AppCong; eauto using EPar.refl.
      sfirstorder use:EPar.renaming.
      move /iha.
      move /SN_AppInv => [+ _].
      hauto l:on use:sn_antirenaming.
    + sauto lq:on.
  - sauto lq:on.
  - sauto lq:on.
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
      hauto lq:on use:EPar.morphing, EPar.refl inv:option.
  - sauto.
  - move => a b hb ihb c.
    elim /EPar.inv => //= _.
    move => p a0 a1 ha [*]. subst.
    elim  /EPar.inv :  ha => //= _.
    + move => a0 a2 ha' [*]. subst.
      exists (PProj PL a1).
      split. sauto.
      sauto lq:on.
    + sauto lq:on rew:off.
  - move => a b ha iha c.
    elim /EPar.inv => //=_.
    move => p a0 a1 + [*]. subst.
    elim /EPar.inv => //=_.
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
    R (PProj p a0) (PProj p a1)
  | BindCong0 p A0 A1 B :
    R A0 A1 ->
    R (PBind p A0 B) (PBind p A1 B)
  | BindCong1 p A B0 B1 :
    R B0 B1 ->
    R (PBind p A B0) (PBind p A B1).

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

  Ltac2 rec solve_anti_ren () :=
    let x := Fresh.in_goal (Option.get (Ident.of_string "x")) in
    intro $x;
    lazy_match! Constr.type (Control.hyp x) with
    | fin _ -> _ _ => (ltac1:(case;hauto q:on depth:2 ctrs:RRed.R))
    | _ => solve_anti_ren ()
    end.

  Ltac solve_anti_ren := ltac2:(Control.enter solve_anti_ren).

  Lemma antirenaming n m (a : PTm n) (b : PTm m) (ξ : fin n -> fin m) :
    R (ren_PTm ξ a) b -> exists b0, R a b0 /\ ren_PTm ξ b0 = b.
  Proof.
    move E : (ren_PTm ξ a) => u h.
    move : n ξ a E. elim : m u b/h; try solve_anti_ren.
    - move => n a b m ξ []//=. move => []//= t t0 [*]. subst.
      eexists. split. apply AppAbs. by asimpl.
    - move => n p a b m ξ []//=.
      move => p0 []//=. hauto q:on ctrs:R.
  Qed.

  Lemma nf_imp n (a b : PTm n) :
    nf a ->
    R a b -> False.
  Proof. move/[swap]. induction 1; hauto qb:on inv:PTm. Qed.

  Lemma FromRedSN n (a b : PTm n) :
    TRedSN a b ->
    RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:RRed.R. Qed.

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
    R (VarPTm i) (VarPTm i)
  | Univ i :
    R (PUniv i) (PUniv i)
  | BindCong p A0 A1 B0 B1 :
    R A0 A1 ->
    R B0 B1 ->
    R (PBind p A0 B0) (PBind p A1 B1)
  | BotCong :
    R PBot PBot.

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

  Function tstar {n} (a : PTm n) :=
    match a with
    | VarPTm i => a
    | PAbs a => PAbs (tstar a)
    | PApp (PAbs a) b => subst_PTm (scons (tstar b) VarPTm) (tstar a)
    | PApp a b => PApp (tstar a) (tstar b)
    | PPair a b => PPair (tstar a) (tstar b)
    | PProj p (PPair a b) => if p is PL then (tstar a) else (tstar b)
    | PProj p a => PProj p (tstar a)
    | PUniv i => PUniv i
    | PBind p A B => PBind p (tstar A) (tstar B)
    | PBot => PBot
    end.

  Lemma triangle n (a b : PTm n) :
    RPar.R a b -> RPar.R b (tstar a).
  Proof.
    move : b.
    apply tstar_ind => {}n{}a.
    - hauto lq:on ctrs:R inv:R.
    - hauto lq:on ctrs:R inv:R.
    - hauto lq:on rew:off inv:R use:cong ctrs:R.
    - hauto lq:on ctrs:R inv:R.
    - hauto lq:on ctrs:R inv:R.
    - move => p a0 b ? ? ih b0. subst.
      elim /inv => //=_.
      + move => p a1 a2 b1 b2 h0 h1[*]. subst.
        by apply ih.
      + move => p a1 a2 ha [*]. subst.
        elim /inv : ha => //=_.
        move => a1 a3 b0 b1 h0 h1 [*]. subst.
        apply : ProjPair'; eauto using refl.
    - move => p a0 b ? p0 ?. subst.
      case : p0 => //= _.
      move => ih b0. elim /inv => //=_.
      + hauto l:on.
      + move => p a1 a2 ha [*]. subst.
        elim /inv : ha => //=_ > ? ? [*]. subst.
        apply : ProjPair'; eauto using refl.
    - hauto lq:on ctrs:R inv:R.
    - hauto lq:on ctrs:R inv:R.
    - hauto lq:on ctrs:R inv:R.
    - hauto lq:on ctrs:R inv:R.
  Qed.

  Lemma diamond n (a b c : PTm n) :
    R a b -> R a c -> exists d, R b d /\ R c d.
  Proof. eauto using triangle. Qed.
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
  - hauto lq:on inv:RPar.R, SNe ctrs:SNe.
  - qauto l:on ctrs:SN inv:RPar.R.
  - hauto lq:on ctrs:SN inv:RPar.R.
  - hauto lq:on ctrs:SN.
  - hauto q:on ctrs:SN inv:SN, TRedSN'.
  - hauto lq:on ctrs:SN inv:RPar.R.
  - hauto lq:on ctrs:SN inv:RPar.R.
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

  Lemma BindCong n p (A0 A1 : PTm n) B0 B1 :
    rtc RRed.R A0 A1 ->
    rtc RRed.R B0 B1 ->
    rtc RRed.R (PBind p A0 B0) (PBind p A1 B1).
  Proof. solve_s. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    rtc RRed.R a b -> rtc RRed.R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ. elim : a b /h; hauto lq:on ctrs:rtc use:RRed.renaming.
  Qed.

  Lemma FromRPar n (a b : PTm n) (h : RPar.R a b) :
    rtc RRed.R a b.
  Proof.
    elim : n a b /h; eauto using AbsCong, AppCong, PairCong, ProjCong, rtc_refl, BindCong.
    move => n a0 a1 b0 b1 ha iha hb ihb.
    apply : rtc_r; last by apply RRed.AppAbs.
    by eauto using AppCong, AbsCong.

    move => n p a0 a1 b0 b1 ha iha hb ihb.
    apply : rtc_r; last by apply RRed.ProjPair.
    by eauto using PairCong, ProjCong.
  Qed.

  Lemma RParIff n (a b : PTm n) :
    rtc RRed.R a b <-> rtc RPar.R a b.
  Proof.
    split.
    induction 1; hauto l:on ctrs:rtc use:RPar.FromRRed, @relations.rtc_transitive.
    induction 1; hauto l:on ctrs:rtc use:FromRPar, @relations.rtc_transitive.
  Qed.

  Lemma nf_refl n (a b : PTm n) :
    rtc RRed.R a b -> nf a -> a = b.
  Proof. induction 1; sfirstorder use:RRed.nf_imp. Qed.

  Lemma FromRedSNs n (a b : PTm n) :
    rtc TRedSN a b ->
    rtc RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:rtc use:RRed.FromRedSN. Qed.

End RReds.


Lemma ne_nf_ren n m (a : PTm n) (ξ : fin n -> fin m) :
  (ne a <-> ne (ren_PTm ξ a)) /\ (nf a <-> nf (ren_PTm ξ a)).
Proof.
  move : m ξ. elim : n / a => //=; solve [hauto b:on].
Qed.

Module NeEPar.
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
  | Univ i :
    R_nonelim (PUniv i) (PUniv i)
  | BindCong p A0 A1 B0 B1 :
    R_nonelim A0 A1 ->
    R_nonelim B0 B1 ->
    R_nonelim (PBind p A0 B0) (PBind p A1 B1)
  | BotCong :
    R_nonelim PBot PBot
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
    R_elim (VarPTm i) (VarPTm i)
  | NUniv i :
    R_elim (PUniv i) (PUniv i)
  | NBindCong p A0 A1 B0 B1 :
    R_nonelim A0 A1 ->
    R_nonelim B0 B1 ->
    R_elim (PBind p A0 B0) (PBind p A1 B1)
  | NBotCong :
    R_elim PBot PBot.

  Scheme epar_elim_ind := Induction for R_elim Sort Prop
      with epar_nonelim_ind := Induction for R_nonelim Sort Prop.

  Combined Scheme epar_mutual from epar_elim_ind, epar_nonelim_ind.

  Lemma R_elim_nf n :
    (forall (a b : PTm n), R_elim a b -> nf b -> nf a) /\
      (forall (a b : PTm n), R_nonelim a b -> nf b -> nf a).
  Proof.
    move : n. apply epar_mutual => n //=.
    - move => a0 a1 b0 b1 h ih h' ih' /andP [h0 h1].
      have hb0 : nf b0 by eauto.
      suff : ne a0 by qauto b:on.
      hauto q:on inv:R_elim.
    - hauto lb:on.
    - hauto lq:on inv:R_elim.
    - hauto b:on.
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
    - sfirstorder b:on.
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

  Lemma ToEPar : forall n, (forall (a b : PTm n), R_elim a b -> EPar.R a b) /\
                 (forall (a b : PTm n), R_nonelim a b -> EPar.R a b).
  Proof.
    apply epar_mutual; qauto l:on ctrs:EPar.R.
  Qed.

End NeEPar.

Module Type NoForbid.
  Parameter P : forall n, PTm n -> Prop.
  Arguments P {n}.

  Axiom P_EPar : forall n (a b : PTm n), EPar.R a b -> P a -> P b.
  Axiom P_RRed : forall n (a b : PTm n), RRed.R a b -> P a -> P b.
  (* Axiom P_AppPair : forall n (a b c : PTm n), ~ P (PApp (PPair a b) c). *)
  (* Axiom P_ProjAbs : forall n p (a : PTm (S n)), ~ P (PProj p (PAbs a)). *)
  (* Axiom P_ProjBind : forall n p p' (A : PTm n) B, ~ P (PProj p (PBind p' A B)). *)
  (* Axiom P_AppBind : forall n p (A : PTm n) B b, ~ P (PApp (PBind p A B) b). *)
  Axiom PAbs_imp : forall n a b, @ishf n a -> ~~ isabs a -> ~ P (PApp a b).
  Axiom PProj_imp : forall  n p a, @ishf n a -> ~~ ispair a -> ~ P (PProj p a).

  Axiom P_AppInv : forall n (a b : PTm n), P (PApp a b) -> P a /\ P b.
  Axiom P_AbsInv : forall n (a : PTm (S n)), P (PAbs a) -> P a.
  Axiom P_BindInv : forall n p (A : PTm n) B, P (PBind p A B) -> P A /\ P B.

  Axiom P_PairInv : forall n (a b : PTm n), P (PPair a b) -> P a /\ P b.
  Axiom P_ProjInv : forall n p (a : PTm n), P (PProj p a) -> P a.
  Axiom P_renaming : forall n m (ξ : fin n -> fin m) a , P (ren_PTm ξ a) <-> P a.

End NoForbid.

Module Type NoForbid_FactSig (M : NoForbid).

  Axiom P_EPars : forall n (a b : PTm n), rtc EPar.R a b -> M.P a -> M.P b.

  Axiom P_RReds : forall n (a b : PTm n), rtc RRed.R a b -> M.P a -> M.P b.

End NoForbid_FactSig.

Module NoForbid_Fact (M : NoForbid) : NoForbid_FactSig M.
  Import M.

  Lemma P_EPars : forall n (a b : PTm n), rtc EPar.R a b -> P a -> P b.
  Proof.
    induction 1; eauto using P_EPar, rtc_l, rtc_refl.
  Qed.

  Lemma P_RReds : forall n (a b : PTm n), rtc RRed.R a b -> P a -> P b.
  Proof.
    induction 1; eauto using P_RRed, rtc_l, rtc_refl.
  Qed.
End NoForbid_Fact.

Module SN_NoForbid <: NoForbid.
  Definition P := @SN.
  Arguments P {n}.

  Lemma P_EPar : forall n (a b : PTm n), EPar.R a b -> P a -> P b.
  Proof. sfirstorder use:epar_sn_preservation. Qed.

  Lemma P_RRed : forall n (a b : PTm n), RRed.R a b -> P a -> P b.
  Proof. hauto q:on use:red_sn_preservation, RPar.FromRRed. Qed.

  Lemma PAbs_imp : forall n a b, @ishf n a -> ~~ isabs a -> ~ P (PApp a b).
    sfirstorder use:fp_red.PAbs_imp. Qed.
  Lemma PProj_imp : forall  n p a, @ishf n a -> ~~ ispair a -> ~ P (PProj p a).
    sfirstorder use:fp_red.PProj_imp. Qed.

  Lemma P_AppInv : forall n (a b : PTm n), P (PApp a b) -> P a /\ P b.
  Proof. sfirstorder use:SN_AppInv. Qed.

  Lemma P_PairInv : forall n (a b : PTm n), P (PPair a b) -> P a /\ P b.
    move => n a b. move E : (PPair a b) => u h.
    move : a b E. elim : n u / h; sauto lq:on rew:off. Qed.

  Lemma P_ProjInv : forall n p (a : PTm n), P (PProj p a) -> P a.
  Proof. sfirstorder use:SN_ProjInv. Qed.

  Lemma P_BindInv : forall n p (A : PTm n) B, P (PBind p A B) -> P A /\ P B.
  Proof.
    move => n p A B.
    move E : (PBind p A B) => u hu.
    move : p A B E. elim : n u /hu=>//=;sauto lq:on rew:off.
  Qed.

  Lemma P_AbsInv : forall n (a : PTm (S n)), P (PAbs a) -> P a.
  Proof.
    move => n a. move E : (PAbs a) => u h.
    move : E. move : a.
    induction h; sauto lq:on rew:off.
  Qed.

  Lemma P_renaming : forall n m (ξ : fin n -> fin m) a , P (ren_PTm ξ a) <-> P  a.
  Proof. hauto lq:on use:sn_antirenaming, sn_renaming. Qed.

  Lemma P_ProjBind : forall n p p' (A : PTm n) B, ~ P (PProj p (PBind p' A B)).
  Proof. sfirstorder use:PProjBind_imp. Qed.

  Lemma P_AppBind : forall n p (A : PTm n) B b, ~ P (PApp (PBind p A B) b).
  Proof. sfirstorder use:PAppBind_imp. Qed.

End SN_NoForbid.

Module NoForbid_FactSN := NoForbid_Fact SN_NoForbid.

Module UniqueNF (M : NoForbid) (MFacts : NoForbid_FactSig M).
  Import M MFacts.
  #[local]Hint Resolve P_EPar P_RRed PAbs_imp PProj_imp : forbid.

  Lemma η_split n (a0 a1 : PTm n) :
    EPar.R a0 a1 ->
    P a0 ->
    exists b, rtc RRed.R a0 b /\ NeEPar.R_nonelim b a1.
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
      apply NeEPar.AppEta=>//.
      sfirstorder use:NeEPar.R_nonelim_nothf.
      case /orP : (orbN (isabs b)).
      + case : b ih0 ih1 => //= p ih0 ih1 _ _.
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
      + move /P_AbsInv in hP.
        have {}hP : P (PApp (ren_PTm shift b) (VarPTm var_zero))
          by sfirstorder use:P_RReds, RReds.AppCong, @rtc_refl, RReds.renaming.
        move => ? ?.
        have ? : ~~ isabs (ren_PTm shift b) by scongruence use:isabs_ren.
        have ? : ishf (ren_PTm shift b) by scongruence use:ishf_ren.
        exfalso.
        sfirstorder use:PAbs_imp.
    - move => n a0 a1 h ih /[dup] hP.
      move /P_PairInv => [/P_ProjInv + _].
      move : ih => /[apply].
      move => [b [ih0 ih1]].
      case /orP : (orNb (ishf b)).
      exists (PPair (PProj PL b) (PProj PR b)).
      split. sfirstorder use:RReds.PairCong,RReds.ProjCong.
      hauto lq:on ctrs:NeEPar.R_nonelim use:NeEPar.R_nonelim_nothf.
      case /orP : (orbN (ispair b)).
      + case : b ih0 ih1 => //=.
        move => t0 t1 ih0 h1 _ _.
        exists (PPair t0 t1).
        split => //=.
        apply RReds.PairCong.
        apply : rtc_r; eauto using RReds.ProjCong.
        apply RRed.ProjPair.
        apply : rtc_r; eauto using RReds.ProjCong.
        apply RRed.ProjPair.
      + move => ? ?. exfalso.
        move/P_PairInv : hP=>[hP _].
        have : rtc RRed.R (PProj PL a0) (PProj PL b)
          by eauto using RReds.ProjCong.
        move : P_RReds hP. repeat move/[apply] => /=.
        sfirstorder use:PProj_imp.
    - hauto lq:on ctrs:NeEPar.R_nonelim use:RReds.AbsCong, P_AbsInv.
    - move => n a0 a1 b0 b1 ha iha hb ihb.
      move => /[dup] hP /P_AppInv [hP0 hP1].
      have {iha} [a2 [iha0 iha1]]  := iha hP0.
      have {ihb} [b2 [ihb0 ihb1]]  := ihb hP1.
      case /orP : (orNb (ishf a2)) => [h|].
      + exists (PApp a2 b2). split; first by eauto using RReds.AppCong.
        hauto lq:on ctrs:NeEPar.R_nonelim use:NeEPar.R_nonelim_nothf.
      + case /orP : (orbN (isabs a2)).
        (* case : a2 iha0 iha1 => //=. *)
        * case : a2 iha0 iha1 => //= p h0 h1 _ _.
          inversion h1; subst.
          ** exists (PApp a2 b2).
             split.
             apply : rtc_r.
             apply RReds.AppCong; eauto.
             apply RRed.AppAbs'. by asimpl.
             hauto lq:on ctrs:NeEPar.R_nonelim.
          ** hauto lq:on ctrs:NeEPar.R_nonelim,NeEPar.R_elim use:RReds.AppCong.
        (* Impossible *)
        * move =>*. exfalso.
          have : P (PApp a2 b0) by sfirstorder use:RReds.AppCong, @rtc_refl, P_RReds.
          sfirstorder use:PAbs_imp.
    - hauto lq:on ctrs:NeEPar.R_nonelim use:RReds.PairCong, P_PairInv.
    - move => n p a0 a1 ha ih /[dup] hP /P_ProjInv.
      move : ih => /[apply]. move => [a2 [iha0 iha1]].
      case /orP : (orNb (ishf a2)) => [h|].
      exists (PProj p a2).
      split.  eauto using RReds.ProjCong.
      qauto l:on ctrs:NeEPar.R_nonelim, NeEPar.R_elim use:NeEPar.R_nonelim_nothf.

      case /orP : (orNb (ispair a2)).
      + move => *. exfalso.
        have : rtc RRed.R (PProj p a0) (PProj p a2)
          by sfirstorder use:RReds.ProjCong ctrs:rtc.
        move : P_RReds hP. repeat move/[apply].
        sfirstorder use:PProj_imp.
      + case : a2 iha0 iha1 => //= u0 u1 iha0 iha1 _ _.
        inversion iha1; subst.
        * exists (PProj p a2). split.
          apply : rtc_r.
          apply RReds.ProjCong; eauto.
          clear. hauto l:on inv:PTag.
          hauto lq:on ctrs:NeEPar.R_nonelim.
        * hauto lq:on ctrs:NeEPar.R_nonelim,NeEPar.R_elim use:RReds.ProjCong.
    - hauto lq:on ctrs:rtc, NeEPar.R_nonelim.
    - hauto l:on.
    - hauto lq:on ctrs:NeEPar.R_nonelim, rtc use:RReds.BindCong, P_BindInv.
    - hauto lq:on ctrs:NeEPar.R_nonelim, rtc use:RReds.BindCong, P_BindInv.
  Qed.


  Lemma eta_postponement n a b c :
    @P n a ->
    EPar.R a b ->
    RRed.R b c ->
    exists d, rtc RRed.R a d /\ EPar.R d c.
  Proof.
    move => + h.
    move : c.
    elim : n a b /h => //=.
    - move => n a0 a1 ha iha c /[dup] hP /P_AbsInv /P_AppInv [/P_renaming hP' _] hc.
      move : iha (hP') (hc); repeat move/[apply].
      move => [d [h0 h1]].
      exists  (PAbs (PApp (ren_PTm shift d) (VarPTm var_zero))).
      split. hauto lq:on rew:off ctrs:rtc use:RReds.AbsCong, RReds.AppCong, RReds.renaming.
      hauto lq:on ctrs:EPar.R.
    - move => n a0 a1 ha iha c /P_PairInv [/P_ProjInv + _].
      move /iha => /[apply].
      move => [d [h0 h1]].
      exists (PPair (PProj PL d) (PProj PR d)).
      hauto lq:on ctrs:EPar.R use:RReds.PairCong, RReds.ProjCong.
    - move => n a0 a1 ha iha c  /P_AbsInv /[swap].
      elim /RRed.inv => //=_.
      move => a2 a3 + [? ?]. subst.
      move : iha; repeat move/[apply].
      hauto lq:on use:RReds.AbsCong ctrs:EPar.R.
    - move => n a0 a1 b0 b1 ha iha hb ihb c hP.
      elim /RRed.inv => //= _.
      + move => a2 b2 [*]. subst.
        have [hP' hP''] : P a0 /\ P b0 by sfirstorder use:P_AppInv.
        move {iha ihb}.
        move /η_split /(_ hP') : ha.
        move => [b [h0 h1]].
        inversion h1; subst.
        * inversion H0; subst.
          exists (subst_PTm (scons b0 VarPTm) a3).
          split; last by scongruence use:EPar.morphing.
          apply : relations.rtc_transitive.
          apply RReds.AppCong.
          eassumption.
          apply rtc_refl.
          apply : rtc_l.
          apply RRed.AppCong0. apply RRed.AbsCong. simpl. apply RRed.AppAbs.
          asimpl.
          apply rtc_once.
          apply RRed.AppAbs.
        * exfalso.
          move : hP h0. clear => hP h0.
          have : rtc RRed.R (PApp a0 b0) (PApp (PPair (PProj PL a1) (PProj PR a1)) b0)
            by qauto l:on ctrs:rtc use:RReds.AppCong.
          move : P_RReds hP. repeat move/[apply].
          sfirstorder use:PAbs_imp.
        * exists (subst_PTm (scons b0 VarPTm) a1).
          split.
          apply : rtc_r; last by apply RRed.AppAbs.
          hauto lq:on ctrs:rtc use:RReds.AppCong.
          hauto l:on inv:option use:EPar.morphing,NeEPar.ToEPar.
      + move => a2 a3 b2 ha2 [*]. subst.
        move : iha (ha2) {ihb} => /[apply].
        have : P a0 by sfirstorder use:P_AppInv.
        move /[swap]/[apply].
        move => [d [h0 h1]].
        exists (PApp d b0).
        hauto lq:on ctrs:EPar.R, rtc use:RReds.AppCong.
      + move => a2 b2 b3 hb2 [*]. subst.
        move {iha}.
        have : P b0 by sfirstorder use:P_AppInv.
        move : ihb hb2; repeat move /[apply].
        hauto lq:on rew:off ctrs:EPar.R, rtc use:RReds.AppCong.
    - move => n a0 a1 b0 b1 ha iha hb ihb c /P_PairInv [hP hP'].
      elim /RRed.inv => //=_;
        hauto lq:on rew:off ctrs:EPar.R, rtc use:RReds.PairCong.
    - move => n p a0 a1 ha iha c /[dup] hP /P_ProjInv hP'.
      elim / RRed.inv => //= _.
      + move => p0 a2 b0 [*]. subst.
        move : η_split hP'  ha; repeat move/[apply].
        move => [a1 [h0 h1]].
        inversion h1; subst.
        * sauto q:on ctrs:rtc use:RReds.ProjCong, PProj_imp, P_RReds.
        * inversion H0; subst.
          exists (if p is PL then a1 else b1).
          split; last by scongruence use:NeEPar.ToEPar.
          apply : relations.rtc_transitive.
          apply RReds.ProjCong; eauto.
          apply : rtc_l.
          apply RRed.ProjCong.
          apply RRed.PairCong0.
          apply RRed.ProjPair.
          apply : rtc_l.
          apply RRed.ProjCong.
          apply RRed.PairCong1.
          apply RRed.ProjPair.
          apply rtc_once. apply RRed.ProjPair.
        * exists (if p is PL then a3 else b1).
          split; last by hauto lq:on use:NeEPar.ToEPar.
          apply : relations.rtc_transitive.
          eauto using RReds.ProjCong.
          apply rtc_once.
          apply RRed.ProjPair.
      + move => p0 a2 a3 h0 [*]. subst.
        move : iha hP' h0;repeat move/[apply].
        hauto lq:on ctrs:rtc, EPar.R use:RReds.ProjCong.
    - hauto lq:on inv:RRed.R.
    - hauto lq:on inv:RRed.R ctrs:rtc.
    - sauto lq:on ctrs:EPar.R, rtc use:RReds.BindCong, P_BindInv, @relations.rtc_transitive.
    - hauto lq:on inv:RRed.R ctrs:rtc.
  Qed.

  Lemma η_postponement_star n a b c :
    @P n a ->
    EPar.R a b ->
    rtc RRed.R b c ->
    exists d, rtc RRed.R a d /\ EPar.R d c.
  Proof.
    move => + + h. move : a.
    elim : b c / h.
    - sfirstorder.
    - move => a0 a1 a2 ha ha' iha u hu hu'.
      move : eta_postponement (hu) ha hu'; repeat move/[apply].
      move => [d [h0 h1]].
      have : P d by sfirstorder use:P_RReds.
      move : iha h1; repeat move/[apply].
      sfirstorder use:@relations.rtc_transitive.
  Qed.

  Lemma η_postponement_star' n a b c :
    @P n a ->
    EPar.R a b ->
    rtc RRed.R b c ->
    exists d, rtc RRed.R a d /\ NeEPar.R_nonelim d c.
  Proof.
    move => h0 h1 h2.
    have : exists d, rtc RRed.R a d /\ EPar.R d c by eauto using η_postponement_star.
    move => [d [h3 /η_split]].
    move /(_ ltac:(eauto using P_RReds)).
    sfirstorder use:@relations.rtc_transitive.
  Qed.

End UniqueNF.

Module SN_UniqueNF := UniqueNF SN_NoForbid NoForbid_FactSN.

Module ERed.
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
    R (PProj p a0) (PProj p a1)
  | BindCong0 p A0 A1 B :
    R A0 A1 ->
    R (PBind p A0 B) (PBind p A1 B)
  | BindCong1 p A B0 B1 :
    R B0 B1 ->
    R (PBind p A B0) (PBind p A B1).

  Derive Dependent Inversion inv with (forall n (a b : PTm n), R a b) Sort Prop.

  Lemma ToEPar n (a b : PTm n) :
    ERed.R a b -> EPar.R a b.
  Proof.
    induction 1; hauto lq:on use:EPar.refl ctrs:EPar.R.
  Qed.

  Ltac2 rec solve_anti_ren () :=
    let x := Fresh.in_goal (Option.get (Ident.of_string "x")) in
    intro $x;
    lazy_match! Constr.type (Control.hyp x) with
    | fin _ -> _ _ => (ltac1:(case;hauto q:on depth:2 ctrs:ERed.R))
    | _ => solve_anti_ren ()
    end.

  Ltac solve_anti_ren := ltac2:(Control.enter solve_anti_ren).

  (* Definition down n m (ξ : fin n -> fin m) (a : fin (S n)) : fin m. *)
  (*   destruct a. *)
  (*   exact (ξ f). *)

  Lemma up_injective n m (ξ : fin n -> fin m) :
    (forall i j, ξ i = ξ j -> i = j) ->
    forall i j, (upRen_PTm_PTm ξ)  i = (upRen_PTm_PTm ξ) j -> i = j.
  Proof.
    sblast inv:option.
  Qed.

  Lemma ren_injective n m (a b : PTm n) (ξ : fin n -> fin m) :
    (forall i j, ξ i = ξ j -> i = j) ->
    ren_PTm ξ a = ren_PTm ξ b ->
    a = b.
  Proof.
    move : m ξ b.
    elim : n / a => //; try solve_anti_ren.

    move => n a iha m ξ []//=.
    move => u hξ [h].
    apply iha in h. by subst.
    destruct i, j=>//=.
    hauto l:on.

    move => n p A ihA B ihB m ξ []//=.
    move => b A0 B0  hξ [?]. subst.
    move => ?. have ? : A0 = A by firstorder. subst.
    move => ?. have : B = B0. apply : ihB; eauto.
    sauto.
    congruence.
  Qed.

  Lemma AppEta' n a u :
    u = (@PApp (S n) (ren_PTm shift a) (VarPTm var_zero)) ->
    R (PAbs u) a.
  Proof. move => ->. apply AppEta. Qed.

  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : m ξ.
    elim : n a b /h.

    move => n a m ξ /=.
    apply AppEta'; eauto. by asimpl.
    all : qauto ctrs:R.
  Qed.

  (* Need to generalize to injective renaming *)
  Lemma antirenaming n m (a : PTm n) (b : PTm m) (ξ : fin n -> fin m) :
    (forall i j, ξ i = ξ j -> i = j) ->
    R (ren_PTm ξ a) b -> exists b0, R a b0 /\ ren_PTm ξ b0 = b.
  Proof.
    move => hξ.
    move E : (ren_PTm ξ a) => u hu.
    move : n ξ a hξ E.
    elim : m u b / hu; try solve_anti_ren.
    - move => n a m ξ []//=.
      move => u hξ [].
      case : u => //=.
      move => u0 u1 [].
      case : u1 => //=.
      move => i /[swap] [].
      case : i => //= _ h.
      have : exists p, ren_PTm shift p = u0 by admit.
      move => [p ?]. subst.
      move : h. asimpl.
      replace (ren_PTm (funcomp shift ξ) p) with
        (ren_PTm shift (ren_PTm ξ p)); last by asimpl.
      move /ren_injective.
      move /(_ ltac:(hauto l:on)).
      move => ?. subst.
      exists p. split=>//. apply AppEta.
    - move => n a m ξ [] //=.
      move => u u0 hξ [].
      case : u => //=.
      case : u0 => //=.
      move => p p0 p1 p2 [? ?] [? h]. subst.
      have ? : p0 = p2 by eauto using ren_injective. subst.
      hauto l:on.
    - move => n a0 a1 ha iha m ξ []//= p hξ [?]. subst.
      sauto lq:on use:up_injective.
    - move => n p A B0 B1 hB ihB m ξ + hξ.
      case => //= p' A2 B2 [*]. subst.
      have : (forall i j, (upRen_PTm_PTm ξ) i = (upRen_PTm_PTm ξ) j -> i = j) by sauto.
      move => {}/ihB => ihB.
      spec_refl.
      sauto lq:on.
  Admitted.

End ERed.

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

  Lemma BindCong n p (A0 A1 : PTm n) B0 B1 :
    rtc ERed.R A0 A1 ->
    rtc ERed.R B0 B1 ->
    rtc ERed.R (PBind p A0 B0) (PBind p A1 B1).
  Proof. solve_s. Qed.


  Lemma renaming n m (a b : PTm n) (ξ : fin n -> fin m) :
    rtc ERed.R a b -> rtc ERed.R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof. induction 1; hauto l:on use:ERed.renaming ctrs:rtc. Qed.

  Lemma FromEPar n (a b : PTm n) :
    EPar.R a b ->
    rtc ERed.R a b.
  Proof.
    move => h. elim : n a b /h; eauto using AbsCong, AppCong, PairCong, ProjCong, rtc_refl, BindCong.
    - move => n a0 a1 _ h.
      have {}h : rtc ERed.R (ren_PTm shift a0) (ren_PTm shift a1) by apply renaming.
      apply : rtc_r. apply AbsCong. apply AppCong; eauto. apply rtc_refl.
      apply ERed.AppEta.
    - move => n a0 a1 _ h.
      apply : rtc_r.
      apply PairCong; eauto using ProjCong.
      apply ERed.PairEta.
  Qed.

  Lemma FromEPars n (a b : PTm n) :
    rtc EPar.R a b ->
    rtc ERed.R a b.
  Proof. induction 1; hauto l:on use:FromEPar, @relations.rtc_transitive. Qed.

End EReds.

#[export]Hint Constructors ERed.R RRed.R EPar.R : red.


Module RERed.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a b :
    R (PApp (PAbs a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

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
    R (PProj p a0) (PProj p a1)
  | BindCong0 p A0 A1 B :
    R A0 A1 ->
    R (PBind p A0 B) (PBind p A1 B)
  | BindCong1 p A B0 B1 :
    R B0 B1 ->
    R (PBind p A B0) (PBind p A B1).

  Lemma ToBetaEta n (a b : PTm n) :
    R a b ->
    ERed.R a b \/ RRed.R a b.
  Proof. induction 1; hauto lq:on db:red. Qed.

  Lemma FromBeta n (a b : PTm n) :
    RRed.R a b -> RERed.R a b.
  Proof. induction 1; qauto l:on ctrs:R. Qed.

  Lemma FromEta n (a b : PTm n) :
    ERed.R a b -> RERed.R a b.
  Proof. induction 1; qauto l:on ctrs:R. Qed.

  Lemma ToBetaEtaPar n (a b : PTm n) :
    R a b ->
    EPar.R a b \/ RRed.R a b.
  Proof.
    hauto q:on use:ERed.ToEPar, ToBetaEta.
  Qed.

  Lemma sn_preservation n (a b : PTm n) :
    R a b ->
    SN a ->
    SN b.
  Proof. hauto q:on use:ToBetaEtaPar, epar_sn_preservation, red_sn_preservation, RPar.FromRRed. Qed.

  Lemma bind_preservation n (a b : PTm n) :
    R a b -> isbind a -> isbind b.
  Proof. hauto q:on inv:R. Qed.

  Lemma univ_preservation n (a b : PTm n) :
    R a b -> isuniv a -> isuniv b.
  Proof. hauto q:on inv:R. Qed.

  Lemma sne_preservation n (a b : PTm n) :
    R a b -> SNe a -> SNe b.
  Proof.
    hauto q:on use:ToBetaEtaPar, RPar.FromRRed use:red_sn_preservation, epar_sn_preservation.
  Qed.

End RERed.

Module REReds.
  Lemma sn_preservation n (a b : PTm n) :
    rtc RERed.R a b ->
    SN a ->
    SN b.
  Proof. induction 1; eauto using RERed.sn_preservation. Qed.

  Lemma FromRReds n (a b : PTm n) :
    rtc RRed.R a b ->
    rtc RERed.R a b.
  Proof. induction 1; hauto lq:on ctrs:rtc use:RERed.FromBeta. Qed.

  Lemma FromEReds n (a b : PTm n) :
    rtc ERed.R a b ->
    rtc RERed.R a b.
  Proof. induction 1; hauto lq:on ctrs:rtc use:RERed.FromEta. Qed.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:RERed.R.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong n (a b : PTm (S n)) :
    rtc RERed.R a b ->
    rtc RERed.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    rtc RERed.R a0 a1 ->
    rtc RERed.R b0 b1 ->
    rtc RERed.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    rtc RERed.R a0 a1 ->
    rtc RERed.R b0 b1 ->
    rtc RERed.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1  : PTm n) :
    rtc RERed.R a0 a1 ->
    rtc RERed.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma BindCong n p (A0 A1 : PTm n) B0 B1 :
    rtc RERed.R A0 A1 ->
    rtc RERed.R B0 B1 ->
    rtc RERed.R (PBind p A0 B0) (PBind p A1 B1).
  Proof. solve_s. Qed.

  Lemma bind_preservation n (a b : PTm n) :
    rtc RERed.R a b -> isbind a -> isbind b.
  Proof. induction 1; qauto l:on ctrs:rtc use:RERed.bind_preservation. Qed.

  Lemma univ_preservation n (a b : PTm n) :
    rtc RERed.R a b -> isuniv a -> isuniv b.
  Proof. induction 1; qauto l:on ctrs:rtc use:RERed.univ_preservation. Qed.

  Lemma sne_preservation n (a b : PTm n) :
    rtc RERed.R a b -> SNe a -> SNe b.
  Proof. induction 1; qauto l:on ctrs:rtc use:RERed.sne_preservation. Qed.

  Lemma bind_inv n p A B C :
    rtc (@RERed.R n) (PBind p A B) C ->
    exists A0 B0, C = PBind p A0 B0 /\ rtc RERed.R A A0 /\ rtc RERed.R B B0.
  Proof.
    move E : (PBind p A B) => u hu.
    move : p A B E.
    elim : u C / hu; sauto lq:on rew:off.
  Qed.

  Lemma univ_inv n i C :
    rtc (@RERed.R n) (PUniv i) C  ->
    C = PUniv i.
  Proof.
    move E : (PUniv i) => u hu.
    move : i E. elim : u C / hu=>//=.
    hauto lq:on rew:off ctrs:rtc inv:RERed.R.
  Qed.

End REReds.

Module LoRed.
  Inductive R {n} : PTm n -> PTm n ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a b :
    R (PApp (PAbs a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

  (*************** Congruence ********************)
  | AbsCong a0 a1 :
    R a0 a1 ->
    R (PAbs a0) (PAbs a1)
  | AppCong0 a0 a1 b :
    ~~ ishf a0 ->
    R a0 a1 ->
    R (PApp a0 b) (PApp a1 b)
  | AppCong1 a b0 b1 :
    ne a ->
    R b0 b1 ->
    R (PApp a b0) (PApp a b1)
  | PairCong0 a0 a1 b :
    R a0 a1 ->
    R (PPair a0 b) (PPair a1 b)
  | PairCong1 a b0 b1 :
    nf a ->
    R b0 b1 ->
    R (PPair a b0) (PPair a b1)
  | ProjCong p a0 a1 :
    ~~ ishf a0 ->
    R a0 a1 ->
    R (PProj p a0) (PProj p a1)
  | BindCong0 p A0 A1 B :
    R A0 A1 ->
    R (PBind p A0 B) (PBind p A1 B)
  | BindCong1 p A B0 B1 :
    nf A ->
    R B0 B1 ->
    R (PBind p A B0) (PBind p A B1).

  Lemma hf_preservation n (a b : PTm n) :
    LoRed.R a b ->
    ishf a ->
    ishf b.
  Proof.
    move => h. elim : n a b /h=>//=.
  Qed.

  Lemma ToRRed n (a b : PTm n) :
    LoRed.R a b ->
    RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:RRed.R. Qed.

End LoRed.

Module LoReds.
  Lemma hf_preservation n (a b : PTm n) :
    rtc LoRed.R a b ->
    ishf a ->
    ishf b.
  Proof.
    induction 1; eauto using LoRed.hf_preservation.
  Qed.

  Lemma hf_ne_imp n (a b : PTm n) :
    rtc LoRed.R a b ->
    ne b ->
    ~~ ishf a.
  Proof.
    move : hf_preservation. repeat move/[apply].
    case : a; case : b => //=; itauto.
  Qed.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:LoRed.R, rtc use:hf_ne_imp.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); (move => *; apply rtc_refl).

  Lemma AbsCong n (a b : PTm (S n)) :
    rtc LoRed.R a b ->
    rtc LoRed.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    rtc LoRed.R a0 a1 ->
    rtc LoRed.R b0 b1 ->
    ne a1 ->
    rtc LoRed.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    rtc LoRed.R a0 a1 ->
    rtc LoRed.R b0 b1 ->
    nf a1 ->
    rtc LoRed.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong n p (a0 a1  : PTm n) :
    rtc LoRed.R a0 a1 ->
    ne a1 ->
    rtc LoRed.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma BindCong n p (A0 A1 : PTm n) B0 B1 :
    rtc LoRed.R A0 A1 ->
    rtc LoRed.R B0 B1 ->
    nf A1 ->
    rtc LoRed.R (PBind p A0 B0) (PBind p A1 B1).
  Proof. solve_s. Qed.

  Local Ltac triv := simpl in *; itauto.

  Lemma FromSN_mutual : forall n,
    (forall (a : PTm n) (_ : SNe a), exists v, rtc LoRed.R a v /\ ne v) /\
    (forall (a : PTm n) (_ : SN a), exists v, rtc LoRed.R a v /\ nf v) /\
    (forall (a b : PTm n) (_ : TRedSN a b), LoRed.R a b).
  Proof.
    apply sn_mutual.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on rew:off use:LoReds.AppCong solve+:triv.
    - hauto l:on use:LoReds.ProjCong solve+:triv.
    - hauto lq:on ctrs:rtc.
    - hauto q:on use:LoReds.PairCong solve+:triv.
    - hauto q:on use:LoReds.AbsCong solve+:triv.
    - sfirstorder use:ne_nf.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on use:LoReds.BindCong solve+:triv.
    - hauto lq:on ctrs:rtc.
    - qauto ctrs:LoRed.R.
    - move => n a0 a1 b hb ihb h.
      have : ~~ ishf a0 by inversion h.
      hauto lq:on ctrs:LoRed.R.
    - qauto ctrs:LoRed.R.
    - qauto ctrs:LoRed.R.
    - move => n p a b h.
      have : ~~ ishf a by inversion h.
      hauto lq:on ctrs:LoRed.R.
  Qed.

  Lemma FromSN : forall n a, @SN n a -> exists v, rtc LoRed.R a v /\ nf v.
  Proof. firstorder using FromSN_mutual. Qed.

  Lemma ToRReds : forall n (a b : PTm n), rtc LoRed.R a b -> rtc RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:rtc use:LoRed.ToRRed. Qed.

End LoReds.


Fixpoint size_PTm {n} (a : PTm n) :=
  match a with
  | VarPTm _ => 1
  | PAbs a => 3 + size_PTm a
  | PApp a b => 1 + Nat.add (size_PTm a) (size_PTm b)
  | PProj p a => 1 + size_PTm a
  | PPair a b => 3 + Nat.add (size_PTm a) (size_PTm b)
  | PUniv _ => 3
  | PBind p A B => 3 + Nat.add (size_PTm A) (size_PTm B)
  | PBot => 1
  end.

Lemma size_PTm_ren n m (ξ : fin n -> fin m) a : size_PTm (ren_PTm ξ a) = size_PTm a.
Proof.
  move : m ξ. elim : n / a => //=; scongruence.
Qed.

#[export]Hint Rewrite size_PTm_ren : sizetm.

Lemma ered_size {n} (a b : PTm n) :
  ERed.R a b ->
  size_PTm b < size_PTm a.
Proof.
  move => h. elim : n a b /h; hauto l:on rew:db:sizetm.
Qed.

Lemma ered_sn n (a : PTm n) : sn ERed.R a.
Proof.
  hauto lq:on rew:off use:size_PTm_ren, ered_size,
          well_founded_lt_compat unfold:well_founded.
Qed.

Lemma ered_local_confluence n (a b c : PTm n) :
  ERed.R a b ->
  ERed.R a c ->
  exists d, rtc ERed.R b d  /\ rtc ERed.R c d.
Proof.
  move => h. move : c.
  elim : n a b / h => n.
  - move => a c.
    elim /ERed.inv => //= _.
    + move => a0 [+ ?]. subst => h.
      apply f_equal with (f := subst_PTm (scons (PAbs (VarPTm var_zero)) VarPTm)) in h.
      move : h. asimpl => ?. subst.
      eauto using rtc_refl.
    + move => a0 a1 ha [*]. subst.
      elim /ERed.inv : ha => //= _.
      * move => a0 a2 b0 ha [*]. subst. rename a2 into a1.
        move /ERed.antirenaming : ha.
        move /(_ ltac:(hauto lq:on)) => [a' [h0 h1]]. subst.
        hauto lq:on ctrs:rtc, ERed.R.
      * hauto q:on ctrs:rtc, ERed.R inv:ERed.R.
  - move => a c ha.
    elim /ERed.inv : ha => //= _.
    + hauto l:on.
    + move => a0 a1 b0 ha [*]. subst.
      elim /ERed.inv : ha => //= _.
      move => p a0 a2 ha [*]. subst.
      hauto q:on ctrs:rtc, ERed.R.
    + move => a0 b0 b1 ha [*]. subst.
      elim /ERed.inv : ha => //= _.
      move => p a0 a2 ha [*]. subst.
      hauto q:on ctrs:rtc, ERed.R.
  - move => a0 a1 ha iha c.
    elim /ERed.inv => //= _.
    + move => a2 [*]. subst.
      elim /ERed.inv : ha => //=_.
      * move => a0 a2 b0 ha [*] {iha}. subst.
        have [a0 [h0 h1]] : exists a0, ERed.R c a0 /\ a2 = ren_PTm shift a0 by hauto lq:on use:ERed.antirenaming. subst.
        exists a0. split; last by apply relations.rtc_once.
        apply relations.rtc_once. apply ERed.AppEta.
      * hauto q:on inv:ERed.R.
    + hauto lq:on use:EReds.AbsCong.
  - move => a0 a1 b ha iha c.
    elim /ERed.inv => //= _.
    + hauto lq:on ctrs:rtc use:EReds.AppCong.
    + hauto lq:on use:@relations.rtc_once ctrs:ERed.R.
  - move => a b0 b1 hb ihb c.
    elim /ERed.inv => //=_.
    + move => a0 a1 a2 ha [*]. subst.
      move {ihb}. exists (PApp a1 b1).
      hauto lq:on use:@relations.rtc_once ctrs:ERed.R.
    + hauto lq:on ctrs:rtc use:EReds.AppCong.
  - move => a0 a1 b ha iha c.
    elim /ERed.inv => //= _.
    + sauto lq:on.
    + hauto lq:on ctrs:rtc use:EReds.PairCong.
    + hauto lq:on ctrs:ERed.R use:@relations.rtc_once.
  - move => a b0 b1 hb hc c. elim /ERed.inv => //= _.
    + move => ? [*]. subst.
      sauto lq:on.
    + hauto lq:on ctrs:ERed.R use:@relations.rtc_once.
    + hauto lq:on ctrs:rtc use:EReds.PairCong.
  - qauto l:on inv:ERed.R use:EReds.ProjCong.
  - move => p A0 A1 B hA ihA u.
    elim /ERed.inv => //=_;
      hauto lq:on ctrs:rtc use:EReds.BindCong.
  - move => p A B0 B1 hB ihB u.
    elim /ERed.inv => //=_;
      hauto lq:on ctrs:rtc use:EReds.BindCong.
Qed.

Lemma ered_confluence n (a b c : PTm n) :
  rtc ERed.R a b ->
  rtc ERed.R a c ->
  exists d, rtc ERed.R b d  /\ rtc ERed.R c d.
Proof.
  sfirstorder use:relations.locally_confluent_confluent, ered_sn, ered_local_confluence.
Qed.

Lemma red_confluence n (a b c : PTm n) :
  rtc RRed.R a b ->
  rtc RRed.R a c ->
  exists d, rtc RRed.R b d  /\ rtc RRed.R c d.
  suff : rtc RPar.R a b -> rtc RPar.R a c -> exists d : PTm n, rtc RPar.R b d /\ rtc RPar.R c d
             by hauto lq:on use:RReds.RParIff.
  apply relations.diamond_confluent.
  rewrite /relations.diamond.
  eauto using RPar.diamond.
Qed.

Lemma red_uniquenf n (a b c : PTm n) :
  rtc RRed.R a b ->
  rtc RRed.R a c ->
  nf b ->
  nf c ->
  b = c.
Proof.
  move : red_confluence; repeat move/[apply].
  move => [d [h0 h1]].
  move => *.
  suff [] : b = d /\ c = d by congruence.
  sfirstorder use:RReds.nf_refl.
Qed.

Module NeEPars.
  Lemma R_nonelim_nf n (a b : PTm n) :
    rtc NeEPar.R_nonelim a b ->
    nf b ->
    nf a.
  Proof. induction 1; sfirstorder use:NeEPar.R_elim_nf. Qed.

  Lemma ToEReds : forall n, (forall (a b : PTm n), rtc NeEPar.R_nonelim a b -> rtc ERed.R a b).
  Proof.
    induction 1; hauto l:on use:NeEPar.ToEPar, EReds.FromEPar, @relations.rtc_transitive.
  Qed.
End NeEPars.


Lemma rered_standardization n (a c : PTm n) :
  SN a ->
  rtc RERed.R a c ->
  exists b, rtc RRed.R a b /\ rtc NeEPar.R_nonelim b c.
Proof.
  move => + h. elim : a c /h.
  by eauto using rtc_refl.
  move => a b c.
  move /RERed.ToBetaEtaPar.
  case.
  - move => h0 h1 ih hP.
    have  : SN b by qauto use:epar_sn_preservation.
    move => {}/ih [b' [ihb0 ihb1]].
    hauto lq:on ctrs:rtc use:SN_UniqueNF.η_postponement_star'.
  - hauto lq:on ctrs:rtc use:red_sn_preservation, RPar.FromRRed.
Qed.

Lemma rered_confluence n (a b c : PTm n) :
  SN a ->
  rtc RERed.R a b ->
  rtc RERed.R a c ->
  exists d, rtc RERed.R b d  /\ rtc RERed.R c d.
Proof.
  move => hP hb hc.
  have [] : SN b /\ SN c by qauto use:REReds.sn_preservation.
  move => /LoReds.FromSN [bv [/LoReds.ToRReds /REReds.FromRReds hbv  hbv']].
  move => /LoReds.FromSN [cv [/LoReds.ToRReds /REReds.FromRReds hcv  hcv']].
  have [] : SN b /\ SN c by sfirstorder use:REReds.sn_preservation.
  move : rered_standardization hbv; repeat move/[apply]. move => [bv' [hb0 hb1]].
  move : rered_standardization hcv; repeat move/[apply]. move => [cv' [hc0 hc1]].

  have [] : rtc RERed.R a bv' /\ rtc RERed.R a cv'
    by sfirstorder use:@relations.rtc_transitive, REReds.FromRReds.
  move : rered_standardization (hP). repeat move/[apply]. move => [bv'' [hb3 hb4]].
  move : rered_standardization (hP). repeat move/[apply]. move => [cv'' [hc3 hc4]].
  have hb2 : rtc NeEPar.R_nonelim bv'' bv by hauto lq:on use:@relations.rtc_transitive.
  have hc2 : rtc NeEPar.R_nonelim cv'' cv by hauto lq:on use:@relations.rtc_transitive.
  have [hc5 hb5] : nf cv'' /\ nf bv'' by sfirstorder use:NeEPars.R_nonelim_nf.
  have ? : bv'' = cv'' by sfirstorder use:red_uniquenf. subst.
  apply NeEPars.ToEReds in hb2, hc2.
  move : ered_confluence (hb2) (hc2); repeat move/[apply].
  move => [v [hv hv']].
  exists v. split.
  move /NeEPars.ToEReds /REReds.FromEReds : hb1.
  move /REReds.FromRReds : hb0. move /REReds.FromEReds : hv. eauto using relations.rtc_transitive.
  move /NeEPars.ToEReds /REReds.FromEReds : hc1.
  move /REReds.FromRReds : hc0. move /REReds.FromEReds : hv'. eauto using relations.rtc_transitive.
Qed.

(* "Declarative" Joinability *)
Module DJoin.
  Definition R {n} (a b : PTm n) := exists c, rtc RERed.R a c /\ rtc RERed.R b c.

  Lemma refl n (a : PTm n) : R a a.
  Proof. sfirstorder use:@rtc_refl unfold:R. Qed.

  Lemma symmetric n (a b : PTm n) : R a b -> R b a.
  Proof. sfirstorder unfold:R. Qed.

  Lemma transitive n (a b c : PTm n) : SN b -> R a b -> R b c -> R a c.
  Proof.
    rewrite /R.
    move => + [ab [ha +]] [bc [+ hc]].
    move : rered_confluence; repeat move/[apply].
    move => [v [h0 h1]].
    exists v. sfirstorder use:@relations.rtc_transitive.
  Qed.

  Lemma AbsCong n (a b : PTm (S n)) :
    R a b ->
    R (PAbs a) (PAbs b).
  Proof. hauto lq:on use:REReds.AbsCong unfold:R. Qed.

  Lemma AppCong n (a0 a1 b0 b1 : PTm n) :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp a0 b0) (PApp a1 b1).
  Proof. hauto lq:on use:REReds.AppCong unfold:R. Qed.

  Lemma PairCong n (a0 a1 b0 b1 : PTm n) :
    R a0 a1 ->
    R b0 b1 ->
    R (PPair a0 b0) (PPair a1 b1).
  Proof. hauto q:on use:REReds.PairCong. Qed.

  Lemma ProjCong n p (a0 a1  : PTm n) :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1).
  Proof. hauto q:on use:REReds.ProjCong. Qed.

  Lemma FromRedSNs n (a b : PTm n) :
    rtc TRedSN a b ->
    R a b.
  Proof.
    move /RReds.FromRedSNs /REReds.FromRReds.
    sfirstorder use:@rtc_refl unfold:R.
  Qed.

  Lemma sne_bind_noconf n (a b : PTm n) :
    R a b -> SNe a -> isbind b -> False.
  Proof.
    move => [c [? ?]] *.
    have : SNe c /\ isbind c by sfirstorder use:REReds.sne_preservation, REReds.bind_preservation.
    qauto l:on inv:SNe.
  Qed.

  Lemma sne_univ_noconf n (a b : PTm n) :
    R a b -> SNe a -> isuniv b -> False.
  Proof.
    hauto q:on use:REReds.sne_preservation,
          REReds.univ_preservation inv:SNe.
  Qed.

  Lemma bind_univ_noconf n (a b : PTm n) :
    R a b -> isbind a -> isuniv b -> False.
  Proof.
    move => [c [h0 h1]] h2 h3.
    have {h0 h1 h2 h3} : isbind c /\ isuniv c by
      hauto l:on use:REReds.bind_preservation,
          REReds.univ_preservation.
    case : c => //=; itauto.
  Qed.

  Lemma bind_inj n p0 p1 (A0 A1 : PTm n) B0 B1 :
    DJoin.R (PBind p0 A0 B0) (PBind p1 A1 B1) ->
    p0 = p1 /\ DJoin.R A0 A1 /\ DJoin.R B0 B1.
  Proof.
    rewrite /R.
    hauto lq:on rew:off use:REReds.bind_inv.
  Qed.

  Lemma univ_inj n i j :
    @R n (PUniv i) (PUniv j)  -> i = j.
  Proof.
    sauto lq:on rew:off use:REReds.univ_inv.
  Qed.

  Lemma FromRRed0 n (a b : PTm n) :
    RRed.R a b -> R a b.
  Proof.
    hauto lq:on ctrs:rtc use:RERed.FromBeta unfold:R.
  Qed.

  Lemma FromRRed1 n (a b : PTm n) :
    RRed.R b a -> R a b.
  Proof.
    hauto lq:on ctrs:rtc use:RERed.FromBeta unfold:R.
  Qed.



End DJoin.
