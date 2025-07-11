From Ltac2 Require Ltac2.
Import Ltac2.Notations.

Import Ltac2.Control.
Require Import ssreflect ssrbool.
Require Import FunInd.
Require Import Arith.Wf_nat (well_founded_lt_compat).
Require Import Psatz.
From stdpp Require Import relations (rtc (..), rtc_once, rtc_r, sn).
From Hammer Require Import Tactics.
Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common.
Require Import Btauto.


Ltac2 spec_refl () :=
  List.iter
    (fun a => match a with
           | (i, _, _) =>
               let h := Control.hyp i in
               try (specialize $h with (1 := eq_refl))
           end)  (Control.hyps ()).

Ltac spec_refl := ltac2:(Control.enter spec_refl).

Module EPar.
  Inductive R : PTm -> PTm ->  Prop :=
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
  | NatCong :
    R PNat PNat
  | IndCong P0 P1 a0 a1 b0 b1 c0 c1 :
    R P0 P1 ->
    R a0 a1 ->
    R b0 b1 ->
    R c0 c1 ->
    (* ----------------------- *)
    R (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1)
  | ZeroCong :
    R PZero PZero
  | SucCong a0 a1 :
    R a0 a1 ->
    (* ------------ *)
    R (PSuc a0) (PSuc a1).

  Lemma refl (a : PTm) : R a a.
  Proof.
    elim : a; hauto lq:on ctrs:R.
  Qed.

  Derive Dependent Inversion inv with (forall (a b : PTm), R a b) Sort Prop.

  Lemma AppEta' a0 a1 (u : PTm) :
    u = (PAbs (PApp (ren_PTm shift a0) (VarPTm var_zero))) ->
    R a0 a1 ->
    R u a1.
  Proof. move => ->. apply AppEta. Qed.

  Lemma renaming (a b : PTm) (ξ : nat -> nat) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : ξ.
    elim : a b /h.

    all : try qauto ctrs:R.

    move => a0 a1 ha iha ξ /=.
    eapply AppEta'; eauto. by asimpl.
  Qed.

  Lemma morphing_ren (ρ0 ρ1 : nat -> PTm) (ξ : nat -> nat) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R (funcomp (ren_PTm ξ) ρ0 i) ((funcomp (ren_PTm ξ) ρ1) i)).
  Proof. eauto using renaming. Qed.

  Lemma morphing_ext (ρ0 ρ1 : nat -> PTm) a b  :
    R a b ->
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((scons a ρ0) i) ((scons b ρ1) i)).
  Proof. hauto q:on inv:nat. Qed.

  Lemma morphing_up (ρ0 ρ1 : nat -> PTm) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R (up_PTm_PTm ρ0 i) (up_PTm_PTm ρ1 i)).
  Proof. hauto l:on ctrs:R use:morphing_ext, morphing_ren unfold:up_PTm_PTm. Qed.

  Lemma morphing (a b : PTm) (ρ0 ρ1 : nat -> PTm) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    R a b -> R (subst_PTm ρ0 a) (subst_PTm ρ1 b).
  Proof.
    move => + h. move : ρ0 ρ1. elim : a b / h.
    move => a0 a1 ha iha ρ0 ρ1 hρ /=.
    eapply AppEta'; eauto. by asimpl.
    all : hauto lq:on ctrs:R use:morphing_up.
  Qed.

  Lemma substing (a b : PTm) (ρ : nat -> PTm) :
    R a b -> R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof. hauto l:on use:morphing, refl. Qed.

End EPar.

Inductive SNe : PTm -> Prop :=
| N_Var i :
  SNe (VarPTm i)
| N_App a b :
  SNe a ->
  SN b ->
  SNe (PApp a b)
| N_Proj p a :
  SNe a ->
  SNe (PProj p a)
| N_Ind P a b c :
  SN P ->
  SNe a ->
  SN b ->
  SN c ->
  SNe (PInd P a b c)
with SN  : PTm -> Prop :=
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
| N_Nat :
  SN PNat
| N_Zero :
  SN PZero
| N_Suc a :
  SN a ->
  SN (PSuc a)
with TRedSN : PTm -> PTm -> Prop :=
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
  TRedSN (PProj p a) (PProj p b)
| N_IndZero P b c :
  SN P ->
  SN b ->
  SN c ->
  TRedSN (PInd P PZero b c) b
| N_IndSuc P a b c :
  SN P ->
  SN a ->
  SN b ->
  SN c ->
  TRedSN (PInd P (PSuc a) b c) (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c)
| N_IndCong P a0 a1 b c :
  SN P ->
  SN b ->
  SN c ->
  TRedSN a0 a1 ->
  TRedSN (PInd P a0 b c) (PInd P a1 b c).

Derive Inversion tred_inv with (forall (a b : PTm), TRedSN a b) Sort Prop.

Inductive SNat : PTm -> Prop :=
| S_Zero : SNat PZero
| S_Neu a : SNe a -> SNat a
| S_Suc a : SNat a -> SNat (PSuc a)
| S_Red a b : TRedSN a b -> SNat b -> SNat a.

Lemma PProj_imp p a :
  ishf a ->
  ~~ ispair a ->
  ~ SN (PProj p a).
Proof.
  move => + + h. move E  : (PProj p a) h => u h.
  move : p a E.
  elim : u / h => //=.
  hauto lq:on inv:SNe,PTm.
  hauto lq:on inv:TRedSN.
Qed.

Lemma PApp_imp a b :
  ishf a ->
  ~~ isabs a ->
  ~ SN (PApp a b).
Proof.
  move => + + h. move E : (PApp a b) h => u h.
  move : a b E. elim  : u /h=>//=.
  hauto lq:on inv:SNe,PTm.
  hauto lq:on inv:TRedSN.
Qed.

Lemma PInd_imp P (a : PTm) b c :
  ishf a ->
  ~~ iszero a ->
  ~~ issuc a ->
  ~ SN (PInd P a b c).
Proof.
  move => + + + h. move E : (PInd P a b c) h => u h.
  move : P a b c E.
  elim : u /h => //=.
  hauto lq:on inv:SNe,PTm.
  hauto lq:on inv:TRedSN.
Qed.

Lemma PProjAbs_imp p (a : PTm) :
  ~ SN (PProj p (PAbs a)).
Proof.
  sfirstorder use:PProj_imp.
Qed.

Lemma PAppPair_imp (a b0 b1 : PTm ) :
  ~ SN (PApp (PPair b0 b1) a).
Proof.
  sfirstorder use:PApp_imp.
Qed.

Lemma PAppBind_imp p (A : PTm) B b :
  ~ SN (PApp (PBind p A B) b).
Proof.
  sfirstorder use:PApp_imp.
Qed.

Lemma PProjBind_imp p p' (A : PTm) B :
  ~ SN (PProj p (PBind p' A B)).
Proof.
  move E :(PProj p (PBind p' A B)) => u hu.
  move : p p' A B E.
  elim : u /hu=>//=.
  hauto lq:on inv:SNe.
  hauto lq:on inv:TRedSN.
Qed.

Scheme sne_ind := Induction for SNe Sort Prop
  with sn_ind := Induction for SN Sort Prop
  with sred_ind := Induction for TRedSN Sort Prop.

Combined Scheme sn_mutual from sne_ind, sn_ind, sred_ind.

Fixpoint ne (a : PTm) :=
  match a with
  | VarPTm i => true
  | PApp a b => ne a && nf b
  | PAbs a => false
  | PPair _ _ => false
  | PProj _ a => ne a
  | PUniv _ => false
  | PBind _ _ _ => false
  | PInd P a b c => nf P && ne a && nf b && nf c
  | PNat => false
  | PSuc a => false
  | PZero => false
  end
with nf (a : PTm) :=
  match a with
  | VarPTm i => true
  | PApp a b => ne a && nf b
  | PAbs a => nf a
  | PPair a b => nf a && nf b
  | PProj _ a => ne a
  | PUniv _ => true
  | PBind _ A B => nf A && nf B
  | PInd P a b c => nf P && ne a && nf b && nf c
  | PNat => true
  | PSuc a => nf a
  | PZero => true
end.

Lemma ne_nf a : ne a -> nf a.
Proof. elim : a => //=. Qed.

Lemma ne_nf_ren (a : PTm) (ξ : nat -> nat) :
  (ne a <-> ne (ren_PTm ξ a)) /\ (nf a <-> nf (ren_PTm ξ a)).
Proof.
  move : ξ. elim : a => //=; solve [hauto b:on].
Qed.

Inductive TRedSN' (a : PTm) : PTm -> Prop :=
| T_Refl :
  TRedSN' a a
| T_Once b :
  TRedSN a b ->
  TRedSN' a b.

Lemma SN_Proj p (a : PTm) :
  SN (PProj p a) -> SN a.
Proof.
  move E : (PProj p a) => u h.
  move : a E.
  elim : u / h => n //=; sauto.
Qed.

Lemma N_β' a (b : PTm) u :
  u = (subst_PTm (scons b VarPTm) a) ->
  SN b ->
  TRedSN (PApp (PAbs a) b) u.
Proof. move => ->. apply N_β. Qed.

Lemma N_IndSuc' P a b c u :
  u = (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c) ->
  SN P ->
  SN a ->
  SN b ->
  SN c ->
  TRedSN (PInd P (PSuc a) b c) u.
Proof. move => ->. apply N_IndSuc. Qed.

Lemma sn_renaming :
  (forall (a : PTm) (s : SNe a), forall (ξ : nat -> nat), SNe (ren_PTm ξ a)) /\
  (forall (a : PTm) (s : SN a), forall (ξ : nat -> nat), SN (ren_PTm ξ a)) /\
  (forall (a b : PTm) (_ : TRedSN a b), forall (ξ : nat -> nat), TRedSN (ren_PTm ξ a) (ren_PTm ξ b)).
Proof.
  apply sn_mutual => n; try qauto ctrs:SN, SNe, TRedSN depth:1.
  move => */=. apply N_β';eauto. by asimpl.

  move => */=. apply N_IndSuc'; eauto. by asimpl.
Qed.

Lemma ne_nf_embed (a : PTm) :
  (ne a -> SNe a) /\ (nf a -> SN a).
Proof.
  elim :  a => //=; hauto qb:on ctrs:SNe, SN.
Qed.

#[export]Hint Constructors SN SNe TRedSN : sn.

Ltac2 rec solve_anti_ren () :=
  let x := Fresh.in_goal (Option.get (Ident.of_string "x")) in
  intro $x;
  lazy_match! Constr.type (Control.hyp x) with
  | nat -> nat => (ltac1:(case;qauto depth:2 db:sn))
  | nat -> PTm => (ltac1:(case;qauto depth:2 db:sn))
  | _ => solve_anti_ren ()
  end.

Ltac solve_anti_ren := ltac2:(Control.enter solve_anti_ren).

Lemma sn_antirenaming :
  (forall (a : PTm) (s : SNe a), forall (ξ : nat -> nat) b, a = ren_PTm ξ b -> SNe b) /\
  (forall (a : PTm) (s : SN a), forall (ξ : nat -> nat) b, a = ren_PTm ξ b -> SN b) /\
  (forall (a b : PTm) (_ : TRedSN a b), forall (ξ : nat -> nat) a0,
      a = ren_PTm ξ a0 -> exists b0, TRedSN a0 b0 /\ b = ren_PTm ξ b0).
Proof.
  apply sn_mutual; try solve_anti_ren.
  move => *. subst. spec_refl. hauto lq:on ctrs:TRedSN, SN.

  move => a b ha iha ξ []//= u u0 [+ ?]. subst.
  case : u => //= => u [*]. subst.
  spec_refl. eexists. split. apply N_β=>//. by asimpl.

  move => a b hb ihb ξ[]//= p p0 [? +]. subst.
  case : p0 => //= p p0 [*]. subst.
  spec_refl. by eauto with sn.

  move => a b ha iha ξ[]//= u u0 [? ]. subst.
  case : u0 => //=. move => p p0 [*]. subst.
  spec_refl. by eauto with sn.

  move => P b c ha iha hb ihb hc ihc ξ []//= P0 a0 b0 c0 [?]. subst.
  case : a0 => //= _ *. subst.
  spec_refl. by eauto with sn.

  move => P a b c hP ihP ha iha hb ihb hc ihc ξ []//= P0 a0 b0 c0 [?]. subst.
  case : a0 => //= a0 [*]. subst.
  spec_refl. eexists; repeat split; eauto with sn.
  by asimpl.
Qed.

Lemma sn_unmorphing :
  (forall (a : PTm) (s : SNe a), forall (ρ : nat -> PTm) b, a = subst_PTm ρ b -> SNe b) /\
  (forall (a : PTm) (s : SN a), forall (ρ : nat -> PTm) b, a = subst_PTm ρ b -> SN b) /\
  (forall (a b : PTm) (_ : TRedSN a b), forall (ρ : nat -> PTm) a0,
      a = subst_PTm ρ a0 -> (exists b0, b = subst_PTm ρ b0 /\ TRedSN a0 b0) \/ SNe a0).
Proof.
  apply sn_mutual; try solve_anti_ren.
  - hauto q:on db:sn.
  - move => a b ha iha  ξ b0.
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
  - move => a0 a1 b hb ihb ha iha ρ []//=.
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
  - move => a b hb ihb ρ []//=.
    + hauto l:on ctrs:TRedSN.
    + move => p p0 [?]. subst.
      case : p0 => //=.
      * hauto lq:on rew:off db:sn.
      * move => p p0 [*]. subst.
        hauto lq:on db:sn.
  - move => a b ha iha ρ []//=; first by hauto l:on db:sn.
    case => //=. move => []//=.
    + hauto lq:on db:sn.
    + hauto lq:on db:sn.
  - move => p a b ha iha ρ []//=; first by hauto l:on db:sn.
    move => t0 t1 [*]. subst.
    spec_refl.
    case : iha.
    + move => [b0 [? h]]. subst.
      left. eexists. split; last by eauto with sn.
      reflexivity.
    + hauto lq:on db:sn.
  - move => P b c hP ihP hb ihb hc ihc ρ []//=.
    + hauto lq:on db:sn.
    + move => p []//=.
      * hauto lq:on db:sn.
      * hauto q:on db:sn.
  - move => P a b c hP ihP ha iha hb ihb hc ihc ρ []//=.
    + hauto lq:on db:sn.
    + move => P0 a0 b0 c0 [?]. subst.
      case : a0 => //=.
      * hauto lq:on db:sn.
      * move => a0 [*]. subst.
        spec_refl.
        left. eexists. split; last by eauto with sn.
        by asimpl.
  - move => P a0 a1 b c hP ihP hb ihb hc ihc ha iha ρ[]//=.
    + hauto lq:on db:sn.
    + move => P1 a2 b2 c2 [*]. subst.
      spec_refl.
      case : iha.
      * move => [a3][?]h. subst.
        left. eexists; split; last by eauto with sn.
        asimpl. eauto with sn.
      * hauto lq:on db:sn.
Qed.

Lemma SN_AppInv : forall (a b : PTm), SN (PApp a b) -> SN a /\ SN b.
Proof.
  move => a b. move E : (PApp a b) => u hu. move : a b E.
  elim : u /hu=>//=.
  hauto lq:on rew:off inv:SNe db:sn.
  move => a b ha hb ihb a0 b0 ?. subst.
  inversion ha; subst.
  move {ihb}.
  hecrush use:sn_unmorphing.
  hauto lq:on db:sn.
Qed.

Lemma SN_ProjInv : forall p (a : PTm), SN (PProj p a) -> SN a.
Proof.
  move => p a. move E : (PProj p a) => u hu.
  move : p a E.
  elim : u / hu => //=.
  hauto lq:on rew:off inv:SNe db:sn.
  hauto lq:on rew:off inv:TRedSN db:sn.
Qed.

Lemma SN_IndInv : forall P (a : PTm) b c, SN (PInd P a b c) -> SN P /\ SN a /\ SN b /\ SN c.
Proof.
  move => P a b c. move E : (PInd P a b c) => u hu. move : P a b c E.
  elim  : u / hu => //=.
  hauto lq:on rew:off inv:SNe db:sn.
  hauto lq:on rew:off inv:TRedSN db:sn.
Qed.

Lemma epar_sn_preservation :
  (forall (a : PTm) (s : SNe a), forall b, EPar.R a b -> SNe b) /\
  (forall (a : PTm) (s : SN a), forall b, EPar.R a b -> SN b) /\
  (forall (a b : PTm) (_ : TRedSN a b), forall c, EPar.R a c -> exists d, TRedSN' c d /\ EPar.R b d).
Proof.
  apply sn_mutual.
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
      hauto lq:on use:EPar.morphing, EPar.refl inv:nat.
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
  - sauto q:on.
  - move => P a b c hP ihP ha iha hb ihb hc ihc u.
    elim /EPar.inv => //=_.
    move => P0 P1 a0 a1 b0 b1 c0 c1 hP0 ha0 hb0 hc0 [*]. subst.
    elim /EPar.inv : ha0 => //=_.
    move => a0 a2 ha0 [*]. subst.
    eexists. split. apply T_Once. apply N_IndSuc; eauto.
    hauto q:on ctrs:EPar.R use:EPar.morphing, EPar.refl inv:nat.
  - sauto q:on.
Qed.

Module RRed.
  Inductive R : PTm -> PTm ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a b :
    R (PApp (PAbs a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

  | IndZero P b c :
    R (PInd P PZero b c) b

  | IndSuc P a b c :
    R (PInd P (PSuc a) b c) (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c)
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
    R (PBind p A B0) (PBind p A B1)
  | IndCong0 P0 P1 a b c :
    R P0 P1 ->
    R (PInd P0 a b c) (PInd P1 a b c)
  | IndCong1 P a0 a1 b c :
    R a0 a1 ->
    R (PInd P a0 b c) (PInd P a1 b c)
  | IndCong2 P a b0 b1 c :
    R b0 b1 ->
    R (PInd P a b0 c) (PInd P a b1 c)
  | IndCong3 P a b c0 c1 :
    R c0 c1 ->
    R (PInd P a b c0) (PInd P a b c1)
  | SucCong a0 a1 :
    R a0 a1 ->
    R (PSuc a0) (PSuc a1).

  Derive Inversion inv with (forall (a b : PTm), R a b) Sort Prop.

  Lemma AppAbs' a (b : PTm) u :
    u = (subst_PTm (scons b VarPTm) a) ->
    R (PApp (PAbs a) b)  u.
  Proof.
    move => ->. by apply AppAbs. Qed.

  Lemma IndSuc' P a b c u :
    u = (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c) ->
    R (PInd P (PSuc a) b c) u.
  Proof. move => ->. apply IndSuc. Qed.

  Lemma renaming (a b : PTm) (ξ : nat -> nat) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : ξ.
    elim : a b /h.

    all : try qauto ctrs:R.
    move => a b ξ /=.
    apply AppAbs'. by asimpl.
    move => */=; apply IndSuc'; eauto. by asimpl.
  Qed.

  Ltac2 rec solve_anti_ren () :=
    let x := Fresh.in_goal (Option.get (Ident.of_string "x")) in
    intro $x;
    lazy_match! Constr.type (Control.hyp x) with
    | nat -> nat => (ltac1:(case;hauto q:on depth:2 ctrs:RRed.R))
    | nat -> PTm => (ltac1:(case;hauto q:on depth:2 ctrs:RRed.R))
    | _ => solve_anti_ren ()
    end.

  Ltac solve_anti_ren := ltac2:(Control.enter solve_anti_ren).

  Lemma antirenaming (a : PTm) (b : PTm) (ξ : nat -> nat) :
    R (ren_PTm ξ a) b -> exists b0, R a b0 /\ ren_PTm ξ b0 = b.
  Proof.
    move E : (ren_PTm ξ a) => u h.
    move : ξ a E. elim : u b/h; try solve_anti_ren.
    - move => a b ξ []//=. move => []//= t t0 [*]. subst.
      eexists. split. apply AppAbs. by asimpl.
    - move => p a b ξ []//=.
      move => p0 []//=. hauto q:on ctrs:R.
    - move => p b c ξ []//= P a0 b0 c0 [*]. subst.
      destruct a0 => //=.
      hauto lq:on ctrs:R.
    - move => P a b c ξ []//=.
      move => p p0 p1 p2 [?].  subst.
      case : p0 => //=.
      move => p0 [?] *. subst. eexists. split; eauto using IndSuc.
      by asimpl.
  Qed.

  Lemma nf_imp (a b : PTm) :
    nf a ->
    R a b -> False.
  Proof. move/[swap]. induction 1; hauto qb:on inv:PTm. Qed.

  Lemma FromRedSN (a b : PTm) :
    TRedSN a b ->
    RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:RRed.R. Qed.

  Lemma substing (a b : PTm) (ρ : nat -> PTm) :
    R a b -> R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    move => h. move :  ρ. elim : a b / h => n.

    all : try hauto lq:on ctrs:R.
    move => */=. eapply AppAbs'; eauto; cycle 1. by asimpl.
    move => */=; apply : IndSuc'; eauto. by asimpl.
  Qed.

  Lemma abs_preservation a b : isabs a -> R a b -> isabs b. hauto q:on inv:R. Qed.

End RRed.

Module RPar.
  Inductive R : PTm -> PTm ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0)  (subst_PTm (scons b1 VarPTm) a1)

  | ProjPair p a0 a1 b0 b1 :
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) (if p is PL then a1 else b1)

  | IndZero P b0 b1  c :
    R b0 b1 ->
    R (PInd P PZero b0 c) b1

  | IndSuc P0 P1 a0 a1 b0 b1 c0 c1 :
    R P0 P1 ->
    R a0 a1 ->
    R b0 b1 ->
    R c0 c1 ->
    (* ----------------------------- *)
    R (PInd P0 (PSuc a0) b0 c0) (subst_PTm (scons (PInd P1 a1 b1 c1) (scons a1 VarPTm)) c1)

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
  | NatCong :
    R PNat PNat
  | IndCong P0 P1 a0 a1 b0 b1 c0 c1 :
    R P0 P1 ->
    R a0 a1 ->
    R b0 b1 ->
    R c0 c1 ->
    (* ----------------------- *)
    R (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1)
  | ZeroCong :
    R PZero PZero
  | SucCong a0 a1 :
    R a0 a1 ->
    (* ------------ *)
    R (PSuc a0) (PSuc a1).

  Lemma refl (a : PTm) : R a a.
  Proof.
    elim : a; hauto lq:on ctrs:R.
  Qed.

  Derive Dependent Inversion inv with (forall (a b : PTm), R a b) Sort Prop.

  Lemma AppAbs' a0 a1 (b0 b1 : PTm) u :
    u = (subst_PTm (scons b1 VarPTm) a1) ->
    R a0 a1 ->
    R b0 b1 ->
    R (PApp (PAbs a0) b0)  u.
  Proof. move => ->. apply AppAbs. Qed.

  Lemma ProjPair' p u (a0 a1 b0 b1 : PTm) :
    u = (if p is PL then a1 else b1) ->
    R a0 a1 ->
    R b0 b1 ->
    R (PProj p (PPair a0 b0)) u.
  Proof. move => ->. apply ProjPair. Qed.

  Lemma IndSuc' P0 P1 (a0 a1 : PTm) b0 b1 c0 c1 u :
    u = (subst_PTm (scons (PInd P1 a1 b1 c1) (scons a1 VarPTm)) c1) ->
    R P0 P1 ->
    R a0 a1 ->
    R b0 b1 ->
    R c0 c1 ->
    (* ----------------------------- *)
    R (PInd P0 (PSuc a0) b0 c0) u.
  Proof. move => ->. apply IndSuc. Qed.

  Lemma renaming (a b : PTm) (ξ : nat -> nat) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : ξ.
    elim : a b /h.

    all : try qauto ctrs:R use:ProjPair'.

    move => a0 a1 b0 b1 ha iha hb ihb ξ /=.
    eapply AppAbs'; eauto. by asimpl.

    move => * /=. apply : IndSuc'; eauto. by asimpl.
  Qed.

  Lemma morphing_ren (ρ0 ρ1 : nat -> PTm) (ξ : nat -> nat) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((funcomp (ren_PTm ξ) ρ0) i) ((funcomp (ren_PTm ξ) ρ1) i)).
  Proof. eauto using renaming. Qed.

  Lemma morphing_ext (ρ0 ρ1 : nat -> PTm) a b  :
    R a b ->
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R ((scons a ρ0) i) ((scons b ρ1) i)).
  Proof. hauto q:on inv:nat. Qed.

  Lemma morphing_up (ρ0 ρ1 : nat -> PTm) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    (forall i, R (up_PTm_PTm ρ0 i) (up_PTm_PTm ρ1 i)).
  Proof. hauto l:on ctrs:R use:morphing_ext, morphing_ren unfold:up_PTm_PTm. Qed.

  Lemma morphing (a b : PTm) (ρ0 ρ1 : nat -> PTm) :
    (forall i, R (ρ0 i) (ρ1 i)) ->
    R a b -> R (subst_PTm ρ0 a) (subst_PTm ρ1 b).
  Proof.
    move => + h. move : ρ0 ρ1. elim : a b / h.
    all : try hauto lq:on ctrs:R use:morphing_up, ProjPair'.
    move => a0 a1 b0 b1 ha iha hb ihb ρ0 ρ1 hρ /=.
    eapply AppAbs'; eauto; cycle 1. sfirstorder use:morphing_up. by asimpl.
    move => */=; eapply IndSuc'; eauto; cycle 1.
    sfirstorder use:morphing_up.
    sfirstorder use:morphing_up.
    by asimpl.
  Qed.

  Lemma substing (a : PTm) b (ρ : nat -> PTm) :
    R a b ->
    R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    hauto l:on use:morphing, refl.
  Qed.

  Lemma cong (a0 a1 : PTm) b0 b1  :
    R a0 a1 ->
    R b0 b1 ->
    R (subst_PTm (scons b0 VarPTm) a0) (subst_PTm (scons b1 VarPTm) a1).
  Proof.
    move => h0 h1. apply morphing=>//.
    hauto q:on inv:nat ctrs:R.
  Qed.

  Lemma FromRRed (a b : PTm) :
    RRed.R a b -> RPar.R a b.
  Proof.
    induction 1; qauto l:on use:RPar.refl ctrs:RPar.R.
  Qed.

  Function tstar (a : PTm) :=
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
    | PNat => PNat
    | PZero => PZero
    | PSuc a => PSuc (tstar a)
    | PInd P PZero b c => tstar b
    | PInd P (PSuc a) b c =>
        (subst_PTm (scons (PInd (tstar P) (tstar a) (tstar b) (tstar c)) (scons (tstar a) VarPTm)) (tstar c))
    | PInd P a b c => PInd (tstar P) (tstar a) (tstar b) (tstar c)
    end.

  Lemma triangle (a b : PTm) :
    RPar.R a b -> RPar.R b (tstar a).
  Proof.
    move : b.
    apply tstar_ind => {}a.
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
    - hauto lq:on ctrs:R inv:R.
    - hauto lq:on ctrs:R inv:R.
    - hauto lq:on ctrs:R inv:R.
    - move => P a0 b c ? hP ihP ha iha hb ihb u. subst.
      elim /inv => //= _.
      + move => P0 P1 a1 a2 b0 b1 c0 c1 hP' ha' hb' hc' [*]. subst.
        apply morphing. hauto lq:on ctrs:R inv:nat.
        eauto.
      + sauto q:on ctrs:R.
    - sauto lq:on.
  Qed.

  Lemma diamond (a b c : PTm) :
    R a b -> R a c -> exists d, R b d /\ R c d.
  Proof. eauto using triangle. Qed.
End RPar.

Lemma red_sn_preservation :
  (forall (a : PTm) (s : SNe a), forall b, RPar.R a b -> SNe b) /\
  (forall (a : PTm) (s : SN a), forall b, RPar.R a b -> SN b) /\
  (forall (a b : PTm) (_ : TRedSN a b), forall c, RPar.R a c -> exists d, TRedSN' c d /\ RPar.R b d).
Proof.
  apply sn_mutual.
  - hauto l:on inv:RPar.R.
  - qauto l:on inv:RPar.R,SNe,SN ctrs:SNe.
  - hauto lq:on inv:RPar.R, SNe ctrs:SNe.
  - hauto lq:on inv:RPar.R, SNe ctrs:SNe.
  (* - qauto l:on inv:RPar.R, SN,SNe ctrs:SNe. *)
  - qauto l:on ctrs:SN inv:RPar.R.
  - hauto lq:on ctrs:SN inv:RPar.R.
  - hauto lq:on ctrs:SN.
  - hauto q:on ctrs:SN inv:SN, TRedSN'.
  - hauto lq:on ctrs:SN inv:RPar.R.
  - hauto lq:on ctrs:SN inv:RPar.R.
  - hauto l:on inv:RPar.R.
  - hauto l:on inv:RPar.R.
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
  - sauto.
  - move => P a b c hP ihP ha iha hb ihb hc ihc u.
    elim /RPar.inv => //=_.
    + move => P0 P1 a0 a1 b0 b1 c0 c1 hP' ha' hb' hc' [*]. subst.
      eexists. split; first by apply T_Refl.
      apply RPar.morphing=>//. hauto lq:on ctrs:RPar.R inv:nat.
    + move => P0 P1 a0 a1 b0 b1 c0 c1 hP' ha' hb' hc' [*]. subst.
      elim /RPar.inv : ha' => //=_.
      move => a0 a2 ha' [*]. subst.
      eexists. split. apply T_Once.
      apply N_IndSuc; eauto.
      hauto q:on use:RPar.morphing ctrs:RPar.R inv:nat.
  - sauto q:on.
Qed.

Module RReds.

  Lemma abs_preservation a b : isabs a -> rtc RRed.R a b -> isabs b.
    induction 2; hauto lq:on use:RRed.abs_preservation. Qed.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:RRed.R.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong (a b : PTm) :
    rtc RRed.R a b ->
    rtc RRed.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong (a0 a1 b0 b1 : PTm) :
    rtc RRed.R a0 a1 ->
    rtc RRed.R b0 b1 ->
    rtc RRed.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong (a0 a1 b0 b1 : PTm) :
    rtc RRed.R a0 a1 ->
    rtc RRed.R b0 b1 ->
    rtc RRed.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong p (a0 a1  : PTm) :
    rtc RRed.R a0 a1 ->
    rtc RRed.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma SucCong (a0 a1 : PTm) :
    rtc RRed.R a0 a1 ->
    rtc RRed.R (PSuc a0) (PSuc a1).
  Proof. solve_s. Qed.

  Lemma IndCong P0 P1 (a0 a1 : PTm) b0 b1 c0 c1 :
    rtc RRed.R P0 P1 ->
    rtc RRed.R a0 a1 ->
    rtc RRed.R b0 b1 ->
    rtc RRed.R c0 c1 ->
    rtc RRed.R (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1).
  Proof. solve_s. Qed.

  Lemma BindCong p (A0 A1 : PTm) B0 B1 :
    rtc RRed.R A0 A1 ->
    rtc RRed.R B0 B1 ->
    rtc RRed.R (PBind p A0 B0) (PBind p A1 B1).
  Proof. solve_s. Qed.

  Lemma renaming (a b : PTm) (ξ : nat -> nat) :
    rtc RRed.R a b -> rtc RRed.R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : ξ. elim : a b /h; hauto lq:on ctrs:rtc use:RRed.renaming.
  Qed.

  Lemma FromRPar (a b : PTm) (h : RPar.R a b) :
    rtc RRed.R a b.
  Proof.
    elim : a b /h; eauto using AbsCong, AppCong, PairCong, ProjCong, rtc_refl, BindCong, IndCong, SucCong.
    move => a0 a1 b0 b1 ha iha hb ihb.
    apply : rtc_r; last by apply RRed.AppAbs.
    by eauto using AppCong, AbsCong.

    move => p a0 a1 b0 b1 ha iha hb ihb.
    apply : rtc_r; last by apply RRed.ProjPair.
    by eauto using PairCong, ProjCong.

    hauto lq:on ctrs:RRed.R, rtc.

    move => *.
    apply : rtc_r; last by apply RRed.IndSuc.
    by eauto using SucCong, IndCong.
  Qed.

  Lemma RParIff (a b : PTm) :
    rtc RRed.R a b <-> rtc RPar.R a b.
  Proof.
    split.
    induction 1; hauto l:on ctrs:rtc use:RPar.FromRRed, @relations.rtc_transitive.
    induction 1; hauto l:on ctrs:rtc use:FromRPar, @relations.rtc_transitive.
  Qed.

  Lemma nf_refl (a b : PTm) :
    rtc RRed.R a b -> nf a -> a = b.
  Proof. induction 1; sfirstorder use:RRed.nf_imp. Qed.

  Lemma FromRedSNs (a b : PTm) :
    rtc TRedSN a b ->
    rtc RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:rtc use:RRed.FromRedSN. Qed.

End RReds.


Module NeEPar.
  Inductive R_nonelim : PTm -> PTm ->  Prop :=
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
  | R_inj a b :
    R_elim a b ->
    R_nonelim a b
  with R_elim : PTm -> PTm -> Prop :=
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
  | NNatCong :
    R_elim PNat PNat
  | NIndCong P0 P1 a0 a1 b0 b1 c0 c1 :
    R_nonelim P0 P1 ->
    R_elim a0 a1 ->
    R_nonelim b0 b1 ->
    R_nonelim c0 c1 ->
    (* ----------------------- *)
    R_elim (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1)
  | NZeroCong :
    R_elim PZero PZero
  | NSucCong a0 a1 :
    R_nonelim a0 a1 ->
    (* ------------ *)
    R_elim (PSuc a0) (PSuc a1).

  Scheme epar_elim_ind := Induction for R_elim Sort Prop
      with epar_nonelim_ind := Induction for R_nonelim Sort Prop.

  Combined Scheme epar_mutual from epar_elim_ind, epar_nonelim_ind.

  Lemma R_elim_nf :
    (forall (a b : PTm), R_elim a b -> nf b -> nf a) /\
      (forall (a b : PTm), R_nonelim a b -> nf b -> nf a).
  Proof.
    apply epar_mutual => //=.
    - move => a0 a1 b0 b1 h ih h' ih' /andP [h0 h1].
      have hb0 : nf b0 by eauto.
      suff : ne a0 by qauto b:on.
      hauto q:on inv:R_elim.
    - hauto lb:on.
    - hauto lq:on inv:R_elim.
    - hauto b:on.
    - hauto lqb:on inv:R_elim.
    - move => a0 a1 /negP ha' ha ih ha1.
      have {ih} := ih ha1.
      move => ha0.
      suff : ne a0 by hauto lb:on drew:off use:ne_nf_ren.
      inversion ha; subst => //=.
    - move => a0 a1 /negP ha' ha ih ha1.
      have {}ih := ih ha1.
      have : ne a0 by hauto lq:on inv:PTm.
      qauto lb:on.
  Qed.

  Lemma R_nonelim_nothf (a b : PTm) :
    R_nonelim a b ->
    ~~ ishf a ->
    R_elim a b.
  Proof.
    move => h. elim : a b /h=>//=; hauto lq:on ctrs:R_elim.
  Qed.

  Lemma R_elim_nonelim (a b : PTm) :
    R_elim a b ->
    R_nonelim a b.
    hauto lq:on ctrs:R_nonelim.
  Qed.

  Lemma ToEPar : (forall (a b : PTm), R_elim a b -> EPar.R a b) /\
                 (forall (a b : PTm), R_nonelim a b -> EPar.R a b).
  Proof.
    apply epar_mutual; qauto l:on ctrs:EPar.R.
  Qed.

End NeEPar.

Module Type NoForbid.
  Parameter P : PTm -> Prop.

  Axiom P_EPar : forall (a b : PTm), EPar.R a b -> P a -> P b.
  Axiom P_RRed : forall (a b : PTm), RRed.R a b -> P a -> P b.
  Axiom PApp_imp : forall a b, ishf a -> ~~ isabs a -> ~ P (PApp a b).
  Axiom PProj_imp : forall p a, ishf a -> ~~ ispair a -> ~ P (PProj p a).
  Axiom PInd_imp : forall Q (a : PTm) b c,
  ishf a ->
  ~~ iszero a ->
  ~~ issuc a  -> ~ P (PInd Q a b c).

  Axiom P_AppInv : forall (a b : PTm), P (PApp a b) -> P a /\ P b.
  Axiom P_AbsInv : forall (a : PTm), P (PAbs a) -> P a.
  Axiom P_SucInv : forall (a : PTm), P (PSuc a) -> P a.
  Axiom P_BindInv : forall p (A : PTm) B, P (PBind p A B) -> P A /\ P B.
  Axiom P_IndInv : forall Q (a : PTm) b c, P (PInd Q a b c) -> P Q /\ P a /\ P b /\ P c.

  Axiom P_PairInv : forall (a b : PTm), P (PPair a b) -> P a /\ P b.
  Axiom P_ProjInv : forall p (a : PTm), P (PProj p a) -> P a.
  Axiom P_renaming : forall (ξ : nat -> nat) a , P (ren_PTm ξ a) -> P a.
End NoForbid.

Module Type NoForbid_FactSig (M : NoForbid).

  Axiom P_EPars : forall (a b : PTm), rtc EPar.R a b -> M.P a -> M.P b.

  Axiom P_RReds : forall (a b : PTm), rtc RRed.R a b -> M.P a -> M.P b.

End NoForbid_FactSig.

Module NoForbid_Fact (M : NoForbid) : NoForbid_FactSig M.
  Import M.

  Lemma P_EPars : forall (a b : PTm), rtc EPar.R a b -> P a -> P b.
  Proof.
    induction 1; eauto using P_EPar, rtc_l, rtc_refl.
  Qed.

  Lemma P_RReds : forall (a b : PTm), rtc RRed.R a b -> P a -> P b.
  Proof.
    induction 1; eauto using P_RRed, rtc_l, rtc_refl.
  Qed.
End NoForbid_Fact.

Module SN_NoForbid <: NoForbid.
  Definition P := @SN.

  Lemma P_EPar : forall (a b : PTm), EPar.R a b -> P a -> P b.
  Proof. sfirstorder use:epar_sn_preservation. Qed.

  Lemma P_RRed : forall (a b : PTm), RRed.R a b -> P a -> P b.
  Proof. hauto q:on use:red_sn_preservation, RPar.FromRRed. Qed.

  Lemma PApp_imp : forall a b, ishf a -> ~~ isabs a -> ~ P (PApp a b).
    sfirstorder use:fp_red.PApp_imp. Qed.
  Lemma PProj_imp : forall p a, ishf a -> ~~ ispair a -> ~ P (PProj p a).
    sfirstorder use:fp_red.PProj_imp. Qed.

  Lemma PInd_imp : forall Q (a : PTm) b c,
      ishf a ->
      ~~ iszero a ->
      ~~ issuc a  -> ~ P (PInd Q a b c).
  Proof. sfirstorder use: fp_red.PInd_imp. Qed.

  Lemma P_AppInv : forall (a b : PTm), P (PApp a b) -> P a /\ P b.
  Proof. sfirstorder use:SN_AppInv. Qed.

  Lemma P_PairInv : forall (a b : PTm), P (PPair a b) -> P a /\ P b.
    move => a b. move E : (PPair a b) => u h.
    move : a b E. elim : u / h; sauto lq:on rew:off. Qed.

  Lemma P_ProjInv : forall p (a : PTm), P (PProj p a) -> P a.
  Proof. sfirstorder use:SN_ProjInv. Qed.

  Lemma P_BindInv : forall p (A : PTm) B, P (PBind p A B) -> P A /\ P B.
  Proof.
    move => p A B.
    move E : (PBind p A B) => u hu.
    move : p A B E. elim : u /hu=>//=;sauto lq:on rew:off.
  Qed.

  Lemma P_SucInv : forall (a : PTm), P (PSuc a) -> P a.
  Proof. sauto lq:on. Qed.

  Lemma P_AbsInv : forall (a : PTm), P (PAbs a) -> P a.
  Proof.
    move => a. move E : (PAbs a) => u h.
    move : E. move : a.
    induction h; sauto lq:on rew:off.
  Qed.

  Lemma P_renaming : forall (ξ : nat -> nat) a , P (ren_PTm ξ a) -> P  a.
  Proof. hauto lq:on use:sn_antirenaming, sn_renaming. Qed.

  Lemma P_IndInv : forall Q (a : PTm) b c, P (PInd Q a b c) -> P Q /\ P a /\ P b /\ P c.
  Proof. sfirstorder use:SN_IndInv. Qed.

End SN_NoForbid.

Module NoForbid_FactSN := NoForbid_Fact SN_NoForbid.

Module UniqueNF (M : NoForbid) (MFacts : NoForbid_FactSig M).
  Import M MFacts.
  #[local]Hint Resolve P_EPar P_RRed PApp_imp PProj_imp : forbid.

  Lemma η_split (a0 a1 : PTm) :
    EPar.R a0 a1 ->
    P a0 ->
    exists b, rtc RRed.R a0 b /\ NeEPar.R_nonelim b a1.
  Proof.
    move => h. elim : a0 a1 /h .
    - move => a0 a1 ha ih /[dup] hP.
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
        apply RRed.AppAbs'. asimpl.
        set y := subst_PTm _ _.
        suff : ren_PTm id p = y. by asimpl.
        subst y.
        substify.
        apply ext_PTm.
        case => //=.
      (* violates SN *)
      + move /P_AbsInv in hP.
        have {}hP : P (PApp (ren_PTm shift b) (VarPTm var_zero))
          by sfirstorder use:P_RReds, RReds.AppCong, @rtc_refl, RReds.renaming.
        move => ? ?.
        have ? : ~~ isabs (ren_PTm shift b) by scongruence use:isabs_ren.
        have ? : ishf (ren_PTm shift b) by scongruence use:ishf_ren.
        exfalso.
        sfirstorder use:PApp_imp.
    - move => a0 a1 h ih /[dup] hP.
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
    - hauto lq:on ctrs:NeEPar.R_elim, NeEPar.R_nonelim use:RReds.AbsCong, P_AbsInv.
    - move => a0 a1 b0 b1 ha iha hb ihb.
      move => /[dup] hP /P_AppInv [hP0 hP1].
      have {iha} [a2 [iha0 iha1]]  := iha hP0.
      have {ihb} [b2 [ihb0 ihb1]]  := ihb hP1.
      case /orP : (orNb (ishf a2)) => [h|].
      + exists (PApp a2 b2). split; first by eauto using RReds.AppCong.
        hauto lq:on ctrs:NeEPar.R_nonelim, NeEPar.R_elim use:NeEPar.R_nonelim_nothf.
      + case /orP : (orbN (isabs a2)).
        (* case : a2 iha0 iha1 => //=. *)
        * case : a2 iha0 iha1 => //= p h0 h1 _ _.
          inversion h1; subst.
          ** exists (PApp a2 b2).
             split.
             apply : rtc_r.
             apply RReds.AppCong; eauto.
             apply RRed.AppAbs'. by asimpl.
             hauto lq:on ctrs:NeEPar.R_nonelim, NeEPar.R_elim.
          ** hauto lq:on ctrs:NeEPar.R_nonelim,NeEPar.R_elim use:RReds.AppCong.
        (* Impossible *)
        * move =>*. exfalso.
          have : P (PApp a2 b0) by sfirstorder use:RReds.AppCong, @rtc_refl, P_RReds.
          sfirstorder use:PApp_imp.
    - hauto lq:on ctrs:NeEPar.R_nonelim, NeEPar.R_elim use:RReds.PairCong, P_PairInv.
    - move => p a0 a1 ha ih /[dup] hP /P_ProjInv.
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
          hauto lq:on ctrs:NeEPar.R_nonelim, NeEPar.R_elim.
        * hauto lq:on ctrs:NeEPar.R_nonelim,NeEPar.R_elim use:RReds.ProjCong.
    - hauto lq:on ctrs:rtc, NeEPar.R_nonelim,NeEPar.R_elim.
    - hauto lq:on ctrs:NeEPar.R_nonelim,NeEPar.R_elim,rtc.
    - hauto lq:on ctrs:NeEPar.R_nonelim, rtc,NeEPar.R_elim use:RReds.BindCong, P_BindInv.
    - hauto lq:on ctrs:NeEPar.R_nonelim, rtc ,NeEPar.R_elim use:RReds.BindCong, P_BindInv.
    - move => P0 P1 a0 a1 b0 b1 c0 c1 hP ihP ha iha hb ihb hc ihc /[dup] hInd /P_IndInv.
      move => []. move : ihP => /[apply].
      move => [P01][ihP0]ihP1.
      move => []. move : iha => /[apply].
      move => [a01][iha0]iha1.
      move => []. move : ihb => /[apply].
      move => [b01][ihb0]ihb1.
      move : ihc => /[apply].
      move => [c01][ihc0]ihc1.
      case /orP : (orNb (ishf a01)) => [h|].
      + eexists. split. by eauto using RReds.IndCong.
        hauto q:on ctrs:NeEPar.R_nonelim, NeEPar.R_elim use:NeEPar.R_nonelim_nothf.
      + move => h.
        case /orP : (orNb (issuc a01 || iszero a01)).
        * move /norP.
          have : P (PInd P01 a01 b01 c01) by eauto using P_RReds, RReds.IndCong.
          hauto lq:on use:PInd_imp.
        * move => ha01.
          eexists. split. eauto using RReds.IndCong.
          apply NeEPar.R_inj.
          apply NeEPar.NIndCong; eauto.
          move : iha1 ha01. clear.
          inversion 1; subst => //=; hauto lq:on ctrs:NeEPar.R_elim.
    - hauto lq:on ctrs:NeEPar.R_nonelim,NeEPar.R_elim,rtc.
    - hauto lq:on ctrs:NeEPar.R_nonelim, NeEPar.R_elim use:RReds.SucCong, P_SucInv.
  Qed.

  Lemma eta_postponement a b c :
    P a ->
    EPar.R a b ->
    RRed.R b c ->
    exists d, rtc RRed.R a d /\ EPar.R d c.
  Proof.
    move => + h.
    move : c.
    elim : a b /h => //=.
    - move => a0 a1 ha iha c /[dup] hP /P_AbsInv /P_AppInv [/P_renaming hP' _] hc.
      move : iha (hP') (hc); repeat move/[apply].
      move => [d [h0 h1]].
      exists  (PAbs (PApp (ren_PTm shift d) (VarPTm var_zero))).
      split. hauto lq:on rew:off ctrs:rtc use:RReds.AbsCong, RReds.AppCong, RReds.renaming.
      hauto lq:on ctrs:EPar.R.
    - move => a0 a1 ha iha c /P_PairInv [/P_ProjInv + _].
      move /iha => /[apply].
      move => [d [h0 h1]].
      exists (PPair (PProj PL d) (PProj PR d)).
      hauto lq:on ctrs:EPar.R use:RReds.PairCong, RReds.ProjCong.
    - move => a0 a1 ha iha c  /P_AbsInv /[swap].
      elim /RRed.inv => //=_.
      move => a2 a3 + [? ?]. subst.
      move : iha; repeat move/[apply].
      hauto lq:on use:RReds.AbsCong ctrs:EPar.R.
    - move => a0 a1 b0 b1 ha iha hb ihb c hP.
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
          apply RRed.AppAbs'. by asimpl.
        * exfalso.
          move : hP h0. clear => hP h0.
          have : rtc RRed.R (PApp a0 b0) (PApp (PPair (PProj PL a1) (PProj PR a1)) b0)
            by qauto l:on ctrs:rtc use:RReds.AppCong.
          move : P_RReds hP. repeat move/[apply].
          sfirstorder use:PApp_imp.
        * inversion H; subst.
          exists (subst_PTm (scons b0 VarPTm) a1).
          split.
          apply : rtc_r; last by apply RRed.AppAbs.
          hauto lq:on ctrs:rtc use:RReds.AppCong.
          hauto l:on inv:nat use:EPar.morphing,NeEPar.ToEPar.
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
    - move => a0 a1 b0 b1 ha iha hb ihb c /P_PairInv [hP hP'].
      elim /RRed.inv => //=_;
        hauto lq:on rew:off ctrs:EPar.R, rtc use:RReds.PairCong.
    - move => p a0 a1 ha iha c /[dup] hP /P_ProjInv hP'.
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
        * inversion H; subst.
          exists (if p is PL then a3 else b1).
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
    - move => P0 P1 a0 a1 b0 b1 c0 c1 hP ihP ha iha hb ihb hc ihc u.
      move => /[dup] hInd.
      move /P_IndInv.
      move => [pP0][pa0][pb0]pc0.
      elim /RRed.inv => //= _.
      + move => P2 b2 c2 [*]. subst.
        move /η_split : pa0 ha; repeat move/[apply].
        move => [a1][h0]h1 {iha}.
        inversion h1; subst.
        * exfalso.
          have :P (PInd P0 (PAbs (PApp (ren_PTm shift a2) (VarPTm var_zero))) b0 c0) by eauto using RReds.IndCong, rtc_refl, P_RReds.
          clear. hauto lq:on use:PInd_imp.
        * have :P (PInd P0 (PPair (PProj PL a2) (PProj PR a2)) b0 c0) by eauto using RReds.IndCong, rtc_refl, P_RReds.
          clear. hauto lq:on use:PInd_imp.
        * eexists. split; eauto.
          apply : rtc_r.
          apply : RReds.IndCong; eauto; eauto using rtc_refl.
          inversion H; subst.
          apply RRed.IndZero.
      + move => P2 a2 b2 c [*]. subst.
        move /η_split /(_ pa0) : ha.
        move => [a1][h0]h1.
        inversion h1; subst.
        * have :P (PInd P0 (PAbs (PApp (ren_PTm shift a3) (VarPTm var_zero))) b0 c0) by eauto using RReds.IndCong, rtc_refl, P_RReds.
          clear. hauto q:on use:PInd_imp.
        * have :P (PInd P0 (PPair (PProj PL a3) (PProj PR a3)) b0 c0) by eauto using RReds.IndCong, rtc_refl, P_RReds.
          clear. hauto q:on use:PInd_imp.
        * inversion H; subst.
          eexists. split.
          apply : rtc_r.
          apply RReds.IndCong; eauto; eauto using rtc_refl.
          apply RRed.IndSuc.
          apply EPar.morphing;eauto.
          case => [|].
          hauto lq:on rew:off ctrs:EPar.R use:NeEPar.ToEPar.
          case => [|i].
          hauto lq:on rew:off ctrs:EPar.R use:NeEPar.ToEPar.
          asimpl. apply EPar.VarTm.
      + move => P2 P3 a2 b2 c hP0 [*]. subst.
        move : ihP hP0 pP0. repeat move/[apply].
        move => [P2][h0]h1.
        exists (PInd P2 a0 b0 c0).
        sfirstorder use:RReds.IndCong, @rtc_refl, EPar.IndCong.
      + move => P2 a2 a3 b2 c + [*]. subst.
        move : iha pa0; repeat move/[apply].
        move => [a2][*].
        exists (PInd P0 a2 b0 c0).
        sfirstorder use:RReds.IndCong, @rtc_refl, EPar.IndCong.
      + move => P2 a2 b2 b3 c + [*]. subst.
        move : ihb pb0; repeat move/[apply].
        move => [b2][*].
        exists (PInd P0 a0 b2 c0).
        sfirstorder use:RReds.IndCong, @rtc_refl, EPar.IndCong.
      + move => P2 a2 b2 b3 c + [*]. subst.
        move : ihc pc0; repeat move/[apply].
        move => [c2][*].
        exists (PInd P0 a0 b0 c2).
        sfirstorder use:RReds.IndCong, @rtc_refl, EPar.IndCong.
    - hauto lq:on inv:RRed.R ctrs:rtc, EPar.R.
    - move => a0 a1 ha iha u /P_SucInv ha0.
      elim /RRed.inv => //= _ a2 a3 h [*]. subst.
      move : iha (ha0) (h); repeat move/[apply].
      move => [a2 [ih0 ih1]].
      exists (PSuc a2).
      split. by apply RReds.SucCong.
      by apply EPar.SucCong.
  Qed.

  Lemma η_postponement_star a b c :
    P a ->
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

  Lemma η_postponement_star' a b c :
    P a ->
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
  Inductive R : PTm -> PTm ->  Prop :=

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
    R (PBind p A B0) (PBind p A B1)
  | IndCong0 P0 P1 a b c :
    R P0 P1 ->
    R (PInd P0 a b c) (PInd P1 a b c)
  | IndCong1 P a0 a1 b c :
    R a0 a1 ->
    R (PInd P a0 b c) (PInd P a1 b c)
  | IndCong2 P a b0 b1 c :
    R b0 b1 ->
    R (PInd P a b0 c) (PInd P a b1 c)
  | IndCong3 P a b c0 c1 :
    R c0 c1 ->
    R (PInd P a b c0) (PInd P a b c1)
  | SucCong a0 a1 :
    R a0 a1 ->
    R (PSuc a0) (PSuc a1).

  Derive Inversion inv with (forall (a b : PTm), R a b) Sort Prop.

  Lemma abs_back_preservation (a b : PTm) :
    SN a -> R a b -> isabs b -> isabs a.
  Proof.
    move => + h.
    elim : a b /h => //=.
    case => //=. move => p. move /SN_NoForbid.P_PairInv.
    sfirstorder use:SN_NoForbid.PProj_imp.
  Qed.

  Lemma ToEPar (a b : PTm) :
    ERed.R a b -> EPar.R a b.
  Proof.
    induction 1; hauto lq:on use:EPar.refl ctrs:EPar.R.
  Qed.

  Ltac2 rec solve_anti_ren () :=
    let x := Fresh.in_goal (Option.get (Ident.of_string "x")) in
    intro $x;
    lazy_match! Constr.type (Control.hyp x) with
    | nat -> _ => (ltac1:(case;hauto q:on depth:2 ctrs:ERed.R))
    | _ => solve_anti_ren ()
    end.

  Ltac solve_anti_ren := ltac2:(Control.enter solve_anti_ren).

  Lemma AppEta' a u :
    u = (PApp (ren_PTm shift a) (VarPTm var_zero)) ->
    R (PAbs u) a.
  Proof. move => ->. apply AppEta. Qed.

  Lemma renaming (a b : PTm) (ξ : nat -> nat) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : ξ.
    elim : a b /h.

    move => a ξ /=.
    apply AppEta'; eauto. by asimpl.
    all : qauto ctrs:R.
  Qed.

  (* Characterization of variable freeness conditions *)
  Definition tm_i_free a (i : nat) := exists (ξ ξ0 : nat -> nat), ξ i <> ξ0 i /\ ren_PTm ξ a = ren_PTm ξ0 a.

  Lemma subst_differ_one_ren_up i (ξ0 ξ1 : nat -> nat) :
    (forall j, i <> j -> ξ0 j = ξ1 j) ->
    (forall j, shift i <> j -> upRen_PTm_PTm ξ0 j =  upRen_PTm_PTm ξ1 j).
  Proof.
    move => hξ.
    case => // j.
    asimpl.
    move => h. have :  i<> j by hauto lq:on rew:off.
    move /hξ. by rewrite /funcomp => ->.
  Qed.

  Lemma tm_free_ren_any a i :
    tm_i_free a i ->
    forall (ξ0 ξ1 : nat -> nat), (forall j, i <> j -> ξ0 j = ξ1 j) ->
             ren_PTm ξ0 a = ren_PTm ξ1 a.
  Proof.
    rewrite /tm_i_free.
    move => [+ [+ [+ +]]].
    move : i.
    elim : a.
    - hauto q:on.
    - move => a iha i ρ0 ρ1 h [] h' ξ0 ξ1 hξ /=.
      f_equal. move /subst_differ_one_ren_up in hξ.
      move /(_ (shift i)) in iha.
      move : iha hξ; move/[apply].
      apply; cycle 1; eauto.
    - hauto lq:on rew:off.
    - hauto lq:on rew:off.
    - hauto lq:on rew:off.
    - move => p A ihA a iha i ρ0 ρ1 hρ [] ? h ξ0 ξ1 hξ /=.
      f_equal. hauto lq:on rew:off.
      move /subst_differ_one_ren_up in hξ.
      move /(_ (shift i)) in iha.
      move : iha (hξ). repeat move/[apply].
      move /(_ (upRen_PTm_PTm ρ0) (upRen_PTm_PTm ρ1)).
      apply. simpl. rewrite /funcomp. scongruence.
      sfirstorder.
    - hauto lq:on rew:off.
    - hauto lq:on rew:off.
    - hauto lq:on rew:off.
    - hauto lq:on rew:off.
    - move => P ihP a iha b ihb c ihc i ρ0 ρ1 hρ /= []hP
               ha hb hc ξ0 ξ1 hξ.
      f_equal;eauto.
      apply : ihP; cycle 1; eauto using subst_differ_one_ren_up.
      apply : ihc; cycle 1; eauto using subst_differ_one_ren_up.
      hauto l:on.
  Qed.

  Lemma antirenaming (a : PTm) (b : PTm) (ξ : nat -> nat) :
    (forall i j, ξ i = ξ j -> i = j) ->
    R (ren_PTm ξ a) b -> exists b0, R a b0 /\ ren_PTm ξ b0 = b.
  Proof.
    move => hξ.
    move E : (ren_PTm ξ a) => u hu.
    move : ξ a hξ E.
    elim : u b / hu; try solve_anti_ren.
    - move => a ξ []//=.
      move => u hξ [].
      case : u => //=.
      move => u0 u1 [].
      case : u1 => //=.
      move => i /[swap] [].
      case : i => //= _ h.
      suff : exists p, ren_PTm shift p = u0.
      move => [p ?]. subst.
      move : h. asimpl.
      replace (ren_PTm (funcomp S ξ) p) with
        (ren_PTm shift (ren_PTm ξ p)); last by asimpl.
      move /ren_injective.
      move /(_ ltac:(hauto l:on unfold:ren_inj)).
      move => ?. subst.
      exists p. split=>//. apply AppEta.
      set u := ren_PTm (scons 0 id) u0.
      suff : ren_PTm shift u = u0 by eauto.
      subst u.
      asimpl.
      have hE : u0 = ren_PTm id u0 by asimpl.
      rewrite {2}hE. move{hE}.
      apply (tm_free_ren_any _ 0); last by qauto l:on inv:nat.
      rewrite /tm_i_free.
      have h' := h.
      apply f_equal with (f := ren_PTm (scons 0 id)) in h.
      apply f_equal with (f := ren_PTm (scons 1 id)) in h'.
      move : h'. asimpl => *. subst.
      move : h. asimpl. move => *. do 2 eexists. split; eauto.
      scongruence.
    - move => a ξ [] //=.
      move => u u0 hξ [].
      case : u => //=.
      case : u0 => //=.
      move => p p0 p1 p2 [? ?] [? h]. subst.
      have ? : p0 = p2 by eauto using ren_injective. subst.
      hauto l:on.
    - move => a0 a1 ha iha ξ []//= p hξ [?]. subst.
      fcrush use:up_injective.
    - move => p A B0 B1 hB ihB ξ + hξ.
      case => //= p' A2 B2 [*]. subst.
      have : (forall i j, (upRen_PTm_PTm ξ) i = (upRen_PTm_PTm ξ) j -> i = j) by sfirstorder use:up_injective.
      move => {}/ihB => ihB.
      spec_refl.
      sauto lq:on.
    - move => P0 P1 a b c hP ihP ξ []//=.
      move => > /up_injective.
      hauto q:on ctrs:R.
    - move => P a b c0 c1 hc ihc ξ []//=.
      move => > /up_injective /up_injective.
      hauto q:on ctrs:R.
  Qed.

  Lemma substing (a b : PTm) (ρ : nat -> PTm) :
    R a b -> R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    move => h. move : ρ. elim : a b /h.
    move => a ρ /=.
    eapply AppEta'; eauto. by asimpl.
    all : hauto lq:on ctrs:R.
  Qed.

  Lemma nf_preservation (a b : PTm) :
    ERed.R a b -> (nf a -> nf b) /\ (ne a -> ne b).
  Proof.
    move => h.
    elim : a b /h => //=;
      hauto lqb:on use:ne_nf_ren,ne_nf.
  Qed.

End ERed.

Module EReds.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:ERed.R.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong (a b : PTm) :
    rtc ERed.R a b ->
    rtc ERed.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong (a0 a1 b0 b1 : PTm) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R b0 b1 ->
    rtc ERed.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong (a0 a1 b0 b1 : PTm) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R b0 b1 ->
    rtc ERed.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong p (a0 a1  : PTm) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma BindCong p (A0 A1 : PTm) B0 B1 :
    rtc ERed.R A0 A1 ->
    rtc ERed.R B0 B1 ->
    rtc ERed.R (PBind p A0 B0) (PBind p A1 B1).
  Proof. solve_s. Qed.

  Lemma SucCong (a0 a1 : PTm) :
    rtc ERed.R a0 a1 ->
    rtc ERed.R (PSuc a0) (PSuc a1).
  Proof. solve_s. Qed.

  Lemma IndCong P0 P1 (a0 a1 : PTm) b0 b1 c0 c1 :
    rtc ERed.R P0 P1 ->
    rtc ERed.R a0 a1 ->
    rtc ERed.R b0 b1 ->
    rtc ERed.R c0 c1 ->
    rtc ERed.R (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1).
  Proof. solve_s. Qed.

  Lemma renaming (a b : PTm) (ξ : nat -> nat) :
    rtc ERed.R a b -> rtc ERed.R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof. induction 1; hauto l:on use:ERed.renaming ctrs:rtc. Qed.

  Lemma FromEPar (a b : PTm) :
    EPar.R a b ->
    rtc ERed.R a b.
  Proof.
    move => h. elim : a b /h; eauto using AbsCong, AppCong, PairCong, ProjCong, rtc_refl, BindCong, IndCong, SucCong.
    - move => a0 a1 _ h.
      have {}h : rtc ERed.R (ren_PTm shift a0) (ren_PTm shift a1) by apply renaming.
      apply : rtc_r. apply AbsCong. apply AppCong; eauto. apply rtc_refl.
      apply ERed.AppEta.
    - move => a0 a1 _ h.
      apply : rtc_r.
      apply PairCong; eauto using ProjCong.
      apply ERed.PairEta.
  Qed.

  Lemma FromEPars (a b : PTm) :
    rtc EPar.R a b ->
    rtc ERed.R a b.
  Proof. induction 1; hauto l:on use:FromEPar, @relations.rtc_transitive. Qed.

  Lemma substing (a b : PTm) (ρ : nat -> PTm) :
    rtc ERed.R a b -> rtc ERed.R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    induction 1; hauto lq:on ctrs:rtc use:ERed.substing.
  Qed.

  Lemma app_inv (a0 b0 C : PTm) :
    rtc ERed.R (PApp a0 b0) C ->
    exists a1 b1, C = PApp a1 b1 /\
               rtc ERed.R a0 a1 /\
               rtc ERed.R b0 b1.
  Proof.
    move E : (PApp a0 b0) => u hu.
    move : a0 b0 E.
    elim : u C / hu.
    - hauto lq:on ctrs:rtc.
    - move => a0 a1 a2 ha ha0 iha b0 b1 ?. subst.
      inversion ha; subst; spec_refl;
      hauto lq:on rew:off ctrs:rtc, ERed.R inv:ERed.R.
  Qed.

  Lemma proj_inv p (a C : PTm) :
    rtc ERed.R (PProj p a) C ->
    exists c, C = PProj p c /\ rtc ERed.R a c.
  Proof.
    move E : (PProj p a) => u hu.
    move : p a E.
    elim : u C /hu;
      scrush ctrs:rtc,ERed.R inv:ERed.R.
  Qed.

  Lemma bind_inv p (A : PTm) B C :
    rtc ERed.R (PBind p A B) C ->
    exists A0 B0, C = PBind p A0 B0 /\ rtc ERed.R A A0 /\ rtc ERed.R B B0.
  Proof.
    move E : (PBind p A B) => u hu.
    move : p A B E.
    elim : u C / hu.
    hauto lq:on ctrs:rtc.
    hauto lq:on rew:off ctrs:rtc, ERed.R inv:ERed.R, rtc.
  Qed.

  Lemma suc_inv (a : PTm) C :
    rtc ERed.R (PSuc a) C ->
    exists b, rtc ERed.R a b /\ C = PSuc b.
  Proof.
    move E : (PSuc a) => u hu.
    move : a E.
    elim : u C / hu=>//=.
    - hauto l:on.
    - hauto lq:on rew:off ctrs:rtc, ERed.R inv:ERed.R, rtc.
  Qed.

  Lemma zero_inv (C : PTm) :
    rtc ERed.R PZero C -> C = PZero.
    move E : PZero => u hu.
    move : E. elim : u C /hu=>//=.
    - hauto lq:on rew:off ctrs:rtc, ERed.R inv:ERed.R, rtc.
  Qed.

  Lemma ind_inv P (a : PTm) b c C :
    rtc ERed.R (PInd P a b c) C ->
    exists P0 a0 b0 c0,  rtc ERed.R P P0 /\ rtc ERed.R a a0 /\
                      rtc ERed.R b b0 /\ rtc ERed.R c c0 /\
                      C = PInd P0 a0 b0 c0.
  Proof.
    move E : (PInd P a b c) => u hu.
    move : P a b c E.
    elim : u C / hu.
    - hauto lq:on ctrs:rtc.
    - scrush ctrs:rtc, ERed.R inv:ERed.R, rtc.
  Qed.

End EReds.

#[export]Hint Constructors ERed.R RRed.R EPar.R : red.

Module EJoin.
  Definition R (a b : PTm) := exists c, rtc ERed.R a c /\ rtc ERed.R b c.

  Lemma hne_app_inj (a0 b0 a1 b1 : PTm) :
    R (PApp a0 b0) (PApp a1 b1) ->
    R a0 a1 /\ R b0 b1.
  Proof.
    hauto lq:on use:EReds.app_inv.
  Qed.

  Lemma hne_proj_inj p0 p1 (a0 a1 : PTm) :
    R (PProj p0 a0) (PProj p1 a1) ->
    p0 = p1 /\ R a0 a1.
  Proof.
    hauto lq:on rew:off use:EReds.proj_inv.
  Qed.

  Lemma bind_inj p0 p1 (A0 A1 : PTm) B0 B1 :
    R (PBind p0 A0 B0) (PBind p1 A1 B1) ->
    p0 = p1 /\ R A0 A1 /\ R B0 B1.
  Proof.
    hauto lq:on rew:off use:EReds.bind_inv.
  Qed.

  Lemma suc_inj (A0 A1 : PTm)  :
    R (PSuc A0) (PSuc A1) ->
    R A0 A1.
  Proof.
    hauto lq:on rew:off use:EReds.suc_inv.
  Qed.

  Lemma ind_inj P0 P1 (a0 a1 : PTm) b0 b1 c0 c1 :
    R (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1) ->
    R P0 P1 /\ R a0 a1 /\ R b0 b1 /\ R c0 c1.
  Proof. hauto q:on use:EReds.ind_inv. Qed.

End EJoin.

Module RERed.
  Inductive R : PTm -> PTm ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a b :
    R (PApp (PAbs a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

  | IndZero P b c :
    R (PInd P PZero b c) b

  | IndSuc P a b c :
    R (PInd P (PSuc a) b c) (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c)

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
    R (PBind p A B0) (PBind p A B1)
  | IndCong0 P0 P1 a b c :
    R P0 P1 ->
    R (PInd P0 a b c) (PInd P1 a b c)
  | IndCong1 P a0 a1 b c :
    R a0 a1 ->
    R (PInd P a0 b c) (PInd P a1 b c)
  | IndCong2 P a b0 b1 c :
    R b0 b1 ->
    R (PInd P a b0 c) (PInd P a b1 c)
  | IndCong3 P a b c0 c1 :
    R c0 c1 ->
    R (PInd P a b c0) (PInd P a b c1)
  | SucCong a0 a1 :
    R a0 a1 ->
    R (PSuc a0) (PSuc a1).

  Lemma ToBetaEta (a b : PTm) :
    R a b ->
    ERed.R a b \/ RRed.R a b.
  Proof. induction 1; hauto lq:on db:red. Qed.

  Lemma FromBeta (a b : PTm) :
    RRed.R a b -> RERed.R a b.
  Proof. induction 1; qauto l:on ctrs:R. Qed.

  Lemma FromEta (a b : PTm) :
    ERed.R a b -> RERed.R a b.
  Proof. induction 1; qauto l:on ctrs:R. Qed.

  Lemma ToBetaEtaPar (a b : PTm) :
    R a b ->
    EPar.R a b \/ RRed.R a b.
  Proof.
    hauto q:on use:ERed.ToEPar, ToBetaEta.
  Qed.

  Lemma sn_preservation (a b : PTm) :
    R a b ->
    SN a ->
    SN b.
  Proof. hauto q:on use:ToBetaEtaPar, epar_sn_preservation, red_sn_preservation, RPar.FromRRed. Qed.

  Lemma bind_preservation (a b : PTm) :
    R a b -> isbind a -> isbind b.
  Proof. hauto q:on inv:R. Qed.

  Lemma univ_preservation (a b : PTm) :
    R a b -> isuniv a -> isuniv b.
  Proof. hauto q:on inv:R. Qed.

  Lemma nat_preservation (a b : PTm) :
    R a b -> isnat a -> isnat b.
  Proof. hauto q:on inv:R. Qed.

  Lemma sne_preservation (a b : PTm) :
    R a b -> SNe a -> SNe b.
  Proof.
    hauto q:on use:ToBetaEtaPar, RPar.FromRRed use:red_sn_preservation, epar_sn_preservation.
  Qed.

  Lemma substing (a b : PTm) (ρ : nat -> PTm) :
    RERed.R a b -> RERed.R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    hauto q:on use:ToBetaEta, FromBeta, FromEta, RRed.substing, ERed.substing.
  Qed.

  Lemma hne_preservation (a b : PTm) :
    RERed.R a b -> ishne a -> ishne b.
  Proof.  induction 1; sfirstorder. Qed.

End RERed.

Module REReds.
  Lemma hne_preservation (a b : PTm) :
    rtc RERed.R a b -> ishne a -> ishne b.
  Proof.  induction 1; eauto using RERed.hne_preservation, rtc_refl, rtc. Qed.

  Lemma sn_preservation (a b : PTm) :
    rtc RERed.R a b ->
    SN a ->
    SN b.
  Proof. induction 1; eauto using RERed.sn_preservation. Qed.

  Lemma FromRReds (a b : PTm) :
    rtc RRed.R a b ->
    rtc RERed.R a b.
  Proof. induction 1; hauto lq:on ctrs:rtc use:RERed.FromBeta. Qed.

  Lemma FromEReds (a b : PTm) :
    rtc ERed.R a b ->
    rtc RERed.R a b.
  Proof. induction 1; hauto lq:on ctrs:rtc use:RERed.FromEta. Qed.

  #[local]Ltac solve_s_rec :=
    move => *; eapply rtc_l; eauto;
           hauto lq:on ctrs:RERed.R.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); apply rtc_refl.

  Lemma AbsCong (a b : PTm) :
    rtc RERed.R a b ->
    rtc RERed.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong (a0 a1 b0 b1 : PTm) :
    rtc RERed.R a0 a1 ->
    rtc RERed.R b0 b1 ->
    rtc RERed.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong (a0 a1 b0 b1 : PTm) :
    rtc RERed.R a0 a1 ->
    rtc RERed.R b0 b1 ->
    rtc RERed.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong p (a0 a1  : PTm) :
    rtc RERed.R a0 a1 ->
    rtc RERed.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma SucCong (a0 a1 : PTm) :
    rtc RERed.R a0 a1 ->
    rtc RERed.R (PSuc a0) (PSuc a1).
  Proof. solve_s. Qed.

  Lemma IndCong P0 P1 (a0 a1 : PTm) b0 b1 c0 c1 :
    rtc RERed.R P0 P1 ->
    rtc RERed.R a0 a1 ->
    rtc RERed.R b0 b1 ->
    rtc RERed.R c0 c1 ->
    rtc RERed.R (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1).
  Proof. solve_s. Qed.

  Lemma BindCong p (A0 A1 : PTm) B0 B1 :
    rtc RERed.R A0 A1 ->
    rtc RERed.R B0 B1 ->
    rtc RERed.R (PBind p A0 B0) (PBind p A1 B1).
  Proof. solve_s. Qed.

  Lemma bind_preservation (a b : PTm) :
    rtc RERed.R a b -> isbind a -> isbind b.
  Proof. induction 1; qauto l:on ctrs:rtc use:RERed.bind_preservation. Qed.

  Lemma univ_preservation (a b : PTm) :
    rtc RERed.R a b -> isuniv a -> isuniv b.
  Proof. induction 1; qauto l:on ctrs:rtc use:RERed.univ_preservation. Qed.

  Lemma nat_preservation (a b : PTm) :
    rtc RERed.R a b -> isnat a -> isnat b.
  Proof. induction 1; qauto l:on ctrs:rtc use:RERed.nat_preservation. Qed.

  Lemma sne_preservation (a b : PTm) :
    rtc RERed.R a b -> SNe a -> SNe b.
  Proof. induction 1; qauto l:on ctrs:rtc use:RERed.sne_preservation. Qed.

  Lemma bind_inv p A B C :
    rtc RERed.R(PBind p A B) C ->
    exists A0 B0, C = PBind p A0 B0 /\ rtc RERed.R A A0 /\ rtc RERed.R B B0.
  Proof.
    move E : (PBind p A B) => u hu.
    move : p A B E.
    elim : u C / hu; sauto lq:on rew:off.
  Qed.

  Lemma univ_inv i C :
    rtc RERed.R (PUniv i) C  ->
    C = PUniv i.
  Proof.
    move E : (PUniv i) => u hu.
    move : i E. elim : u C / hu=>//=.
    hauto lq:on rew:off ctrs:rtc inv:RERed.R.
  Qed.

  Lemma var_inv (i : nat) C :
    rtc RERed.R (VarPTm i) C ->
    C = VarPTm i.
  Proof.
    move E : (VarPTm i) => u hu.
    move : i E. elim : u C /hu; hauto lq:on rew:off inv:RERed.R.
  Qed.

  Lemma hne_app_inv (a0 b0 C : PTm) :
    rtc RERed.R (PApp a0 b0) C ->
    ishne a0 ->
    exists a1 b1, C = PApp a1 b1 /\
               rtc RERed.R a0 a1 /\
               rtc RERed.R b0 b1.
  Proof.
    move E : (PApp a0 b0) => u hu.
    move : a0 b0 E.
    elim : u C / hu.
    - hauto lq:on ctrs:rtc.
    - move => a b c ha0 ha1 iha a0 b0 ?. subst.
      hauto lq:on rew:off ctrs:rtc, RERed.R use:RERed.hne_preservation inv:RERed.R.
  Qed.

  Lemma hne_proj_inv p (a C : PTm) :
    rtc RERed.R (PProj p a) C ->
    ishne a ->
    exists c, C = PProj p c /\ rtc RERed.R a c.
  Proof.
    move E : (PProj p a) => u hu.
    move : p a E.
    elim : u C /hu => //=;
      scrush ctrs:rtc,RERed.R use:RERed.hne_preservation inv:RERed.R.
  Qed.

  Lemma hne_ind_inv P a b c (C : PTm) :
    rtc RERed.R (PInd P a b c) C -> ishne a ->
    exists P0 a0 b0 c0, C = PInd P0 a0 b0 c0 /\
                     rtc RERed.R P P0 /\
                     rtc RERed.R a a0 /\
                     rtc RERed.R b b0 /\
                     rtc RERed.R c c0.
  Proof.
    move E : (PInd P a b c) => u hu.
    move : P a b c E.
    elim  : u C / hu => //=;
      scrush ctrs:rtc,RERed.R use:RERed.hne_preservation inv:RERed.R.
  Qed.

  Lemma substing (a b : PTm) (ρ : nat -> PTm) :
    rtc RERed.R a b -> rtc RERed.R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    induction 1; hauto lq:on ctrs:rtc use:RERed.substing.
  Qed.


  Lemma cong_up (ρ0 ρ1 : nat -> PTm) :
    (forall i, rtc RERed.R (ρ0 i) (ρ1 i)) ->
    (forall i, rtc RERed.R (up_PTm_PTm ρ0 i) (up_PTm_PTm ρ1 i)).
  Proof. move => h [|i]; cycle 1.
         simpl. rewrite /funcomp.
         substify. by apply substing.
         apply rtc_refl.
  Qed.

  Lemma cong_up2 (ρ0 ρ1 : nat -> PTm) :
    (forall i, rtc RERed.R (ρ0 i) (ρ1 i)) ->
    (forall i, rtc RERed.R (up_PTm_PTm (up_PTm_PTm ρ0) i) (up_PTm_PTm (up_PTm_PTm ρ1) i)).
  Proof. hauto l:on use:cong_up. Qed.

  Lemma cong (a : PTm) (ρ0 ρ1 : nat -> PTm) :
    (forall i, rtc RERed.R (ρ0 i) (ρ1 i)) ->
    rtc RERed.R (subst_PTm ρ0 a) (subst_PTm ρ1 a).
  Proof.
    move : ρ0 ρ1. elim : a => /=;
      eauto 20 using AppCong, AbsCong, BindCong, ProjCong, PairCong, cong_up, rtc_refl, IndCong, SucCong, cong_up2.
  Qed.

  Lemma cong' (a b : PTm) (ρ0 ρ1 : nat -> PTm) :
    rtc RERed.R a b ->
    (forall i, rtc RERed.R (ρ0 i) (ρ1 i)) ->
    rtc RERed.R (subst_PTm ρ0 a) (subst_PTm ρ1 b).
  Proof.
    move => h0 h1.
    have : rtc RERed.R (subst_PTm ρ0 a) (subst_PTm ρ1 a) by eauto using cong.
    move => ?. apply : relations.rtc_transitive; eauto.
    hauto l:on use:substing.
  Qed.

  Lemma ToEReds (a b : PTm) :
    nf a ->
    rtc RERed.R a b -> rtc ERed.R a b.
  Proof.
    move => + h.
    induction h; hauto lq:on rew:off ctrs:rtc use:RERed.ToBetaEta, RReds.nf_refl, @rtc_once, ERed.nf_preservation.
  Qed.

  Lemma zero_inv (C : PTm) :
    rtc RERed.R PZero C -> C = PZero.
    move E : PZero => u hu.
    move : E. elim : u C /hu=>//=.
    - hauto lq:on rew:off ctrs:rtc, RERed.R inv:RERed.R, rtc.
  Qed.

  Lemma suc_inv (a : PTm) C :
    rtc RERed.R (PSuc a) C ->
    exists b, rtc RERed.R a b /\ C = PSuc b.
  Proof.
    move E : (PSuc a) => u hu.
    move : a E.
    elim : u C / hu=>//=.
    - hauto l:on.
    - hauto lq:on rew:off ctrs:rtc, RERed.R inv:RERed.R, rtc.
  Qed.

  Lemma nat_inv C :
    rtc RERed.R PNat C ->
    C = PNat.
  Proof.
    move E : PNat => u hu. move : E.
    elim : u C / hu=>//=.
    hauto lq:on rew:off ctrs:rtc, RERed.R inv:RERed.R.
  Qed.

End REReds.

Module LoRed.
  Inductive R : PTm -> PTm ->  Prop :=
  (****************** Beta ***********************)
  | AppAbs a b :
    R (PApp (PAbs a) b)  (subst_PTm (scons b VarPTm) a)

  | ProjPair p a b :
    R (PProj p (PPair a b)) (if p is PL then a else b)

  | IndZero P b c :
      R (PInd P PZero b c) b

  | IndSuc P a b c :
    R (PInd P (PSuc a) b c) (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c)


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
    R (PBind p A B0) (PBind p A B1)
  | IndCong0 P0 P1 a b c :
    ne a ->
    R P0 P1 ->
    R (PInd P0 a b c) (PInd P1 a b c)
  | IndCong1 P a0 a1 b c :
    ~~ ishf a0 ->
    R a0 a1 ->
    R (PInd P a0 b c) (PInd P a1 b c)
  | IndCong2 P a b0 b1 c :
    nf P ->
    ne a ->
    R b0 b1 ->
    R (PInd P a b0 c) (PInd P a b1 c)
  | IndCong3 P a b c0 c1 :
    nf P ->
    ne a ->
    nf b ->
    R c0 c1 ->
    R (PInd P a b c0) (PInd P a b c1)
  | SucCong a0 a1 :
    R a0 a1 ->
    R (PSuc a0) (PSuc a1).

  Lemma hf_preservation (a b : PTm) :
    LoRed.R a b ->
    ishf a ->
    ishf b.
  Proof.
    move => h. elim : a b /h=>//=.
  Qed.

  Lemma ToRRed (a b : PTm) :
    LoRed.R a b ->
    RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:RRed.R. Qed.

  Lemma AppAbs' a (b : PTm) u :
    u = (subst_PTm (scons b VarPTm) a) ->
    R (PApp (PAbs a) b)  u.
  Proof. move => ->. apply AppAbs. Qed.

  Lemma IndSuc' P a b c u :
    u = (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c) ->
    R (@PInd P (PSuc a) b c) u.
  Proof. move => ->. apply IndSuc. Qed.

  Lemma renaming (a b : PTm) (ξ : nat -> nat) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : ξ.
    elim : a b /h.

    move => a b ξ /=.
    apply AppAbs'. by asimpl.
    all : try qauto ctrs:R use:ne_nf_ren, ishf_ren.
    move => * /=; apply IndSuc'. by asimpl.
  Qed.

End LoRed.

Module LoReds.
  Lemma hf_preservation (a b : PTm) :
    rtc LoRed.R a b ->
    ishf a ->
    ishf b.
  Proof.
    induction 1; eauto using LoRed.hf_preservation.
  Qed.

  Lemma hf_ne_imp (a b : PTm) :
    rtc LoRed.R a b ->
    ne b ->
    ~~ ishf a.
  Proof.
    move : hf_preservation. repeat move/[apply].
    case : a; case : b => //=; sfirstorder b:on.
  Qed.

  #[local]Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:LoRed.R, rtc use:hf_ne_imp.

  #[local]Ltac solve_s :=
    repeat (induction 1; last by solve_s_rec); (move => *; apply rtc_refl).

  Lemma AbsCong (a b : PTm) :
    rtc LoRed.R a b ->
    rtc LoRed.R (PAbs a) (PAbs b).
  Proof. solve_s. Qed.

  Lemma AppCong (a0 a1 b0 b1 : PTm) :
    rtc LoRed.R a0 a1 ->
    rtc LoRed.R b0 b1 ->
    ne a1 ->
    rtc LoRed.R (PApp a0 b0) (PApp a1 b1).
  Proof. solve_s. Qed.

  Lemma PairCong (a0 a1 b0 b1 : PTm) :
    rtc LoRed.R a0 a1 ->
    rtc LoRed.R b0 b1 ->
    nf a1 ->
    rtc LoRed.R (PPair a0 b0) (PPair a1 b1).
  Proof. solve_s. Qed.

  Lemma ProjCong p (a0 a1  : PTm) :
    rtc LoRed.R a0 a1 ->
    ne a1 ->
    rtc LoRed.R (PProj p a0) (PProj p a1).
  Proof. solve_s. Qed.

  Lemma BindCong p (A0 A1 : PTm) B0 B1 :
    rtc LoRed.R A0 A1 ->
    rtc LoRed.R B0 B1 ->
    nf A1 ->
    rtc LoRed.R (PBind p A0 B0) (PBind p A1 B1).
  Proof. solve_s. Qed.

  Lemma IndCong P0 P1 (a0 a1 : PTm) b0 b1 c0 c1 :
    rtc LoRed.R a0 a1 ->
    rtc LoRed.R P0 P1 ->
    rtc LoRed.R b0 b1 ->
    rtc LoRed.R c0 c1 ->
    ne a1 ->
    nf P1 ->
    nf b1 ->
    rtc LoRed.R (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1).
  Proof. solve_s. Qed.

  Lemma SucCong (a0 a1 : PTm) :
    rtc LoRed.R a0 a1 ->
    rtc LoRed.R (PSuc a0) (PSuc a1).
  Proof. solve_s. Qed.

  Local Ltac triv := simpl in *; sfirstorder b:on.

  Lemma FromSN_mutual :
    (forall (a : PTm) (_ : SNe a), exists v, rtc LoRed.R a v /\ ne v) /\
    (forall (a : PTm) (_ : SN a), exists v, rtc LoRed.R a v /\ nf v) /\
    (forall (a b : PTm) (_ : TRedSN a b), LoRed.R a b).
  Proof.
    apply sn_mutual.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on rew:off use:LoReds.AppCong solve+:triv.
    - hauto l:on use:LoReds.ProjCong solve+:triv.
    - hauto lq:on use:LoReds.IndCong solve+:triv.
    - hauto q:on use:LoReds.PairCong solve+:triv.
    - hauto q:on use:LoReds.AbsCong solve+:triv.
    - sfirstorder use:ne_nf.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on use:LoReds.BindCong solve+:triv.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on ctrs:rtc.
    - hauto l:on use:SucCong.
    - qauto ctrs:LoRed.R.
    - move => a0 a1 b hb ihb h.
      have : ~~ ishf a0 by inversion h.
      hauto lq:on ctrs:LoRed.R.
    - qauto ctrs:LoRed.R.
    - qauto ctrs:LoRed.R.
    - move => p a b h.
      have : ~~ ishf a by inversion h.
      hauto lq:on ctrs:LoRed.R.
    - sfirstorder.
    - sfirstorder.
    - move => P a0 a1 b c hP ihP hb ihb hc ihc hr.
      have : ~~ ishf a0 by inversion hr.
      hauto q:on ctrs:LoRed.R.
  Qed.

  Lemma FromSN : forall a, SN a -> exists v, rtc LoRed.R a v /\ nf v.
  Proof. firstorder using FromSN_mutual. Qed.

  Lemma ToRReds : forall (a b : PTm), rtc LoRed.R a b -> rtc RRed.R a b.
  Proof. induction 1; hauto lq:on ctrs:rtc use:LoRed.ToRRed. Qed.
End LoReds.


Fixpoint size_PTm (a : PTm) :=
  match a with
  | VarPTm _ => 1
  | PAbs a => 3 + size_PTm a
  | PApp a b => 1 + Nat.add (size_PTm a) (size_PTm b)
  | PProj p a => 1 + size_PTm a
  | PPair a b => 3 + Nat.add (size_PTm a) (size_PTm b)
  | PUniv _ => 3
  | PBind p A B => 3 + Nat.add (size_PTm A) (size_PTm B)
  | PInd P a b c => 3 + size_PTm P + size_PTm a + size_PTm b + size_PTm c
  | PNat => 3
  | PSuc a => 3 + size_PTm a
  | PZero => 3
  end.

Lemma size_PTm_ren (ξ : nat -> nat) a : size_PTm (ren_PTm ξ a) = size_PTm a.
Proof.
  move : ξ. elim : a => //=; scongruence.
Qed.

#[export]Hint Rewrite size_PTm_ren : sizetm.

Lemma ered_size (a b : PTm) :
  ERed.R a b ->
  size_PTm b < size_PTm a.
Proof.
  move => h. elim : a b /h; try hauto l:on rew:db:sizetm solve+:lia.
Qed.

Lemma ered_sn (a : PTm) : sn ERed.R a.
Proof.
  hauto lq:on rew:off use:size_PTm_ren, ered_size,
          well_founded_lt_compat unfold:well_founded.
Qed.

Lemma ered_local_confluence (a b c : PTm) :
  ERed.R a b ->
  ERed.R a c ->
  exists d, rtc ERed.R b d  /\ rtc ERed.R c d.
Proof.
  move => h. move : c.
  elim : a b / h.
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
  - move => P0 P1 a b c hP ihP u.
    elim /ERed.inv => //=_.
    + move => P2 P3 a0 b0 c0 hP' [*]. subst.
      move : ihP hP' => /[apply]. move => [P4][hP0]hP1.
      eauto using EReds.IndCong, rtc_refl.
    + move => P2 a0 a1 b0 c0  + [*]. subst.
      eauto 20 using rtc_refl, EReds.IndCong, rtc_l.
    + move => P2 a0 b0 b1 c0 hb [*] {ihP}. subst.
      eauto 20 using rtc_refl, EReds.IndCong, rtc_l.
    + move => P2 a0 b0 c0 c1 h [*] {ihP}. subst.
      eauto 20 using rtc_refl, EReds.IndCong, rtc_l.
  - move => P a0 a1 b c ha iha u.
    elim /ERed.inv => //=_;
                     try solve [move => P0 P1 a2 b0 c0 hP[*]; subst;
      eauto 20 using rtc_refl, EReds.IndCong, rtc_l].
    move => P0 P1 a2 b0 c0 hP[*]. subst.
    move : iha hP => /[apply].
    move => [? [*]].
    eauto 20 using rtc_refl, EReds.IndCong, rtc_l.
  - move => P a b0 b1 c hb ihb u.
    elim /ERed.inv => //=_;
      try solve [
          move => P0 P1 a0 b2 c0 hP [*]; subst;
          eauto 20 using rtc_refl, EReds.IndCong, rtc_l].
    move => P0 a0 b2 b3 c0 h [*]. subst.
    move : ihb h => /[apply]. move => [b2 [*]].
    eauto 20 using rtc_refl, EReds.IndCong, rtc_l.
  - move => P a b c0 c1 hc ihc u.
    elim /ERed.inv => //=_;
      try solve [
          move => P0 P1 a0 b0 c hP [*]; subst;
          eauto 20 using rtc_refl, EReds.IndCong, rtc_l].
    move => P0 a0 b0 c2 c3 h [*]. subst.
    move : ihc h => /[apply]. move => [c2][*].
    eauto 20 using rtc_refl, EReds.IndCong, rtc_l.
  - qauto l:on inv:ERed.R ctrs:rtc use:EReds.SucCong.
Qed.

Lemma ered_confluence (a b c : PTm) :
  rtc ERed.R a b ->
  rtc ERed.R a c ->
  exists d, rtc ERed.R b d  /\ rtc ERed.R c d.
Proof.
  sfirstorder use:relations.locally_confluent_confluent, ered_sn, ered_local_confluence.
Qed.

Lemma red_confluence (a b c : PTm) :
  rtc RRed.R a b ->
  rtc RRed.R a c ->
  exists d, rtc RRed.R b d  /\ rtc RRed.R c d.
  suff : rtc RPar.R a b -> rtc RPar.R a c -> exists d : PTm, rtc RPar.R b d /\ rtc RPar.R c d
             by hauto lq:on use:RReds.RParIff.
  apply relations.diamond_confluent.
  rewrite /relations.diamond.
  eauto using RPar.diamond.
Qed.

Lemma red_uniquenf (a b c : PTm) :
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
  Lemma R_nonelim_nf (a b : PTm) :
    rtc NeEPar.R_nonelim a b ->
    nf b ->
    nf a.
  Proof. induction 1; sfirstorder use:NeEPar.R_elim_nf. Qed.

  Lemma ToEReds : (forall (a b : PTm), rtc NeEPar.R_nonelim a b -> rtc ERed.R a b).
  Proof.
    induction 1; hauto l:on use:NeEPar.ToEPar, EReds.FromEPar, @relations.rtc_transitive.
  Qed.
End NeEPars.


Lemma rered_standardization (a c : PTm) :
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

Lemma rered_confluence (a b c : PTm) :
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

(* Beta joinability *)
Module BJoin.
  Definition R (a b : PTm) := exists c, rtc RRed.R a c /\ rtc RRed.R b c.
  Lemma refl (a : PTm) : R a a.
  Proof. sfirstorder use:@rtc_refl unfold:R. Qed.

  Lemma symmetric (a b : PTm) : R a b -> R b a.
  Proof. sfirstorder unfold:R. Qed.

  Lemma transitive (a b c : PTm) : R a b -> R b c -> R a c.
  Proof.
    rewrite /R.
    move => [ab [ha +]] [bc [+ hc]].
    move : red_confluence; repeat move/[apply].
    move => [v [h0 h1]].
    exists v. sfirstorder use:@relations.rtc_transitive.
  Qed.

  (* Lemma AbsCong n (a b : PTm (S n)) : *)
  (*   R a b -> *)
  (*   R (PAbs a) (PAbs b). *)
  (* Proof. hauto lq:on use:RReds.AbsCong unfold:R. Qed. *)

  (* Lemma AppCong n (a0 a1 b0 b1 : PTm) : *)
  (*   R a0 a1 -> *)
  (*   R b0 b1 -> *)
  (*   R (PApp a0 b0) (PApp a1 b1). *)
  (* Proof. hauto lq:on use:RReds.AppCong unfold:R. Qed. *)
End BJoin.

Module DJoin.
  Definition R (a b : PTm) := exists c, rtc RERed.R a c /\ rtc RERed.R b c.

  Lemma refl (a : PTm) : R a a.
  Proof. sfirstorder use:@rtc_refl unfold:R. Qed.

  Lemma FromEJoin (a b : PTm) : EJoin.R a b -> DJoin.R a b.
  Proof. hauto q:on use:REReds.FromEReds. Qed.

  Lemma ToEJoin (a b : PTm) : nf a -> nf b -> DJoin.R a b -> EJoin.R a b.
  Proof. hauto q:on use:REReds.ToEReds. Qed.

  Lemma symmetric (a b : PTm) : R a b -> R b a.
  Proof. sfirstorder unfold:R. Qed.

  Lemma transitive (a b c : PTm) : SN b -> R a b -> R b c -> R a c.
  Proof.
    rewrite /R.
    move => + [ab [ha +]] [bc [+ hc]].
    move : rered_confluence; repeat move/[apply].
    move => [v [h0 h1]].
    exists v. sfirstorder use:@relations.rtc_transitive.
  Qed.

  Lemma AbsCong (a b : PTm) :
    R a b ->
    R (PAbs a) (PAbs b).
  Proof. hauto lq:on use:REReds.AbsCong unfold:R. Qed.

  Lemma AppCong (a0 a1 b0 b1 : PTm) :
    R a0 a1 ->
    R b0 b1 ->
    R (PApp a0 b0) (PApp a1 b1).
  Proof. hauto lq:on use:REReds.AppCong unfold:R. Qed.

  Lemma PairCong (a0 a1 b0 b1 : PTm) :
    R a0 a1 ->
    R b0 b1 ->
    R (PPair a0 b0) (PPair a1 b1).
  Proof. hauto q:on use:REReds.PairCong. Qed.

  Lemma ProjCong p (a0 a1  : PTm) :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1).
  Proof. hauto q:on use:REReds.ProjCong. Qed.

  Lemma BindCong p (A0 A1 : PTm) B0 B1 :
    R A0 A1 ->
    R B0 B1 ->
    R (PBind p A0 B0) (PBind p A1 B1).
  Proof. hauto q:on use:REReds.BindCong. Qed.

  Lemma IndCong P0 P1 (a0 a1 : PTm) b0 b1 c0 c1 :
    R P0 P1 ->
    R a0 a1 ->
    R b0 b1 ->
    R c0 c1 ->
    R (PInd P0 a0 b0 c0) (PInd P1 a1 b1 c1).
  Proof. hauto q:on use:REReds.IndCong. Qed.

  Lemma SucCong (a0 a1 : PTm) :
    R a0 a1 ->
    R (PSuc a0) (PSuc a1).
  Proof. qauto l:on use:REReds.SucCong. Qed.

  Lemma FromRedSNs (a b : PTm) :
    rtc TRedSN a b ->
    R a b.
  Proof.
    move /RReds.FromRedSNs /REReds.FromRReds.
    sfirstorder use:@rtc_refl unfold:R.
  Qed.

  Lemma sne_nat_noconf (a b : PTm) :
    R a b -> SNe a -> isnat b -> False.
  Proof.
    move => [c [? ?]] *.
    have : SNe c /\ isnat c by sfirstorder use:REReds.sne_preservation, REReds.nat_preservation.
    qauto l:on inv:SNe.
  Qed.

  Lemma sne_bind_noconf (a b : PTm) :
    R a b -> SNe a -> isbind b -> False.
  Proof.
    move => [c [? ?]] *.
    have : SNe c /\ isbind c by sfirstorder use:REReds.sne_preservation, REReds.bind_preservation.
    qauto l:on inv:SNe.
  Qed.

  Lemma sne_univ_noconf (a b : PTm) :
    R a b -> SNe a -> isuniv b -> False.
  Proof.
    hauto q:on use:REReds.sne_preservation,
          REReds.univ_preservation inv:SNe.
  Qed.

  Lemma bind_univ_noconf (a b : PTm) :
    R a b -> isbind a -> isuniv b -> False.
  Proof.
    move => [c [h0 h1]] h2 h3.
    have {h0 h1 h2 h3} : isbind c /\ isuniv c by
      hauto l:on use:REReds.bind_preservation,
          REReds.univ_preservation.
    case : c => //=; sfirstorder b:on.
  Qed.

  Lemma hne_univ_noconf (a b : PTm) :
    R a b -> ishne a -> isuniv b -> False.
  Proof.
    move => [c [h0 h1]] h2 h3.
    have {h0 h1 h2 h3} : ishne c /\ isuniv c by
      hauto l:on use:REReds.hne_preservation,
          REReds.univ_preservation.
    move => [].
    case : c => //=.
  Qed.

  Lemma hne_bind_noconf (a b : PTm) :
    R a b -> ishne a -> isbind b -> False.
  Proof.
    move => [c [h0 h1]] h2 h3.
    have {h0 h1 h2 h3} : ishne c /\ isbind c by
      hauto l:on use:REReds.hne_preservation,
          REReds.bind_preservation.
    move => [].
    case : c => //=.
  Qed.

  Lemma hne_nat_noconf (a b : PTm) :
    R a b -> ishne a -> isnat b -> False.
  Proof.
    move => [c [h0 h1]] h2 h3.
    have : ishne c /\ isnat c by sfirstorder use:REReds.hne_preservation, REReds.nat_preservation.
    clear. case : c => //=; sfirstorder b:on.
  Qed.

  Lemma bind_inj p0 p1 (A0 A1 : PTm) B0 B1 :
    DJoin.R (PBind p0 A0 B0) (PBind p1 A1 B1) ->
    p0 = p1 /\ DJoin.R A0 A1 /\ DJoin.R B0 B1.
  Proof.
    rewrite /R.
    hauto lq:on rew:off use:REReds.bind_inv.
  Qed.

  Lemma var_inj (i j : nat) :
    R (VarPTm i) (VarPTm j) -> i = j.
  Proof. sauto lq:on rew:off use:REReds.var_inv unfold:R. Qed.

  Lemma univ_inj i j :
    @R (PUniv i) (PUniv j)  -> i = j.
  Proof.
    sauto lq:on rew:off use:REReds.univ_inv.
  Qed.

  Lemma suc_inj  (A0 A1 : PTm)  :
    R (PSuc A0) (PSuc A1) ->
    R A0 A1.
  Proof.
    hauto lq:on rew:off use:REReds.suc_inv.
  Qed.

  Lemma hne_app_inj (a0 b0 a1 b1 : PTm) :
    R (PApp a0 b0) (PApp a1 b1) ->
    ishne a0 ->
    ishne a1 ->
    R a0 a1 /\ R b0 b1.
  Proof.
    hauto lq:on use:REReds.hne_app_inv.
  Qed.

  Lemma hne_proj_inj p0 p1 (a0 a1 : PTm) :
    R (PProj p0 a0) (PProj p1 a1) ->
    ishne a0 ->
    ishne a1 ->
    p0 = p1 /\ R a0 a1.
  Proof.
    sauto lq:on use:REReds.hne_proj_inv.
  Qed.

  Lemma FromRRed0 (a b : PTm) :
    RRed.R a b -> R a b.
  Proof.
    hauto lq:on ctrs:rtc use:RERed.FromBeta unfold:R.
  Qed.

  Lemma FromRRed1 (a b : PTm) :
    RRed.R b a -> R a b.
  Proof.
    hauto lq:on ctrs:rtc use:RERed.FromBeta unfold:R.
  Qed.

  Lemma FromRReds (a b : PTm) :
    rtc RRed.R b a -> R a b.
  Proof.
    hauto lq:on ctrs:rtc use:REReds.FromRReds unfold:R.
  Qed.

  Lemma FromBJoin (a b : PTm) :
    BJoin.R a b -> R a b.
  Proof.
    hauto lq:on ctrs:rtc use:REReds.FromRReds unfold:R, BJoin.R.
  Qed.

  Lemma substing (a b : PTm) (ρ : nat -> PTm) :
    R a b -> R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    hauto lq:on rew:off ctrs:rtc unfold:R use:REReds.substing.
  Qed.

  Lemma renaming (a b : PTm) (ρ : nat -> nat) :
    R a b -> R (ren_PTm ρ a) (ren_PTm ρ b).
  Proof. substify. apply substing. Qed.

  Lemma weakening (a b : PTm)  :
    R a b -> R (ren_PTm shift a) (ren_PTm shift b).
  Proof. apply renaming. Qed.

  Lemma cong (a : PTm) c d (ρ : nat -> PTm) :
    R c d -> R (subst_PTm (scons c ρ) a) (subst_PTm (scons d ρ) a).
  Proof.
    rewrite /R. move => [cd [h0 h1]].
    exists (subst_PTm (scons cd ρ) a).
    hauto q:on ctrs:rtc inv:nat use:REReds.cong.
  Qed.

  Lemma cong' (a b : PTm) c d (ρ : nat -> PTm) :
    R a b ->
    R c d -> R (subst_PTm (scons c ρ) a) (subst_PTm (scons d ρ) b).
  Proof.
    rewrite /R. move => [ab [h2 h3]] [cd [h0 h1]].
    exists (subst_PTm (scons cd ρ) ab).
    hauto q:on ctrs:rtc inv:nat use:REReds.cong'.
  Qed.

  Lemma pair_inj (a0 a1 b0 b1 : PTm) :
    SN (PPair a0 b0) ->
    SN (PPair a1 b1) ->
    R (PPair a0 b0) (PPair a1 b1) ->
    R a0 a1 /\ R b0 b1.
  Proof.
    move => sn0 sn1.
    have [? [? [? ?]]] : SN a0 /\ SN b0 /\ SN a1 /\ SN b1 by sfirstorder use:SN_NoForbid.P_PairInv.
    have ? : SN (PProj PL (PPair a0 b0)) by hauto lq:on db:sn.
    have ? : SN (PProj PR (PPair a0 b0)) by hauto lq:on db:sn.
    have ? : SN (PProj PL (PPair a1 b1)) by hauto lq:on db:sn.
    have ? : SN (PProj PR (PPair a1 b1)) by hauto lq:on db:sn.
    have h0L : RRed.R (PProj PL (PPair a0 b0)) a0 by eauto with red.
    have h0R : RRed.R (PProj PR (PPair a0 b0)) b0 by eauto with red.
    have h1L : RRed.R (PProj PL (PPair a1 b1)) a1 by eauto with red.
    have h1R : RRed.R (PProj PR (PPair a1 b1)) b1 by eauto with red.
    move => h2.
    move /ProjCong in h2.
    have h2L := h2 PL.
    have {h2}h2R := h2 PR.
    move /FromRRed1 in h0L.
    move /FromRRed0 in h1L.
    move /FromRRed1 in h0R.
    move /FromRRed0 in h1R.
    split; eauto using transitive.
  Qed.

  Lemma ejoin_pair_inj (a0 a1 b0 b1 : PTm) :
    nf a0 -> nf b0 -> nf a1 -> nf b1 ->
    EJoin.R (PPair a0 b0) (PPair a1 b1) ->
    EJoin.R a0 a1 /\ EJoin.R b0 b1.
  Proof.
    move => h0 h1 h2 h3 /FromEJoin.
    have [? ?] : SN (PPair a0 b0) /\ SN (PPair a1 b1) by sauto lqb:on rew:off use:ne_nf_embed.
    move => ?.
    have : R a0 a1 /\ R b0 b1 by hauto l:on use:pair_inj.
    hauto l:on use:ToEJoin.
  Qed.

  Lemma abs_inj (a0 a1 : PTm) :
    SN a0 -> SN a1 ->
    R (PAbs a0) (PAbs a1) ->
    R a0 a1.
  Proof.
    move => sn0 sn1.
    move /weakening => /=.
    move /AppCong. move /(_ (VarPTm var_zero) (VarPTm var_zero)).
    move => /(_ ltac:(sfirstorder use:refl)).
    move => h.
    have /FromRRed1 h0 : RRed.R (PApp (PAbs (ren_PTm (upRen_PTm_PTm shift) a0)) (VarPTm var_zero)) a0. apply RRed.AppAbs'; asimpl. by rewrite subst_scons_id.
    have /FromRRed0 h1 : RRed.R (PApp (PAbs (ren_PTm (upRen_PTm_PTm shift) a1)) (VarPTm var_zero)) a1 by
      apply RRed.AppAbs'; eauto; by asimpl; rewrite ?subst_scons_id.
    have sn0' := sn0.
    have sn1' := sn1.
    eapply sn_renaming with (ξ := (upRen_PTm_PTm shift)) in sn0.
    eapply sn_renaming with (ξ := (upRen_PTm_PTm shift)) in sn1.
    apply : transitive; try apply h0.
    apply : N_Exp. apply N_β. sauto.
    asimpl. by rewrite subst_scons_id.
    apply : transitive; try apply h1.
    apply : N_Exp. apply N_β. sauto.
    by asimpl; rewrite subst_scons_id.
    eauto.
  Qed.

  Lemma ejoin_abs_inj (a0 a1 : PTm) :
    nf a0 -> nf a1 ->
    EJoin.R (PAbs a0) (PAbs a1) ->
    EJoin.R a0 a1.
  Proof.
    move => h0 h1.
    have [? [? [? ?]]] : SN a0 /\ SN a1 /\ SN (PAbs a0) /\ SN (PAbs a1) by sauto lqb:on rew:off use:ne_nf_embed.
    move /FromEJoin.
    move /abs_inj.
    hauto l:on use:ToEJoin.
  Qed.

  Lemma standardization (a b : PTm) :
    SN a -> SN b -> R a b ->
    exists va vb, rtc RRed.R a va /\ rtc RRed.R b vb /\ nf va /\ nf vb /\ EJoin.R va vb.
  Proof.
    move => h0 h1 [ab [hv0 hv1]].
    have hv : SN ab by sfirstorder use:REReds.sn_preservation.
    have : exists v, rtc RRed.R ab v  /\ nf v by sfirstorder use:LoReds.FromSN, LoReds.ToRReds.
    move => [v [hv2 hv3]].
    have : rtc RERed.R a v by hauto q:on use:@relations.rtc_transitive, REReds.FromRReds.
    have : rtc RERed.R b v by hauto q:on use:@relations.rtc_transitive, REReds.FromRReds.
    move : h0 h1 hv3. clear.
    move => h0 h1 hv hbv hav.
    move : rered_standardization (h0) hav. repeat move/[apply].
    move => [a1 [ha0 ha1]].
    move : rered_standardization (h1) hbv. repeat move/[apply].
    move => [b1 [hb0 hb1]].
    have [*] : nf a1 /\ nf b1 by sfirstorder use:NeEPars.R_nonelim_nf.
    hauto q:on use:NeEPars.ToEReds unfold:EJoin.R.
  Qed.

  Lemma standardization_lo (a b : PTm) :
    SN a -> SN b -> R a b ->
    exists va vb, rtc LoRed.R a va /\ rtc LoRed.R b vb /\ nf va /\ nf vb /\ EJoin.R va vb.
  Proof.
    move => /[dup] sna + /[dup] snb.
    move : standardization; repeat move/[apply].
    move => [va][vb][hva][hvb][nfva][nfvb]hj.
    move /LoReds.FromSN : sna => [va' [hva' hva'0]].
    move /LoReds.FromSN : snb => [vb' [hvb' hvb'0]].
    exists va', vb'.
    repeat split => //=.
    have : va = va' /\ vb = vb' by sfirstorder use:red_uniquenf, LoReds.ToRReds.
    case; congruence.
  Qed.
End DJoin.

Module Sub1.
  Inductive R : PTm -> PTm -> Prop :=
  | Refl a :
    R a a
  | Univ i j :
    i <= j ->
    R (PUniv i) (PUniv j)
  | PiCong A0 A1 B0 B1 :
    R A1 A0 ->
    R B0 B1 ->
    R (PBind PPi A0 B0) (PBind PPi A1 B1)
  | SigCong A0 A1 B0 B1 :
    R A0 A1 ->
    R B0 B1 ->
    R (PBind PSig A0 B0) (PBind PSig A1 B1).

  Lemma transitive0 (A B C : PTm) :
    R A B -> (R B C -> R A C) /\ (R C A -> R C B).
  Proof.
    move => h. move : C.
    elim : A B /h; hauto lq:on ctrs:R inv:R solve+:lia.
  Qed.

  Lemma transitive (A B C : PTm) :
    R A B -> R B C -> R A C.
  Proof. hauto q:on use:transitive0. Qed.

  Lemma refl (A : PTm) : R A A.
  Proof. sfirstorder. Qed.

  Lemma commutativity0 (A B C : PTm) :
    R A B ->
    (RERed.R A C ->
    exists D, RERed.R B D /\ R C D) /\
    (RERed.R B C ->
    exists D, RERed.R A D /\ R D C).
  Proof.
    move => h. move : C.
    elim : A B / h; hauto lq:on ctrs:RERed.R, R inv:RERed.R.
  Qed.

  Lemma commutativity_Ls (A B C : PTm) :
    R A B ->
    rtc RERed.R A C ->
    exists D, rtc RERed.R B D /\ R C D.
  Proof.
    move => + h. move : B.
    induction h; ecrush use:commutativity0.
  Qed.

  Lemma commutativity_Rs (A B C : PTm) :
    R A B ->
    rtc RERed.R B C ->
    exists D, rtc RERed.R A D /\ R D C.
  Proof.
    move => + h. move : A. induction h; ecrush use:commutativity0.
  Qed.

  Lemma sn_preservation  :
  (forall (a : PTm) (s : SNe a), forall b, R a b \/ R b a -> a = b) /\
  (forall (a : PTm) (s : SN a), forall b, R a b \/ R b a -> SN b) /\
  (forall (a b : PTm) (_ : TRedSN a b), forall c, R a c \/ R c a -> a = c).
  Proof.
    apply sn_mutual; hauto lq:on inv:R ctrs:SN.
  Qed.

  Lemma bind_preservation (a b : PTm) :
    R a b -> isbind a = isbind b.
  Proof. hauto q:on inv:R. Qed.

  Lemma univ_preservation (a b : PTm) :
    R a b -> isuniv a = isuniv b.
  Proof. hauto q:on inv:R. Qed.

  Lemma sne_preservation (a b : PTm) :
    R a b -> SNe a <-> SNe b.
  Proof. hfcrush use:sn_preservation. Qed.

  Lemma renaming (a b : PTm) (ξ : nat -> nat) :
    R a b -> R (ren_PTm ξ a) (ren_PTm ξ b).
  Proof.
    move => h. move : ξ.
    elim : a b /h; hauto lq:on ctrs:R.
  Qed.

  Lemma substing (a b : PTm) (ρ : nat -> PTm) :
    R a b -> R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof. move => h. move : ρ. elim : a b /h; hauto lq:on ctrs:R. Qed.

  Lemma hne_refl (a b : PTm) :
    ishne a \/ ishne b -> R a b -> a = b.
  Proof. hauto q:on inv:R. Qed.

End Sub1.

Module ESub.
  Definition R (a b : PTm) := exists c0 c1, rtc ERed.R a c0 /\ rtc ERed.R b c1 /\ Sub1.R c0 c1.

  Lemma pi_inj (A0 A1 : PTm) B0 B1 :
    R (PBind PPi A0 B0) (PBind PPi A1 B1) ->
    R A1 A0 /\ R B0 B1.
  Proof.
    move => [u0 [u1 [h0 [h1 h2]]]].
    move /EReds.bind_inv : h0 => [A2][B2][?][h3]h4. subst.
    move /EReds.bind_inv : h1 => [A3][B3][?][h5]h6. subst.
    sauto lq:on rew:off inv:Sub1.R.
  Qed.

  Lemma sig_inj (A0 A1 : PTm) B0 B1 :
    R (PBind PSig A0 B0) (PBind PSig A1 B1) ->
    R A0 A1 /\ R B0 B1.
  Proof.
    move => [u0 [u1 [h0 [h1 h2]]]].
    move /EReds.bind_inv : h0 => [A2][B2][?][h3]h4. subst.
    move /EReds.bind_inv : h1 => [A3][B3][?][h5]h6. subst.
    sauto lq:on rew:off inv:Sub1.R.
  Qed.

  Lemma suc_inj (a b : PTm) :
    R (PSuc a) (PSuc b) ->
    R a b.
  Proof.
    sauto lq:on use:EReds.suc_inv inv:Sub1.R.
  Qed.

End ESub.

Module Sub.
  Definition R (a b : PTm) := exists c d, rtc RERed.R a c /\ rtc RERed.R b d /\ Sub1.R c d.

  Lemma refl (a : PTm) : R a a.
  Proof. sfirstorder use:@rtc_refl unfold:R. Qed.

  Lemma ToJoin (a b : PTm) :
    ishne a \/ ishne b ->
    R a b ->
    DJoin.R a b.
  Proof.
    move => h [c][d][h0][h1]h2.
    have : ishne c \/ ishne d by hauto q:on use:REReds.hne_preservation.
    hauto lq:on rew:off use:Sub1.hne_refl.
  Qed.

  Lemma transitive (a b c : PTm) : SN b -> R a b -> R b c -> R a c.
  Proof.
    rewrite /R.
    move => h  [a0][b0][ha][hb]ha0b0 [b1][c0][hb'][hc]hb1c0.
    move : hb hb'.
    move : rered_confluence h. repeat move/[apply].
    move => [b'][hb0]hb1.
    have [a' ?] : exists a', rtc RERed.R a0 a' /\ Sub1.R a' b' by hauto l:on use:Sub1.commutativity_Rs.
    have [c' ?] : exists a', rtc RERed.R c0 a' /\ Sub1.R b' a' by hauto l:on use:Sub1.commutativity_Ls.
    exists a',c'; hauto l:on use:Sub1.transitive, @relations.rtc_transitive.
  Qed.

  Lemma FromJoin (a b : PTm) : DJoin.R a b -> R a b.
  Proof. sfirstorder. Qed.

  Lemma PiCong (A0 A1 : PTm) B0 B1 :
    R A1 A0 ->
    R B0 B1 ->
    R (PBind PPi A0 B0) (PBind PPi A1 B1).
  Proof.
    rewrite /R.
    move => [A][A'][h0][h1]h2.
    move => [B][B'][h3][h4]h5.
    exists (PBind PPi A' B), (PBind PPi A B').
    repeat split; eauto using REReds.BindCong, Sub1.PiCong.
  Qed.

  Lemma SigCong (A0 A1 : PTm) B0 B1 :
    R A0 A1 ->
    R B0 B1 ->
    R (PBind PSig A0 B0) (PBind PSig A1 B1).
  Proof.
    rewrite /R.
    move => [A][A'][h0][h1]h2.
    move => [B][B'][h3][h4]h5.
    exists (PBind PSig A B), (PBind PSig A' B').
    repeat split; eauto using REReds.BindCong, Sub1.SigCong.
  Qed.

  Lemma UnivCong i j :
    i <= j ->
    @R (PUniv i) (PUniv j).
  Proof. hauto lq:on ctrs:Sub1.R, rtc. Qed.

  Lemma sne_nat_noconf (a b : PTm) :
    R a b -> SNe a -> isnat b -> False.
  Proof.
    move => [c [d [h0 [h1 h2]]]] *.
    have : SNe c /\ isnat d by sfirstorder use:REReds.sne_preservation, REReds.nat_preservation, Sub1.sne_preservation.
    move : h2. clear. hauto q:on inv:Sub1.R, SNe.
  Qed.

  Lemma nat_sne_noconf (a b : PTm) :
    R a b -> isnat a -> SNe b -> False.
  Proof.
    move => [c [d [h0 [h1 h2]]]] *.
    have : SNe d /\ isnat c by sfirstorder use:REReds.sne_preservation, REReds.nat_preservation.
    move : h2. clear. hauto q:on inv:Sub1.R, SNe.
  Qed.

  Lemma sne_bind_noconf (a b : PTm) :
    R a b -> SNe a -> isbind b -> False.
  Proof.
    rewrite /R.
    move => [c[d] [? []]] *.
    have : SNe c /\ isbind c by
      hauto l:on use:REReds.sne_preservation, REReds.bind_preservation, Sub1.sne_preservation, Sub1.bind_preservation.
    qauto l:on inv:SNe.
  Qed.

  Lemma hne_bind_noconf (a b : PTm) :
    R a b -> ishne a -> isbind b -> False.
  Proof.
    rewrite /R.
    move => [c[d] [? []]] h0 h1 h2 h3.
    have : ishne c by eauto using REReds.hne_preservation.
    have : isbind d by eauto using REReds.bind_preservation.
    move : h1. clear. inversion 1; subst => //=.
    clear. case : d => //=.
  Qed.

  Lemma bind_sne_noconf (a b : PTm) :
    R a b -> SNe b -> isbind a -> False.
  Proof.
    rewrite /R.
    move => [c[d] [? []]] *.
    have : SNe c /\ isbind c by
      hauto l:on use:REReds.sne_preservation, REReds.bind_preservation, Sub1.sne_preservation, Sub1.bind_preservation.
    qauto l:on inv:SNe.
  Qed.

  Lemma sne_univ_noconf (a b : PTm) :
    R a b -> SNe a -> isuniv b -> False.
  Proof.
    hauto l:on use:REReds.sne_preservation,
          REReds.univ_preservation, Sub1.sne_preservation, Sub1.univ_preservation inv:SNe.
  Qed.

  Lemma univ_sne_noconf (a b : PTm) :
    R a b -> SNe b -> isuniv a -> False.
  Proof.
    move => [c[d] [? []]] *.
    have ? : SNe d by eauto using REReds.sne_preservation.
    have : SNe c by sfirstorder use:Sub1.sne_preservation.
    have : isuniv c by sfirstorder use:REReds.univ_preservation.
    clear. case : c => //=. inversion 2.
  Qed.

  Lemma univ_nat_noconf (a b : PTm)  :
    R a b -> isuniv b -> isnat a -> False.
  Proof.
    move => [c[d] [? []]] h0 h1 h2 h3.
    have : isuniv d by eauto using REReds.univ_preservation.
    have : isnat c by sfirstorder use:REReds.nat_preservation.
    inversion h1; subst => //=.
    clear. case : d => //=.
  Qed.

  Lemma nat_univ_noconf (a b : PTm)  :
    R a b -> isnat b -> isuniv a -> False.
  Proof.
    move => [c[d] [? []]] h0 h1 h2 h3.
    have : isuniv c by eauto using REReds.univ_preservation.
    have : isnat d by sfirstorder use:REReds.nat_preservation.
    inversion h1; subst => //=.
    clear. case : d => //=.
  Qed.

  Lemma bind_nat_noconf (a b : PTm)  :
    R a b -> isbind b -> isnat a -> False.
  Proof.
    move => [c[d] [? []]] h0 h1 h2 h3.
    have : isbind d by eauto using REReds.bind_preservation.
    have : isnat c by sfirstorder use:REReds.nat_preservation.
    move : h1. clear.
    inversion 1; subst => //=.
    case : d h1 => //=.
  Qed.

  Lemma nat_bind_noconf (a b : PTm)  :
    R a b -> isnat b -> isbind a -> False.
  Proof.
    move => [c[d] [? []]] h0 h1 h2 h3.
    have : isbind c by eauto using REReds.bind_preservation.
    have : isnat d by sfirstorder use:REReds.nat_preservation.
    move : h1. clear.
    inversion 1; subst => //=.
    case : d h1 => //=.
  Qed.

  Lemma bind_univ_noconf (a b : PTm) :
    R a b -> isbind a -> isuniv b -> False.
  Proof.
    move => [c[d] [h0 [h1 h1']]] h2 h3.
    have : isbind c /\ isuniv c by
      hauto l:on use:REReds.bind_preservation,
            REReds.univ_preservation, Sub1.bind_preservation, Sub1.univ_preservation.
    move : h2 h3. clear.
    case : c => //=; sfirstorder b:on.
  Qed.

  Lemma univ_bind_noconf (a b : PTm) :
    R a b -> isbind b -> isuniv a -> False.
  Proof.
    move => [c[d] [h0 [h1 h1']]] h2 h3.
    have : isbind c /\ isuniv c by
      hauto l:on use:REReds.bind_preservation,
            REReds.univ_preservation, Sub1.bind_preservation, Sub1.univ_preservation.
    move : h2 h3. clear.
    case : c => //=; sfirstorder b:on.
  Qed.

  Lemma bind_inj p0 p1 (A0 A1 : PTm) B0 B1 :
    R (PBind p0 A0 B0) (PBind p1 A1 B1) ->
    p0 = p1 /\ (if p0 is PPi then R A1 A0 else R A0 A1) /\ R B0 B1.
  Proof.
    rewrite /R.
    move => [u][v][h0][h1]h.
    move /REReds.bind_inv : h0 => [A2][B2][?][h00]h01. subst.
    move /REReds.bind_inv : h1 => [A3][B3][?][h10]h11. subst.
    inversion h; subst; sauto lq:on.
  Qed.

  Lemma univ_inj i j :
    @R (PUniv i) (PUniv j)  -> i <= j.
  Proof.
    sauto lq:on rew:off use:REReds.univ_inv.
  Qed.

  Lemma suc_inj (A0 A1 : PTm)  :
    R (PSuc A0) (PSuc A1) ->
    R A0 A1.
  Proof.
    sauto q:on use:REReds.suc_inv.
  Qed.


  Lemma cong (a b : PTm) c d (ρ : nat -> PTm) :
    R a b -> DJoin.R c d -> R (subst_PTm (scons c ρ) a) (subst_PTm (scons d ρ) b).
  Proof.
    rewrite /R.
    move => [a0][b0][h0][h1]h2.
    move => [cd][h3]h4.
    exists (subst_PTm (scons cd ρ) a0), (subst_PTm (scons cd ρ) b0).
    repeat split.
    hauto l:on use:REReds.cong' inv:nat.
    hauto l:on use:REReds.cong' inv:nat.
    eauto using Sub1.substing.
  Qed.

  Lemma substing (a b : PTm) (ρ : nat -> PTm) :
    R a b -> R (subst_PTm ρ a) (subst_PTm ρ b).
  Proof.
    rewrite /R.
    move => [a0][b0][h0][h1]h2.
    hauto ctrs:rtc use:REReds.cong', Sub1.substing.
  Qed.

  Lemma ToESub (a b : PTm) : nf a -> nf b -> R a b -> ESub.R a b.
  Proof. hauto q:on use:REReds.ToEReds. Qed.

  Lemma standardization (a b : PTm) :
    SN a -> SN b -> R a b ->
    exists va vb, rtc RRed.R a va /\ rtc RRed.R b vb /\ nf va /\ nf vb /\ ESub.R va vb.
  Proof.
    move => h0 h1 hS.
    have : exists v, rtc RRed.R a v  /\ nf v by sfirstorder use:LoReds.FromSN, LoReds.ToRReds.
    move => [v [hv2 hv3]].
    have : exists v, rtc RRed.R b v  /\ nf v by sfirstorder use:LoReds.FromSN, LoReds.ToRReds.
    move => [v' [hv2' hv3']].
    move : (hv2) (hv2') => *.
    apply DJoin.FromRReds in hv2, hv2'.
    move/DJoin.symmetric in hv2'.
    apply FromJoin in hv2, hv2'.
    have hv : R v v' by eauto using transitive.
    have {}hv : ESub.R v v' by hauto l:on use:ToESub.
    hauto lq:on.
  Qed.

  Lemma standardization_lo (a b : PTm) :
    SN a -> SN b -> R a b ->
    exists va vb, rtc LoRed.R a va /\ rtc LoRed.R b vb /\ nf va /\ nf vb /\ ESub.R va vb.
  Proof.
    move => /[dup] sna + /[dup] snb.
    move : standardization; repeat move/[apply].
    move => [va][vb][hva][hvb][nfva][nfvb]hj.
    move /LoReds.FromSN : sna => [va' [hva' hva'0]].
    move /LoReds.FromSN : snb => [vb' [hvb' hvb'0]].
    exists va', vb'.
    repeat split => //=.
    have : va = va' /\ vb = vb' by sfirstorder use:red_uniquenf, LoReds.ToRReds.
    case; congruence.
  Qed.

End Sub.
