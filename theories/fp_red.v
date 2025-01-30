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
      admit.
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
Admitted.

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
  - move => a0 a1 b ha iha c.
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

  (* Lemma morphing_ext n m (ρ0 ρ1 : fin n -> PTm m) a b  : *)
  (*   R a b -> *)
  (*   (forall i, R (ρ0 i) (ρ1 i)) -> *)
  (*   (forall i, R ((scons a ρ0) i) ((scons b ρ1) i)). *)
  (* Proof. hauto q:on inv:option. Qed. *)

  (* Lemma morphing_up n m (ρ0 ρ1 : fin n -> PTm m) : *)
  (*   (forall i, R (ρ0 i) (ρ1 i)) -> *)
  (*   (forall i, R (up_PTm_PTm ρ0 i) (up_PTm_PTm ρ1 i)). *)
  (* Proof. hauto l:on ctrs:R use:morphing_ext, morphing_ren unfold:up_PTm_PTm. Qed. *)

  (* Lemma morphing n m (a b : PTm n) (ρ0 ρ1 : fin n -> PTm m) : *)
  (*   (forall i, R (ρ0 i) (ρ1 i)) -> *)
  (*   R a b -> R (subst_PTm ρ0 a) (subst_PTm ρ1 b). *)
  (* Proof. *)
  (*   move => + h. move : m ρ0 ρ1. elim : n a b / h => n. *)
  (*   move => a0 a1 ha iha m ρ0 ρ1 hρ /=. *)
  (*   eapply AppEta'; eauto. by asimpl. *)
  (*   all : hauto lq:on ctrs:R use:morphing_up. *)
  (* Qed. *)

  (* Lemma substing n m (a : PTm n) b (ρ : fin n -> PTm m) : *)
  (*   R a b -> *)
  (*   R (subst_PTm ρ a) (subst_PTm ρ b). *)
  (* Proof. *)
  (*   hauto l:on use:morphing, refl. *)
  (* Qed. *)

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

End NoForbid.

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

End SN_NoForbid.

Lemma bool_dec (a : bool) : a \/ ~~ a.
Proof. hauto lq:on inv:bool. Qed.

Lemma η_split n (a0 a1 : PTm n) :
  ERed.R a0 a1 ->
  exists b, rtc RRed.R a0 b /\ NeERed.R_nonelim b a1.
Proof.
  move => h. elim : n a0 a1 /h .
  - move => n a0 a1 ha [b [ih0 ih1]].
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
    + admit.
  - move => n a0 a1 h.
    move => [b [ih0 ih1]].
    case /orP : (orNb (ishf b)).
    exists (PPair (PProj PL b) (PProj PR b)).
    split. sfirstorder use:RReds.PairCong,RReds.ProjCong.
    hauto lq:on ctrs:NeERed.R_nonelim use:NeERed.R_nonelim_nothf.

    case : b ih0 ih1 => //=.
    (* violates SN *)
    + admit.
    + move => t0 t1 ih0 h1 _.
      exists (PPair t0 t1).
      split => //=.
      apply RReds.PairCong.
      apply : rtc_r; eauto using RReds.ProjCong.
      apply RRed.ProjPair.
      apply : rtc_r; eauto using RReds.ProjCong.
      apply RRed.ProjPair.
  - hauto lq:on ctrs:NeERed.R_nonelim use:RReds.AbsCong.
  - move => n a0 a1 b0 b1 ha [a2 [iha0 iha1]] hb [b2 [ihb0 ihb1]].
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
      * admit.
  - hauto lq:on ctrs:NeERed.R_nonelim use:RReds.PairCong.
  - move => n p a0 a1 ha [a2 [iha0 iha1]].
    case /orP : (orNb (ishf a2)) => [h|].
    exists (PProj p a2).
    split.  eauto using RReds.ProjCong.
    qauto l:on ctrs:NeERed.R_nonelim, NeERed.R_elim use:NeERed.R_nonelim_nothf.

    case : a2 iha0 iha1 => //=.
    + move => u iha0 iha1 _.
      (* Impossible by SN *)
      admit.
    + move => u0 u1 iha0 iha1 _.
      inversion iha1; subst.
      * exists (PProj p a2). split.
        apply : rtc_r.
        apply RReds.ProjCong; eauto.
        clear. hauto l:on inv:PTag.
        hauto lq:on ctrs:NeERed.R_nonelim.
      * hauto lq:on ctrs:NeERed.R_nonelim,NeERed.R_elim use:RReds.ProjCong.
  - hauto lq:on ctrs:rtc, NeERed.R_nonelim.
Admitted.

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



Lemma η_nf'' n (a b : PTm n) : ERed'.R a b -> nf b -> nf a \/ rtc RRed.R a b.
Proof.
  move => h.
  elim : n a b / h.
  - move => n a.
    case : a => //=.
    * tauto.
    * move => p hp. right.
      apply rtc_once.
      apply RRed.AbsCong.
      apply RRed.AppAbs'. by asimpl.
    * hauto lb:on use:ne_nf_ren.
    * move => p p0 /andP [h0 h1].
      right.
      (* violates SN *)
      admit.
    * move => p u h.
      hauto lb:on use:ne_nf_ren.
  - move => n a ha.
    case : a ha => //=.
    * tauto.
    * move => p hp. right.
      (* violates SN *)
      admit.
    * sfirstorder b:on.
    * hauto lq:on ctrs:rtc,RRed.R.
    * qauto b:on.
  - move => n a0 a1 ha h0 /= h1.
    specialize h0 with (1 := h1).
    case : h0. tauto.
    eauto using RReds.AbsCong.
  - move => n a0 a1 b ha h /= /andP [h0 h1].
    have h2 : nf a1 by sfirstorder use:ne_nf.
    have {}h := h h2.
    case : h => h.
    + have : ne a0 \/ ~~ ne a0 by sauto lq:on.
      case; first by sfirstorder b:on.
      move : η_nf_to_ne (ha) h h0; repeat move/[apply].
      case => ?; subst.
      * simpl.
        right.
        apply rtc_once.
        apply : RRed.AppAbs'.
        by asimpl.
      * simpl.
        (* violates SN *)
        admit.
    + right.
      hauto lq:on ctrs:rtc use:RReds.AppCong.
  - move => n a b0 b1 h h0 /=.
    move /andP => [h1 h2].
    have {h0} := h0 h2.
    case => h3.
    + sfirstorder b:on.
    + right.
      hauto lq:on ctrs:rtc use:RReds.AppCong.
  - hauto lqb:on drew:off use:RReds.PairCong.
  - hauto lqb:on drew:off use:RReds.PairCong.
  - move => n p a0 a1 h0 h1 h2.
    simpl in h2.
    have : nf a1 by sfirstorder use:ne_nf.
    move : h1 => /[apply].
    case=> h.
    + have : ne a0 \/ ~~ ne a0 by sauto lq:on.
      case;first by tauto.
      move : η_nf_to_ne (h0) h h2; repeat move/[apply].
      case => ?. subst => //=.
      * right.
        (* violates SN *)
        admit.
      * right.
        subst.
        apply rtc_once.
        sauto lq:on rew:off ctrs:RRed.R.
    + hauto lq:on use:RReds.ProjCong.
Admitted.

Lemma η_nf' n (a b : PTm n) : ERed'.R a b -> rtc ERed'.R (tstar a) (tstar b).
Proof.
  move => h.
  elim : n a b /h.
  - move => n a /=.
    set p := (X in (PAbs X)).
    have : (exists a1, ren_PTm shift a = PAbs a1 /\ p = subst_PTm (scons (VarPTm var_zero) VarPTm) (tstar a1)) \/
             p = PApp (tstar (ren_PTm shift a)) (VarPTm var_zero) by hauto lq:on rew:off.
    case.
    + move => [a2 [+]].
      subst p.
      case : a   => //=.
      move => p [h0]  . subst => _.
      rewrite TStar.renaming. asimpl.
      sfirstorder.
    + move => ->.
      rewrite TStar.renaming.
      hauto lq:on ctrs:ERed'.R, rtc.
  - move => n a.
    case : (tstar_proj n a).
    + move => [_ h].
      rewrite TStar.pair.
      rewrite !h.
      hauto lq:on ctrs:ERed'.R, rtc.
    + move => [a2][b0][?]. subst.
      move => h.
      rewrite TStar.pair.
      rewrite !h.
      sfirstorder.
  - (* easy *)
    eauto using EReds.AbsCong.
    (* hard application cases *)
  - admit.
  - admit.
  (* Trivial congruence cases *)
  - move => n a0 a1 b ha iha.
    hauto lq:on ctrs:rtc use:EReds.PairCong.
  - hauto lq:on ctrs:rtc use:EReds.PairCong.
  (* hard projection cases *)
  - move => n p a0 a1 h0 h1.
    case : (tstar_proj n a0).
    + move => [ha0 ->].
      case : (tstar_proj n a1).
      * move => [ha1 ->].
        (* Trivial by proj cong *)
        hauto lq:on use:EReds.ProjCong.
      * move => [a2][b0][?]. subst.
        move => ->.
        elim /ERed'.inv : h0 => //_.
        ** move => a1 a3 ? *. subst.
           (* Contradiction *)
           admit.
        ** hauto lqb:on.
        ** hauto lqb:on.
        ** hauto lqb:on.
    + move => [a2][b0][?] ->. subst.
      case : (tstar_proj n a1).
      * move => [ha1 ->].
        simpl in h1.
        inversion h0; subst.
        ** hauto lq:on.
        ** hauto lqb:on.
        ** hauto lqb:on.
      * move => [a0][b1][?]. subst => ->.
        rewrite !TStar.pair in h1.
        inversion h0; subst.
        ** admit.
        ** best.

Lemma η_nf n (a b : PTm n) : ERed.R a b -> ERed.R (tstar a) (tstar b).
Proof.
  move => h.
  elim : n a b /h.
  - move => n a0 a1 h h0 /=.
    set p := (X in (PAbs X)).
    have : (exists a1, ren_PTm shift a0 = PAbs a1 /\ p = subst_PTm (scons (VarPTm var_zero) VarPTm) (tstar a1)) \/
             p = PApp (tstar (ren_PTm shift a0)) (VarPTm var_zero) by hauto lq:on rew:off.
    case.
    + move => [a2 [+]].
      subst p.
      case : a0 h h0  => //=.
      move => p h0 h1 [?]. subst => _.
      rewrite TStar.renaming. by asimpl.
    + move => ->.
      rewrite TStar.renaming.
      hauto lq:on ctrs:ERed.R.
  - move => n a0 a1 ha iha.
    case : (tstar_proj n a0).
    + move => [_ h].
      change (tstar (PPair (PProj PL a0) (PProj PR a0))) with
        (PPair (tstar (PProj PL a0)) (tstar (PProj PR a0))).
      rewrite !h.
      hauto lq:on ctrs:ERed.R.
    + move => [a2][b0][?]. subst.
      move => h.
      rewrite TStar.pair.
      rewrite !h.
      sfirstorder.
  - hauto lq:on ctrs:ERed.R.
  - admit.
  - hauto lq:on ctrs:ERed.R.
  - move => n p a0 a1 h0 h1.
    case : (tstar_proj n a0).
    + move => [ha0 ->].
      case : (tstar_proj n a1).
      * move => [ha1 ->].
        hauto lq:on ctrs:ERed.R.
      * move => [a2][b0][?]. subst.
        move => ->.
        elim /ERed.inv : h0 => //_.
        ** move => a1 a3 ? *. subst.
           (* Contradiction *)
           admit.
        ** hauto lqb:on.
        ** hauto lqb:on.
    + move => [a2][b0][?] ->. subst.
      case : (tstar_proj n a1).
      * move => [ha1 ->].
        inversion h0; subst.
        ** admit.
        ** scongruence.
      * move => [a0][b1][?]. subst => ->.
        rewrite !TStar.pair in h1.
        inversion h1; subst.
        **
        ** hauto lq:on.




  move : b.
  apply tstar_ind => {}n {}a => //=.
  - hauto lq:on ctrs:ERed.R inv:ERed.R.
  - move => a0 ? ih. subst.
    move => b hb.
    elim /ERed.inv : hb => //=_.
    + move => a1 a2 ha [*]. subst.
      simpl.
      case : a1 ih ha => //=.


  - move => a0 ? ih u. subst.
    elim /ERed.inv => //=_.
    + move => a1 a2 h [? ?]. subst.
      have : ERed.R (PApp (ren_PTm shift a1) (VarPTm var_zero)) (PApp (ren_PTm shift u) (VarPTm var_zero))
        by hauto lq:on ctrs:ERed.R use:ERed.renaming.
      move /ih.

      move => h0. simpl.

  move => h.
  elim : n a b /h => n.
  - move => a0 a1 ha iha.
    simpl.
    move => h.
    move /iha : (h) {iha}.
    move : ha. clear. best.
    clear.
  - sfirstorder.
  -


Lemma η_nf n (a b c : PTm n) : ERed.R a b -> nf b -> RRed.R a c ->
                                ERed.R c b.
Proof.
  move => h. move : c.
  elim : n a b /h=>//=n.
  - move => a0 a1 ha iha u hu.
    elim /RRed.inv => //= _.
    move => a2 a3 h [*]. subst.
    elim / RRed.inv : h => //_.
    + move => a2 b0 [h0 h1 h2]. subst.
      case : a0 h0 ha iha =>//=.
      move => u [?] ha iha. subst.
      by asimpl.
    + move => a2 b4 b0 h [*]. subst.
      move /RRed.antirenaming : h.
      hauto lq:on ctrs:ERed.R.
    + move => a2 b0 b1 h [*]. subst.
      inversion h.
  - move => a0 b0 a1 ha iha hb ihb u hu.
    elim /RRed.inv => //=_.
    + move => a2 a3 b1 h0 [*]. subst.
      elim /RRed.inv : h0 => //=_.
      * move => p a2 b1 [*]. subst.
        elim /ERed.inv : ha => //=_.
        ** sauto lq:on.
        ** move => a0 a2 b2 b3 h h' [*]. subst.


Lemma η_nf n (a b c : PTm n) : ERed.R a b -> nf b -> RRed.R a c ->
                              ERed.R a c.
Proof.
  move => h. move : c.
  elim : n a b /h=>//=.
  - move => n A a0 a1 ha iha c ha1.
    elim /RRed.inv => //=_.
    move => A0 a2 a3 hr [*]. subst.
    set u := a0 in hr *.
    set q := a3 in hr *.
    elim / RRed.inv : hr => //_.
    + move => A0 a2 b0 [h0] h1 h2. subst.
      subst u q.
      rewrite h0. apply ERed.AppEta.
      subst.
      case : a0 ha iha h0 => //= B a ha iha [*]. subst.
      asimpl.
      admit.
    + subst u q.
      move => a2 a4 b0 hr [*]. subst.
      move /RRed.antirenaming : hr => [b0 [h0 h1]]. subst.
      hauto lq:on ctrs:ERed.R use:ERed.renaming.
    + subst u q.
      move => a2 b0 b1 h [*]. subst.
      inversion h.
  - move => n a0 a1 ha iha v hv.
    elim /RRed.inv => //=_.
    + move => a2 a3 b0 h [*]. subst.
      elim /RRed.inv : h => //=_.
      * move => p a2 b0 [*]. subst.
        elim /ERed.inv : ha=>//= _.
        move => a0 a2 h [*]. subst.
        best.
        apply ERed.PairEta.

  -
