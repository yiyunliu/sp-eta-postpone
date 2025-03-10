Require Import Autosubst2.unscoped Autosubst2.syntax Autosubst2.core ssreflect ssrbool.
From Equations Require Import Equations.
Derive NoConfusion for nat PTag BTag PTm.
Derive EqDec for BTag PTag PTm.
From Ltac2 Require Ltac2.
Import Ltac2.Notations.
Import Ltac2.Control.
From Hammer Require Import Tactics.
From stdpp Require Import relations (rtc(..)).

Inductive lookup : nat -> list PTm -> PTm -> Prop :=
| here A Γ : lookup 0 (cons A Γ) (ren_PTm shift A)
| there i Γ A B :
  lookup i Γ A ->
  lookup (S i) (cons B Γ) (ren_PTm shift A).

Lemma lookup_deter i Γ A B :
  lookup i Γ A ->
  lookup i Γ B ->
  A = B.
Proof. move => h. move : B. induction h; hauto lq:on inv:lookup. Qed.

Lemma here' A Γ U : U = ren_PTm shift A -> lookup 0 (A :: Γ) U.
Proof.  move => ->. apply here. Qed.

Lemma there' i Γ A B U : U = ren_PTm shift A -> lookup i Γ A ->
                       lookup (S i) (cons B Γ) U.
Proof. move => ->. apply there. Qed.

Derive Inversion lookup_inv with (forall i Γ A, lookup i Γ A).

Definition renaming_ok (Γ : list PTm) (Δ : list PTm) (ξ : nat -> nat) :=
  forall i A, lookup i Δ A -> lookup (ξ i) Γ (ren_PTm ξ A).

Definition ren_inj (ξ : nat -> nat) := forall i j, ξ i = ξ j -> i = j.

Lemma up_injective (ξ : nat -> nat) :
  ren_inj ξ ->
  ren_inj (upRen_PTm_PTm ξ).
Proof.
  move => h i j.
  case : i => //=; case : j => //=.
  move => i j. rewrite /funcomp. hauto lq:on rew:off unfold:ren_inj.
Qed.

Local Ltac2 rec solve_anti_ren () :=
  let x := Fresh.in_goal (Option.get (Ident.of_string "x")) in
  intro $x;
  lazy_match! Constr.type (Control.hyp x) with
  | nat -> nat => (ltac1:(case => *//=; qauto l:on use:up_injective unfold:ren_inj))
  | _ => solve_anti_ren ()
  end.

Local Ltac solve_anti_ren := ltac2:(Control.enter solve_anti_ren).

Lemma ren_injective (a b : PTm) (ξ : nat -> nat) :
  ren_inj ξ ->
  ren_PTm ξ a = ren_PTm ξ b ->
  a = b.
Proof.
  move : ξ b. elim : a => //; try solve_anti_ren.
  move => p ihp ξ []//=. hauto lq:on inv:PTm, nat ctrs:- use:up_injective.
Qed.

Inductive HF : Set :=
| H_Pair | H_Abs | H_Univ | H_Bind (p : BTag) | H_Nat | H_Suc | H_Zero | H_Bot.

Definition ishf (a : PTm) :=
  match a with
  | PPair _ _ => true
  | PAbs _ => true
  | PUniv _ => true
  | PBind _ _ _ => true
  | PNat => true
  | PSuc _ => true
  | PZero => true
  | _ => false
  end.

Definition toHF (a : PTm) :=
  match a with
  | PPair _ _ => H_Pair
  | PAbs _ => H_Abs
  | PUniv _ => H_Univ
  | PBind p _ _ => H_Bind p
  | PNat => H_Nat
  | PSuc _ => H_Suc
  | PZero => H_Zero
  | _ => H_Bot
  end.

Fixpoint ishne (a : PTm) :=
  match a with
  | VarPTm _ => true
  | PApp a _ => ishne a
  | PProj _ a => ishne a
  | PInd _ n _ _ => ishne n
  | _ => false
  end.

Definition isbind (a : PTm) := if a is PBind _ _ _ then true else false.

Definition isuniv (a : PTm) := if a is PUniv _ then true else false.

Definition ispair (a : PTm) :=
  match a with
  | PPair _ _ => true
  | _ => false
  end.

Definition isnat (a : PTm) := if a is PNat then true else false.

Definition iszero (a : PTm) := if a is PZero then true else false.

Definition issuc (a : PTm) := if a is PSuc _ then true else false.

Definition isabs (a : PTm) :=
  match a with
  | PAbs _ => true
  | _ => false
  end.

Definition tm_nonconf (a b : PTm) : bool :=
  match a, b with
  | PAbs _, _ => (~~ ishf b) || isabs b
  | _, PAbs _ => ~~ ishf a
  | VarPTm _, VarPTm _ => true
  | PPair _ _, _ => (~~ ishf b) || ispair b
  | _, PPair _ _ => ~~ ishf a
  | PZero, PZero => true
  | PSuc _, PSuc _ => true
  | PApp _ _, PApp _ _ => true
  | PProj _ _, PProj _ _ => true
  | PInd _ _ _ _, PInd _ _ _ _ => true
  | PNat, PNat => true
  | PUniv _, PUniv _ => true
  | PBind _ _ _, PBind _ _ _ => true
  | _,_=> false
  end.

Definition tm_conf (a b : PTm) := ~~ tm_nonconf a b.

Definition ishf_ren (a : PTm)  (ξ : nat -> nat) :
  ishf (ren_PTm ξ a) = ishf a.
Proof. case : a => //=. Qed.

Definition isabs_ren (a : PTm)  (ξ : nat -> nat) :
  isabs (ren_PTm ξ a) = isabs a.
Proof. case : a => //=. Qed.

Definition ispair_ren (a : PTm)  (ξ : nat -> nat) :
  ispair (ren_PTm ξ a) = ispair a.
Proof. case : a => //=. Qed.

Definition ishne_ren (a : PTm)  (ξ : nat -> nat) :
  ishne (ren_PTm ξ a) = ishne a.
Proof. move : ξ. elim : a => //=. Qed.

Lemma renaming_shift Γ A :
  renaming_ok (cons A Γ) Γ shift.
Proof. rewrite /renaming_ok. hauto lq:on ctrs:lookup. Qed.

Lemma subst_scons_id (a : PTm) :
  subst_PTm (scons (VarPTm 0) (funcomp VarPTm shift)) a = a.
Proof.
  have E : subst_PTm VarPTm a = a by asimpl.
  rewrite -{2}E.
  apply ext_PTm. case => //=.
Qed.

Module HRed.
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
  | AppCong a0 a1 b :
    R a0 a1 ->
    R (PApp a0 b) (PApp a1 b)
  | ProjCong p a0 a1 :
    R a0 a1 ->
    R (PProj p a0) (PProj p a1)
  | IndCong P a0 a1 b c :
    R a0 a1 ->
    R (PInd P a0 b c) (PInd P a1 b c).

    Definition nf a := forall b, ~ R a b.
End HRed.

Inductive algo_dom : PTm -> PTm -> Prop :=
| A_AbsAbs a b :
  algo_dom_r a b ->
  (* --------------------- *)
  algo_dom (PAbs a) (PAbs b)

| A_AbsNeu a u :
  ishne u ->
  algo_dom_r a (PApp (ren_PTm shift u) (VarPTm var_zero)) ->
  (* --------------------- *)
  algo_dom (PAbs a) u

| A_NeuAbs a u :
  ishne u ->
  algo_dom_r (PApp (ren_PTm shift u) (VarPTm var_zero)) a ->
  (* --------------------- *)
  algo_dom u (PAbs a)

| A_PairPair a0 a1 b0 b1 :
  algo_dom_r a0 a1 ->
  algo_dom_r b0 b1 ->
  (* ---------------------------- *)
  algo_dom (PPair a0 b0) (PPair a1 b1)

| A_PairNeu a0 a1 u :
  ishne u ->
  algo_dom_r a0 (PProj PL u) ->
  algo_dom_r a1 (PProj PR u) ->
  (* ----------------------- *)
  algo_dom (PPair a0 a1) u

| A_NeuPair a0 a1 u :
  ishne u ->
  algo_dom_r (PProj PL u) a0 ->
  algo_dom_r (PProj PR u) a1 ->
  (* ----------------------- *)
  algo_dom u (PPair a0 a1)

| A_ZeroZero :
  algo_dom PZero PZero

| A_SucSuc a0 a1 :
  algo_dom_r a0 a1 ->
  algo_dom (PSuc a0) (PSuc a1)

| A_UnivCong i j :
  (* -------------------------- *)
  algo_dom (PUniv i) (PUniv j)

| A_BindCong p0 p1 A0 A1 B0 B1 :
  algo_dom_r A0 A1 ->
  algo_dom_r B0 B1 ->
  (* ---------------------------- *)
  algo_dom (PBind p0 A0 B0) (PBind p1 A1 B1)

| A_NatCong :
  algo_dom PNat PNat

| A_NeuNeu a b :
  algo_dom_neu a b ->
  algo_dom a b

| A_Conf a b :
  ishf a ->
  ishf b ->
  tm_conf a b ->
  algo_dom a b

with algo_dom_neu : PTm -> PTm -> Prop :=
| A_VarCong i j :
  (* -------------------------- *)
  algo_dom_neu (VarPTm i) (VarPTm j)

| A_AppCong u0 u1 a0 a1 :
  ishne u0 ->
  ishne u1 ->
  algo_dom_neu u0 u1 ->
  algo_dom_r a0 a1 ->
  (* ------------------------- *)
  algo_dom_neu (PApp u0 a0) (PApp u1 a1)

| A_ProjCong p0 p1 u0 u1 :
  ishne u0 ->
  ishne u1 ->
  algo_dom_neu u0 u1 ->
  (* ---------------------  *)
  algo_dom_neu (PProj p0 u0) (PProj p1 u1)

| A_IndCong P0 P1 u0 u1 b0 b1 c0 c1 :
  ishne u0 ->
  ishne u1 ->
  algo_dom_r P0 P1 ->
  algo_dom_neu u0 u1 ->
  algo_dom_r b0 b1 ->
  algo_dom_r c0 c1 ->
  algo_dom_neu (PInd P0 u0 b0 c0) (PInd P1 u1 b1 c1)

| A_NeuConf a b :
  ishne a ->
  ishne b ->
  tm_conf a b ->
  algo_dom_neu a b

with algo_dom_r : PTm  -> PTm -> Prop :=
| A_NfNf a b :
  algo_dom a b ->
  algo_dom_r a b

| A_HRedL a a' b  :
  HRed.R a a' ->
  algo_dom_r a' b ->
  (* ----------------------- *)
  algo_dom_r a b

| A_HRedR a b b'  :
  HRed.nf a ->
  HRed.R b b' ->
  algo_dom_r a b' ->
  (* ----------------------- *)
  algo_dom_r a b.

Scheme algo_ind := Induction for algo_dom Sort Prop
  with algo_neu_ind := Induction for algo_dom_neu Sort Prop
  with algor_ind := Induction for algo_dom_r Sort Prop.

Combined Scheme algo_dom_mutual from algo_ind, algo_neu_ind, algor_ind.
#[export]Hint Constructors algo_dom algo_dom_neu algo_dom_r : adom.

Definition stm_nonconf a b :=
  match a, b with
  | PUniv _, PUniv _ => true
  | PBind PPi _ _, PBind PPi _ _ => true
  | PBind PSig _ _, PBind PSig _ _ => true
  | PNat, PNat => true
  | VarPTm _, VarPTm _ => true
  | PApp _ _, PApp _ _ => (~~ ishf a) && (~~ ishf b)
  | PProj _ _, PProj _ _ => (~~ ishf a) && (~~ ishf b)
  | PInd _ _ _ _, PInd _ _ _ _ => (~~ ishf a) && (~~ ishf b)
  | _, _ => false
  end.

Lemma stm_tm_nonconf a b :
  stm_nonconf a b -> tm_nonconf a b.
Proof. apply /implyP.
       destruct a ,b =>//=; hauto lq:on inv:PTag, BTag.
Qed.

Definition stm_conf a b := ~~ stm_nonconf a b.

Lemma tm_stm_conf a b :
  tm_conf a b -> stm_conf a b.
Proof.
  rewrite /tm_conf /stm_conf.
  apply /contra /stm_tm_nonconf.
Qed.

Inductive salgo_dom : PTm -> PTm -> Prop :=
| S_UnivCong i j :
  (* -------------------------- *)
  salgo_dom (PUniv i) (PUniv j)

| S_PiCong  A0 A1 B0 B1 :
  salgo_dom_r A1 A0 ->
  salgo_dom_r B0 B1 ->
  (* ---------------------------- *)
  salgo_dom (PBind PPi A0 B0) (PBind PPi A1 B1)

| S_SigCong  A0 A1 B0 B1 :
  salgo_dom_r A0 A1 ->
  salgo_dom_r B0 B1 ->
  (* ---------------------------- *)
  salgo_dom (PBind PSig A0 B0) (PBind PSig A1 B1)

| S_NatCong :
  salgo_dom PNat PNat

| S_NeuNeu a b :
  algo_dom_neu a b ->
  salgo_dom a b

| S_Conf a b :
  HRed.nf a ->
  HRed.nf b ->
  stm_conf a b ->
  salgo_dom a b

with salgo_dom_r : PTm -> PTm -> Prop :=
| S_NfNf a b :
  salgo_dom a b ->
  salgo_dom_r a b

| S_HRedL a a' b  :
  HRed.R a a' ->
  salgo_dom_r a' b ->
  (* ----------------------- *)
  salgo_dom_r a b

| S_HRedR a b b'  :
  HRed.nf a ->
  HRed.R b b' ->
  salgo_dom_r a b' ->
  (* ----------------------- *)
  salgo_dom_r a b.

Lemma hf_no_hred (a b : PTm) :
  ishf a ->
  HRed.R a b ->
  False.
Proof. hauto l:on inv:HRed.R. Qed.

Lemma hne_no_hred (a b : PTm) :
  ishne a ->
  HRed.R a b ->
  False.
Proof. elim : a b => //=; hauto l:on inv:HRed.R. Qed.

Ltac2 destruct_salgo () :=
  lazy_match! goal with
  | [h : is_true (ishne ?a) |- is_true (stm_conf ?a _) ] =>
      if Constr.is_var a then destruct $a; ltac1:(done) else ()
  | [|- is_true (stm_conf _ _)] =>
      unfold stm_conf; ltac1:(done)
  end.

Ltac destruct_salgo := ltac2:(destruct_salgo ()).

Lemma algo_dom_r_inv a b :
  algo_dom_r a b -> exists a0 b0, algo_dom a0 b0 /\ rtc HRed.R a a0 /\ rtc HRed.R b b0.
Proof.
  induction 1; hauto lq:on ctrs:rtc.
Qed.

Lemma A_HRedsL a a' b :
  rtc HRed.R a a' ->
  algo_dom_r a' b ->
  algo_dom_r a b.
  induction 1; sfirstorder use:A_HRedL.
Qed.

Lemma A_HRedsR a b b' :
  HRed.nf a ->
  rtc HRed.R b b' ->
  algo_dom a b' ->
  algo_dom_r a b.
Proof. induction 2; sauto. Qed.

Lemma tm_conf_sym a b : tm_conf a b = tm_conf b a.
Proof. case : a; case : b => //=. Qed.

Lemma algo_dom_neu_hne (a b : PTm) :
  algo_dom_neu a b ->
  ishne a /\ ishne b.
Proof. inversion 1; subst => //=. Qed.

Lemma algo_dom_no_hred (a b : PTm) :
  algo_dom a b ->
  HRed.nf a /\ HRed.nf b.
Proof.
  induction 1 =>//=; try hauto inv:HRed.R use:hne_no_hred, hf_no_hred use:algo_dom_neu_hne lq:on unfold:HRed.nf.
Qed.


Lemma A_HRedR' a b b' :
  HRed.R b b' ->
  algo_dom_r a b' ->
  algo_dom_r a b.
Proof.
  move => hb /algo_dom_r_inv.
  move => [a0 [b0 [h0 [h1 h2]]]].
  have {h2} {}hb : rtc HRed.R b b0 by hauto lq:on ctrs:rtc.
  have ? : HRed.nf a0 by sfirstorder use:algo_dom_no_hred.
  hauto lq:on use:A_HRedsL, A_HRedsR.
Qed.

Lemma algo_dom_sym :
  (forall a b (h : algo_dom a b), algo_dom b a) /\
    (forall a b, algo_dom_neu a b -> algo_dom_neu b a) /\
    (forall a b (h : algo_dom_r a b), algo_dom_r b a).
Proof.
  apply algo_dom_mutual; try qauto use:tm_conf_sym,A_HRedR' db:adom.
Qed.

Lemma salgo_dom_r_inv a b :
  salgo_dom_r a b -> exists a0 b0, salgo_dom a0 b0 /\ rtc HRed.R a a0 /\ rtc HRed.R b b0.
Proof.
  induction 1; hauto lq:on ctrs:rtc.
Qed.

Lemma S_HRedsL a a' b :
  rtc HRed.R a a' ->
  salgo_dom_r a' b ->
  salgo_dom_r a b.
  induction 1; sfirstorder use:S_HRedL.
Qed.

Lemma S_HRedsR a b b' :
  HRed.nf a ->
  rtc HRed.R b b' ->
  salgo_dom a b' ->
  salgo_dom_r a b.
Proof. induction 2; sauto. Qed.

Lemma stm_conf_sym a b : stm_conf a b = stm_conf b a.
Proof. case : a; case : b => //=; hauto lq:on inv:PTag, BTag. Qed.

Lemma salgo_dom_no_hred (a b : PTm) :
  salgo_dom a b ->
  HRed.nf a /\ HRed.nf b.
Proof.
  induction 1 =>//=; try hauto inv:HRed.R use:hne_no_hred, hf_no_hred, algo_dom_neu_hne lq:on unfold:HRed.nf.
Qed.

Lemma S_HRedR' a b b' :
  HRed.R b b' ->
  salgo_dom_r a b' ->
  salgo_dom_r a b.
Proof.
  move => hb /salgo_dom_r_inv.
  move => [a0 [b0 [h0 [h1 h2]]]].
  have {h2} {}hb : rtc HRed.R b b0 by hauto lq:on ctrs:rtc.
  have ? : HRed.nf a0 by sfirstorder use:salgo_dom_no_hred.
  hauto lq:on use:S_HRedsL, S_HRedsR.
Qed.

Lemma algo_dom_salgo_dom :
  (forall a b, algo_dom a b -> salgo_dom a b /\ salgo_dom b a) /\
    (forall a b, algo_dom_neu a b -> True) /\
    (forall a b, algo_dom_r a b -> salgo_dom_r a b /\ salgo_dom_r b a).
Proof.
  apply algo_dom_mutual => //=;
                             try hauto lq:on ctrs:salgo_dom, algo_dom_neu, salgo_dom_r use:S_Conf, hne_no_hred, algo_dom_sym, tm_stm_conf, S_HRedR' inv:HRed.R unfold:HRed.nf  solve+:destruct_salgo.
  - case;case; hauto lq:on ctrs:salgo_dom, algo_dom_neu, salgo_dom_r use:S_Conf, hne_no_hred, algo_dom_sym inv:HRed.R unfold:HRed.nf  solve+:destruct_salgo.
  - move => a b ha hb /[dup] /tm_stm_conf h.
    rewrite tm_conf_sym => /tm_stm_conf h0.
    hauto l:on use:S_Conf inv:HRed.R unfold:HRed.nf.
Qed.

Fixpoint hred (a : PTm) : option (PTm) :=
    match a with
    | VarPTm i => None
    | PAbs a => None
    | PApp (PAbs a) b => Some (subst_PTm (scons b VarPTm) a)
    | PApp a b =>
        match hred a with
        | Some a => Some (PApp a b)
        | None => None
        end
    | PPair a b => None
    | PProj p (PPair a b) => if p is PL then Some a else Some b
    | PProj p a =>
        match hred a with
        | Some a => Some (PProj p a)
        | None => None
        end
    | PUniv i => None
    | PBind p A B => None
    | PNat => None
    | PZero => None
    | PSuc a => None
    | PInd P PZero b c => Some b
    | PInd P (PSuc a) b c =>
        Some (subst_PTm (scons (PInd P a b c) (scons a VarPTm)) c)
    | PInd P a b c =>
        match hred a with
        | Some a => Some (PInd P a b c)
        | None => None
        end
    end.

Lemma hred_complete (a b : PTm) :
  HRed.R a b -> hred a = Some b.
Proof.
  induction 1; hauto lq:on rew:off inv:HRed.R b:on.
Qed.

Lemma hred_sound (a b : PTm):
  hred a = Some b -> HRed.R a b.
Proof.
  elim : a b; hauto q:on dep:on ctrs:HRed.R.
Qed.

Lemma hred_deter (a b0 b1 : PTm) :
  HRed.R a b0 -> HRed.R a b1 -> b0 = b1.
Proof.
  move /hred_complete => + /hred_complete. congruence.
Qed.

Definition fancy_hred (a : PTm) : HRed.nf a + {b | HRed.R a b}.
  destruct (hred a) eqn:eq.
  right. exists p. by apply hred_sound in eq.
  left. move => b /hred_complete. congruence.
Defined.
