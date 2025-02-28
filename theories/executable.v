From Equations Require Import Equations.
Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax.
Derive NoConfusion for nat PTag BTag PTm.

Require Import ssreflect ssrbool.
From Hammer Require Import Tactics.


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

Fixpoint ishne (a : PTm) :=
  match a with
  | VarPTm _ => true
  | PApp a _ => ishne a
  | PProj _ a => ishne a
  | PBot => true
  | PInd _ n _ _ => ishne n
  | _ => false
  end.

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

| A_UnivCong i j :
  (* -------------------------- *)
  algo_dom (PUniv i) (PUniv j)

| A_BindCong p0 p1 A0 A1 B0 B1 :
  algo_dom_r A0 A1 ->
  algo_dom_r B0 B1 ->
  (* ---------------------------- *)
  algo_dom (PBind p0 A0 B0) (PBind p1 A1 B1)

| A_VarCong i j :
  (* -------------------------- *)
  algo_dom (VarPTm i) (VarPTm j)

| A_ProjCong p0 p1 u0 u1 :
  ishne u0 ->
  ishne u1 ->
  algo_dom u0 u1 ->
  (* ---------------------  *)
  algo_dom (PProj p0 u0) (PProj p1 u1)

| A_AppCong u0 u1 a0 a1 :
  ishne u0 ->
  ishne u1 ->
  algo_dom u0 u1 ->
  algo_dom_r a0 a1 ->
  (* ------------------------- *)
  algo_dom (PApp u0 a0) (PApp u1 a1)

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
  ishne a \/ ishf a ->
  HRed.R b b' ->
  algo_dom_r a b' ->
  (* ----------------------- *)
  algo_dom_r a b.

Lemma algo_dom_hf_hne (a b : PTm) :
  algo_dom a b ->
  (ishf a \/ ishne a) /\ (ishf b \/ ishne b).
Proof.
  induction 1 =>//=; hauto lq:on.
Qed.

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

Derive Signature for algo_dom.
(* Fixpoint PTm_eqb {n} (a b : PTm n) := *)
(*   match a, b with *)
(*   | VarPTm i, VarPTm j => fin_eq i j *)
(*   | PAbs a, PAbs b => PTm_eqb a b *)
(*   | PApp a0 b0, PApp a1 b1 => PTm_eqb a0 a1 && PTm_eqb b0 b1 *)
(*   | PBind p0 A0 B0, PBind p1 A1 B1 => BTag_beq p0 p1 && PTm_eqb A0 A1 && PTm_eqb B0 B1 *)
(*   | PPair a0 b0, PPair a1 b1 => PTm_eqb a0 a1 && PTm_eqb b0 b1 *)
(*   | *)

(* Lemma hred {n} (a : PTm n) : (relations.nf HRed.R a) + {x | HRed.R a x}. *)
(* Proof. *)
(*   induction a. *)
(*   - hauto lq:on inv:HRed.R unfold:relations.nf. *)
(*   - hauto lq:on inv:HRed.R unfold:relations.nf. *)
(*   - clear IHa2. *)
(*     destruct IHa1. *)
(*     destruct a1. *)

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
    | PBot => None
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

Definition hred_fancy  (a : PTm) :
  HRed.nf a + {x | HRed.R a x}.
Proof.
  destruct (hred a) as [a'|] eqn:eq .
  - right. exists a'. hauto q:on use:hred_sound.
  - left.
    move => a' h.
    move /hred_complete in h.
    congruence.
Defined.

Ltac check_equal_triv :=
  intros;subst;
  lazymatch goal with
  (* | [h : algo_dom (VarPTm _) (PAbs _) |- _] => idtac *)
  | [h : algo_dom _ _ |- _] => try inversion h; by subst
  | _ => idtac
  end.

Scheme Equality for nat. Scheme Equality for PTag.
Scheme Equality for BTag. Scheme Equality for PTm.
(* Program Fixpoint check_equal {n} (a b : PTm n) (h : algo_dom a b) {struct h} : bool := *)
(*   match a, b with *)
(*   | VarPTm i, VarPTm j => fin_beq i j *)
(*   | PAbs a, PAbs b => check_equal_r a b ltac:(check_equal_triv) *)
(*   | _, _ => false *)
(*   end *)
(* with check_equal_r {n} (a b : PTm n) (h : algo_dom_r a b) {struct h} : bool := *)
(*   match hred_fancy _ a with *)
(*   | inr a' => check_equal_r (proj1_sig a') b _ *)
(*   | _ => false *)
(*   end. *)
(* Next Obligation. *)
(*   simpl. *)

Equations check_equal (a b : PTm) (h : algo_dom a b) :
  bool by struct h :=
  check_equal (VarPTm i) (VarPTm j) h := nat_beq i j;
  check_equal (PAbs a) (PAbs b) h := check_equal_r a b ltac:(check_equal_triv);
  check_equal (PAbs a) b h := check_equal_r a (PApp (ren_PTm shift b) (VarPTm var_zero)) ltac:(check_equal_triv);
  check_equal a (PAbs b) h := check_equal_r (PApp (ren_PTm shift a) (VarPTm var_zero)) b ltac:(check_equal_triv);
  check_equal (PPair a0 b0) (PPair a1 b1) h :=
    check_equal_r a0 a1 ltac:(check_equal_triv) && check_equal_r b0 b1 ltac:(check_equal_triv);
  check_equal (PPair a0 b0) u h :=
    check_equal_r a0 (PProj PL u) ltac:(check_equal_triv) && check_equal_r b0 (PProj PR u) ltac:(check_equal_triv);
  check_equal u (PPair a1 b1) h :=
    check_equal_r (PProj PL u) a1 ltac:(check_equal_triv) && check_equal_r (PProj PR u) b1 ltac:(check_equal_triv);
  check_equal (PBind p0 A0 B0) (PBind p1 A1 B1) h :=
    BTag_beq p0 p1 && check_equal_r A0 A1 ltac:(check_equal_triv) && check_equal_r B0 B1 ltac:(check_equal_triv);
  check_equal PNat PNat _ := true;
  check_equal PZero PZero _ := true;
  check_equal (PSuc a) (PSuc b) h := check_equal_r a b ltac:(check_equal_triv);
  check_equal (PUniv i) (PUniv j) _ := Nat.eqb i j;
  check_equal a b h := false;
  with check_equal_r (a b : PTm) (h : algo_dom_r a b) :
  bool by struct h :=
  check_equal_r a b h with hred_fancy a =>
    { check_equal_r a b h (inr a') := check_equal_r (proj1_sig a') b _;
      check_equal_r a b h (inl _) with hred_fancy b =>
        { check_equal_r a b h (inl _) (inl _) := check_equal a b _;
          check_equal_r a b h (inl _) (inr b') := check_equal_r a (proj1_sig b')  _}} .


Next Obligation.
  inversion h; subst=>//=.
  exfalso. sfirstorder.
  exfalso. sfirstorder.
Defined.

Next Obligation.
  simpl.
  inversion h; subst =>//=.
  exfalso. hauto lq:on use:algo_dom_hf_hne, hf_no_hred, hne_no_hred.
  exfalso. sfirstorder.
  have ? : b' = b'0 by eauto using hred_deter.
  subst.
  assumption.
Defined.

Next Obligation.
  inversion h; subst => //=.
  exfalso. hauto lq:on use:algo_dom_hf_hne, hf_no_hred, hne_no_hred.
  suff ? : a'0 = a' by subst; assumption.
  by eauto using hred_deter.
  exfalso. hauto lq:on use:hf_no_hred, hne_no_hred.
Defined.


Search (Bool.reflect (is_true _) _).
Check idP.

Definition metric {n} k (a b : PTm n) :=
  exists i j va vb, nsteps LoRed.R i a va /\ nsteps LoRed.R j b vb /\
  nf va /\ nf vb /\ size_PTm va + size_PTm vb + i + j <= k.

Search (nat -> nat -> bool).
