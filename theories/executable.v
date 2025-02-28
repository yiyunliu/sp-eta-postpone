From Equations Require Import Equations.
Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax.
Derive NoConfusion for sig nat PTag BTag PTm.
Derive EqDec for BTag PTag PTm.
Import Logic (inspect).

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

| A_IndCong P0 P1 u0 u1 b0 b1 c0 c1 :
  ishne u0 ->
  ishne u1 ->
  algo_dom_r P0 P1 ->
  algo_dom u0 u1 ->
  algo_dom_r b0 b1 ->
  algo_dom_r c0 c1 ->
  algo_dom (PInd P0 u0 b0 c0) (PInd P1 u1 b1 c1)

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

Derive Signature for algo_dom algo_dom_r.

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

(* Equations hred_fancy (a : PTm ) : *)
(*   HRed.nf a + {x | HRed.R a x} := *)
(*   hred_fancy a with hra => { *)
(*       hred_fancy a None := inl _; *)
(*       hred_fancy a (Some b) := inr (exist _ b _) *)
(*     } *)
(*   with hra := hred a. *)
(* Next Obligation. *)


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


Ltac solve_check_equal :=
  try solve [intros *;
  match goal with
  | [|- _ = _] => sauto
  | _ => idtac
  end].

(* #[export,global] Obligation Tactic := idtac "fiewof". *)


Equations check_equal (a b : PTm) (h : algo_dom a b) :
  bool by struct h :=
  check_equal (VarPTm i) (VarPTm j) h := nat_eqdec i j;
  check_equal (PAbs a) (PAbs b) h := check_equal_r a b ltac:(check_equal_triv);
  check_equal (PAbs a) b h := check_equal_r a (PApp (ren_PTm shift b) (VarPTm var_zero)) ltac:(check_equal_triv);
  check_equal a (PAbs b) h := check_equal_r (PApp (ren_PTm shift a) (VarPTm var_zero)) b ltac:(check_equal_triv);
  check_equal (PPair a0 b0) (PPair a1 b1) h :=
    check_equal_r a0 a1 ltac:(check_equal_triv) && check_equal_r b0 b1 ltac:(check_equal_triv);
  check_equal (PPair a0 b0) u h :=
    check_equal_r a0 (PProj PL u) ltac:(check_equal_triv) && check_equal_r b0 (PProj PR u) ltac:(check_equal_triv);
  check_equal u (PPair a1 b1) h :=
    check_equal_r (PProj PL u) a1 ltac:(check_equal_triv) && check_equal_r (PProj PR u) b1 ltac:(check_equal_triv);
  check_equal PNat PNat _ := true;
  check_equal PZero PZero _ := true;
  check_equal (PSuc a) (PSuc b) h := check_equal_r a b ltac:(check_equal_triv);
  check_equal (PProj p0 a) (PProj p1 b) h :=
    PTag_eqdec p0 p1 && check_equal a b ltac:(check_equal_triv);
  check_equal (PApp a0 b0) (PApp a1 b1) h :=
    check_equal a0 a1 ltac:(check_equal_triv) && check_equal_r b0 b1 ltac:(check_equal_triv);
  check_equal (PInd P0 u0 b0 c0) (PInd P1 u1 b1 c1) h :=
    check_equal_r P0 P1 ltac:(check_equal_triv) &&
      check_equal u0 u1 ltac:(check_equal_triv) &&
      check_equal_r b0 b1 ltac:(check_equal_triv) &&
      check_equal_r c0 c1 ltac:(check_equal_triv);
  check_equal (PUniv i) (PUniv j) _ := Nat.eqb i j;
  check_equal (PBind p0 A0 B0) (PBind p1 A1 B1) h :=
    BTag_eqdec p0 p1 && check_equal_r A0 A1 ltac:(check_equal_triv) && check_equal_r B0 B1 ltac:(check_equal_triv);
  check_equal a b h := false;
  with check_equal_r (a b : PTm) (h : algo_dom_r a b) :
  bool by struct h :=
  check_equal_r a b h with inspect (hred a) :=
    { check_equal_r a b h (exist _ (Some a') k) := check_equal_r a' b _;
      check_equal_r a b h (exist _ None k) with inspect (hred b) :=
        { | (exist _ None l) => check_equal a b _;
          | (exist _ (Some b') l) => check_equal_r a b'  _}} .

Next Obligation.
  intros.
  destruct h.
  exfalso. apply algo_dom_hf_hne in H.
  apply hred_sound in k.
  destruct H as [[|] _].
  eauto using hf_no_hred.
  eauto using hne_no_hred.
  apply hred_sound in k.
  assert (  a'0 = a')by eauto using hred_deter. subst.
  apply h.
  exfalso.
  apply hred_sound in k.
  destruct H as [|].
  eauto using hne_no_hred.
  eauto using hf_no_hred.
Defined.

Next Obligation.
  simpl. intros.
  inversion h; subst =>//=.
  move {h}. hauto lq:on use:algo_dom_hf_hne, hf_no_hred, hne_no_hred, hred_sound.
  apply False_ind. hauto l:on use:hred_complete.
  assert (b' = b'0) by eauto using hred_deter, hred_sound.
  subst.
  assumption.
Defined.

Next Obligation.
  intros.
  inversion h; subst => //=.
  exfalso. hauto l:on use:hred_complete.
  exfalso. hauto l:on use:hred_complete.
Defined.

Next Obligation.
  sauto.
Defined.
