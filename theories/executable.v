From Equations Require Import Equations.
Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common.
Require Import Logic.PropExtensionality (propositional_extensionality).
Require Import ssreflect ssrbool.
Import Logic (inspect).
From Ltac2 Require Import Ltac2.
Import Ltac2.Constr.
Set Default Proof Mode "Classic".


Require Import ssreflect ssrbool.
From Hammer Require Import Tactics.

Definition tm_nonconf (a b : PTm) : bool :=
  match a, b with
  | PAbs _, _ => (~~ ishf b) || isabs b
  | _, PAbs _ => ~~ ishf a
  | VarPTm _, VarPTm _ => true
  | PPair _ _, _ => (~~ ishf b) || ispair b
  | _, PPair _ _ => ~~ ishf a
  | PZero, PZero => true
  | PSuc _, PSuc _ => true
  | PApp _ _, PApp _ _ => (~~ ishf a) && (~~ ishf b)
  | PProj _ _, PProj _ _ => (~~ ishf a) && (~~ ishf b)
  | PInd _ _ _ _, PInd _ _ _ _ => (~~ ishf a) && (~~ ishf b)
  | PNat, PNat => true
  | PUniv _, PUniv _ => true
  | PBind _ _ _, PBind _ _ _ => true
  | _,_=> false
  end.

Definition tm_conf (a b : PTm) := ~~ tm_nonconf a b.

Inductive eq_view : PTm -> PTm -> Type :=
| V_AbsAbs a b :
  eq_view (PAbs a) (PAbs b)
| V_AbsNeu a b :
  ~~ ishf b ->
  eq_view (PAbs a) b
| V_NeuAbs a b :
  ~~ ishf a ->
  eq_view a (PAbs b)
| V_VarVar i j :
  eq_view (VarPTm i) (VarPTm j)
| V_PairPair a0 b0 a1 b1 :
  eq_view (PPair a0 b0) (PPair a1 b1)
| V_PairNeu a0 b0 u :
  ~~ ishf u ->
  eq_view (PPair a0 b0) u
| V_NeuPair u a1 b1 :
  ~~ ishf u ->
  eq_view u (PPair a1 b1)
| V_ZeroZero :
  eq_view PZero PZero
| V_SucSuc a b :
  eq_view (PSuc a) (PSuc b)
| V_AppApp u0 b0 u1 b1 :
  eq_view (PApp u0 b0) (PApp u1 b1)
| V_ProjProj p0 u0 p1 u1 :
  eq_view (PProj p0 u0) (PProj p1 u1)
| V_IndInd P0 u0 b0 c0  P1 u1 b1 c1 :
  eq_view (PInd P0 u0 b0 c0) (PInd P1 u1 b1 c1)
| V_NatNat :
  eq_view PNat PNat
| V_BindBind p0 A0 B0 p1 A1 B1 :
  eq_view (PBind p0 A0 B0) (PBind p1 A1 B1)
| V_UnivUniv i j :
  eq_view (PUniv i) (PUniv j)
| V_Others a b :
  tm_conf a b ->
  eq_view a b.

Equations tm_to_eq_view (a b : PTm) : eq_view a b :=
  tm_to_eq_view (PAbs a) (PAbs b) := V_AbsAbs a b;
  tm_to_eq_view (PAbs a) (PApp b0 b1) := V_AbsNeu a (PApp b0 b1) _;
  tm_to_eq_view (PAbs a) (VarPTm i) := V_AbsNeu a (VarPTm i) _;
  tm_to_eq_view (PAbs a) (PProj p b) := V_AbsNeu a (PProj p b) _;
  tm_to_eq_view (PAbs a) (PInd P u b c) := V_AbsNeu a (PInd P u b c) _;
  tm_to_eq_view (VarPTm i) (PAbs a) := V_NeuAbs (VarPTm i) a _;
  tm_to_eq_view (PApp b0 b1) (PAbs b) := V_NeuAbs (PApp b0 b1) b _;
  tm_to_eq_view (PProj p b) (PAbs a) := V_NeuAbs (PProj p b) a _;
  tm_to_eq_view (PInd P u b c) (PAbs a) := V_NeuAbs (PInd P u b c) a _;
  tm_to_eq_view (VarPTm i) (VarPTm j) := V_VarVar i j;
  tm_to_eq_view (PPair a0 b0) (PPair a1 b1) := V_PairPair a0 b0 a1 b1;
  (* tm_to_eq_view (PPair a0 b0) u := V_PairNeu a0 b0 u _; *)
  tm_to_eq_view (PPair a0 b0) (VarPTm i) := V_PairNeu a0 b0 (VarPTm i) _;
  tm_to_eq_view (PPair a0 b0) (PApp c0 c1) := V_PairNeu a0 b0 (PApp c0 c1) _;
  tm_to_eq_view (PPair a0 b0) (PProj p c) := V_PairNeu a0 b0 (PProj p c) _;
  tm_to_eq_view (PPair a0 b0) (PInd P t0 t1 t2) := V_PairNeu a0 b0 (PInd P t0 t1 t2) _;
  (* tm_to_eq_view u (PPair a1 b1) := V_NeuPair u a1 b1 _; *)
  tm_to_eq_view (VarPTm i) (PPair a1 b1) := V_NeuPair (VarPTm i) a1 b1 _;
  tm_to_eq_view (PApp t0 t1) (PPair a1 b1) := V_NeuPair (PApp t0 t1) a1 b1 _;
  tm_to_eq_view (PProj t0 t1) (PPair a1 b1) := V_NeuPair (PProj t0 t1) a1 b1 _;
  tm_to_eq_view (PInd t0 t1 t2 t3) (PPair a1 b1) := V_NeuPair (PInd t0 t1 t2 t3) a1 b1 _;
  tm_to_eq_view PZero PZero := V_ZeroZero;
  tm_to_eq_view (PSuc a) (PSuc b) := V_SucSuc a b;
  tm_to_eq_view (PApp a0 b0) (PApp a1 b1) := V_AppApp a0 b0 a1 b1;
  tm_to_eq_view (PProj p0 b0) (PProj p1 b1) := V_ProjProj p0 b0 p1 b1;
  tm_to_eq_view (PInd P0 u0 b0 c0) (PInd P1 u1 b1 c1) := V_IndInd P0 u0 b0 c0 P1 u1 b1 c1;
  tm_to_eq_view PNat PNat := V_NatNat;
  tm_to_eq_view (PUniv i) (PUniv j) := V_UnivUniv i j;
  tm_to_eq_view (PBind p0 A0 B0)  (PBind p1 A1 B1) := V_BindBind p0 A0 B0 p1 A1 B1;
  tm_to_eq_view a b := V_Others a b _.

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

| A_Conf a b :
  HRed.nf a ->
  HRed.nf b ->
  tm_conf a b ->
  algo_dom a b

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
  with algor_ind := Induction for algo_dom_r Sort Prop.

Combined Scheme algo_dom_mutual from algo_ind, algor_ind.

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

Lemma algo_dom_no_hred (a b : PTm) :
  algo_dom a b ->
  HRed.nf a /\ HRed.nf b.
Proof.
  induction 1 =>//=; try hauto inv:HRed.R use:hne_no_hred, hf_no_hred lq:on unfold:HRed.nf.
Qed.

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

Ltac2 destruct_algo () :=
  lazy_match! goal with
  | [h : algo_dom ?a ?b |- _ ] =>
      if is_var a then destruct $a; ltac1:(done)  else
        (if is_var b then destruct $b; ltac1:(done) else ())
  end.


Ltac check_equal_triv :=
  intros;subst;
  lazymatch goal with
  (* | [h : algo_dom (VarPTm _) (PAbs _) |- _] => idtac *)
  | [h : algo_dom _ _ |- _] => try (inversion h; subst => //=; ltac2:(Control.enter destruct_algo))
  | _ => idtac
  end.

Ltac solve_check_equal :=
  try solve [intros *;
  match goal with
  | [|- _ = _] => sauto
  | _ => idtac
  end].

#[derive(equations=no)]Equations check_equal (a b : PTm) (h : algo_dom a b) :
  bool by struct h :=
  check_equal a b h with tm_to_eq_view a b :=
  check_equal _ _ h (V_VarVar i j) := nat_eqdec i j;
  check_equal _ _ h (V_AbsAbs a b) := check_equal_r a b ltac:(check_equal_triv);
  check_equal _ _ h (V_AbsNeu a b h') := check_equal_r a (PApp (ren_PTm shift b) (VarPTm var_zero)) ltac:(check_equal_triv);
  check_equal _ _ h (V_NeuAbs a b _) := check_equal_r (PApp (ren_PTm shift a) (VarPTm var_zero)) b ltac:(check_equal_triv);
  check_equal _ _ h (V_PairPair a0 b0 a1 b1) :=
    check_equal_r a0 a1 ltac:(check_equal_triv) && check_equal_r b0 b1 ltac:(check_equal_triv);
  check_equal _ _ h (V_PairNeu a0 b0 u _) :=
    check_equal_r a0 (PProj PL u) ltac:(check_equal_triv) && check_equal_r b0 (PProj PR u) ltac:(check_equal_triv);
  check_equal _ _ h (V_NeuPair u a1 b1 _) :=
    check_equal_r (PProj PL u) a1 ltac:(check_equal_triv) && check_equal_r (PProj PR u) b1 ltac:(check_equal_triv);
  check_equal _ _ h V_NatNat := true;
  check_equal _ _ h V_ZeroZero := true;
  check_equal _ _ h (V_SucSuc a b) := check_equal_r a b ltac:(check_equal_triv);
  check_equal _ _ h (V_ProjProj p0 a p1 b) :=
    PTag_eqdec p0 p1 && check_equal a b ltac:(check_equal_triv);
  check_equal _ _ h (V_AppApp a0 b0 a1 b1) :=
    check_equal a0 a1 ltac:(check_equal_triv) && check_equal_r b0 b1 ltac:(check_equal_triv);
  check_equal _ _ h (V_IndInd P0 u0 b0 c0 P1 u1 b1 c1) :=
    check_equal_r P0 P1 ltac:(check_equal_triv) &&
      check_equal u0 u1 ltac:(check_equal_triv) &&
      check_equal_r b0 b1 ltac:(check_equal_triv) &&
      check_equal_r c0 c1 ltac:(check_equal_triv);
  check_equal _ _ h (V_UnivUniv i j) := nat_eqdec i j;
  check_equal _ _ h (V_BindBind p0 A0 B0 p1 A1 B1) :=
    BTag_eqdec p0 p1 && check_equal_r A0 A1 ltac:(check_equal_triv) && check_equal_r B0 B1 ltac:(check_equal_triv);
  check_equal _ _ _ _ := false

  (* check_equal a b h := false; *)
  with check_equal_r (a b : PTm) (h0 : algo_dom_r a b) :
  bool by struct h0 :=
    check_equal_r a b h with (fancy_hred a) :=
      check_equal_r a b h (inr a') := check_equal_r (proj1_sig a') b _;
      check_equal_r a b h (inl h')  with (fancy_hred b) :=
        | inr b' := check_equal_r a (proj1_sig b') _;
                 | inl h'' := check_equal a b _.

Next Obligation.
  intros.
  inversion h; subst => //=.
  exfalso. hauto l:on use:hred_complete unfold:HRed.nf.
  exfalso. hauto l:on use:hred_complete unfold:HRed.nf.
Defined.

Next Obligation.
  intros.
  destruct h.
  exfalso. sfirstorder use: algo_dom_no_hred.
  exfalso. sfirstorder.
  assert (  b' = b'0)by eauto using hred_deter. subst.
  apply h.
Defined.

Next Obligation.
  simpl. intros.
  inversion h; subst =>//=.
  exfalso. sfirstorder use:algo_dom_no_hred.
  move {h}.
  assert (a' = a'0) by eauto using hred_deter, hred_sound. by subst.
  exfalso. sfirstorder use:hne_no_hred, hf_no_hred.
Defined.


Lemma check_equal_abs_abs a b h : check_equal (PAbs a) (PAbs b) (A_AbsAbs a b h) = check_equal_r a b h.
Proof. reflexivity. Qed.

Lemma check_equal_abs_neu a u neu h : check_equal (PAbs a) u (A_AbsNeu a u neu h) = check_equal_r a (PApp (ren_PTm shift u) (VarPTm var_zero)) h.
Proof. case : u neu h => //=.  Qed.

Lemma check_equal_neu_abs a u neu h : check_equal u (PAbs a) (A_NeuAbs a u neu h) = check_equal_r (PApp (ren_PTm shift u) (VarPTm var_zero)) a h.
Proof. case : u neu h => //=.  Qed.

Lemma check_equal_pair_pair a0 b0 a1 b1 a h :
  check_equal (PPair a0 b0) (PPair a1 b1) (A_PairPair a0 a1 b0 b1 a h) =
    check_equal_r a0 a1 a && check_equal_r b0 b1 h.
Proof. reflexivity. Qed.

Lemma check_equal_pair_neu a0 a1 u neu h h'
  : check_equal (PPair a0 a1) u (A_PairNeu a0 a1 u neu h h') = check_equal_r a0 (PProj PL u) h && check_equal_r a1 (PProj PR u) h'.
Proof.
  case : u neu h h' => //=.
Qed.

Lemma check_equal_neu_pair a0 a1 u neu h h'
  : check_equal u (PPair a0 a1) (A_NeuPair a0 a1 u neu h h') = check_equal_r  (PProj PL u) a0 h && check_equal_r (PProj PR u) a1 h'.
Proof.
  case : u neu h h' => //=.
Qed.

Lemma check_equal_bind_bind p0 A0 B0 p1 A1 B1 h0 h1 :
  check_equal (PBind p0 A0 B0) (PBind p1 A1 B1) (A_BindCong p0 p1 A0 A1 B0 B1 h0 h1) =
    BTag_eqdec p0 p1 &&  check_equal_r A0 A1 h0 && check_equal_r  B0 B1 h1.
Proof. reflexivity. Qed.

Lemma check_equal_proj_proj p0 u0 p1 u1 neu0 neu1 h :
  check_equal (PProj p0 u0) (PProj p1 u1) (A_ProjCong p0 p1 u0 u1 neu0 neu1 h) =
    PTag_eqdec p0 p1 && check_equal u0 u1 h.
Proof. reflexivity. Qed.

Lemma check_equal_app_app u0 a0 u1 a1 hu0 hu1 hdom hdom' :
  check_equal (PApp u0 a0) (PApp u1 a1) (A_AppCong u0 u1 a0 a1 hu0 hu1 hdom hdom') =
    check_equal u0 u1 hdom && check_equal_r a0 a1 hdom'.
Proof. reflexivity. Qed.

Lemma check_equal_ind_ind P0 u0 b0 c0 P1 u1 b1 c1 neu0 neu1 domP domu domb domc :
  check_equal (PInd P0 u0 b0 c0) (PInd P1 u1 b1 c1)
    (A_IndCong P0 P1 u0 u1 b0 b1 c0 c1 neu0 neu1 domP domu domb domc) =
    check_equal_r P0 P1 domP && check_equal u0 u1 domu && check_equal_r b0 b1 domb && check_equal_r c0 c1 domc.
Proof. reflexivity. Qed.

Lemma hred_none a : HRed.nf a -> hred a = None.
Proof.
  destruct (hred a) eqn:eq;
  sfirstorder use:hred_complete, hred_sound.
Qed.

Lemma check_equal_nfnf a b dom : check_equal_r a b (A_NfNf a b dom) = check_equal a b dom.
Proof.
  have [h0 h1] : HRed.nf a /\ HRed.nf b by hauto l:on use:algo_dom_no_hred.
  have [h3 h4] : hred a = None /\ hred b = None by sfirstorder use:hf_no_hred, hne_no_hred, hred_none.
  simpl.
  rewrite /check_equal_r_functional.
  destruct (fancy_hred a).
  simpl.
  destruct (fancy_hred b).
  reflexivity.
  exfalso. hauto l:on use:hred_complete.
  exfalso. hauto l:on use:hred_complete.
Qed.

Lemma check_equal_hredl a b a' ha doma :
  check_equal_r a b (A_HRedL a a' b ha doma) = check_equal_r a' b doma.
Proof.
  simpl.
  rewrite /check_equal_r_functional.
  destruct (fancy_hred a).
  - hauto q:on unfold:HRed.nf.
  - destruct s as [x ?].
    rewrite /check_equal_r_functional.
    have ? : x = a' by eauto using hred_deter. subst.
    simpl.
    f_equal.
    apply PropExtensionality.proof_irrelevance.
Qed.

Lemma check_equal_hredr a b b' hu r a0 :
  check_equal_r a b (A_HRedR a b b' hu r a0) =
    check_equal_r a b' a0.
Proof.
  simpl. rewrite /check_equal_r_functional.
  destruct (fancy_hred a).
  - simpl.
    destruct (fancy_hred b) as [|[b'' hb']].
    + hauto lq:on unfold:HRed.nf.
    + simpl.
      have ? : (b'' = b') by eauto using hred_deter. subst.
      f_equal.
      apply PropExtensionality.proof_irrelevance.
  - exfalso.
    sfirstorder use:hne_no_hred, hf_no_hred.
Qed.

Lemma check_equal_univ i j :
  check_equal (PUniv i) (PUniv j) (A_UnivCong i j) = nat_eqdec i j.
Proof. reflexivity. Qed.

Lemma check_equal_conf a b nfa nfb nfab :
  check_equal a b (A_Conf a b nfa nfb nfab) = false.
Proof. destruct a; destruct b => //=. Qed.

#[export]Hint Rewrite check_equal_abs_abs check_equal_abs_neu check_equal_neu_abs check_equal_pair_pair check_equal_pair_neu check_equal_neu_pair check_equal_bind_bind check_equal_hredl check_equal_hredr check_equal_nfnf check_equal_conf : ce_prop.

Obligation Tactic := try solve [check_equal_triv | sfirstorder].

Program Fixpoint check_sub (q : bool) (a b : PTm) (h : algo_dom a b) {struct h} :=
  match a, b with
  | PBind PPi A0 B0, PBind PPi A1 B1 =>
      check_sub_r (negb q) A0 A1 _ && check_sub_r q B0 B1 _
  | PBind PSig A0 B0, PBind PSig A1 B1 =>
      check_sub_r q A0 A1 _ && check_sub_r q B0 B1 _
  | PUniv i, PUniv j =>
      if q then PeanoNat.Nat.leb i j else PeanoNat.Nat.leb j i
  | PNat, PNat => true
  | _ ,_ => ishne a && ishne b && check_equal a b h
  end
with check_sub_r (q : bool) (a b : PTm) (h : algo_dom_r a b) {struct h} :=
  match fancy_hred a with
  | inr a' => check_sub_r q (proj1_sig a') b _
  | inl ha' => match fancy_hred b with
            | inr b' => check_sub_r q a (proj1_sig b') _
            | inl hb' => check_sub q a b _
            end
  end.
Next Obligation.
  simpl. intros. clear Heq_anonymous.  destruct a' as [a' ha']. simpl.
  inversion h; subst => //=.
  exfalso. sfirstorder use:algo_dom_no_hred.
  assert (a' = a'0) by eauto using hred_deter. by subst.
  exfalso. sfirstorder.
Defined.

Next Obligation.
  simpl. intros. clear Heq_anonymous Heq_anonymous0.
  destruct b' as [b' hb']. simpl.
  inversion h; subst.
  - exfalso.
    sfirstorder use:algo_dom_no_hred.
  - exfalso.
    sfirstorder.
  - assert (b' = b'0) by eauto using hred_deter. by subst.
Defined.

(* Need to avoid ssreflect tactics since they generate terms that make the termination checker upset *)
Next Obligation.
  move => _ /= a b hdom ha _ hb _.
  inversion hdom; subst.
  - assumption.
  - exfalso; sfirstorder.
  - exfalso; sfirstorder.
Defined.

Lemma check_sub_pi_pi q A0 B0  A1 B1 h0 h1 :
  check_sub q (PBind PPi A0 B0) (PBind PPi A1 B1) (A_BindCong PPi PPi A0 A1 B0 B1 h0 h1) =
    check_sub_r (~~ q) A0 A1 h0 && check_sub_r q B0 B1 h1.
Proof. reflexivity. Qed.

Lemma check_sub_sig_sig q A0 B0  A1 B1 h0 h1 :
  check_sub q (PBind PSig A0 B0) (PBind PSig A1 B1) (A_BindCong PSig PSig A0 A1 B0 B1 h0 h1) =
    check_sub_r q A0 A1 h0 && check_sub_r q B0 B1 h1.
  reflexivity. Qed.

Lemma check_sub_univ_univ i j :
  check_sub true (PUniv i) (PUniv j) (A_UnivCong i j) = PeanoNat.Nat.leb i j.
Proof. reflexivity. Qed.

Lemma check_sub_univ_univ' i j :
  check_sub false (PUniv i) (PUniv j) (A_UnivCong i j) = PeanoNat.Nat.leb j i.
  reflexivity. Qed.

Lemma check_sub_nfnf q a b dom : check_sub_r q a b (A_NfNf a b dom) = check_sub q a b dom.
Proof.
  have [h0 h1] : HRed.nf a /\ HRed.nf b by hauto l:on use:algo_dom_no_hred.
  have [h3 h4] : hred a = None /\ hred b = None by sfirstorder use:hf_no_hred, hne_no_hred, hred_none.
  simpl.
  destruct (fancy_hred b)=>//=.
  destruct (fancy_hred a) =>//=.
  destruct s as [a' ha']. simpl.
  hauto l:on use:hred_complete.
  destruct s as [b' hb']. simpl.
  hauto l:on use:hred_complete.
Qed.

Lemma check_sub_hredl q a b a' ha doma :
  check_sub_r q a b (A_HRedL a a' b ha doma) = check_sub_r q a' b doma.
Proof.
  simpl.
  destruct (fancy_hred a).
  - hauto q:on unfold:HRed.nf.
  - destruct s as [x ?].
    have ? : x = a' by eauto using hred_deter. subst.
    simpl.
    f_equal.
    apply PropExtensionality.proof_irrelevance.
Qed.

Lemma check_sub_hredr q a b b' hu r a0 :
  check_sub_r q a b (A_HRedR a b b' hu r a0) =
    check_sub_r q a b' a0.
Proof.
  simpl.
  destruct (fancy_hred a).
  - simpl.
    destruct (fancy_hred b) as [|[b'' hb']].
    + hauto lq:on unfold:HRed.nf.
    + simpl.
      have ? : (b'' = b') by eauto using hred_deter. subst.
      f_equal.
      apply PropExtensionality.proof_irrelevance.
  - exfalso.
    sfirstorder use:hne_no_hred, hf_no_hred.
Qed.

#[export]Hint Rewrite check_sub_hredl check_sub_hredr check_sub_nfnf check_sub_univ_univ' check_sub_univ_univ check_sub_pi_pi check_sub_sig_sig : ce_prop.
