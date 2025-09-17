Require Import Autosubst2.core Autosubst2.unscoped Autosubst2.syntax common.
Require Import ssreflect ssrbool.
Require Import Arith.PeanoNat (Nat.eq_dec).
From Ltac2 Require Import Ltac2.
Import Ltac2.Constr.
Set Default Proof Mode "Classic".


Require Import ssreflect ssrbool.
From Hammer Require Import Tactics.

Ltac2 destruct_algo () :=
  lazy_match! goal with
  | [_ : algo_dom ?a ?b |- _ ] =>
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

Global Set Transparent Obligations.

Local Obligation Tactic := try solve [sfirstorder | check_equal_triv ].

Scheme Equality for BTag.
Scheme Equality for PTag.

Program Fixpoint check_equal (a b : PTm) (h : algo_dom a b) {struct h} : bool :=
  match a, b with
  | VarPTm i, VarPTm j => Nat.eq_dec i j
  | PAbs a, PAbs b => check_equal_r a b _
  | PAbs a, VarPTm _ => check_equal_r a (PApp (ren_PTm shift b) (VarPTm var_zero)) _
  | PAbs a, PApp _ _ => check_equal_r a (PApp (ren_PTm shift b) (VarPTm var_zero)) _
  | PAbs a, PInd _ _ _ _ => check_equal_r a (PApp (ren_PTm shift b) (VarPTm var_zero)) _
  | PAbs a, PProj _ _ => check_equal_r a (PApp (ren_PTm shift b) (VarPTm var_zero)) _
  | VarPTm _, PAbs b => check_equal_r (PApp (ren_PTm shift a) (VarPTm var_zero)) b _
  | PApp _ _, PAbs b => check_equal_r (PApp (ren_PTm shift a) (VarPTm var_zero)) b _
  | PProj _ _, PAbs b => check_equal_r (PApp (ren_PTm shift a) (VarPTm var_zero)) b _
  | PInd _ _ _ _, PAbs b => check_equal_r (PApp (ren_PTm shift a) (VarPTm var_zero)) b _
  | PPair a0 b0, PPair a1 b1 =>
      check_equal_r a0 a1 _ && check_equal_r b0 b1 _
  | PPair a0 b0, VarPTm _ => check_equal_r a0 (PProj PL b) _ && check_equal_r b0 (PProj PR b) _
  | PPair a0 b0, PProj _ _ => check_equal_r a0 (PProj PL b) _ && check_equal_r b0 (PProj PR b) _
  | PPair a0 b0, PApp _ _ => check_equal_r a0 (PProj PL b) _ && check_equal_r b0 (PProj PR b) _
  | PPair a0 b0, PInd _ _ _ _ => check_equal_r a0 (PProj PL b) _ && check_equal_r b0 (PProj PR b) _
  | VarPTm _, PPair a1 b1 => check_equal_r (PProj PL a) a1 _ && check_equal_r (PProj PR a) b1 _
  | PApp _ _, PPair a1 b1 => check_equal_r (PProj PL a) a1 _ && check_equal_r (PProj PR a) b1 _
  | PProj _ _, PPair a1 b1 => check_equal_r (PProj PL a) a1 _ && check_equal_r (PProj PR a) b1 _
  | PInd _ _ _ _, PPair a1 b1 => check_equal_r (PProj PL a) a1 _ && check_equal_r (PProj PR a) b1 _
  | PNat, PNat => true
  | PZero, PZero => true
  | PSuc a, PSuc b => check_equal_r a b _
  | PProj p0 a, PProj p1 b => PTag_eq_dec p0 p1 && check_equal a b _
  | PApp a0 b0, PApp a1 b1 => check_equal a0 a1 _ && check_equal_r b0 b1 _
  | PInd P0 u0 b0 c0, PInd P1 u1 b1 c1 =>
      check_equal_r P0 P1 _ && check_equal u0 u1 _ && check_equal_r b0 b1 _ && check_equal_r c0 c1 _
  | PUniv i, PUniv j => Nat.eq_dec i j
  | PBind p0 A0 B0, PBind p1 A1 B1 => BTag_eq_dec p0 p1 && check_equal_r A0 A1 _ && check_equal_r B0 B1 _
  | _, _ => false

  end
with check_equal_r (a b : PTm) (h : algo_dom_r a b) {struct h} : bool :=
  match fancy_hred a with
  | inr a' => check_equal_r (proj1_sig a') b _
  | inl ha' => match fancy_hred b with
               | inr b' => check_equal_r a (proj1_sig b') _
            | inl hb' => check_equal a b _
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

(** Need to avoid ssreflect tactics since they generate terms that make the termination checker upset *)
Final Obligation.
  move => /= a b hdom ha _ hb _.
  inversion hdom; subst.
  - assumption.
  - exfalso; sfirstorder.
  - exfalso; sfirstorder.
Defined.

Ltac2 find_last_dom () :=
  intros;
  let (h, _, _) := List.find (fun (_,_,ty) =>
                                lazy_match! ty with
                                | algo_dom _ _ => true
                                | _ => false
                                end)
                     (List.rev (Control.hyps ())) in
  h.

Derive Dependent Inversion algo_dom_inv with (forall a b, algo_dom a b) Sort Prop.
Derive Dependent Inversion algo_dom_r_inv with (forall a b, algo_dom_r a b) Sort Prop.

Ltac2 apply_dom_inv () :=
  let last_dom := Control.hyp (find_last_dom ()) in
  apply algo_dom_inv with (H := $last_dom).

Ltac solve_check_equal_irrel := ltac2:(apply_dom_inv ()) => //=; hfcrush.

Lemma hred_none a : HRed.nf a -> hred a = None.
Proof.
  destruct (hred a) eqn:eq;
  sfirstorder use:hred_complete, hred_sound.
Qed.

Ltac simp_check_r := with_strategy opaque [check_equal] simpl in *.

Lemma check_equal_nfnf a b dom : check_equal_r a b (A_NfNf a b dom) = check_equal a b dom.
Proof.
  have [h0 h1] : HRed.nf a /\ HRed.nf b by hauto l:on use:algo_dom_no_hred.
  have [h3 h4] : hred a = None /\ hred b = None by sfirstorder use:hf_no_hred, hne_no_hred, hred_none.
  simp_check_r.
  destruct (fancy_hred a).
  destruct (fancy_hred b).
  reflexivity.
  exfalso. hauto l:on use:hred_complete.
  exfalso. hauto l:on use:hred_complete.
Qed.

Lemma check_equal_irrel :
  (forall a b (dom : algo_dom a b), forall dom', check_equal a b dom = check_equal a b dom') /\
    (forall a b (dom : algo_dom_r a b), forall dom', check_equal_r a b dom =  check_equal_r a b dom').
Proof.
  apply algo_dom_mutual.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - solve_check_equal_irrel.
  - move => a b dom ihdom dom'.
    apply algo_dom_r_inv with (H := dom').
    + move => _ ? ? h *. subst.
      rewrite !check_equal_nfnf.
      apply ihdom.
    + hauto lq:on use:algo_dom_no_hred unfold:HRed.nf.
    + hauto lq:on use:algo_dom_no_hred unfold:HRed.nf.
  - move => a a' b r dom ihdom dom'.
    apply algo_dom_r_inv with (H := dom') => _.
    + hauto lq:on use:algo_dom_no_hred unfold:HRed.nf.
    + move => a0 a'0 b0 r0 dom'' *. subst.
      have ? : a'0 = a' by eauto using hred_deter. subst.
      simpl.
      case : (fancy_hred a); first by hauto lq:on unfold:HRed.nf.
      case => x p. simpl. have ? : x = a' by eauto using hred_deter. subst.
      eauto.
    + hauto lq:on use:algo_dom_no_hred unfold:HRed.nf.
  - move => a a' b r hr dom ihdom dom'.
    apply algo_dom_r_inv with (H := dom').
    + hauto lq:on use:algo_dom_no_hred unfold:HRed.nf.
    + hauto lq:on use:algo_dom_no_hred unfold:HRed.nf.
    + case : (fancy_hred a); last by hauto lq:on unfold:HRed.nf.
      move => h0 h1 a0 b0 b' n r0 a1 ? ?. subst.
      have ? : b' = b by eauto using hred_deter. subst.
      simpl.
      case : (fancy_hred a); last by hauto lq:on unfold:HRed.nf.
      move => nf'.
      case : (fancy_hred a'); first by hauto lq:on unfold:HRed.nf.
      move => [b' h].
      have ? : b' = b  by eauto using hred_deter. subst.
      hauto lq:on.
Qed.

Lemma check_equal_hredl a b a' ha doma :
  check_equal_r a b (A_HRedL a a' b ha doma) = check_equal_r a' b doma.
Proof.
  simpl.
  destruct (fancy_hred a).
  - hauto q:on unfold:HRed.nf.
  - destruct s as [x ?].
    have ? : x = a' by eauto using hred_deter. subst.
    eapply check_equal_irrel.
Qed.

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
    BTag_eq_dec p0 p1 &&  check_equal_r A0 A1 h0 && check_equal_r  B0 B1 h1.
Proof. reflexivity. Qed.

Lemma check_equal_proj_proj p0 u0 p1 u1 neu0 neu1 h :
  check_equal (PProj p0 u0) (PProj p1 u1) (A_ProjCong p0 p1 u0 u1 neu0 neu1 h) =
    PTag_eq_dec p0 p1 && check_equal u0 u1 h.
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

Lemma check_equal_hredr a b b' hu r a0 :
  check_equal_r a b (A_HRedR a b b' hu r a0) =
    check_equal_r a b' a0.
Proof.
  simpl.
  destruct (fancy_hred a).
  - simpl.
    destruct (fancy_hred b) as [|[b'' hb']].
    + hauto lq:on unfold:HRed.nf.
    + simpl.
      have ? : (b'' = b') by eauto using hred_deter. subst.
      apply check_equal_irrel.
  - exfalso.
    sfirstorder use:hne_no_hred, hf_no_hred.
Qed.

Lemma check_equal_univ i j :
  check_equal (PUniv i) (PUniv j) (A_UnivCong i j) = Nat.eq_dec i j.
Proof. reflexivity. Qed.

Lemma check_equal_conf a b nfa nfb nfab :
  check_equal a b (A_Conf a b nfa nfb nfab) = false.
Proof. destruct a; destruct b => //=. Qed.

#[export]Hint Rewrite check_equal_abs_abs check_equal_abs_neu check_equal_neu_abs check_equal_pair_pair check_equal_pair_neu check_equal_neu_pair check_equal_bind_bind check_equal_hredl check_equal_hredr check_equal_nfnf check_equal_conf : ce_prop.

Ltac2 destruct_salgo () :=
  lazy_match! goal with
  | [_ : salgo_dom ?a ?b |- _ ] =>
      if is_var a then destruct $a; ltac1:(done)  else
        (if is_var b then destruct $b; ltac1:(done) else ())
  end.

Ltac check_sub_triv :=
  intros;subst;
  lazymatch goal with
  (* | [h : algo_dom (VarPTm _) (PAbs _) |- _] => idtac *)
  | [_ : salgo_dom _ _ |- _] => try (inversion h; subst => //=; ltac2:(Control.enter destruct_algo))
  | _ => idtac
  end.

Local Obligation Tactic := try solve [check_sub_triv | sfirstorder].

Program Fixpoint check_sub (a b : PTm) (h : salgo_dom a b) {struct h} :=
  match a, b with
  | PBind PPi A0 B0, PBind PPi A1 B1 =>
      check_sub_r A1 A0 _ && check_sub_r B0 B1 _
  | PBind PSig A0 B0, PBind PSig A1 B1 =>
      check_sub_r A0 A1 _ && check_sub_r B0 B1 _
  | PUniv i, PUniv j =>
      PeanoNat.Nat.leb i j
  | PNat, PNat => true
  | PApp _ _ , PApp _ _ => check_equal a b _
  | VarPTm _, VarPTm _ => check_equal a b _
  | PInd _ _ _ _, PInd _ _ _ _ => check_equal a b _
  | PProj _ _, PProj _ _ => check_equal a b _
  | _, _ => false
  end
with check_sub_r (a b : PTm) (h : salgo_dom_r a b) {struct h} :=
  match fancy_hred a with
  | inr a' => check_sub_r (proj1_sig a') b _
  | inl ha' => match fancy_hred b with
            | inr b' => check_sub_r a (proj1_sig b') _
            | inl hb' => check_sub  a b _
            end
  end.

Next Obligation.
  simpl. intros. clear Heq_anonymous.  destruct a' as [a' ha']. simpl.
  inversion h; subst => //=.
  exfalso. sfirstorder use:salgo_dom_no_hred.
  assert (a' = a'0) by eauto using hred_deter. by subst.
  exfalso. sfirstorder.
Defined.

Next Obligation.
  simpl. intros. clear Heq_anonymous Heq_anonymous0.
  destruct b' as [b' hb']. simpl.
  inversion h; subst.
  - exfalso.
    sfirstorder use:salgo_dom_no_hred.
  - exfalso.
    sfirstorder.
  - assert (b' = b'0) by eauto using hred_deter. by subst.
Defined.

(* Need to avoid ssreflect tactics since they generate terms that make the termination checker upset *)
Next Obligation.
  move => /= a b hdom ha _ hb _.
  inversion hdom; subst.
  - assumption.
  - exfalso; sfirstorder.
  - exfalso; sfirstorder.
Defined.

Lemma check_sub_pi_pi A0 B0  A1 B1 h0 h1 :
  check_sub (PBind PPi A0 B0) (PBind PPi A1 B1) (S_PiCong A0 A1 B0 B1 h0 h1) =
    check_sub_r A1 A0 h0 && check_sub_r B0 B1 h1.
Proof. reflexivity. Qed.

Lemma check_sub_sig_sig A0 B0  A1 B1 h0 h1 :
  check_sub (PBind PSig A0 B0) (PBind PSig A1 B1) (S_SigCong A0 A1 B0 B1 h0 h1) =
    check_sub_r A0 A1 h0 && check_sub_r B0 B1 h1.
Proof. reflexivity. Qed.

Lemma check_sub_univ_univ i j :
  check_sub (PUniv i) (PUniv j) (S_UnivCong i j) = PeanoNat.Nat.leb i j.
Proof. reflexivity. Qed.

Lemma check_sub_nfnf a b dom : check_sub_r a b (S_NfNf a b dom) = check_sub a b dom.
Proof.
  have [h0 h1] : HRed.nf a /\ HRed.nf b by hauto l:on use:salgo_dom_no_hred.
  have [h3 h4] : hred a = None /\ hred b = None by sfirstorder use:hf_no_hred, hne_no_hred, hred_none.
  simpl.
  destruct (fancy_hred b)=>//=.
  destruct (fancy_hred a) =>//=.
  destruct s as [a' ha']. simpl.
  hauto l:on use:hred_complete.
  destruct s as [b' hb']. simpl.
  hauto l:on use:hred_complete.
Qed.

Ltac2 find_last_sdom () :=
  intros;
  let (h, _, _) := List.find (fun (_,_,ty) =>
                                lazy_match! ty with
                                | salgo_dom _ _ => true
                                | _ => false
                                end)
                     (List.rev (Control.hyps ())) in h.

Derive Dependent Inversion salgo_dom_inv with (forall a b, salgo_dom a b) Sort Prop.
Derive Dependent Inversion salgo_dom_r_inv with (forall a b, salgo_dom_r a b) Sort Prop.

Ltac2 apply_sdom_inv () :=
  let last_dom := Control.hyp (find_last_sdom ()) in
  apply salgo_dom_inv with (H := $last_dom).

Ltac solve_check_sub_irrel := ltac2:(apply_sdom_inv ()) => //=; hfcrush.


Lemma check_sub_neuneu a b i a0 : check_sub a b (S_NeuNeu a b i a0) = check_equal a b a0.
Proof. destruct a,b => //=. Qed.

Lemma check_sub_conf a b n n0 i : check_sub a b (S_Conf a b n n0 i) = false.
Proof. destruct a,b=>//=; ecrush inv:BTag. Qed.

Lemma check_sub_irrel :
  (forall a b (dom : salgo_dom a b), forall dom', check_sub a b dom = check_sub a b dom') /\
    (forall a b (dom : salgo_dom_r a b), forall dom', check_sub_r a b dom =  check_sub_r a b dom').
Proof.
  apply salgo_dom_mutual.
  - solve_check_sub_irrel.
  - solve_check_sub_irrel.
  - solve_check_sub_irrel.
  - solve_check_sub_irrel.
  - ltac2:(apply_sdom_inv ()); try qauto.
    + intros. rewrite !check_sub_neuneu. apply check_equal_irrel.
    + hfcrush.
  - solve_check_sub_irrel.
  - move => a b dom ihdom dom'.
    apply salgo_dom_r_inv with (H := dom').
    + move => _ ? ? h *. subst.
      rewrite !check_sub_nfnf.
      apply ihdom.
    + hauto lq:on use:salgo_dom_no_hred unfold:HRed.nf.
    + hauto lq:on use:salgo_dom_no_hred unfold:HRed.nf.
  - move => a a' b r dom ihdom dom'.
    apply salgo_dom_r_inv with (H := dom') => _.
    + hauto lq:on use:salgo_dom_no_hred unfold:HRed.nf.
    + move => a0 a'0 b0 r0 dom'' *. subst.
      have ? : a'0 = a' by eauto using hred_deter. subst.
      simpl.
      case : (fancy_hred a); first by hauto lq:on unfold:HRed.nf.
      case => x p. simpl. have ? : x = a' by eauto using hred_deter. subst.
      eauto.
    + hauto lq:on use:salgo_dom_no_hred unfold:HRed.nf.
  - move => a a' b r hr dom ihdom dom'.
    apply salgo_dom_r_inv with (H := dom').
    + hauto lq:on use:salgo_dom_no_hred unfold:HRed.nf.
    + hauto lq:on use:salgo_dom_no_hred unfold:HRed.nf.
    + case : (fancy_hred a); last by hauto lq:on unfold:HRed.nf.
      move => h0 h1 a0 b0 b' n r0 a1 ? ?. subst.
      have ? : b' = b by eauto using hred_deter. subst.
      simpl.
      case : (fancy_hred a); last by hauto lq:on unfold:HRed.nf.
      move => nf'.
      case : (fancy_hred a'); first by hauto lq:on unfold:HRed.nf.
      move => [b' h].
      have ? : b' = b  by eauto using hred_deter. subst.
      hauto lq:on.
Qed.

Lemma check_sub_hredl a b a' ha doma :
  check_sub_r a b (S_HRedL a a' b ha doma) = check_sub_r a' b doma.
Proof.
  simpl.
  destruct (fancy_hred a).
  - hauto q:on unfold:HRed.nf.
  - destruct s as [x ?].
    have ? : x = a' by eauto using hred_deter. subst.
    simpl.
    apply check_sub_irrel.
Qed.

Lemma check_sub_hredr a b b' hu r a0 :
  check_sub_r a b (S_HRedR a b b' hu r a0) =
    check_sub_r a b' a0.
Proof.
  simpl.
  destruct (fancy_hred a).
  - simpl.
    destruct (fancy_hred b) as [|[b'' hb']].
    + hauto lq:on unfold:HRed.nf.
    + simpl.
      have ? : (b'' = b') by eauto using hred_deter. subst.
      apply check_sub_irrel.
  - exfalso.
    sfirstorder use:hne_no_hred, hf_no_hred.
Qed.

#[export]Hint Rewrite check_sub_neuneu check_sub_conf check_sub_hredl check_sub_hredr check_sub_nfnf check_sub_univ_univ check_sub_pi_pi check_sub_sig_sig : ce_prop.
