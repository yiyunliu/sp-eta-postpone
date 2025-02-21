Require Import Autosubst2.fintype Autosubst2.syntax ssreflect.
From Ltac2 Require Ltac2.
Import Ltac2.Notations.
Import Ltac2.Control.
From Hammer Require Import Tactics.

Definition renaming_ok {n m} (Γ : fin n -> PTm n) (Δ : fin m -> PTm m) (ξ : fin m -> fin n) :=
  forall (i : fin m), ren_PTm ξ (Δ i) = Γ (ξ i).

Lemma up_injective n m (ξ : fin n -> fin m) :
  (forall i j, ξ i = ξ j -> i = j) ->
  forall i j, (upRen_PTm_PTm ξ)  i = (upRen_PTm_PTm ξ) j -> i = j.
Proof.
  sblast inv:option.
Qed.

Local Ltac2 rec solve_anti_ren () :=
  let x := Fresh.in_goal (Option.get (Ident.of_string "x")) in
  intro $x;
  lazy_match! Constr.type (Control.hyp x) with
  | fin _ -> _ _ => (ltac1:(case;hauto lq:on rew:off use:up_injective))
  | _ => solve_anti_ren ()
  end.

Local Ltac solve_anti_ren := ltac2:(Control.enter solve_anti_ren).

Lemma ren_injective n m (a b : PTm n) (ξ : fin n -> fin m) :
  (forall i j, ξ i = ξ j -> i = j) ->
  ren_PTm ξ a = ren_PTm ξ b ->
  a = b.
Proof.
  move : m ξ b. elim : n / a => //; try solve_anti_ren.
Qed.

Definition ishf {n} (a : PTm n) :=
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

Fixpoint ishne {n} (a : PTm n) :=
  match a with
  | VarPTm _ => true
  | PApp a _ => ishne a
  | PProj _ a => ishne a
  | PBot => true
  | PInd _ n _ _ => ishne n
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

Definition ishne_ren n m (a : PTm n)  (ξ : fin n -> fin m) :
  ishne (ren_PTm ξ a) = ishne a.
Proof. move : m ξ. elim : n / a => //=. Qed.
