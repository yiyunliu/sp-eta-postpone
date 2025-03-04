Require Import Autosubst2.unscoped Autosubst2.syntax Autosubst2.core ssreflect.
From Ltac2 Require Ltac2.
Import Ltac2.Notations.
Import Ltac2.Control.
From Hammer Require Import Tactics.

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
End HRed.
