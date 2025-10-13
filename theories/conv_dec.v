(** * The Top-level definition of the decision procedure *)

Require Import executable executable_correct typing common soundness algorithmic
  logrel Autosubst2.syntax ssreflect fp_red.
From Hammer Require Import Tactics.

(** A simple wrapper over [check_sub_r] which turns the well-formedness of the inputs into
    a derivation of [salgo_dom_r], which [check_sub_r] recurses over. *)
Program Definition check_sub_r_wt {Γ A B i j} (h : Γ ⊢ A ∈ PUniv i) (h0 : Γ ⊢ B ∈ PUniv j) :=
  check_sub_r A B _.
Next Obligation.
  move => Γ A B i j h h0.
  have [? ?] : SN A /\ SN B by hauto use:soundness.fundamental_theorem, logrel.SemWt_SN.
  hauto lq:on use:sn_algo_dom, algo_dom_salgo_dom.
Qed.

(** [Conv_dec] composes everything we have proven so far to show that [check_sub_r_wt] agrees
    with the inductive definition of declarative subtyping. *)
Theorem Conv_dec Γ A B i j
  (h0 : Γ ⊢ A ∈ PUniv i )
  (h1 : Γ ⊢ B ∈ PUniv j ) :
  Bool.reflect (Γ ⊢ A ≲ B) (check_sub_r_wt h0 h1).
Proof.
  case E : (check_sub_r_wt h0 h1); rewrite /check_sub_r_wt in E; constructor.
  - eapply check_sub_sound in E.
    eauto using coqleq_sound.
  - move => h.
    eapply check_sub_complete in E.
    eauto using coqleq_complete.
Defined.
