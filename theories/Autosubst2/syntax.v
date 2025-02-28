Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive BTag : Type :=
  | PPi : BTag
  | PSig : BTag.

Lemma congr_PPi : PPi = PPi.
Proof.
exact (eq_refl).
Qed.

Lemma congr_PSig : PSig = PSig.
Proof.
exact (eq_refl).
Qed.

Inductive PTag : Type :=
  | PL : PTag
  | PR : PTag.

Lemma congr_PL : PL = PL.
Proof.
exact (eq_refl).
Qed.

Lemma congr_PR : PR = PR.
Proof.
exact (eq_refl).
Qed.

Inductive PTm : Type :=
  | VarPTm : nat -> PTm
  | PAbs : PTm -> PTm
  | PApp : PTm -> PTm -> PTm
  | PPair : PTm -> PTm -> PTm
  | PProj : PTag -> PTm -> PTm
  | PBind : BTag -> PTm -> PTm -> PTm
  | PUniv : nat -> PTm
  | PBot : PTm
  | PNat : PTm
  | PZero : PTm
  | PSuc : PTm -> PTm
  | PInd : PTm -> PTm -> PTm -> PTm -> PTm.

Lemma congr_PAbs {s0 : PTm} {t0 : PTm} (H0 : s0 = t0) : PAbs s0 = PAbs t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => PAbs x) H0)).
Qed.

Lemma congr_PApp {s0 : PTm} {s1 : PTm} {t0 : PTm} {t1 : PTm} (H0 : s0 = t0)
  (H1 : s1 = t1) : PApp s0 s1 = PApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => PApp x s1) H0))
         (ap (fun x => PApp t0 x) H1)).
Qed.

Lemma congr_PPair {s0 : PTm} {s1 : PTm} {t0 : PTm} {t1 : PTm} (H0 : s0 = t0)
  (H1 : s1 = t1) : PPair s0 s1 = PPair t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => PPair x s1) H0))
         (ap (fun x => PPair t0 x) H1)).
Qed.

Lemma congr_PProj {s0 : PTag} {s1 : PTm} {t0 : PTag} {t1 : PTm}
  (H0 : s0 = t0) (H1 : s1 = t1) : PProj s0 s1 = PProj t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => PProj x s1) H0))
         (ap (fun x => PProj t0 x) H1)).
Qed.

Lemma congr_PBind {s0 : BTag} {s1 : PTm} {s2 : PTm} {t0 : BTag} {t1 : PTm}
  {t2 : PTm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  PBind s0 s1 s2 = PBind t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => PBind x s1 s2) H0))
            (ap (fun x => PBind t0 x s2) H1))
         (ap (fun x => PBind t0 t1 x) H2)).
Qed.

Lemma congr_PUniv {s0 : nat} {t0 : nat} (H0 : s0 = t0) : PUniv s0 = PUniv t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => PUniv x) H0)).
Qed.

Lemma congr_PBot : PBot = PBot.
Proof.
exact (eq_refl).
Qed.

Lemma congr_PNat : PNat = PNat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_PZero : PZero = PZero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_PSuc {s0 : PTm} {t0 : PTm} (H0 : s0 = t0) : PSuc s0 = PSuc t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => PSuc x) H0)).
Qed.

Lemma congr_PInd {s0 : PTm} {s1 : PTm} {s2 : PTm} {s3 : PTm} {t0 : PTm}
  {t1 : PTm} {t2 : PTm} {t3 : PTm} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) : PInd s0 s1 s2 s3 = PInd t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => PInd x s1 s2 s3) H0))
               (ap (fun x => PInd t0 x s2 s3) H1))
            (ap (fun x => PInd t0 t1 x s3) H2))
         (ap (fun x => PInd t0 t1 t2 x) H3)).
Qed.

Lemma upRen_PTm_PTm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_PTm (xi_PTm : nat -> nat) (s : PTm) {struct s} : PTm :=
  match s with
  | VarPTm s0 => VarPTm (xi_PTm s0)
  | PAbs s0 => PAbs (ren_PTm (upRen_PTm_PTm xi_PTm) s0)
  | PApp s0 s1 => PApp (ren_PTm xi_PTm s0) (ren_PTm xi_PTm s1)
  | PPair s0 s1 => PPair (ren_PTm xi_PTm s0) (ren_PTm xi_PTm s1)
  | PProj s0 s1 => PProj s0 (ren_PTm xi_PTm s1)
  | PBind s0 s1 s2 =>
      PBind s0 (ren_PTm xi_PTm s1) (ren_PTm (upRen_PTm_PTm xi_PTm) s2)
  | PUniv s0 => PUniv s0
  | PBot => PBot
  | PNat => PNat
  | PZero => PZero
  | PSuc s0 => PSuc (ren_PTm xi_PTm s0)
  | PInd s0 s1 s2 s3 =>
      PInd (ren_PTm (upRen_PTm_PTm xi_PTm) s0) (ren_PTm xi_PTm s1)
        (ren_PTm xi_PTm s2)
        (ren_PTm (upRen_PTm_PTm (upRen_PTm_PTm xi_PTm)) s3)
  end.

Lemma up_PTm_PTm (sigma : nat -> PTm) : nat -> PTm.
Proof.
exact (scons (VarPTm var_zero) (funcomp (ren_PTm shift) sigma)).
Defined.

Fixpoint subst_PTm (sigma_PTm : nat -> PTm) (s : PTm) {struct s} : PTm :=
  match s with
  | VarPTm s0 => sigma_PTm s0
  | PAbs s0 => PAbs (subst_PTm (up_PTm_PTm sigma_PTm) s0)
  | PApp s0 s1 => PApp (subst_PTm sigma_PTm s0) (subst_PTm sigma_PTm s1)
  | PPair s0 s1 => PPair (subst_PTm sigma_PTm s0) (subst_PTm sigma_PTm s1)
  | PProj s0 s1 => PProj s0 (subst_PTm sigma_PTm s1)
  | PBind s0 s1 s2 =>
      PBind s0 (subst_PTm sigma_PTm s1) (subst_PTm (up_PTm_PTm sigma_PTm) s2)
  | PUniv s0 => PUniv s0
  | PBot => PBot
  | PNat => PNat
  | PZero => PZero
  | PSuc s0 => PSuc (subst_PTm sigma_PTm s0)
  | PInd s0 s1 s2 s3 =>
      PInd (subst_PTm (up_PTm_PTm sigma_PTm) s0) (subst_PTm sigma_PTm s1)
        (subst_PTm sigma_PTm s2)
        (subst_PTm (up_PTm_PTm (up_PTm_PTm sigma_PTm)) s3)
  end.

Lemma upId_PTm_PTm (sigma : nat -> PTm) (Eq : forall x, sigma x = VarPTm x) :
  forall x, up_PTm_PTm sigma x = VarPTm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_PTm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_PTm (sigma_PTm : nat -> PTm)
(Eq_PTm : forall x, sigma_PTm x = VarPTm x) (s : PTm) {struct s} :
subst_PTm sigma_PTm s = s :=
  match s with
  | VarPTm s0 => Eq_PTm s0
  | PAbs s0 =>
      congr_PAbs
        (idSubst_PTm (up_PTm_PTm sigma_PTm) (upId_PTm_PTm _ Eq_PTm) s0)
  | PApp s0 s1 =>
      congr_PApp (idSubst_PTm sigma_PTm Eq_PTm s0)
        (idSubst_PTm sigma_PTm Eq_PTm s1)
  | PPair s0 s1 =>
      congr_PPair (idSubst_PTm sigma_PTm Eq_PTm s0)
        (idSubst_PTm sigma_PTm Eq_PTm s1)
  | PProj s0 s1 => congr_PProj (eq_refl s0) (idSubst_PTm sigma_PTm Eq_PTm s1)
  | PBind s0 s1 s2 =>
      congr_PBind (eq_refl s0) (idSubst_PTm sigma_PTm Eq_PTm s1)
        (idSubst_PTm (up_PTm_PTm sigma_PTm) (upId_PTm_PTm _ Eq_PTm) s2)
  | PUniv s0 => congr_PUniv (eq_refl s0)
  | PBot => congr_PBot
  | PNat => congr_PNat
  | PZero => congr_PZero
  | PSuc s0 => congr_PSuc (idSubst_PTm sigma_PTm Eq_PTm s0)
  | PInd s0 s1 s2 s3 =>
      congr_PInd
        (idSubst_PTm (up_PTm_PTm sigma_PTm) (upId_PTm_PTm _ Eq_PTm) s0)
        (idSubst_PTm sigma_PTm Eq_PTm s1) (idSubst_PTm sigma_PTm Eq_PTm s2)
        (idSubst_PTm (up_PTm_PTm (up_PTm_PTm sigma_PTm))
           (upId_PTm_PTm _ (upId_PTm_PTm _ Eq_PTm)) s3)
  end.

Lemma upExtRen_PTm_PTm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_PTm_PTm xi x = upRen_PTm_PTm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_PTm (xi_PTm : nat -> nat) (zeta_PTm : nat -> nat)
(Eq_PTm : forall x, xi_PTm x = zeta_PTm x) (s : PTm) {struct s} :
ren_PTm xi_PTm s = ren_PTm zeta_PTm s :=
  match s with
  | VarPTm s0 => ap (VarPTm) (Eq_PTm s0)
  | PAbs s0 =>
      congr_PAbs
        (extRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upExtRen_PTm_PTm _ _ Eq_PTm) s0)
  | PApp s0 s1 =>
      congr_PApp (extRen_PTm xi_PTm zeta_PTm Eq_PTm s0)
        (extRen_PTm xi_PTm zeta_PTm Eq_PTm s1)
  | PPair s0 s1 =>
      congr_PPair (extRen_PTm xi_PTm zeta_PTm Eq_PTm s0)
        (extRen_PTm xi_PTm zeta_PTm Eq_PTm s1)
  | PProj s0 s1 =>
      congr_PProj (eq_refl s0) (extRen_PTm xi_PTm zeta_PTm Eq_PTm s1)
  | PBind s0 s1 s2 =>
      congr_PBind (eq_refl s0) (extRen_PTm xi_PTm zeta_PTm Eq_PTm s1)
        (extRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upExtRen_PTm_PTm _ _ Eq_PTm) s2)
  | PUniv s0 => congr_PUniv (eq_refl s0)
  | PBot => congr_PBot
  | PNat => congr_PNat
  | PZero => congr_PZero
  | PSuc s0 => congr_PSuc (extRen_PTm xi_PTm zeta_PTm Eq_PTm s0)
  | PInd s0 s1 s2 s3 =>
      congr_PInd
        (extRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upExtRen_PTm_PTm _ _ Eq_PTm) s0)
        (extRen_PTm xi_PTm zeta_PTm Eq_PTm s1)
        (extRen_PTm xi_PTm zeta_PTm Eq_PTm s2)
        (extRen_PTm (upRen_PTm_PTm (upRen_PTm_PTm xi_PTm))
           (upRen_PTm_PTm (upRen_PTm_PTm zeta_PTm))
           (upExtRen_PTm_PTm _ _ (upExtRen_PTm_PTm _ _ Eq_PTm)) s3)
  end.

Lemma upExt_PTm_PTm (sigma : nat -> PTm) (tau : nat -> PTm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_PTm_PTm sigma x = up_PTm_PTm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_PTm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_PTm (sigma_PTm : nat -> PTm) (tau_PTm : nat -> PTm)
(Eq_PTm : forall x, sigma_PTm x = tau_PTm x) (s : PTm) {struct s} :
subst_PTm sigma_PTm s = subst_PTm tau_PTm s :=
  match s with
  | VarPTm s0 => Eq_PTm s0
  | PAbs s0 =>
      congr_PAbs
        (ext_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (upExt_PTm_PTm _ _ Eq_PTm) s0)
  | PApp s0 s1 =>
      congr_PApp (ext_PTm sigma_PTm tau_PTm Eq_PTm s0)
        (ext_PTm sigma_PTm tau_PTm Eq_PTm s1)
  | PPair s0 s1 =>
      congr_PPair (ext_PTm sigma_PTm tau_PTm Eq_PTm s0)
        (ext_PTm sigma_PTm tau_PTm Eq_PTm s1)
  | PProj s0 s1 =>
      congr_PProj (eq_refl s0) (ext_PTm sigma_PTm tau_PTm Eq_PTm s1)
  | PBind s0 s1 s2 =>
      congr_PBind (eq_refl s0) (ext_PTm sigma_PTm tau_PTm Eq_PTm s1)
        (ext_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (upExt_PTm_PTm _ _ Eq_PTm) s2)
  | PUniv s0 => congr_PUniv (eq_refl s0)
  | PBot => congr_PBot
  | PNat => congr_PNat
  | PZero => congr_PZero
  | PSuc s0 => congr_PSuc (ext_PTm sigma_PTm tau_PTm Eq_PTm s0)
  | PInd s0 s1 s2 s3 =>
      congr_PInd
        (ext_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (upExt_PTm_PTm _ _ Eq_PTm) s0)
        (ext_PTm sigma_PTm tau_PTm Eq_PTm s1)
        (ext_PTm sigma_PTm tau_PTm Eq_PTm s2)
        (ext_PTm (up_PTm_PTm (up_PTm_PTm sigma_PTm))
           (up_PTm_PTm (up_PTm_PTm tau_PTm))
           (upExt_PTm_PTm _ _ (upExt_PTm_PTm _ _ Eq_PTm)) s3)
  end.

Lemma up_ren_ren_PTm_PTm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_PTm_PTm zeta) (upRen_PTm_PTm xi) x = upRen_PTm_PTm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_PTm (xi_PTm : nat -> nat) (zeta_PTm : nat -> nat)
(rho_PTm : nat -> nat)
(Eq_PTm : forall x, funcomp zeta_PTm xi_PTm x = rho_PTm x) (s : PTm) {struct
 s} : ren_PTm zeta_PTm (ren_PTm xi_PTm s) = ren_PTm rho_PTm s :=
  match s with
  | VarPTm s0 => ap (VarPTm) (Eq_PTm s0)
  | PAbs s0 =>
      congr_PAbs
        (compRenRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upRen_PTm_PTm rho_PTm) (up_ren_ren _ _ _ Eq_PTm) s0)
  | PApp s0 s1 =>
      congr_PApp (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s0)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s1)
  | PPair s0 s1 =>
      congr_PPair (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s0)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s1)
  | PProj s0 s1 =>
      congr_PProj (eq_refl s0)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s1)
  | PBind s0 s1 s2 =>
      congr_PBind (eq_refl s0)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s1)
        (compRenRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upRen_PTm_PTm rho_PTm) (up_ren_ren _ _ _ Eq_PTm) s2)
  | PUniv s0 => congr_PUniv (eq_refl s0)
  | PBot => congr_PBot
  | PNat => congr_PNat
  | PZero => congr_PZero
  | PSuc s0 => congr_PSuc (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s0)
  | PInd s0 s1 s2 s3 =>
      congr_PInd
        (compRenRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upRen_PTm_PTm rho_PTm) (up_ren_ren _ _ _ Eq_PTm) s0)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s1)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s2)
        (compRenRen_PTm (upRen_PTm_PTm (upRen_PTm_PTm xi_PTm))
           (upRen_PTm_PTm (upRen_PTm_PTm zeta_PTm))
           (upRen_PTm_PTm (upRen_PTm_PTm rho_PTm))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_PTm)) s3)
  end.

Lemma up_ren_subst_PTm_PTm (xi : nat -> nat) (tau : nat -> PTm)
  (theta : nat -> PTm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_PTm_PTm tau) (upRen_PTm_PTm xi) x = up_PTm_PTm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_PTm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_PTm (xi_PTm : nat -> nat) (tau_PTm : nat -> PTm)
(theta_PTm : nat -> PTm)
(Eq_PTm : forall x, funcomp tau_PTm xi_PTm x = theta_PTm x) (s : PTm) {struct
 s} : subst_PTm tau_PTm (ren_PTm xi_PTm s) = subst_PTm theta_PTm s :=
  match s with
  | VarPTm s0 => Eq_PTm s0
  | PAbs s0 =>
      congr_PAbs
        (compRenSubst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_ren_subst_PTm_PTm _ _ _ Eq_PTm) s0)
  | PApp s0 s1 =>
      congr_PApp (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s0)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PPair s0 s1 =>
      congr_PPair (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s0)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PProj s0 s1 =>
      congr_PProj (eq_refl s0)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PBind s0 s1 s2 =>
      congr_PBind (eq_refl s0)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s1)
        (compRenSubst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_ren_subst_PTm_PTm _ _ _ Eq_PTm) s2)
  | PUniv s0 => congr_PUniv (eq_refl s0)
  | PBot => congr_PBot
  | PNat => congr_PNat
  | PZero => congr_PZero
  | PSuc s0 =>
      congr_PSuc (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s0)
  | PInd s0 s1 s2 s3 =>
      congr_PInd
        (compRenSubst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_ren_subst_PTm_PTm _ _ _ Eq_PTm) s0)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s1)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s2)
        (compRenSubst_PTm (upRen_PTm_PTm (upRen_PTm_PTm xi_PTm))
           (up_PTm_PTm (up_PTm_PTm tau_PTm))
           (up_PTm_PTm (up_PTm_PTm theta_PTm))
           (up_ren_subst_PTm_PTm _ _ _ (up_ren_subst_PTm_PTm _ _ _ Eq_PTm))
           s3)
  end.

Lemma up_subst_ren_PTm_PTm (sigma : nat -> PTm) (zeta_PTm : nat -> nat)
  (theta : nat -> PTm)
  (Eq : forall x, funcomp (ren_PTm zeta_PTm) sigma x = theta x) :
  forall x,
  funcomp (ren_PTm (upRen_PTm_PTm zeta_PTm)) (up_PTm_PTm sigma) x =
  up_PTm_PTm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_PTm shift (upRen_PTm_PTm zeta_PTm)
                (funcomp shift zeta_PTm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_PTm zeta_PTm shift (funcomp shift zeta_PTm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_PTm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_PTm (sigma_PTm : nat -> PTm) (zeta_PTm : nat -> nat)
(theta_PTm : nat -> PTm)
(Eq_PTm : forall x, funcomp (ren_PTm zeta_PTm) sigma_PTm x = theta_PTm x)
(s : PTm) {struct s} :
ren_PTm zeta_PTm (subst_PTm sigma_PTm s) = subst_PTm theta_PTm s :=
  match s with
  | VarPTm s0 => Eq_PTm s0
  | PAbs s0 =>
      congr_PAbs
        (compSubstRen_PTm (up_PTm_PTm sigma_PTm) (upRen_PTm_PTm zeta_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_ren_PTm_PTm _ _ _ Eq_PTm) s0)
  | PApp s0 s1 =>
      congr_PApp (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s0)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s1)
  | PPair s0 s1 =>
      congr_PPair (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s0)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s1)
  | PProj s0 s1 =>
      congr_PProj (eq_refl s0)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s1)
  | PBind s0 s1 s2 =>
      congr_PBind (eq_refl s0)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s1)
        (compSubstRen_PTm (up_PTm_PTm sigma_PTm) (upRen_PTm_PTm zeta_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_ren_PTm_PTm _ _ _ Eq_PTm) s2)
  | PUniv s0 => congr_PUniv (eq_refl s0)
  | PBot => congr_PBot
  | PNat => congr_PNat
  | PZero => congr_PZero
  | PSuc s0 =>
      congr_PSuc (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s0)
  | PInd s0 s1 s2 s3 =>
      congr_PInd
        (compSubstRen_PTm (up_PTm_PTm sigma_PTm) (upRen_PTm_PTm zeta_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_ren_PTm_PTm _ _ _ Eq_PTm) s0)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s1)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s2)
        (compSubstRen_PTm (up_PTm_PTm (up_PTm_PTm sigma_PTm))
           (upRen_PTm_PTm (upRen_PTm_PTm zeta_PTm))
           (up_PTm_PTm (up_PTm_PTm theta_PTm))
           (up_subst_ren_PTm_PTm _ _ _ (up_subst_ren_PTm_PTm _ _ _ Eq_PTm))
           s3)
  end.

Lemma up_subst_subst_PTm_PTm (sigma : nat -> PTm) (tau_PTm : nat -> PTm)
  (theta : nat -> PTm)
  (Eq : forall x, funcomp (subst_PTm tau_PTm) sigma x = theta x) :
  forall x,
  funcomp (subst_PTm (up_PTm_PTm tau_PTm)) (up_PTm_PTm sigma) x =
  up_PTm_PTm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_PTm shift (up_PTm_PTm tau_PTm)
                (funcomp (up_PTm_PTm tau_PTm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_PTm tau_PTm shift
                      (funcomp (ren_PTm shift) tau_PTm) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_PTm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_PTm (sigma_PTm : nat -> PTm) (tau_PTm : nat -> PTm)
(theta_PTm : nat -> PTm)
(Eq_PTm : forall x, funcomp (subst_PTm tau_PTm) sigma_PTm x = theta_PTm x)
(s : PTm) {struct s} :
subst_PTm tau_PTm (subst_PTm sigma_PTm s) = subst_PTm theta_PTm s :=
  match s with
  | VarPTm s0 => Eq_PTm s0
  | PAbs s0 =>
      congr_PAbs
        (compSubstSubst_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_subst_PTm_PTm _ _ _ Eq_PTm) s0)
  | PApp s0 s1 =>
      congr_PApp (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s0)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PPair s0 s1 =>
      congr_PPair (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s0)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PProj s0 s1 =>
      congr_PProj (eq_refl s0)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PBind s0 s1 s2 =>
      congr_PBind (eq_refl s0)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s1)
        (compSubstSubst_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_subst_PTm_PTm _ _ _ Eq_PTm) s2)
  | PUniv s0 => congr_PUniv (eq_refl s0)
  | PBot => congr_PBot
  | PNat => congr_PNat
  | PZero => congr_PZero
  | PSuc s0 =>
      congr_PSuc (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s0)
  | PInd s0 s1 s2 s3 =>
      congr_PInd
        (compSubstSubst_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_subst_PTm_PTm _ _ _ Eq_PTm) s0)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s1)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s2)
        (compSubstSubst_PTm (up_PTm_PTm (up_PTm_PTm sigma_PTm))
           (up_PTm_PTm (up_PTm_PTm tau_PTm))
           (up_PTm_PTm (up_PTm_PTm theta_PTm))
           (up_subst_subst_PTm_PTm _ _ _
              (up_subst_subst_PTm_PTm _ _ _ Eq_PTm)) s3)
  end.

Lemma renRen_PTm (xi_PTm : nat -> nat) (zeta_PTm : nat -> nat) (s : PTm) :
  ren_PTm zeta_PTm (ren_PTm xi_PTm s) = ren_PTm (funcomp zeta_PTm xi_PTm) s.
Proof.
exact (compRenRen_PTm xi_PTm zeta_PTm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_PTm_pointwise (xi_PTm : nat -> nat) (zeta_PTm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_PTm zeta_PTm) (ren_PTm xi_PTm))
    (ren_PTm (funcomp zeta_PTm xi_PTm)).
Proof.
exact (fun s => compRenRen_PTm xi_PTm zeta_PTm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_PTm (xi_PTm : nat -> nat) (tau_PTm : nat -> PTm) (s : PTm) :
  subst_PTm tau_PTm (ren_PTm xi_PTm s) = subst_PTm (funcomp tau_PTm xi_PTm) s.
Proof.
exact (compRenSubst_PTm xi_PTm tau_PTm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_PTm_pointwise (xi_PTm : nat -> nat) (tau_PTm : nat -> PTm) :
  pointwise_relation _ eq (funcomp (subst_PTm tau_PTm) (ren_PTm xi_PTm))
    (subst_PTm (funcomp tau_PTm xi_PTm)).
Proof.
exact (fun s => compRenSubst_PTm xi_PTm tau_PTm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_PTm (sigma_PTm : nat -> PTm) (zeta_PTm : nat -> nat) (s : PTm)
  :
  ren_PTm zeta_PTm (subst_PTm sigma_PTm s) =
  subst_PTm (funcomp (ren_PTm zeta_PTm) sigma_PTm) s.
Proof.
exact (compSubstRen_PTm sigma_PTm zeta_PTm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_PTm_pointwise (sigma_PTm : nat -> PTm) (zeta_PTm : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_PTm zeta_PTm) (subst_PTm sigma_PTm))
    (subst_PTm (funcomp (ren_PTm zeta_PTm) sigma_PTm)).
Proof.
exact (fun s => compSubstRen_PTm sigma_PTm zeta_PTm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_PTm (sigma_PTm : nat -> PTm) (tau_PTm : nat -> PTm)
  (s : PTm) :
  subst_PTm tau_PTm (subst_PTm sigma_PTm s) =
  subst_PTm (funcomp (subst_PTm tau_PTm) sigma_PTm) s.
Proof.
exact (compSubstSubst_PTm sigma_PTm tau_PTm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_PTm_pointwise (sigma_PTm : nat -> PTm)
  (tau_PTm : nat -> PTm) :
  pointwise_relation _ eq (funcomp (subst_PTm tau_PTm) (subst_PTm sigma_PTm))
    (subst_PTm (funcomp (subst_PTm tau_PTm) sigma_PTm)).
Proof.
exact (fun s => compSubstSubst_PTm sigma_PTm tau_PTm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_PTm_PTm (xi : nat -> nat) (sigma : nat -> PTm)
  (Eq : forall x, funcomp (VarPTm) xi x = sigma x) :
  forall x, funcomp (VarPTm) (upRen_PTm_PTm xi) x = up_PTm_PTm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_PTm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_PTm (xi_PTm : nat -> nat) (sigma_PTm : nat -> PTm)
(Eq_PTm : forall x, funcomp (VarPTm) xi_PTm x = sigma_PTm x) (s : PTm)
{struct s} : ren_PTm xi_PTm s = subst_PTm sigma_PTm s :=
  match s with
  | VarPTm s0 => Eq_PTm s0
  | PAbs s0 =>
      congr_PAbs
        (rinst_inst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm sigma_PTm)
           (rinstInst_up_PTm_PTm _ _ Eq_PTm) s0)
  | PApp s0 s1 =>
      congr_PApp (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s0)
        (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s1)
  | PPair s0 s1 =>
      congr_PPair (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s0)
        (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s1)
  | PProj s0 s1 =>
      congr_PProj (eq_refl s0) (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s1)
  | PBind s0 s1 s2 =>
      congr_PBind (eq_refl s0) (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s1)
        (rinst_inst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm sigma_PTm)
           (rinstInst_up_PTm_PTm _ _ Eq_PTm) s2)
  | PUniv s0 => congr_PUniv (eq_refl s0)
  | PBot => congr_PBot
  | PNat => congr_PNat
  | PZero => congr_PZero
  | PSuc s0 => congr_PSuc (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s0)
  | PInd s0 s1 s2 s3 =>
      congr_PInd
        (rinst_inst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm sigma_PTm)
           (rinstInst_up_PTm_PTm _ _ Eq_PTm) s0)
        (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s1)
        (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s2)
        (rinst_inst_PTm (upRen_PTm_PTm (upRen_PTm_PTm xi_PTm))
           (up_PTm_PTm (up_PTm_PTm sigma_PTm))
           (rinstInst_up_PTm_PTm _ _ (rinstInst_up_PTm_PTm _ _ Eq_PTm)) s3)
  end.

Lemma rinstInst'_PTm (xi_PTm : nat -> nat) (s : PTm) :
  ren_PTm xi_PTm s = subst_PTm (funcomp (VarPTm) xi_PTm) s.
Proof.
exact (rinst_inst_PTm xi_PTm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_PTm_pointwise (xi_PTm : nat -> nat) :
  pointwise_relation _ eq (ren_PTm xi_PTm)
    (subst_PTm (funcomp (VarPTm) xi_PTm)).
Proof.
exact (fun s => rinst_inst_PTm xi_PTm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_PTm (s : PTm) : subst_PTm (VarPTm) s = s.
Proof.
exact (idSubst_PTm (VarPTm) (fun n => eq_refl) s).
Qed.

Lemma instId'_PTm_pointwise : pointwise_relation _ eq (subst_PTm (VarPTm)) id.
Proof.
exact (fun s => idSubst_PTm (VarPTm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_PTm (s : PTm) : ren_PTm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_PTm s) (rinstInst'_PTm id s)).
Qed.

Lemma rinstId'_PTm_pointwise : pointwise_relation _ eq (@ren_PTm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_PTm s) (rinstInst'_PTm id s)).
Qed.

Lemma varL'_PTm (sigma_PTm : nat -> PTm) (x : nat) :
  subst_PTm sigma_PTm (VarPTm x) = sigma_PTm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_PTm_pointwise (sigma_PTm : nat -> PTm) :
  pointwise_relation _ eq (funcomp (subst_PTm sigma_PTm) (VarPTm)) sigma_PTm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_PTm (xi_PTm : nat -> nat) (x : nat) :
  ren_PTm xi_PTm (VarPTm x) = VarPTm (xi_PTm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_PTm_pointwise (xi_PTm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_PTm xi_PTm) (VarPTm))
    (funcomp (VarPTm) xi_PTm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_PTm X Y :=
    up_PTm : X -> Y.

#[global]Instance Subst_PTm : (Subst1 _ _ _) := @subst_PTm.

#[global]Instance Up_PTm_PTm : (Up_PTm _ _) := @up_PTm_PTm.

#[global]Instance Ren_PTm : (Ren1 _ _ _) := @ren_PTm.

#[global]
Instance VarInstance_PTm : (Var _ _) := @VarPTm.

Notation "[ sigma_PTm ]" := (subst_PTm sigma_PTm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_PTm ]" := (subst_PTm sigma_PTm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__PTm" := up_PTm (only printing)  : subst_scope.

Notation "↑__PTm" := up_PTm_PTm (only printing)  : subst_scope.

Notation "⟨ xi_PTm ⟩" := (ren_PTm xi_PTm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_PTm ⟩" := (ren_PTm xi_PTm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := VarPTm ( at level 1, only printing)  : subst_scope.

Notation "x '__PTm'" := (@ids _ _ VarInstance_PTm x)
( at level 5, format "x __PTm", only printing)  : subst_scope.

Notation "x '__PTm'" := (VarPTm x) ( at level 5, format "x __PTm")  :
subst_scope.

#[global]
Instance subst_PTm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_PTm)).
Proof.
exact (fun f_PTm g_PTm Eq_PTm s t Eq_st =>
       eq_ind s (fun t' => subst_PTm f_PTm s = subst_PTm g_PTm t')
         (ext_PTm f_PTm g_PTm Eq_PTm s) t Eq_st).
Qed.

#[global]
Instance subst_PTm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_PTm)).
Proof.
exact (fun f_PTm g_PTm Eq_PTm s => ext_PTm f_PTm g_PTm Eq_PTm s).
Qed.

#[global]
Instance ren_PTm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_PTm)).
Proof.
exact (fun f_PTm g_PTm Eq_PTm s t Eq_st =>
       eq_ind s (fun t' => ren_PTm f_PTm s = ren_PTm g_PTm t')
         (extRen_PTm f_PTm g_PTm Eq_PTm s) t Eq_st).
Qed.

#[global]
Instance ren_PTm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_PTm)).
Proof.
exact (fun f_PTm g_PTm Eq_PTm s => extRen_PTm f_PTm g_PTm Eq_PTm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_PTm, Var, ids, Ren_PTm, Ren1, ren1,
                      Up_PTm_PTm, Up_PTm, up_PTm, Subst_PTm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_PTm, Var, ids,
                                            Ren_PTm, Ren1, ren1, Up_PTm_PTm,
                                            Up_PTm, up_PTm, Subst_PTm,
                                            Subst1, subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_PTm_pointwise
                 | progress setoid_rewrite substSubst_PTm
                 | progress setoid_rewrite substRen_PTm_pointwise
                 | progress setoid_rewrite substRen_PTm
                 | progress setoid_rewrite renSubst_PTm_pointwise
                 | progress setoid_rewrite renSubst_PTm
                 | progress setoid_rewrite renRen'_PTm_pointwise
                 | progress setoid_rewrite renRen_PTm
                 | progress setoid_rewrite varLRen'_PTm_pointwise
                 | progress setoid_rewrite varLRen'_PTm
                 | progress setoid_rewrite varL'_PTm_pointwise
                 | progress setoid_rewrite varL'_PTm
                 | progress setoid_rewrite rinstId'_PTm_pointwise
                 | progress setoid_rewrite rinstId'_PTm
                 | progress setoid_rewrite instId'_PTm_pointwise
                 | progress setoid_rewrite instId'_PTm
                 | progress unfold up_PTm_PTm, upRen_PTm_PTm, up_ren
                 | progress cbn[subst_PTm ren_PTm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_PTm, Var, ids, Ren_PTm, Ren1, ren1,
                  Up_PTm_PTm, Up_PTm, up_PTm, Subst_PTm, Subst1, subst1 
                  in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_PTm_pointwise;
                  try setoid_rewrite rinstInst'_PTm.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_PTm_pointwise;
                  try setoid_rewrite_left rinstInst'_PTm.

End Core.

Module Extra.

Import Core.

#[global]Hint Opaque subst_PTm: rewrite.

#[global]Hint Opaque ren_PTm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

