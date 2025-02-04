Require Import core fintype.

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

Inductive PTm (n_PTm : nat) : Type :=
  | VarPTm : fin n_PTm -> PTm n_PTm
  | PAbs : PTm (S n_PTm) -> PTm n_PTm
  | PApp : PTm n_PTm -> PTm n_PTm -> PTm n_PTm
  | PPair : PTm n_PTm -> PTm n_PTm -> PTm n_PTm
  | PProj : PTag -> PTm n_PTm -> PTm n_PTm
  | PBind : BTag -> PTm n_PTm -> PTm (S n_PTm) -> PTm n_PTm
  | PUniv : nat -> PTm n_PTm.

Lemma congr_PAbs {m_PTm : nat} {s0 : PTm (S m_PTm)} {t0 : PTm (S m_PTm)}
  (H0 : s0 = t0) : PAbs m_PTm s0 = PAbs m_PTm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => PAbs m_PTm x) H0)).
Qed.

Lemma congr_PApp {m_PTm : nat} {s0 : PTm m_PTm} {s1 : PTm m_PTm}
  {t0 : PTm m_PTm} {t1 : PTm m_PTm} (H0 : s0 = t0) (H1 : s1 = t1) :
  PApp m_PTm s0 s1 = PApp m_PTm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => PApp m_PTm x s1) H0))
         (ap (fun x => PApp m_PTm t0 x) H1)).
Qed.

Lemma congr_PPair {m_PTm : nat} {s0 : PTm m_PTm} {s1 : PTm m_PTm}
  {t0 : PTm m_PTm} {t1 : PTm m_PTm} (H0 : s0 = t0) (H1 : s1 = t1) :
  PPair m_PTm s0 s1 = PPair m_PTm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => PPair m_PTm x s1) H0))
         (ap (fun x => PPair m_PTm t0 x) H1)).
Qed.

Lemma congr_PProj {m_PTm : nat} {s0 : PTag} {s1 : PTm m_PTm} {t0 : PTag}
  {t1 : PTm m_PTm} (H0 : s0 = t0) (H1 : s1 = t1) :
  PProj m_PTm s0 s1 = PProj m_PTm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => PProj m_PTm x s1) H0))
         (ap (fun x => PProj m_PTm t0 x) H1)).
Qed.

Lemma congr_PBind {m_PTm : nat} {s0 : BTag} {s1 : PTm m_PTm}
  {s2 : PTm (S m_PTm)} {t0 : BTag} {t1 : PTm m_PTm} {t2 : PTm (S m_PTm)}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  PBind m_PTm s0 s1 s2 = PBind m_PTm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => PBind m_PTm x s1 s2) H0))
            (ap (fun x => PBind m_PTm t0 x s2) H1))
         (ap (fun x => PBind m_PTm t0 t1 x) H2)).
Qed.

Lemma congr_PUniv {m_PTm : nat} {s0 : nat} {t0 : nat} (H0 : s0 = t0) :
  PUniv m_PTm s0 = PUniv m_PTm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => PUniv m_PTm x) H0)).
Qed.

Lemma upRen_PTm_PTm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_PTm_PTm (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n)
  : fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_PTm {m_PTm : nat} {n_PTm : nat}
(xi_PTm : fin m_PTm -> fin n_PTm) (s : PTm m_PTm) {struct s} : PTm n_PTm :=
  match s with
  | VarPTm _ s0 => VarPTm n_PTm (xi_PTm s0)
  | PAbs _ s0 => PAbs n_PTm (ren_PTm (upRen_PTm_PTm xi_PTm) s0)
  | PApp _ s0 s1 => PApp n_PTm (ren_PTm xi_PTm s0) (ren_PTm xi_PTm s1)
  | PPair _ s0 s1 => PPair n_PTm (ren_PTm xi_PTm s0) (ren_PTm xi_PTm s1)
  | PProj _ s0 s1 => PProj n_PTm s0 (ren_PTm xi_PTm s1)
  | PBind _ s0 s1 s2 =>
      PBind n_PTm s0 (ren_PTm xi_PTm s1) (ren_PTm (upRen_PTm_PTm xi_PTm) s2)
  | PUniv _ s0 => PUniv n_PTm s0
  end.

Lemma up_PTm_PTm {m : nat} {n_PTm : nat} (sigma : fin m -> PTm n_PTm) :
  fin (S m) -> PTm (S n_PTm).
Proof.
exact (scons (VarPTm (S n_PTm) var_zero) (funcomp (ren_PTm shift) sigma)).
Defined.

Lemma up_list_PTm_PTm (p : nat) {m : nat} {n_PTm : nat}
  (sigma : fin m -> PTm n_PTm) : fin (plus p m) -> PTm (plus p n_PTm).
Proof.
exact (scons_p p (funcomp (VarPTm (plus p n_PTm)) (zero_p p))
         (funcomp (ren_PTm (shift_p p)) sigma)).
Defined.

Fixpoint subst_PTm {m_PTm : nat} {n_PTm : nat}
(sigma_PTm : fin m_PTm -> PTm n_PTm) (s : PTm m_PTm) {struct s} : PTm n_PTm
:=
  match s with
  | VarPTm _ s0 => sigma_PTm s0
  | PAbs _ s0 => PAbs n_PTm (subst_PTm (up_PTm_PTm sigma_PTm) s0)
  | PApp _ s0 s1 =>
      PApp n_PTm (subst_PTm sigma_PTm s0) (subst_PTm sigma_PTm s1)
  | PPair _ s0 s1 =>
      PPair n_PTm (subst_PTm sigma_PTm s0) (subst_PTm sigma_PTm s1)
  | PProj _ s0 s1 => PProj n_PTm s0 (subst_PTm sigma_PTm s1)
  | PBind _ s0 s1 s2 =>
      PBind n_PTm s0 (subst_PTm sigma_PTm s1)
        (subst_PTm (up_PTm_PTm sigma_PTm) s2)
  | PUniv _ s0 => PUniv n_PTm s0
  end.

Lemma upId_PTm_PTm {m_PTm : nat} (sigma : fin m_PTm -> PTm m_PTm)
  (Eq : forall x, sigma x = VarPTm m_PTm x) :
  forall x, up_PTm_PTm sigma x = VarPTm (S m_PTm) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_PTm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_PTm_PTm {p : nat} {m_PTm : nat}
  (sigma : fin m_PTm -> PTm m_PTm) (Eq : forall x, sigma x = VarPTm m_PTm x)
  : forall x, up_list_PTm_PTm p sigma x = VarPTm (plus p m_PTm) x.
Proof.
exact (fun n =>
       scons_p_eta (VarPTm (plus p m_PTm))
         (fun n => ap (ren_PTm (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_PTm {m_PTm : nat} (sigma_PTm : fin m_PTm -> PTm m_PTm)
(Eq_PTm : forall x, sigma_PTm x = VarPTm m_PTm x) (s : PTm m_PTm) {struct s}
   : subst_PTm sigma_PTm s = s :=
  match s with
  | VarPTm _ s0 => Eq_PTm s0
  | PAbs _ s0 =>
      congr_PAbs
        (idSubst_PTm (up_PTm_PTm sigma_PTm) (upId_PTm_PTm _ Eq_PTm) s0)
  | PApp _ s0 s1 =>
      congr_PApp (idSubst_PTm sigma_PTm Eq_PTm s0)
        (idSubst_PTm sigma_PTm Eq_PTm s1)
  | PPair _ s0 s1 =>
      congr_PPair (idSubst_PTm sigma_PTm Eq_PTm s0)
        (idSubst_PTm sigma_PTm Eq_PTm s1)
  | PProj _ s0 s1 =>
      congr_PProj (eq_refl s0) (idSubst_PTm sigma_PTm Eq_PTm s1)
  | PBind _ s0 s1 s2 =>
      congr_PBind (eq_refl s0) (idSubst_PTm sigma_PTm Eq_PTm s1)
        (idSubst_PTm (up_PTm_PTm sigma_PTm) (upId_PTm_PTm _ Eq_PTm) s2)
  | PUniv _ s0 => congr_PUniv (eq_refl s0)
  end.

Lemma upExtRen_PTm_PTm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_PTm_PTm xi x = upRen_PTm_PTm zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_PTm_PTm {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_PTm_PTm p xi x = upRen_list_PTm_PTm p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_PTm {m_PTm : nat} {n_PTm : nat}
(xi_PTm : fin m_PTm -> fin n_PTm) (zeta_PTm : fin m_PTm -> fin n_PTm)
(Eq_PTm : forall x, xi_PTm x = zeta_PTm x) (s : PTm m_PTm) {struct s} :
ren_PTm xi_PTm s = ren_PTm zeta_PTm s :=
  match s with
  | VarPTm _ s0 => ap (VarPTm n_PTm) (Eq_PTm s0)
  | PAbs _ s0 =>
      congr_PAbs
        (extRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upExtRen_PTm_PTm _ _ Eq_PTm) s0)
  | PApp _ s0 s1 =>
      congr_PApp (extRen_PTm xi_PTm zeta_PTm Eq_PTm s0)
        (extRen_PTm xi_PTm zeta_PTm Eq_PTm s1)
  | PPair _ s0 s1 =>
      congr_PPair (extRen_PTm xi_PTm zeta_PTm Eq_PTm s0)
        (extRen_PTm xi_PTm zeta_PTm Eq_PTm s1)
  | PProj _ s0 s1 =>
      congr_PProj (eq_refl s0) (extRen_PTm xi_PTm zeta_PTm Eq_PTm s1)
  | PBind _ s0 s1 s2 =>
      congr_PBind (eq_refl s0) (extRen_PTm xi_PTm zeta_PTm Eq_PTm s1)
        (extRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upExtRen_PTm_PTm _ _ Eq_PTm) s2)
  | PUniv _ s0 => congr_PUniv (eq_refl s0)
  end.

Lemma upExt_PTm_PTm {m : nat} {n_PTm : nat} (sigma : fin m -> PTm n_PTm)
  (tau : fin m -> PTm n_PTm) (Eq : forall x, sigma x = tau x) :
  forall x, up_PTm_PTm sigma x = up_PTm_PTm tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_PTm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_PTm_PTm {p : nat} {m : nat} {n_PTm : nat}
  (sigma : fin m -> PTm n_PTm) (tau : fin m -> PTm n_PTm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_PTm_PTm p sigma x = up_list_PTm_PTm p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_PTm (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_PTm {m_PTm : nat} {n_PTm : nat}
(sigma_PTm : fin m_PTm -> PTm n_PTm) (tau_PTm : fin m_PTm -> PTm n_PTm)
(Eq_PTm : forall x, sigma_PTm x = tau_PTm x) (s : PTm m_PTm) {struct s} :
subst_PTm sigma_PTm s = subst_PTm tau_PTm s :=
  match s with
  | VarPTm _ s0 => Eq_PTm s0
  | PAbs _ s0 =>
      congr_PAbs
        (ext_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (upExt_PTm_PTm _ _ Eq_PTm) s0)
  | PApp _ s0 s1 =>
      congr_PApp (ext_PTm sigma_PTm tau_PTm Eq_PTm s0)
        (ext_PTm sigma_PTm tau_PTm Eq_PTm s1)
  | PPair _ s0 s1 =>
      congr_PPair (ext_PTm sigma_PTm tau_PTm Eq_PTm s0)
        (ext_PTm sigma_PTm tau_PTm Eq_PTm s1)
  | PProj _ s0 s1 =>
      congr_PProj (eq_refl s0) (ext_PTm sigma_PTm tau_PTm Eq_PTm s1)
  | PBind _ s0 s1 s2 =>
      congr_PBind (eq_refl s0) (ext_PTm sigma_PTm tau_PTm Eq_PTm s1)
        (ext_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (upExt_PTm_PTm _ _ Eq_PTm) s2)
  | PUniv _ s0 => congr_PUniv (eq_refl s0)
  end.

Lemma up_ren_ren_PTm_PTm {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_PTm_PTm zeta) (upRen_PTm_PTm xi) x = upRen_PTm_PTm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_PTm_PTm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_PTm_PTm p zeta) (upRen_list_PTm_PTm p xi) x =
  upRen_list_PTm_PTm p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_PTm {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
(xi_PTm : fin m_PTm -> fin k_PTm) (zeta_PTm : fin k_PTm -> fin l_PTm)
(rho_PTm : fin m_PTm -> fin l_PTm)
(Eq_PTm : forall x, funcomp zeta_PTm xi_PTm x = rho_PTm x) (s : PTm m_PTm)
{struct s} : ren_PTm zeta_PTm (ren_PTm xi_PTm s) = ren_PTm rho_PTm s :=
  match s with
  | VarPTm _ s0 => ap (VarPTm l_PTm) (Eq_PTm s0)
  | PAbs _ s0 =>
      congr_PAbs
        (compRenRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upRen_PTm_PTm rho_PTm) (up_ren_ren _ _ _ Eq_PTm) s0)
  | PApp _ s0 s1 =>
      congr_PApp (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s0)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s1)
  | PPair _ s0 s1 =>
      congr_PPair (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s0)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s1)
  | PProj _ s0 s1 =>
      congr_PProj (eq_refl s0)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s1)
  | PBind _ s0 s1 s2 =>
      congr_PBind (eq_refl s0)
        (compRenRen_PTm xi_PTm zeta_PTm rho_PTm Eq_PTm s1)
        (compRenRen_PTm (upRen_PTm_PTm xi_PTm) (upRen_PTm_PTm zeta_PTm)
           (upRen_PTm_PTm rho_PTm) (up_ren_ren _ _ _ Eq_PTm) s2)
  | PUniv _ s0 => congr_PUniv (eq_refl s0)
  end.

Lemma up_ren_subst_PTm_PTm {k : nat} {l : nat} {m_PTm : nat}
  (xi : fin k -> fin l) (tau : fin l -> PTm m_PTm)
  (theta : fin k -> PTm m_PTm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_PTm_PTm tau) (upRen_PTm_PTm xi) x = up_PTm_PTm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_PTm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_PTm_PTm {p : nat} {k : nat} {l : nat} {m_PTm : nat}
  (xi : fin k -> fin l) (tau : fin l -> PTm m_PTm)
  (theta : fin k -> PTm m_PTm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_PTm_PTm p tau) (upRen_list_PTm_PTm p xi) x =
  up_list_PTm_PTm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_PTm (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_PTm {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
(xi_PTm : fin m_PTm -> fin k_PTm) (tau_PTm : fin k_PTm -> PTm l_PTm)
(theta_PTm : fin m_PTm -> PTm l_PTm)
(Eq_PTm : forall x, funcomp tau_PTm xi_PTm x = theta_PTm x) (s : PTm m_PTm)
{struct s} : subst_PTm tau_PTm (ren_PTm xi_PTm s) = subst_PTm theta_PTm s :=
  match s with
  | VarPTm _ s0 => Eq_PTm s0
  | PAbs _ s0 =>
      congr_PAbs
        (compRenSubst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_ren_subst_PTm_PTm _ _ _ Eq_PTm) s0)
  | PApp _ s0 s1 =>
      congr_PApp (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s0)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PPair _ s0 s1 =>
      congr_PPair (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s0)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PProj _ s0 s1 =>
      congr_PProj (eq_refl s0)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PBind _ s0 s1 s2 =>
      congr_PBind (eq_refl s0)
        (compRenSubst_PTm xi_PTm tau_PTm theta_PTm Eq_PTm s1)
        (compRenSubst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_ren_subst_PTm_PTm _ _ _ Eq_PTm) s2)
  | PUniv _ s0 => congr_PUniv (eq_refl s0)
  end.

Lemma up_subst_ren_PTm_PTm {k : nat} {l_PTm : nat} {m_PTm : nat}
  (sigma : fin k -> PTm l_PTm) (zeta_PTm : fin l_PTm -> fin m_PTm)
  (theta : fin k -> PTm m_PTm)
  (Eq : forall x, funcomp (ren_PTm zeta_PTm) sigma x = theta x) :
  forall x,
  funcomp (ren_PTm (upRen_PTm_PTm zeta_PTm)) (up_PTm_PTm sigma) x =
  up_PTm_PTm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_PTm shift (upRen_PTm_PTm zeta_PTm)
                (funcomp shift zeta_PTm) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_PTm zeta_PTm shift (funcomp shift zeta_PTm)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_PTm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_PTm_PTm {p : nat} {k : nat} {l_PTm : nat}
  {m_PTm : nat} (sigma : fin k -> PTm l_PTm)
  (zeta_PTm : fin l_PTm -> fin m_PTm) (theta : fin k -> PTm m_PTm)
  (Eq : forall x, funcomp (ren_PTm zeta_PTm) sigma x = theta x) :
  forall x,
  funcomp (ren_PTm (upRen_list_PTm_PTm p zeta_PTm)) (up_list_PTm_PTm p sigma)
    x = up_list_PTm_PTm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (VarPTm (plus p m_PTm)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_PTm (shift_p p) (upRen_list_PTm_PTm p zeta_PTm)
                  (funcomp (shift_p p) zeta_PTm)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_PTm zeta_PTm (shift_p p)
                        (funcomp (shift_p p) zeta_PTm) (fun x => eq_refl)
                        (sigma n))) (ap (ren_PTm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_PTm {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
(sigma_PTm : fin m_PTm -> PTm k_PTm) (zeta_PTm : fin k_PTm -> fin l_PTm)
(theta_PTm : fin m_PTm -> PTm l_PTm)
(Eq_PTm : forall x, funcomp (ren_PTm zeta_PTm) sigma_PTm x = theta_PTm x)
(s : PTm m_PTm) {struct s} :
ren_PTm zeta_PTm (subst_PTm sigma_PTm s) = subst_PTm theta_PTm s :=
  match s with
  | VarPTm _ s0 => Eq_PTm s0
  | PAbs _ s0 =>
      congr_PAbs
        (compSubstRen_PTm (up_PTm_PTm sigma_PTm) (upRen_PTm_PTm zeta_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_ren_PTm_PTm _ _ _ Eq_PTm) s0)
  | PApp _ s0 s1 =>
      congr_PApp (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s0)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s1)
  | PPair _ s0 s1 =>
      congr_PPair (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s0)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s1)
  | PProj _ s0 s1 =>
      congr_PProj (eq_refl s0)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s1)
  | PBind _ s0 s1 s2 =>
      congr_PBind (eq_refl s0)
        (compSubstRen_PTm sigma_PTm zeta_PTm theta_PTm Eq_PTm s1)
        (compSubstRen_PTm (up_PTm_PTm sigma_PTm) (upRen_PTm_PTm zeta_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_ren_PTm_PTm _ _ _ Eq_PTm) s2)
  | PUniv _ s0 => congr_PUniv (eq_refl s0)
  end.

Lemma up_subst_subst_PTm_PTm {k : nat} {l_PTm : nat} {m_PTm : nat}
  (sigma : fin k -> PTm l_PTm) (tau_PTm : fin l_PTm -> PTm m_PTm)
  (theta : fin k -> PTm m_PTm)
  (Eq : forall x, funcomp (subst_PTm tau_PTm) sigma x = theta x) :
  forall x,
  funcomp (subst_PTm (up_PTm_PTm tau_PTm)) (up_PTm_PTm sigma) x =
  up_PTm_PTm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_PTm shift (up_PTm_PTm tau_PTm)
                (funcomp (up_PTm_PTm tau_PTm) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_PTm tau_PTm shift
                      (funcomp (ren_PTm shift) tau_PTm) (fun x => eq_refl)
                      (sigma fin_n))) (ap (ren_PTm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_PTm_PTm {p : nat} {k : nat} {l_PTm : nat}
  {m_PTm : nat} (sigma : fin k -> PTm l_PTm)
  (tau_PTm : fin l_PTm -> PTm m_PTm) (theta : fin k -> PTm m_PTm)
  (Eq : forall x, funcomp (subst_PTm tau_PTm) sigma x = theta x) :
  forall x,
  funcomp (subst_PTm (up_list_PTm_PTm p tau_PTm)) (up_list_PTm_PTm p sigma) x =
  up_list_PTm_PTm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (VarPTm (plus p l_PTm)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_PTm (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_PTm (shift_p p) (up_list_PTm_PTm p tau_PTm)
                  (funcomp (up_list_PTm_PTm p tau_PTm) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_PTm tau_PTm (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_PTm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_PTm {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
(sigma_PTm : fin m_PTm -> PTm k_PTm) (tau_PTm : fin k_PTm -> PTm l_PTm)
(theta_PTm : fin m_PTm -> PTm l_PTm)
(Eq_PTm : forall x, funcomp (subst_PTm tau_PTm) sigma_PTm x = theta_PTm x)
(s : PTm m_PTm) {struct s} :
subst_PTm tau_PTm (subst_PTm sigma_PTm s) = subst_PTm theta_PTm s :=
  match s with
  | VarPTm _ s0 => Eq_PTm s0
  | PAbs _ s0 =>
      congr_PAbs
        (compSubstSubst_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_subst_PTm_PTm _ _ _ Eq_PTm) s0)
  | PApp _ s0 s1 =>
      congr_PApp (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s0)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PPair _ s0 s1 =>
      congr_PPair (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s0)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PProj _ s0 s1 =>
      congr_PProj (eq_refl s0)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s1)
  | PBind _ s0 s1 s2 =>
      congr_PBind (eq_refl s0)
        (compSubstSubst_PTm sigma_PTm tau_PTm theta_PTm Eq_PTm s1)
        (compSubstSubst_PTm (up_PTm_PTm sigma_PTm) (up_PTm_PTm tau_PTm)
           (up_PTm_PTm theta_PTm) (up_subst_subst_PTm_PTm _ _ _ Eq_PTm) s2)
  | PUniv _ s0 => congr_PUniv (eq_refl s0)
  end.

Lemma renRen_PTm {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
  (xi_PTm : fin m_PTm -> fin k_PTm) (zeta_PTm : fin k_PTm -> fin l_PTm)
  (s : PTm m_PTm) :
  ren_PTm zeta_PTm (ren_PTm xi_PTm s) = ren_PTm (funcomp zeta_PTm xi_PTm) s.
Proof.
exact (compRenRen_PTm xi_PTm zeta_PTm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_PTm_pointwise {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
  (xi_PTm : fin m_PTm -> fin k_PTm) (zeta_PTm : fin k_PTm -> fin l_PTm) :
  pointwise_relation _ eq (funcomp (ren_PTm zeta_PTm) (ren_PTm xi_PTm))
    (ren_PTm (funcomp zeta_PTm xi_PTm)).
Proof.
exact (fun s => compRenRen_PTm xi_PTm zeta_PTm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_PTm {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
  (xi_PTm : fin m_PTm -> fin k_PTm) (tau_PTm : fin k_PTm -> PTm l_PTm)
  (s : PTm m_PTm) :
  subst_PTm tau_PTm (ren_PTm xi_PTm s) = subst_PTm (funcomp tau_PTm xi_PTm) s.
Proof.
exact (compRenSubst_PTm xi_PTm tau_PTm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_PTm_pointwise {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
  (xi_PTm : fin m_PTm -> fin k_PTm) (tau_PTm : fin k_PTm -> PTm l_PTm) :
  pointwise_relation _ eq (funcomp (subst_PTm tau_PTm) (ren_PTm xi_PTm))
    (subst_PTm (funcomp tau_PTm xi_PTm)).
Proof.
exact (fun s => compRenSubst_PTm xi_PTm tau_PTm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_PTm {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
  (sigma_PTm : fin m_PTm -> PTm k_PTm) (zeta_PTm : fin k_PTm -> fin l_PTm)
  (s : PTm m_PTm) :
  ren_PTm zeta_PTm (subst_PTm sigma_PTm s) =
  subst_PTm (funcomp (ren_PTm zeta_PTm) sigma_PTm) s.
Proof.
exact (compSubstRen_PTm sigma_PTm zeta_PTm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_PTm_pointwise {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
  (sigma_PTm : fin m_PTm -> PTm k_PTm) (zeta_PTm : fin k_PTm -> fin l_PTm) :
  pointwise_relation _ eq (funcomp (ren_PTm zeta_PTm) (subst_PTm sigma_PTm))
    (subst_PTm (funcomp (ren_PTm zeta_PTm) sigma_PTm)).
Proof.
exact (fun s => compSubstRen_PTm sigma_PTm zeta_PTm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_PTm {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
  (sigma_PTm : fin m_PTm -> PTm k_PTm) (tau_PTm : fin k_PTm -> PTm l_PTm)
  (s : PTm m_PTm) :
  subst_PTm tau_PTm (subst_PTm sigma_PTm s) =
  subst_PTm (funcomp (subst_PTm tau_PTm) sigma_PTm) s.
Proof.
exact (compSubstSubst_PTm sigma_PTm tau_PTm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_PTm_pointwise {k_PTm : nat} {l_PTm : nat} {m_PTm : nat}
  (sigma_PTm : fin m_PTm -> PTm k_PTm) (tau_PTm : fin k_PTm -> PTm l_PTm) :
  pointwise_relation _ eq (funcomp (subst_PTm tau_PTm) (subst_PTm sigma_PTm))
    (subst_PTm (funcomp (subst_PTm tau_PTm) sigma_PTm)).
Proof.
exact (fun s => compSubstSubst_PTm sigma_PTm tau_PTm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_PTm_PTm {m : nat} {n_PTm : nat} (xi : fin m -> fin n_PTm)
  (sigma : fin m -> PTm n_PTm)
  (Eq : forall x, funcomp (VarPTm n_PTm) xi x = sigma x) :
  forall x,
  funcomp (VarPTm (S n_PTm)) (upRen_PTm_PTm xi) x = up_PTm_PTm sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_PTm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_PTm_PTm {p : nat} {m : nat} {n_PTm : nat}
  (xi : fin m -> fin n_PTm) (sigma : fin m -> PTm n_PTm)
  (Eq : forall x, funcomp (VarPTm n_PTm) xi x = sigma x) :
  forall x,
  funcomp (VarPTm (plus p n_PTm)) (upRen_list_PTm_PTm p xi) x =
  up_list_PTm_PTm p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (VarPTm (plus p n_PTm)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_PTm (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_PTm {m_PTm : nat} {n_PTm : nat}
(xi_PTm : fin m_PTm -> fin n_PTm) (sigma_PTm : fin m_PTm -> PTm n_PTm)
(Eq_PTm : forall x, funcomp (VarPTm n_PTm) xi_PTm x = sigma_PTm x)
(s : PTm m_PTm) {struct s} : ren_PTm xi_PTm s = subst_PTm sigma_PTm s :=
  match s with
  | VarPTm _ s0 => Eq_PTm s0
  | PAbs _ s0 =>
      congr_PAbs
        (rinst_inst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm sigma_PTm)
           (rinstInst_up_PTm_PTm _ _ Eq_PTm) s0)
  | PApp _ s0 s1 =>
      congr_PApp (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s0)
        (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s1)
  | PPair _ s0 s1 =>
      congr_PPair (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s0)
        (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s1)
  | PProj _ s0 s1 =>
      congr_PProj (eq_refl s0) (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s1)
  | PBind _ s0 s1 s2 =>
      congr_PBind (eq_refl s0) (rinst_inst_PTm xi_PTm sigma_PTm Eq_PTm s1)
        (rinst_inst_PTm (upRen_PTm_PTm xi_PTm) (up_PTm_PTm sigma_PTm)
           (rinstInst_up_PTm_PTm _ _ Eq_PTm) s2)
  | PUniv _ s0 => congr_PUniv (eq_refl s0)
  end.

Lemma rinstInst'_PTm {m_PTm : nat} {n_PTm : nat}
  (xi_PTm : fin m_PTm -> fin n_PTm) (s : PTm m_PTm) :
  ren_PTm xi_PTm s = subst_PTm (funcomp (VarPTm n_PTm) xi_PTm) s.
Proof.
exact (rinst_inst_PTm xi_PTm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_PTm_pointwise {m_PTm : nat} {n_PTm : nat}
  (xi_PTm : fin m_PTm -> fin n_PTm) :
  pointwise_relation _ eq (ren_PTm xi_PTm)
    (subst_PTm (funcomp (VarPTm n_PTm) xi_PTm)).
Proof.
exact (fun s => rinst_inst_PTm xi_PTm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_PTm {m_PTm : nat} (s : PTm m_PTm) :
  subst_PTm (VarPTm m_PTm) s = s.
Proof.
exact (idSubst_PTm (VarPTm m_PTm) (fun n => eq_refl) s).
Qed.

Lemma instId'_PTm_pointwise {m_PTm : nat} :
  pointwise_relation _ eq (subst_PTm (VarPTm m_PTm)) id.
Proof.
exact (fun s => idSubst_PTm (VarPTm m_PTm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_PTm {m_PTm : nat} (s : PTm m_PTm) : ren_PTm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_PTm s) (rinstInst'_PTm id s)).
Qed.

Lemma rinstId'_PTm_pointwise {m_PTm : nat} :
  pointwise_relation _ eq (@ren_PTm m_PTm m_PTm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_PTm s) (rinstInst'_PTm id s)).
Qed.

Lemma varL'_PTm {m_PTm : nat} {n_PTm : nat}
  (sigma_PTm : fin m_PTm -> PTm n_PTm) (x : fin m_PTm) :
  subst_PTm sigma_PTm (VarPTm m_PTm x) = sigma_PTm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_PTm_pointwise {m_PTm : nat} {n_PTm : nat}
  (sigma_PTm : fin m_PTm -> PTm n_PTm) :
  pointwise_relation _ eq (funcomp (subst_PTm sigma_PTm) (VarPTm m_PTm))
    sigma_PTm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_PTm {m_PTm : nat} {n_PTm : nat}
  (xi_PTm : fin m_PTm -> fin n_PTm) (x : fin m_PTm) :
  ren_PTm xi_PTm (VarPTm m_PTm x) = VarPTm n_PTm (xi_PTm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_PTm_pointwise {m_PTm : nat} {n_PTm : nat}
  (xi_PTm : fin m_PTm -> fin n_PTm) :
  pointwise_relation _ eq (funcomp (ren_PTm xi_PTm) (VarPTm m_PTm))
    (funcomp (VarPTm n_PTm) xi_PTm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_PTm X Y :=
    up_PTm : X -> Y.

#[global]
Instance Subst_PTm  {m_PTm n_PTm : nat}: (Subst1 _ _ _) :=
 (@subst_PTm m_PTm n_PTm).

#[global]
Instance Up_PTm_PTm  {m n_PTm : nat}: (Up_PTm _ _) := (@up_PTm_PTm m n_PTm).

#[global]
Instance Ren_PTm  {m_PTm n_PTm : nat}: (Ren1 _ _ _) := (@ren_PTm m_PTm n_PTm).

#[global]
Instance VarInstance_PTm  {n_PTm : nat}: (Var _ _) := (@VarPTm n_PTm).

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
Instance subst_PTm_morphism  {m_PTm : nat} {n_PTm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_PTm m_PTm n_PTm)).
Proof.
exact (fun f_PTm g_PTm Eq_PTm s t Eq_st =>
       eq_ind s (fun t' => subst_PTm f_PTm s = subst_PTm g_PTm t')
         (ext_PTm f_PTm g_PTm Eq_PTm s) t Eq_st).
Qed.

#[global]
Instance subst_PTm_morphism2  {m_PTm : nat} {n_PTm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_PTm m_PTm n_PTm)).
Proof.
exact (fun f_PTm g_PTm Eq_PTm s => ext_PTm f_PTm g_PTm Eq_PTm s).
Qed.

#[global]
Instance ren_PTm_morphism  {m_PTm : nat} {n_PTm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_PTm m_PTm n_PTm)).
Proof.
exact (fun f_PTm g_PTm Eq_PTm s t Eq_st =>
       eq_ind s (fun t' => ren_PTm f_PTm s = ren_PTm g_PTm t')
         (extRen_PTm f_PTm g_PTm Eq_PTm s) t Eq_st).
Qed.

#[global]
Instance ren_PTm_morphism2  {m_PTm : nat} {n_PTm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_PTm m_PTm n_PTm)).
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
                 | progress
                    unfold up_list_PTm_PTm, up_PTm_PTm, upRen_list_PTm_PTm,
                     upRen_PTm_PTm, up_ren
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

Import
Core.

Arguments VarPTm {n_PTm}.

Arguments PUniv {n_PTm}.

Arguments PBind {n_PTm}.

Arguments PProj {n_PTm}.

Arguments PPair {n_PTm}.

Arguments PApp {n_PTm}.

Arguments PAbs {n_PTm}.

#[global]Hint Opaque subst_PTm: rewrite.

#[global]Hint Opaque ren_PTm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

