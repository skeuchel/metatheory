Require Import Core.

(* Term stuff *)

Inductive red : Tm → Tm → Prop :=
  | red_beta {T11 t12 t2} :
      red (app (abs T11 t12) t2) (t12[sub_id · t2])
  | red_abs {T1 t2 t2'} :
      red t2 t2' → red (abs T1 t2) (abs T1 t2')
  | red_app1 {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | red_app2 {t1 t2 t2'} :
      red t2 t2' → red (app t1 t2) (app t1 t2').

Lemma red_subst {t t'} (r: red t t') :
  forall σ, red (t[σ]) (t'[σ]).
Proof.
  induction r; intros; simpl; try constructor; auto.
  - rewrite sub_inst_comp.
    rewrite <- sub_comm.
    rewrite <- sub_inst_comp.
    constructor.
Qed.

Inductive SN (t : Tm) : Prop :=
  | SNi : (forall t', red t t' → SN t') → SN t.

Lemma SNd {t} (sn_t: SN t) : forall t', red t t' → SN t'.
Proof. destruct sn_t; auto. Qed.

Lemma SNtt : SN tt.
Proof. constructor; intros; inversion H. Qed.

Lemma SNappl {t1} t2 (sn: SN (app t1 t2)) : SN t1.
Proof.
  depind sn; constructor; intros; subst.
  eapply H0; eauto using red.
Qed.

Lemma SNvar {t} n (sn: SN (subTm t (sub_id · var n))) : SN t.
Proof. depind sn; constructor; eauto using red_subst. Qed.


Record CR (P:Cand) :=
  { cr_sn : forall t, P t → SN t;
    cr_cl : forall t, P t → forall t', red t t' → P t';
    cr_nt : forall t, Neutral t → (forall t', red t t' → P t') → P t
  }.
Arguments cr_sn [_] _ [_] _.
Arguments cr_cl [_] _ [_] _ [_] _.
Arguments cr_nt [_] _ [_] _ _.

(* Lemma CR_tt {P:Cand} {crP : CR P} : P tt. *)
(* Proof. *)
(*   intros; apply cr_nt; simpl; auto; intros. *)
(*   inversion H. *)
(* Qed. *)

Lemma CR_var {P:Cand} (crP : CR P) : forall n, P (var n).
Proof.
  intros; apply cr_nt; simpl; auto; intros.
  inversion H.
Qed.

Lemma CR_SN : CR SN.
Proof. constructor; eauto using SNd, SNi. Qed.

Definition ARR (P R: Cand) : Cand :=
  fun (t1: Tm) => forall t2, P t2 → R (app t1 t2).
Definition PI (F: Cand → Cand) : Cand :=
  fun M => forall P, CR P → F P M.

Lemma CR_ARR {P R} {CR_P: CR P} {CR_R: CR R} : CR (ARR P R).
Proof with simpl; eauto using red.
  constructor.
  - intros t ARR_t; eapply (SNappl (var 0)), (cr_sn CR_R), ARR_t, CR_var...
  - intros t ARR_t t' r s P_s; eapply (cr_cl CR_R)...
  - intros t neutral_t Hyp t' P_t'; apply (cr_nt CR_R)...
    generalize (cr_sn CR_P P_t').
    induction 1 as [t']; intros t'' r.
    inversion r; subst.
    + destruct neutral_t.
    + eapply Hyp...
    + eapply cr_nt... eapply H0... eapply cr_cl...
Qed.

Lemma CR_PI {F} (CR_F: (forall P, CR P → CR (F P))) : CR (PI F).
Proof.
  constructor; simpl.
  - intros t PI_t; refine (cr_sn (CR_F _ CR_SN) (PI_t _ CR_SN)).
  - intros t PI_t t' r P CR_P; refine (cr_cl (CR_F _ CR_P) (PI_t _ CR_P) r).
  - intros t NT_t PI_t' P CR_P; refine (cr_nt (CR_F _ CR_P) NT_t _).
    intros; apply PI_t'; eauto using CR_SN.
Qed.

Lemma Lam_Sound {P R} (crP: CR P) (crR: CR R) :
  forall T M, (forall N, P N → R (subTm M (sub_id · N))) →
    ARR P R (abs T M).
Proof.
  intros T M H.
  assert (SN_M : SN M) by eauto using (SNvar 0), (cr_sn crR), (CR_var crP).
  revert H.
  induction SN_M; intros Hyp L1 ?.
  assert (SN_L1: SN L1) by eauto using (cr_sn crP).
  induction SN_L1.
  apply (cr_nt crR); simpl; auto.
  intros ? r.
  depind r; eauto.
  * dependent destruction r; eauto.
    unfold ARR in *; eauto using (cr_cl crR), red_subst.
  * eauto using (cr_cl crP).
Qed.

(* Type stuff *)

Fixpoint Int (T: Ty) : Cand :=
  match T with
    | tunit      => SN
    | tarr T1 T2 => ARR (Int T1) (Int T2)
  end.

Lemma CR_Int (T: Ty) : CR (Int T).
Proof.
  induction T; eauto using CR_SN, CR_ARR.
Qed.

Definition IntEnv Γ (σ: Sub) : Prop :=
  forall x T, lookup_evar Γ x T → Int T (σ x).

Theorem fundamental {Γ M T} (wt: Typing Γ M T) :
  forall σ, IntEnv Γ σ → Int T (M[σ]).
Proof.
  induction wt; intros σ IntEnv_Γ; simpl; auto using SNtt.
  - apply Lam_Sound; simpl; intros; eauto using CR_Int.
    rewrite sub_inst_comp.
    apply IHwt; simpl.
    unfold IntEnv; intros.
    dependent destruction H0; simpl.
    + rewrite sub_up_def; simpl.
      rewrite sub_comp_snoc; simpl.
      auto.
    + rewrite sub_up_def; simpl.
      rewrite sub_comp_snoc; simpl.
      rewrite sub_comp_assoc; simpl.
      rewrite sub_comp_id_right; simpl.
      auto.
  - simpl in *; unfold ARR in *; auto.
Qed.

Lemma fundamental_id {Γ M T} (wt: Typing Γ M T) : Int T M.
Proof.
  rewrite <- sub_inst_id; apply (fundamental wt).
  unfold IntEnv; intros; apply CR_var.
  eauto using CR_Int.
Qed.

Theorem strong_normalization {Γ t T} (wt: Typing Γ t T) : SN t.
Proof.
  eauto using (cr_sn (CR_Int T)), fundamental_id.
Qed.
