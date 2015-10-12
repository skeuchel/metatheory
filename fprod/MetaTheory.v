Require Export DeclarationEvaluation.
Require Export DeclarationTyping.

(******************************************************************************)
(* Missing infrastructure                                                     *)
(******************************************************************************)

Ltac rewrite_domainEnv_appendEnv :=
  match goal with
    | |- context[domainEnv (appendEnv _ _)] =>
      autorewrite with interaction_domain_append
    | H: context[domainEnv (appendEnv _ _)] |- _ =>
      autorewrite with interaction_domain_append in H
  end.

Hint Extern 10 (wfTy _ _) => rewrite_domainEnv_appendEnv : wf infra.
Hint Extern 10 (wfindex _ _) => rewrite_domainEnv_appendEnv : wf infra.

Fixpoint subhvl_tm (h: Hvl) : Prop :=
  match h with
    | H0 => True
    | HS a h =>
      match a with
        | tm => subhvl_tm h
        | ty => False
      end
  end.

Lemma subhvl_tm_append {h1 h2}
      (subh1: subhvl_tm h1)
      (subh2: subhvl_tm h2) :
  subhvl_tm (appendHvl h1 h2).
Proof.
  induction h2 as [|[]]; simpl; eauto.
Qed.
Hint Resolve subhvl_tm_append : infra wf.

Lemma Pat_bindPat_subhvl_tm :
  ∀ p, subhvl_tm (bindPat p).
Proof.
  induction p; simpl; auto using subhvl_tm_append.
Qed.
Hint Resolve Pat_bindPat_subhvl_tm : infra wf.

Lemma wfTy_strengthen_subhvl_tm1 {h1} h2 :
  ∀ T,
    subhvl_tm h2 →
    wfTy (appendHvl h1 h2) (weakenTy T h2) →
    wfTy h1 T.
Proof.
  induction h2 as [|[]]; intros; simpl; eauto with infra; intuition.
Qed.

Hint Extern 2 (wfTy _ _) =>
  match goal with
    | H: wfTy _ (tvar _)    |- _ => inversion H; subst; clear H
    | H: wfTy _ (tarr _ _)  |- _ => inversion H; subst; clear H
    | H: wfTy _ (tall _)    |- _ => inversion H; subst; clear H
    | H: wfTy _ (tprod _ _) |- _ => inversion H; subst; clear H
    | H: wfTy
           (appendHvl _ ?h)
           (weakenTy _ ?h)  |- _ => eapply wfTy_strengthen_subhvl_tm1 in H
  end : wf infra.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma PTyping_domainEnv_subhvl_tm {Γ p T Δ} :
  PTyping Γ p T Δ → subhvl_tm (domainEnv Δ).
Proof.
  induction 1; isimpl; eauto with infra.
Qed.
Hint Resolve PTyping_domainEnv_subhvl_tm : infra shift subst wf.

Lemma PTyping_bindPat_domainEnv {Γ p T Δ} :
  PTyping Γ p T Δ → bindPat p = domainEnv Δ.
Proof.

  induction 1; isimpl; try congruence; eauto.
Qed.

Lemma shift_etvar_ptyping {Γ1 p T Δ} (wt: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 →
    PTyping Γ2 (tshiftPat c p) (tshiftTy c T) (tshiftEnv c Δ).
Proof.
  induction wt; isimpl; econstructor; isimpl;
    autorewrite with weaken_shift; eauto with shift.
Qed.

Lemma shift_etvar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt; isimpl; econstructor;
    eauto using shift_etvar_ptyping with shift.
  - rewrite (PTyping_bindPat_domainEnv H); isimpl;
    autorewrite  with weaken_shift; eauto with shift.
Qed.

Lemma shift_evar_ptyping {Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wp; simpl; econstructor; eauto with infra.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; simpl; econstructor; eauto using shift_evar_ptyping with shift.
  - rewrite (PTyping_bindPat_domainEnv H); isimpl; eauto with shift.
Qed.

Lemma weaken_typing {Γ} Δ : ∀ {t T}, Typing Γ t T →
  Typing (appendEnv Γ Δ) (weakenTm t (domainEnv Δ)) (weakenTy T (domainEnv Δ)).
Proof.
  induction Δ; simpl;
    eauto using shift_evar_typing, shift_etvar_typing with shift.
Qed.

Lemma shift_value {t} :
  ∀ {c}, Value t → Value (shiftTm c t).
Proof.
  induction t; simpl; intros; try contradiction; destruct_conjs; auto.
Qed.

Lemma tshift_value {t} :
  ∀ {c}, Value t → Value (tshiftTm c t).
Proof.
  induction t; simpl; intros; try contradiction; destruct_conjs; auto.
Qed.

Lemma weaken_value u :
  ∀ {t}, Value t → Value (weakenTm t u).
Proof.
  induction u as [|[]]; simpl; auto using shift_value, tshift_value.
Qed.

(******************************************************************************)
(* Well-formedness                                                            *)
(******************************************************************************)

Lemma typing_wf {Γ t T} (wt: Typing Γ t T) : wfTy (domainEnv Γ) T.
Proof.
  induction wt; isimpl; eauto with infra.
Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Lemma subst_etvar_ptyping {Γ S Γ1 p T Δ}
  (wfS: wfTy (domainEnv Γ) S) (wt: PTyping Γ1 p T Δ) :
  ∀ {X Γ2}, subst_etvar Γ S X Γ1 Γ2 →
     PTyping Γ2 (tsubstPat X S p) (tsubstTy X S T) (tsubstEnv X S Δ).
Proof.
  induction wt; simpl; intros; isimpl; econstructor; eauto with subst.
  - rewrite weakenPat_tsubstPat, weakenTy_tsubstTy; isimpl; eauto with subst.
Qed.

Lemma subst_etvar_typing {Γ S Γ1 t T} (wS: wfTy (domainEnv Γ) S)
  (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, subst_etvar Γ S X Γ1 Γ2 →
     Typing Γ2 (tsubstTm X S t) (tsubstTy X S T).
Proof.
  induction wt; simpl; intros;
    try (isimpl; econstructor; eauto with infra; fail).
  - simpl; eapply T_Abs; eauto with infra.
    (* Urgs, ugly. *)
    replace (tsubstTy X S T2) with (tsubstTy (XS tm X) S T2)
      by apply tsubstTy_tm; eauto with infra.
  - eapply T_Let; eauto using subst_etvar_ptyping with infra.
    rewrite (PTyping_bindPat_domainEnv H); isimpl;
      autorewrite with weaken_subst; eauto with subst.
Qed.

Lemma subst_evar_ptyping {Γ s S} (wts: Typing Γ s S)
  {Γ1 p T Δ} (wtp: PTyping Γ1 p T Δ) :
  ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wtp; simpl; econstructor; eauto with subst.
Qed.

Lemma subst_evar_lookup_evar {Γ s S x Γ1 Γ2} (ws: Typing Γ s S)
  (esub: subst_evar Γ S s x Γ1 Γ2) :
  ∀ {y T}, lookup_evar Γ1 y T → Typing Γ2 (substIndex x s y) T.
Proof.
  induction esub; inversion 1; subst; simpl;
    eauto using T_Var, shift_evar_typing, shift_etvar_typing with subst.
Qed.

Lemma subst_evar_typing {Γ s S Γ1 t T} (ws: Typing Γ s S) (wt: Typing Γ1 t T) :
  ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 → Typing Γ2 (substTm x s t) T.
Proof.
  induction wt; simpl; eauto using subst_evar_lookup_evar;
    econstructor; eauto using subst_evar_ptyping with subst.
  - rewrite (PTyping_bindPat_domainEnv H); eauto with subst.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tarr {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tarr T1 T2)) :
  ∃ t2, t = abs T1 t2.
Proof.
  depind wt; try contradiction; exists t; reflexivity.
Qed.

Lemma can_form_tall {Γ t T} (v: Value t) (wt: Typing Γ t (tall T)) :
  ∃ t1, t = tabs t1.
Proof.
  depind wt; try contradiction; exists t; reflexivity.
Qed.

Lemma can_form_tprod {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tprod T1 T2)) :
  ∃ t1 t2, t = prod t1 t2 ∧ Typing Γ t1 T1 ∧ Typing Γ t2 T2.
Proof.
  depind wt; try contradiction; exists t1, t2; auto.
Qed.

Lemma matching_defined {Γ p T1 Δ} (wp: PTyping Γ p T1 Δ) :
  ∀ {t1}, Value t1 → Typing Γ t1 T1 → ∀ t2, ∃ t2', Match p t1 t2 t2'.
Proof.
  induction wp; intros t1 v1 wt1 t2.
  - exists (substTm X0 t1 t2).
    refine M_Var.
  - destruct (can_form_tprod v1 wt1) as (t11 & t12 & eq & wt11 & wt12); subst.
    destruct v1 as [v11 v12].
    apply (weaken_typing Δ1) in wt12.
    assert (val12' : Value (weakenTm t12 (domainEnv Δ1)))
       by (apply weaken_value; auto).
    destruct (IHwp2 (weakenTm t12 (domainEnv Δ1)) val12' wt12 t2) as [t2' m2].
    destruct (IHwp1 _ v11 wt11 t2') as [t2'' m1].
    rewrite <- (PTyping_bindPat_domainEnv wp1) in m2.
    exists t2''.
    exact (M_Prod m2 m1).
Qed.

Lemma progress {t U} (wt: Typing empty t U) :
  Value t ∨ ∃ t', red t t'.
Proof with destruct_conjs; subst; eauto using red.
  depind wt; simpl; auto.
  - inversion H.
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  - destruct IHwt as [vt|[t1' r1]]...
    destruct (can_form_tall vt wt)...
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct (matching_defined H v1 wt1 t2)...
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma local_preservation_lett {p t1 t2 t2'} (m: Match p t1 t2 t2') :
  ∀ {Γ T1 T2 Δ}, PTyping Γ p T1 Δ → Typing Γ t1 T1 →
    Typing (appendEnv Γ Δ) t2 (weakenTy T2 (domainEnv Δ)) →
    Typing Γ t2' T2.
Proof.
  induction m; intros Γ T1 T2 Δ wp wt1 wt2.
  - dependent destruction wp; simpl in *.
    eauto using subst_evar_typing with infra.
  - dependent destruction wp.
    dependent destruction wt1.
    rewrite (PTyping_bindPat_domainEnv wp1) in *.
    rewrite appendEnv_assoc, domainEnv_appendEnv, <- weakenTy_append in wt2.
    eauto using weaken_typing.
Qed.

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst; eauto using Typing.
  - dependent destruction wt1; eauto using subst_evar_typing with subst.
  - dependent destruction wt; eauto using subst_etvar_typing with subst.
  - eauto using local_preservation_lett.
Qed.
