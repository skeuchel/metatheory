Require Import Coq.omega.Omega.
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

Hint Extern 10 (wfTy _ _) => rewrite_domainEnv_appendEnv.
Hint Extern 10 (wfindex _ _) => rewrite_domainEnv_appendEnv.

Hint Rewrite domainEnv_tshiftEnv : interaction.
Hint Rewrite tshiftEnv_appendEnv : interaction.

(* forward reasoning about inversion *)
Hint Extern 2 (wfTy _ _) =>
  match goal with
    | H: wfTy _ (tvar _)    |- _ => inversion H; subst; clear H
    | H: wfTy _ (top)       |- _ => inversion H; subst; clear H
    | H: wfTy _ (tarr _ _)  |- _ => inversion H; subst; clear H
    | H: wfTy _ (tall _ _)  |- _ => inversion H; subst; clear H
  end : wf infra.

(* forward reasoning *)
Hint Extern 10 (wfTy _ _) =>
  match goal with
    | H: lookup_etvar _ _ _  |- _ => apply lookup_etvar_wf in H
    | H: lookup_evar _ _ _   |- _ => apply lookup_evar_wf in H
  end : infra shift wf.

Hint Extern 10 (wfindex _ _) =>
  match goal with
    | H: lookup_etvar _ _ _  |- _ => apply lookup_etvar_wfindex in H
    | H: lookup_evar _ _ _   |- _ => apply lookup_evar_wfindex in H
  end : infra shift wf.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma shift_etvar_sub {Γ1 U V} (sub: Sub Γ1 U V) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Sub Γ2 (tshiftTy c U) (tshiftTy c V).
Proof.
  induction sub; simpl; econstructor; eauto with shift.
Qed.
Hint Resolve shift_etvar_sub : infra shift.

Lemma shift_evar_sub {Γ1 U V} (sub: Sub Γ1 U V) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Sub Γ2 U V.
Proof.
  induction sub; simpl; econstructor; eauto with shift.
Qed.
Hint Resolve shift_evar_sub : infra shift.

Lemma weaken_sub {Γ U V} (sub: Sub Γ U V) :
  ∀ Δ, Sub (appendEnv Γ Δ)
         (weakenTy U (domainEnv Δ)) (weakenTy V (domainEnv Δ)).
Proof.
  induction Δ; simpl; eauto with shift.
Qed.

Lemma shift_etvar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt; isimpl; econstructor; eauto with shift.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; simpl; econstructor; eauto with shift.
Qed.

(******************************************************************************)
(* Well-formedness                                                            *)
(******************************************************************************)

Lemma sub_wf {Γ U V} (sub: Sub Γ U V) :
  wfTy (domainEnv Γ) U ∧ wfTy (domainEnv Γ) V.
Proof.
  induction sub; destruct_conjs; eauto with wf.
Qed.

Hint Extern 8 (wfTy _ _) =>
  match goal with
    | H: Sub _ _ _ |- _ => destruct (sub_wf H); clear H
  end : infra shift wf.

Lemma typing_wf {Γ t T} (wt: Typing Γ t T) : wfTy (domainEnv Γ) T.
Proof.
  induction wt; simpl; eauto with wf.
Qed.

(******************************************************************************)
(* Reflexivity, transitivity and narrowing                                    *)
(******************************************************************************)

Lemma sub_refl {Γ T} (wfT: wfTy (domainEnv Γ) T) : Sub Γ T T.
Proof.
  depind wfT; simpl; econstructor; eauto with wf.
Qed.

Lemma narrow_lookup_etvar_ne {Γ T1 T2 Δ} :
  ∀ {X U}, X ≠ (weakenIndexty I0 (domainEnv Δ)) →
    lookup_etvar (appendEnv (etvar Γ T1) Δ) X U →
    lookup_etvar (appendEnv (etvar Γ T2) Δ) X U.
Proof.
  induction Δ; inversion 2; isimpl; try constructor; isimpl; intuition.
  - apply IHΔ; congruence.
Qed.

Definition Trans Q :=
  ∀ Γ S T, Sub Γ S Q → Sub Γ Q T → Sub Γ S T.

Definition Narrow Q :=
  ∀ Γ Δ S T, Sub (appendEnv (etvar Γ Q) Δ) S T →
    ∀ R, Sub Γ R Q → Sub (appendEnv (etvar Γ R) Δ) S T.

Lemma trans_case Q
  (hypT : ∀ R, size_Ty R < size_Ty Q → Trans R)
  (hypN : ∀ R, size_Ty R < size_Ty Q → Narrow R) :
  Trans Q.
Proof with simpl; eauto with infra; try omega.
  intros Γ S T subSQ subQT; revert T subQT.
  induction subSQ; intros; auto.
  - dependent destruction subQT; constructor; auto.
  - eapply SA_Trans_TVar; eauto.
  - dependent destruction subQT; simpl; constructor...
    + apply (hypT T1)...
    + apply (hypT T2)...
  - dependent destruction subQT; constructor...
    + apply (hypT T1)...
    + apply (hypT T2)...
      refine (hypN T1 _ Γ empty _ _ subSQ2 _ subQT1)...
Qed.

Lemma narrow_case Q (hyp : ∀ (R : Ty), size_Ty R = size_Ty Q → Trans R) :
  Narrow Q.
Proof.
  intros Γ Δ U T subUT; depind subUT; intros R subQ.
  - apply SA_Top; isimpl; auto.
  - apply SA_Refl_TVar; isimpl; auto.
  - destruct (sub_wf subQ) as [wfR wfQ].
    case (eq_index_dec X (weakenIndexty I0 (domainEnv Δ))); intros; subst.
    + pose proof (lookup_etvar_functional H (weaken_lookup_etvar_here Δ wfQ)).
      (* The lookup position X is the one that is being narrowed, so U is in
         fact Q weakened and hence we can use transitivity for U.  U. We can
         derive the goal like this:

                               Γ ⊢ R<:Q
                             ------------- shift_etvar_sub
                             Γ,x<:R ⊢ R<:Q
                            --------------- weaken_sub
         (x<:R) ∈ Γ,x<:R,Δ  Γ,x<:R,Δ ⊢ R<:Q
         ---------------------------------- SA_Trans  -------------- IH
                   Γ,x<:R,Δ ⊢ x<:U                    Γ,x:R,Δ ⊢ U<:T
         ----------------------------------------------------------- hyp U
                                 Γ,x<:R,Δ ⊢ x<:T
      *)
      apply (hyp U); subst; isimpl; auto.
      eapply SA_Trans_TVar; eauto using weaken_sub with infra.
    (* Just push the narrowing into the subtyping part. *)
    + eapply SA_Trans_TVar; eauto using narrow_lookup_etvar_ne.
  - constructor; auto.
  - constructor; auto; apply (IHsubUT2 (etvar Δ T1) _ Q); auto.
Qed.

Lemma sub_trans_and_narrow Q : Trans Q ∧ Narrow Q.
Proof.
  induction Q using (sizeind size_Ty); intros; split.
  - apply trans_case; apply H; auto.
  - apply narrow_case; intros R eq.
    apply trans_case; rewrite eq; apply H.
Qed.

Lemma sub_trans {Q Γ S T} : Sub Γ S Q → Sub Γ Q T → Sub Γ S T.
Proof.
  intros; eapply sub_trans_and_narrow; eauto.
Qed.

Lemma sub_narrow {Γ Δ Q R S T} (subQ: Sub Γ R Q) :
  Sub (appendEnv (etvar Γ Q) Δ) S T → Sub (appendEnv (etvar Γ R) Δ) S T.
Proof.
  intros; eapply sub_trans_and_narrow; eauto.
Qed.

Lemma lookup_evar_narrow {Γ Δ Q R} :
  ∀ {x T}, lookup_evar (appendEnv (etvar Γ Q) Δ) x T →
           lookup_evar (appendEnv (etvar Γ R) Δ) x T.
Proof.
  induction Δ; inversion 1; isimpl; constructor; isimpl; eauto with wf.
Qed.

Lemma typing_narrow {Γ} Δ {Q R t T} (subQ: Sub Γ R Q) :
  Typing (appendEnv (etvar Γ Q) Δ) t T → Typing (appendEnv (etvar Γ R) Δ) t T.
Proof.
  intro wt; depind wt; eauto using Typing, lookup_evar_narrow, sub_narrow.
  - eapply T_Abs; isimpl; eauto.
    refine (IHwt Γ (evar Δ T1) _ _ eq_refl); auto.
  - eapply T_Tabs; isimpl; eauto.
    refine (IHwt Γ (etvar _ _) _ _ eq_refl); auto.
Qed.

Lemma typing_narrow0 {Γ Q R t T} (subQ: Sub Γ R Q) :
  Typing (etvar Γ Q) t T → Typing (etvar Γ R) t T.
Proof.
  apply (typing_narrow empty subQ).
Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Lemma subst_etvar_lookup_etvar {Γ B S X Γ1 Γ2} (wS : wfTy (domainEnv Γ) S)
  (subS: Sub Γ S B) (esub: subst_etvar Γ B S X Γ1 Γ2) :
  ∀ Y U, lookup_etvar Γ1 Y U → Sub Γ2 (tsubstIndex X S Y) (tsubstTy X S U).
Proof.
  induction esub; inversion 1; isimpl;
    try refine (SA_Trans_TVar _ (sub_refl _)); eauto with infra.
Qed.

Lemma subst_etvar_sub {Γ B Γ1 S U V} (wS : wfTy (domainEnv Γ) S)
  (subS: Sub Γ S B) (sub: Sub Γ1 U V) :
  ∀ Γ2 X, subst_etvar Γ B S X Γ1 Γ2 → Sub Γ2 (tsubstTy X S U) (tsubstTy X S V).
Proof.
  induction sub; isimpl; try econstructor; eauto using sub_refl with infra;
    eauto using subst_etvar_lookup_etvar, sub_trans with infra.
Qed.

Lemma subst_etvar_typing {Γ B S Γ1 t T} (wS: wfTy (domainEnv Γ) S)
  (subS: Sub Γ S B) (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, subst_etvar Γ B S X Γ1 Γ2 →
     Typing Γ2 (tsubstTm X S t) (tsubstTy X S T).
Proof.
  induction wt; simpl; intros;
    try (isimpl; econstructor; eauto using subst_etvar_sub with infra; fail).
  - eapply T_Abs; eauto with infra.
    (* Urgs, ugly. *)
    replace (tsubstTy X S T2) with (tsubstTy (XS tm X) S T2)
      by apply tsubstTy_tm; eauto with infra.
Qed.

Lemma subst_evar_sub {Γ D t Γ1 T1 T2} (st: Sub Γ1 T1 T2) :
  ∀ {Y Γ2}, subst_evar Γ D t Y Γ1 Γ2 → Sub Γ2 T1 T2.
Proof.
  induction st; isimpl; econstructor; eauto with subst.
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
    econstructor; eauto using subst_evar_sub with subst.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tarr {t T1 T2} (v: Value t) (wt: Typing empty t (tarr T1 T2)) :
  ∃ T1' t2, t = abs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion H; eauto; inversion H0.
Qed.

Lemma can_form_tall {t T1 T2} (v: Value t) (wt: Typing empty t (tall T1 T2)) :
  ∃ T1' t2, t = tabs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion H; eauto; inversion H0.
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
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma t_abs_inversion {Γ t T0 T1} (wt: Typing Γ (abs T1 t) T0) :
  ∀ {T2 T3}, Sub Γ T0 (tarr T2 T3) → Sub Γ T2 T1 ∧ Typing (evar Γ T1) t T3.
Proof.
  depind wt.
  - inversion 1; eauto using T_Sub, shift_evar_sub with shift.
  - eauto using sub_trans.
Qed.

Lemma t_tabs_inversion {Γ t T0 T1} (wt: Typing Γ (tabs T1 t) T0) :
  ∀ {T2 T3}, Sub Γ T0 (tall T2 T3) → Sub Γ T2 T1 ∧ Typing (etvar Γ T2) t T3.
Proof.
  depind wt.
  - inversion 1; subst; split; eauto using T_Sub, typing_narrow0.
  - eauto using sub_trans.
Qed.

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst; eauto using Typing.
  - destruct (t_abs_inversion wt1 (sub_refl (typing_wf wt1))).
    eauto using subst_evar_typing, T_Sub with subst.
  - destruct (t_tabs_inversion wt (sub_refl (typing_wf wt))).
    eauto using subst_etvar_typing, T_Sub with infra.
Qed.
