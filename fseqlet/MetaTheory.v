Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export DeclarationEvaluation.
Require Export DeclarationTyping.
Set Implicit Arguments.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma DTyping_bind_domainEnv {Γ ds Δ} (wd : DTyping Γ ds Δ) :
  bind ds = domainEnv Δ.
Proof.
  induction wd; simpl; auto.
  - rewrite IHwd, domainEnv_appendEnv; simpl.
    reflexivity.
Qed.

Lemma shift_etvar_typing {Γ1 t T} (wt : Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt using ind_typing with
  (P0 := fun Γ1 ds Δ wtd =>
           ∀ {c Γ2}, shift_etvar c Γ1 Γ2 →
             DTyping Γ2 (tshiftDecls c ds) (tshiftEnv c Δ)); simpl; intros;
      isimpl; econstructor; autorewrite with weaken_shift; eauto with infra.
  - rewrite (DTyping_bind_domainEnv d), domainEnv_tshiftEnv; eauto with shift.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
 ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt using ind_typing with
  (P0 := fun Γ1 ds Δ wtd =>
           ∀ {c Γ2}, shift_evar c Γ1 Γ2 →
             DTyping Γ2 (shiftDecls c ds) Δ); simpl; intros;
    econstructor; try erewrite DTyping_bind_domainEnv; eauto with infra.
Qed.

Lemma weakening_typing_extend {Γ Δ t T} (wt: Typing Γ t T) :
  Typing (appendEnv Γ Δ) (weakenTm t (domainEnv Δ)) (weakenTy T (domainEnv Δ)).
Proof.
  revert t T wt; induction Δ; simpl;
    eauto using shift_etvar_typing, shift_evar_typing with infra.
Qed.

Lemma value_shift c {t : Tm} :
  Value t → Value (shiftTm c t).
Proof.
  revert c; induction t; simpl; try contradiction; auto; intros.
Qed.

Lemma value_tshift c {t : Tm} :
  Value t → Value (tshiftTm c t).
Proof.
  revert c; induction t; simpl; try contradiction; auto; intros.
Qed.

Lemma weaken_value u :
  ∀ {t}, Value t → Value (weakenTm t u).
Proof.
  induction u as [|[]]; simpl; eauto using value_shift, value_tshift.
Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Lemma subst_evar_lookup_evar {Γ s S x Γ1 Γ2} (ws: Typing Γ s S)
  (esub: subst_evar Γ S s x Γ1 Γ2) :
  ∀ {y T}, lookup_evar Γ1 y T → Typing Γ2 (substIndex x s y) T.
Proof.
  induction esub; inversion 1; subst; simpl;
    eauto using T_Var, shift_evar_typing, shift_etvar_typing with subst.
Qed.

Lemma subst_evar_typing_dtyping {Γ s S} (ws: Typing Γ s S) :
  ∀ Γ1,
  (∀ {t T} (wt : Typing Γ1 t T),
    ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 →
                 Typing Γ2 (substTm x s t) T) ∧
  (∀ {ds Δ} (wtd : DTyping Γ1 ds Δ),
    ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 →
                 DTyping Γ2 (substDecls x s ds) Δ).
Proof.
  apply ind_typing_dtyping; simpl; eauto using subst_evar_lookup_evar;
    try econstructor; eauto with subst.
  rewrite (DTyping_bind_domainEnv d); eauto with subst.
Qed.

(* Lemma subst_evar_typing_ind : *)
(*   (∀ {Γ1 t T} (wt : Typing Γ1 t T), *)
(*     ∀ {x t' Γ2}, subst_evar x t' Γ1 Γ2 → *)
(*                  Typing Γ2 (substTm x t' t) T). *)
(* Proof. *)
(*   apply subst_evar_typing_dtyping_ind. *)
(* Qed. *)

Lemma subst_evar_typing {Γ s S} (ws: Typing Γ s S) :
  ∀ Γ1 t T (wt : Typing Γ1 t T) {x Γ2}, subst_evar Γ S s x Γ1 Γ2 →
                 Typing Γ2 (substTm x s t) T.
Proof. apply subst_evar_typing_dtyping; auto. Qed.

Lemma subst_evar_dtyping {Γ s S} (ws: Typing Γ s S) :
  ∀ Γ1 ds Δ (wtd : DTyping Γ1 ds Δ) {x Γ2}, subst_evar Γ S s x Γ1 Γ2 →
                 DTyping Γ2 (substDecls x s ds) Δ.
Proof. apply subst_evar_typing_dtyping; auto. Qed.

Lemma subst_etvar_typing_dtyping_ind {Γ S} (wS: wfTy (domainEnv Γ) S) :
  ∀ Γ1,
  (∀ {t T} (wt : Typing Γ1 t T) {X Γ2}, subst_etvar Γ S X Γ1 Γ2 →
     Typing Γ2 (tsubstTm X S t) (tsubstTy X S T)) ∧
  (∀ {ds Δ} (wtd : DTyping Γ1 ds Δ) {X Γ2}, subst_etvar Γ S X Γ1 Γ2 →
                 DTyping Γ2 (tsubstDecls X S ds) (tsubstEnv X S Δ)).
Proof.
  apply ind_typing_dtyping; simpl; intros;
    try (isimpl; econstructor; eauto with infra; fail).
  - simpl; eapply T_Abs; eauto with infra.
    (* Urgs, ugly. *)
    replace (tsubstTy X S T2) with (tsubstTy (XS tm X) S T2)
      by apply tsubstTy_tm; eauto with infra.
  - eapply T_Let; eauto.
    rewrite (DTyping_bind_domainEnv d); isimpl;
      autorewrite with weaken_subst; eauto with subst.
  - rewrite tsubstEnv_appendEnv; econstructor; simpl; eauto with subst.
Qed.

Lemma subst_etvar_typing {Γ S} (wS: wfTy (domainEnv Γ) S) :
  ∀ Γ1 t T (wt : Typing Γ1 t T) {X Γ2},
    subst_etvar Γ S X Γ1 Γ2 → Typing Γ2 (tsubstTm X S t) (tsubstTy X S T).
Proof.
  apply subst_etvar_typing_dtyping_ind; auto.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tarr {t : Tm} {T1 T2} :
  Value t → Typing empty t (tarr T1 T2) →
  exists t' T1', t = abs T1' t'.
Proof.
  intros val_t wt_t.
  depind wt_t; try contradiction.
  exists t, T1; reflexivity.
Qed.

Lemma can_form_tall {t : Tm} {T} :
  Value t → Typing empty t (tall T) →
  exists t', t = tabs t'.
Proof.
  intros val_t wt_t.
  depind wt_t; try contradiction.
  exists t; auto.
Qed.

Lemma progress {Γ t U} (wt: Typing Γ t U) :
  Γ = empty → Value t ∨ ∃ t', red t t'.
Proof with destruct_conjs; subst; simpl; eauto using red, redds'.
  induction wt using ind_typing with
  (P0 := fun Γ ds Δ wds => Γ = empty → ValueH ds ∨ ∃ ds', redds' ds ds');
    intros...
  - inversion l.
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  - destruct IHwt as [vt|[t1' r1]]...
    destruct (can_form_tall vt wt)...
  - destruct IHwt as [v1|[t1' r1]]...
    dependent destruction d...
  - destruct IHwt as [vt|[t1' r1]]...
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt using ind_typing
  with (P0 := fun Γ ds Δ wds => ∀ ds', redds' ds ds' → DTyping Γ ds' Δ);
    intros t' rd; inversion rd; subst; eauto using Typing, DTyping.
  - dependent destruction wt1; eauto using subst_evar_typing with subst.
  - dependent destruction wt; eauto using subst_etvar_typing with subst.
  - dependent destruction d; auto.
  - dependent destruction d; eauto.
    rewrite (DTyping_bind_domainEnv d).
    rewrite appendEnv_assoc, domainEnv_appendEnv, <- weakenTy_append in wt.
    eauto using T_Let, subst_evar_dtyping, subst_evar_typing with infra.
Qed.
