Require Import Coq.Program.Equality.
Require Export DeclarationEvaluation.
Require Export DeclarationTyping.
Set Implicit Arguments.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma shift_etvar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt; isimpl; econstructor; eauto with shift.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; isimpl; econstructor; eauto with shift.
Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Lemma subst_etvar_typing {Γ S Γ1 t T}
  (wS: wfTy (domainEnv Γ) S) (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, subst_etvar Γ S X Γ1 Γ2 →
    Typing Γ2 (tsubstTm X S t) (tsubstTy X S T).
Proof.
  induction wt; simpl; intros;
    try (isimpl; econstructor; eauto with infra; fail).
  - simpl; eapply T_Abs; eauto with infra.
    (* Urgs, ugly. *)
    replace (tsubstTy X S T2) with (tsubstTy (XS tm X) S T2)
      by apply tsubstTy_tm; eauto with infra.
Qed.

Lemma subst_evar_lookup_evar {Γ s S} (wt: Typing Γ s S)
  {x Γ1 Γ2} (esub: subst_evar Γ S s x Γ1 Γ2) :
  ∀ {y T}, lookup_evar Γ1 y T → Typing Γ2 (substIndex x s y) T.
Proof.
  induction esub; inversion 1; subst; simpl;
    eauto using T_Var, shift_etvar_typing, shift_evar_typing with subst.
Qed.

Lemma subst_evar_typing {Γ Γ1 s S t T} (ws: Typing Γ s S) (wt: Typing Γ1 t T) :
  ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 → Typing Γ2 (substTm x s t) T.
Proof.
  induction wt; simpl; try econstructor;
    eauto using subst_evar_lookup_evar with subst.
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

Lemma progress {t U} (wt: Typing empty t U) :
  Value t ∨ ∃ t', red t t'.
Proof with try (subst; eauto using red).
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

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst; eauto using Typing.
  - inversion wt1; eauto using subst_evar_typing with subst.
  - inversion wt; eauto using subst_etvar_typing with subst.
Qed.
