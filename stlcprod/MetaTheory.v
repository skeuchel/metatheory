Require Export DeclarationEvaluation.
Require Export DeclarationTyping.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma PTyping_bindPat_domainEnv {Γ p T Δ} (wp: PTyping Γ p T Δ) :
  bindPat p = domainEnv Δ.
Proof.
  induction wp; isimpl; congruence.
Qed.

Lemma shift_evar_ptyping {Γ1 p T Δ} (wt: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wt; econstructor; eauto with infra.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; simpl; intros; try (econstructor; eauto with infra; fail).
  - rewrite (PTyping_bindPat_domainEnv H).
    econstructor; eauto using shift_evar_ptyping with infra.
Qed.

Lemma weaken_typing {Γ} Δ :
  ∀ {t T}, Typing Γ t T → Typing (appendEnv Γ Δ) (weakenTm t (domainEnv Δ)) T.
Proof.
  induction Δ; simpl; eauto using shift_evar_typing with infra.
Qed.

Lemma shift_value {t} :
  ∀ {c}, Value t → Value (shiftTm c t).
Proof.
  induction t; simpl; intros; try contradiction; destruct_conjs; auto.
Qed.

Lemma weaken_value u :
  ∀ {t}, Value t → Value (weakenTm t u).
Proof.
  induction u as [|[]]; simpl; auto using shift_value.
Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Lemma subst_evar_ptyping {Γ s S} (wts: Typing Γ s S)
  {Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wp; simpl; econstructor; eauto with infra.
Qed.

Lemma subst_evar_lookup_evar {Γ s S} (wt: Typing Γ s S)
  {x Γ1 Γ2} (esub: subst_evar Γ S s x Γ1 Γ2) :
  ∀ {y T}, lookup_evar Γ1 y T → Typing Γ2 (substIndex x s y) T.
Proof.
  induction esub; inversion 1; subst; simpl;
    eauto using T_Var, shift_evar_typing with infra.
Qed.

Lemma subst_evar_typing {Γ s S Γ1 t T} (wts: Typing Γ s S) (wt: Typing Γ1 t T) :
  ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 → Typing Γ2 (substTm x s t) T.
Proof.
  induction wt; simpl; intros; eauto using subst_evar_lookup_evar;
    try (econstructor; eauto with infra; fail).
  - rewrite (PTyping_bindPat_domainEnv H).
    eapply T_Let; eauto using subst_evar_ptyping with infra.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tarr {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tarr T1 T2)) :
  ∃ t2, t = abs T1 t2.
Proof.
  depind wt; try contradiction; exists t; reflexivity.
Qed.

Lemma can_form_tprod {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tprod T1 T2)) :
  ∃ t1 t2, t = prod t1 t2 ∧ Typing Γ t1 T1 ∧ Typing Γ t2 T2.
Proof.
  depind wt; try contradiction; exists t1, t2; split; auto.
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
Proof with try (subst; eauto using red).
  depind wt; simpl; auto.
  - inversion H.
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
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
    Typing (appendEnv Γ Δ) t2 T2 → Typing Γ t2' T2.
Proof.
  induction m; intros Γ T1 T2 Δ wtp wt1 wt2.
  - dependent destruction wtp.
    eauto using subst_evar_typing with infra.
  - dependent destruction wtp.
    dependent destruction wt1.
    rewrite (PTyping_bindPat_domainEnv wtp1) in *.
    rewrite appendEnv_assoc in wt2.
    eauto using weaken_typing.
Qed.

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst;
    eauto using Typing, local_preservation_lett.
  - inversion wt1; eauto using subst_evar_typing with infra.
Qed.
