Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export DeclarationEvaluation.
Require Export DeclarationTyping.
Set Implicit Arguments.

(******************************************************************************)
(* Record field lookup                                                        *)
(******************************************************************************)

Lemma option_map_id {A} (ma: option A) :
  option_map (λ x, x) ma = ma.
Proof. destruct ma; auto. Qed.

Lemma option_map_com {A B C} (f: A → B) (g : B → C) (ma: option A) :
  option_map g (option_map f ma) = option_map (λ x, g (f x)) ma.
Proof.
  destruct ma; auto.
Qed.

Ltac get_comm :=
  let t:=fresh in
    intro t; induction t; simpl;
    [ auto | intros; case (eq_lab_dec _ _); auto ].

Lemma get_tshifttrec :
  ∀ (Tr : TRec) l c, tshiftTRec c Tr l = option_map (tshiftTy c) (Tr l).
Proof. get_comm. Qed.

Lemma get_tsubsttrec :
  ∀ (Tr : TRec) l X S, tsubstTRec X S Tr l = option_map (tsubstTy X S) (Tr l).
Proof. get_comm. Qed.

Lemma get_weaken_trec h :
  ∀ (Tr : TRec) l,
    weakenTRec Tr h l = option_map (fun T => weakenTy T h) (Tr l).
Proof.
  induction h as [|[]]; simpl; intros; try rewrite option_map_id; auto.
  - rewrite <- option_map_com, get_tshifttrec; f_equal; auto.
Qed.

Lemma get_shiftrec :
  ∀ (tr : Rec) l c, shiftRec c tr l = option_map (shiftTm c) (tr l).
Proof. get_comm. Qed.

Lemma get_tshiftrec :
  ∀ (tr : Rec) l c, tshiftRec c tr l = option_map (tshiftTm c) (tr l).
Proof. get_comm. Qed.

Lemma get_weaken_rec h :
  ∀ (tr : Rec) l,
    weakenRec tr h l = option_map (fun t => weakenTm t h) (tr l).
Proof.
  induction h as [|[]]; simpl; intros; try rewrite option_map_id; auto.
  - rewrite <- option_map_com, get_shiftrec; f_equal; auto.
  - rewrite <- option_map_com, get_tshiftrec; f_equal; auto.
Qed.

Lemma incl_map (Sr Tr: TRec) (f : Ty → Ty) l
   (hyp: ∀ T, Tr l = Some T → ∃ S : Ty, Sr l = Some S) :
   ∀ T, option_map f (Tr l) = Some T → ∃ S : Ty, option_map f (Sr l) = Some S.
Proof.
  induction (Tr l) as [T'|]; simpl; try discriminate; intros.
  destruct (hyp T' eq_refl) as [S' Srl]; rewrite Srl; simpl; eauto.
Qed.

(******************************************************************************)
(* Well-formedness                                                            *)
(******************************************************************************)

Lemma PTyping_PRTyping_domainEnv_subhvl_tm :
  ∀ Γ,
    (∀ p T Δ, PTyping Γ p T Δ → subhvl_tm (domainEnv Δ)) ∧
    (∀ ps T Δ, PRTyping Γ ps T Δ → subhvl_tm (domainEnv Δ)).
Proof.
  apply ind_ptyping_prtyping; isimpl; eauto with infra.
Qed.

Lemma PTyping_domainEnv_subhvl_tm :
  ∀ Γ p T Δ, PTyping Γ p T Δ → subhvl_tm (domainEnv Δ).
Proof.
  eapply (PTyping_PRTyping_domainEnv_subhvl_tm).
Qed.
Hint Resolve PTyping_domainEnv_subhvl_tm : infra shift subst wf.

Lemma PRTyping_domainEnv_subhvl_tm :
  ∀ Γ ps T Δ, PRTyping Γ ps T Δ → subhvl_tm (domainEnv Δ).
Proof.
  eapply (PTyping_PRTyping_domainEnv_subhvl_tm).
Qed.
Hint Resolve PRTyping_domainEnv_subhvl_tm : infra shift subst wf.

Lemma lookup_tref_wf {h Tr} (wTr: wfTRec h Tr) :
  ∀ l T, Tr l = Some T → wfTy h T.
Proof.
  induction wTr; simpl; intros k Tk; try discriminate.
  - destruct (eq_lab_dec k _); inversion 1; subst; eauto.
Qed.

(* Uff have to remove this one. *)
Lemma lab_wf h l : wfLab h l.
Proof.
  induction l; eauto using wfLab.
Qed.
Hint Resolve lab_wf.

Lemma sub_wf {Γ U V} (sub: Sub Γ U V) :
  wfTy (domainEnv Γ) U ∧ wfTy (domainEnv Γ) V.
Proof.
  induction sub; destruct_conjs; split; eauto with wf.
Qed.

Hint Extern 8 (wfTy _ _) =>
  match goal with
    | H: Sub _ _ _ |- _ => destruct (sub_wf H); clear H
  end : infra shift wf.

Lemma typing_wf {Γ t T} (wt: Typing Γ t T) : wfTy (domainEnv Γ) T.
Proof.
  induction wt using ind_typing with
  (P0 := fun Γ tr Tr wt => wfTRec (domainEnv Γ) Tr);
    isimpl; eauto with wf.
  - inversion IHwt; subst. eapply (lookup_tref_wf wf); eauto.
Qed.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma PTyping_bindPat_domainEnv {Γ p T Δ} (wp: PTyping Γ p T Δ) :
  bindPat p = domainEnv Δ.
Proof.
  induction wp using ind_ptyping with
  (P0 := fun Γ pr Tr Δ wpr => bindPRec pr = domainEnv Δ);
    isimpl; try congruence; eauto.
Qed.

Lemma shift_etvar_sub {Γ1 U V} (sub: Sub Γ1 U V) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Sub Γ2 (tshiftTy c U) (tshiftTy c V).
Proof.
  induction sub; simpl in *; intros;
    try (econstructor; eauto with shift; fail).
  - constructor; eauto with wf.
    + intro l; repeat rewrite get_tshifttrec; eauto using incl_map.
    + intros l S2 T2; repeat rewrite get_tshifttrec; intros E1 E2.
      specialize (H l).
      induction (Tr l); try discriminate; inversion E1.
      induction (Sr l); try discriminate; inversion E2.
      eauto.
Qed.

Lemma shift_evar_sub {Γ1 U V} (sub: Sub Γ1 U V) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Sub Γ2 U V.
Proof.
  induction sub; simpl; econstructor; eauto with shift.
Qed.

Lemma weaken_sub {Γ U V} (sub: Sub Γ U V) :
  ∀ Δ, Sub (appendEnv Γ Δ)
         (weakenTy U (domainEnv Δ)) (weakenTy V (domainEnv Δ)).
Proof.
  induction Δ; simpl; eauto using shift_evar_sub, shift_etvar_sub with shift.
Qed.

Lemma shift_etvar_ptyping {Γ1 p T Δ} (wt: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 →
    PTyping Γ2 (tshiftPat c p) (tshiftTy c T) (tshiftEnv c Δ).
Proof.
  induction wt using ind_ptyping with
  (P0 := fun Γ1 pr Tr Δ wpr =>
           ∀ {c Γ2}, shift_etvar c Γ1 Γ2 →
             PRTyping Γ2 (tshiftPRec c pr) (tshiftTRec c Tr) (tshiftEnv c Δ));
    isimpl; econstructor; isimpl;
    autorewrite with weaken_shift; eauto with shift.
  - rewrite get_tshifttrec, e; auto.
Qed.

Lemma shift_etvar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt using ind_typing with
  (P0 := fun Γ1 tr Tr wtr =>
           ∀ {c Γ2}, shift_etvar c Γ1 Γ2 →
             RTyping Γ2 (tshiftRec c tr) (tshiftTRec c Tr)); simpl; intros;
    try (isimpl; econstructor; isimpl; autorewrite with weaken_shift;
         eauto using shift_etvar_sub with infra; fail).
  - econstructor; eauto using shift_etvar_ptyping.
    + rewrite (PTyping_bindPat_domainEnv p0); isimpl;
        autorewrite  with weaken_shift; eauto with shift.
  - apply T_Proj with (Tr := tshiftTRec c Tr); eauto.
    + rewrite get_tshifttrec, lIn; trivial.
Qed.

Lemma shift_evar_ptyping {Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wp using ind_ptyping with
  (P0 := fun Γ1 pr Tr Δ wpr =>
           ∀ {c Γ2}, shift_evar c Γ1 Γ2 →
             PRTyping Γ2 pr Tr Δ);
    simpl; econstructor; eauto with infra.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt using ind_typing with
  (P0 := fun Γ1 tr Tr wtr =>
           ∀ {c Γ2}, shift_evar c Γ1 Γ2 → RTyping Γ2 (shiftRec c tr) Tr);
    simpl; econstructor;
      eauto using shift_evar_sub, shift_evar_ptyping with shift.
  - rewrite (PTyping_bindPat_domainEnv p0); isimpl; eauto with shift.
Qed.

Lemma weaken_typing {Γ} Δ :
  ∀ {t T}, Typing Γ t T →
    Typing (appendEnv Γ Δ)
      (weakenTm t (domainEnv Δ)) (weakenTy T (domainEnv Δ)).
Proof.
  induction Δ; simpl;
    eauto using shift_evar_typing, shift_etvar_typing with shift.
Qed.

Lemma shift_value_rvalue :
  (∀ t {c}, Value t → Value (shiftTm c t)) ∧
  (∀ ts {c}, RValue ts → RValue (shiftRec c ts)).
Proof.
  apply ind_Tm_Rec; simpl; intros; try contradiction; destruct_conjs; auto.
Qed.

Lemma tshift_value_rvalue :
  (∀ t {c}, Value t → Value (tshiftTm c t)) ∧
  (∀ ts {c}, RValue ts → RValue (tshiftRec c ts)).
Proof.
  apply ind_Tm_Rec; simpl; intros; try contradiction; destruct_conjs; auto.
Qed.

Lemma weaken_value u :
  ∀ {t}, Value t → Value (weakenTm t u).
Proof.
  induction u as [|[]]; simpl; auto; intros.
  - apply shift_value_rvalue; auto.
  - apply tshift_value_rvalue; auto.
Qed.

Lemma weaken_rvalue u :
  ∀ {vr}, RValue vr → RValue (weakenRec vr u).
Proof.
  induction u as [|[]]; simpl; auto; intros.
  - apply shift_value_rvalue; auto.
  - apply tshift_value_rvalue; auto.
Qed.

(******************************************************************************)
(* Reflexivity, transitivity and narrowing                                    *)
(******************************************************************************)

Lemma sub_refl : ∀ {Γ T} (wT: wfTy (domainEnv Γ) T), Sub Γ T T.
Proof.
  cut (∀ h T, wfTy h T → ∀ Γ, h = domainEnv Γ → Sub Γ T T); eauto.
  intros h T wT. induction wT using ind_wfTy with
  (P := fun h (Tr : TRec) wTr =>
           ∀ Γ, h = domainEnv Γ →
             ∀ l T, Tr l = Some T → Sub Γ T T); simpl; intros; subst;
    try discriminate; try (econstructor; eauto with wf; fail).
  - destruct (eq_lab_dec l l51); eauto.
    + inversion H0; subst; auto.
  - constructor; eauto.
    + intros l S T El1 El2; rewrite El1 in El2; inversion El2; subst; eauto.
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

Lemma size_lookup {Tr : TRec} {k T} :
  Tr k = Some T → size_Ty T < S (size_TRec Tr).
Proof.
  induction Tr; simpl; intros E; try discriminate.
  - destruct (eq_lab_dec k l).
    + inversion E; omega.
    + specialize (IHTr E); omega.
Qed.

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
  - dependent destruction subQT; constructor...
    + intros l ? Tr0l; destruct (incl0 _ _ Tr0l) as [? Trl].
      destruct (incl _ _ Trl) as [? Srl]; eauto.
    + intros l S T0 Tr0l Srl; destruct (incl0 _ _ Tr0l) as [T Trl].
      apply (hypT T); eauto using (size_lookup Trl).
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
      eapply SA_Trans_TVar; eauto using shift_etvar_sub, weaken_sub with infra.
    (* Just push the narrowing into the subtyping part. *)
    + eapply SA_Trans_TVar; eauto using narrow_lookup_etvar_ne.
  - constructor; auto.
  - constructor; auto; apply (IHsubUT2 (etvar Δ T1) _ Q); auto.
  - constructor; isimpl; eauto.
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

Lemma ptyping_narrow {Γ R Q Γ' p T Δp} (subQ: Sub Γ R Q) :
  PTyping Γ' p T Δp → ∀ Δ, Γ' = appendEnv (etvar Γ Q) Δ →
    PTyping (appendEnv (etvar Γ R) Δ) p T Δp.
Proof.
  intro wp; induction wp using ind_ptyping with
  (P0 := fun Γ' pr Tr Δpr wpr => ∀ Δ, Γ' = appendEnv (etvar Γ Q) Δ →
    PRTyping (appendEnv (etvar Γ R) Δ) pr Tr Δpr);
      econstructor; subst; isimpl; eauto.
  - rewrite <- appendEnv_assoc.
    eapply IHwp0; eauto.
    rewrite <- appendEnv_assoc; auto.
Qed.

Lemma typing_narrow {Γ Q R} (subQ: Sub Γ R Q) {Γ' t T} (wt: Typing Γ' t T) :
  ∀ Δ, Γ' = (appendEnv (etvar Γ Q) Δ) →
       Typing (appendEnv (etvar Γ R) Δ) t T.
Proof.
  induction wt using ind_typing with
  (P0 := fun Γ' tr Tr wtr => ∀ Δ, Γ' = appendEnv (etvar Γ Q) Δ →
           RTyping (appendEnv (etvar Γ R) Δ) tr Tr); simpl; intros; subst;
    eauto using Typing, RTyping, lookup_evar_narrow, sub_narrow.
  - eapply T_Abs; isimpl; eauto.
    refine (IHwt (evar Δ _) _); auto.
  - eapply T_Tabs; isimpl; eauto.
    refine (IHwt (etvar Δ _) _); auto.
  - eapply T_Let; eauto using ptyping_narrow.
    rewrite <- appendEnv_assoc in *; eauto.
Qed.

Lemma typing_narrow0 {Γ Q R t T} (sub: Sub Γ R Q) :
  Typing (etvar Γ Q) t T → Typing (etvar Γ R) t T.
Proof. intro wt; apply (typing_narrow sub wt empty); auto. Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Lemma subst_etvar_lookup_etvar {Γ B S X Γ1 Γ2} (wS : wfTy (domainEnv Γ) S)
  (subS: Sub Γ S B) (esub: subst_etvar Γ B S X Γ1 Γ2) :
  ∀ Y U, lookup_etvar Γ1 Y U → Sub Γ2 (tsubstIndex X S Y) (tsubstTy X S U).
Proof.
  induction esub; inversion 1; isimpl;
    try refine (SA_Trans_TVar _ _ (sub_refl _));
    eauto using shift_etvar_sub, shift_evar_sub with infra.
Qed.

Lemma subst_etvar_sub {Γ B Γ1 S U V} (wS : wfTy (domainEnv Γ) S)
  (subS: Sub Γ S B) (sub: Sub Γ1 U V) :
  ∀ Γ2 X, subst_etvar Γ B S X Γ1 Γ2 → Sub Γ2 (tsubstTy X S U) (tsubstTy X S V).
Proof.
  induction sub; simpl in *; intros;
    try (try econstructor; eauto using sub_refl with infra;
         eauto using subst_etvar_lookup_etvar, sub_trans with infra;
         fail).
  - constructor; eauto with wf.
    + intro l; specialize (incl l).
      repeat rewrite get_tsubsttrec; eauto using incl_map.
    + intros l S2 T2; repeat rewrite get_tsubsttrec; intros E1 E2.
      specialize (H l).
      induction (Tr l); try discriminate; inversion E1.
      induction (Sr l); try discriminate; inversion E2.
      eauto.
Qed.

Lemma subst_etvar_ptyping {Γ B S Γ1 p T Δp}
  (wfS: wfTy (domainEnv Γ) S) (sub: Sub Γ S B) (wt: PTyping Γ1 p T Δp) :
  ∀ {X Γ2}, subst_etvar Γ B S X Γ1 Γ2 →
     PTyping Γ2 (tsubstPat X S p) (tsubstTy X S T) (tsubstEnv X S Δp).
Proof.
  induction wt using ind_ptyping
  with (P0 := fun Γ1 pr Tr Δpr wpr =>
    ∀ {X Γ2}, subst_etvar Γ B S X Γ1 Γ2 →
      PRTyping Γ2 (tsubstPRec X S pr) (tsubstTRec X S Tr) (tsubstEnv X S Δpr));
      simpl; intros; isimpl; econstructor;
      eauto using subst_etvar_sub with subst.
  - autorewrite with weaken_subst; isimpl; eauto with subst.
  - rewrite get_tsubsttrec, e; auto.
Qed.

Lemma subst_etvar_typing {Γ B S Γ1 t T} (wS: wfTy (domainEnv Γ) S)
  (subS: Sub Γ S B) (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, subst_etvar Γ B S X Γ1 Γ2 →
     Typing Γ2 (tsubstTm X S t) (tsubstTy X S T).
Proof.
  induction wt using ind_typing
  with (P0 := fun Γ1 tr Tr wtr =>
                ∀ {X Γ2}, subst_etvar Γ B S X Γ1 Γ2 →
                  RTyping Γ2 (tsubstRec X S tr) (tsubstTRec X S Tr));
    simpl; intros; try (isimpl; econstructor;
      eauto using subst_etvar_sub with infra; fail).
  - eapply T_Abs; eauto with infra.
    (* Urgs, ugly. *)
    replace (tsubstTy X S T2) with (tsubstTy (XS tm X) S T2)
      by apply tsubstTy_tm; eauto with infra.
  - eapply T_Let; eauto using subst_etvar_ptyping with infra.
    rewrite (PTyping_bindPat_domainEnv p0); isimpl;
      autorewrite with weaken_subst; eauto with subst.
  - refine (@T_Proj Γ2 _ l _ (tsubstTRec X S Tr) _ _); eauto.
    rewrite get_tsubsttrec, lIn; auto.
Qed.

Lemma subst_evar_sub {Γ D t Γ1 T1 T2} (st: Sub Γ1 T1 T2) :
  ∀ {Y Γ2}, subst_evar Γ D t Y Γ1 Γ2 → Sub Γ2 T1 T2.
Proof.
  induction st; isimpl; econstructor; eauto with subst.
Qed.

Lemma subst_evar_ptyping {Γ s S} (wts: Typing Γ s S)
  {Γ1 p T Δp} (wp: PTyping Γ1 p T Δp) :
  ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 → PTyping Γ2 p T Δp.
Proof.
  induction wp using ind_ptyping
  with (P0 := fun Γ1 pr Tr Δpr wpr =>
      ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 → PRTyping Γ2 pr Tr Δpr);
    simpl; econstructor; eauto with subst.
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
  induction wt using ind_typing
  with (P0 := fun Γ1 tr Tr wtr =>
      ∀ {x Γ2}, subst_evar Γ S s x Γ1 Γ2 → RTyping Γ2 (substRec x s tr) Tr);
   simpl; eauto using subst_evar_lookup_evar;
  econstructor; eauto using subst_evar_sub, subst_evar_ptyping with subst.
  - rewrite (PTyping_bindPat_domainEnv p0); eauto with subst.
Qed.

(******************************************************************************)
(* Inversion lemmas                                                           *)
(******************************************************************************)

Lemma sub_trec_inversion {Γ S Tr} (subST: Sub Γ S (trec Tr)) :
  (∃ X, S = tvar X) ∨
  (∃ Sr, S = trec Sr ∧
     ∀ l T, Tr l = Some T → ∃ S, Sr l = Some S ∧ Sub Γ S T).
Proof.
  dependent destruction subST; eauto.
  - right; exists Sr; split; auto; intros l T Trl.
    destruct (incl _ _ Trl) as [S Srl]; eauto.
Qed.

Lemma rtyping_trec_inversion {Γ tr Tr k T} (wt: RTyping Γ tr Tr) :
  Tr k = Some T → ∃ t, tr k = Some t ∧ Typing Γ t T.
Proof.
  induction wt; simpl; try discriminate.
  - destruct (eq_lab_dec k l); simpl; intros E; subst.
    + inversion E; subst; exists t; split; auto.
    + apply IHwt; auto.
Qed.

Lemma typing_rec_inversion {Γ tr S} (wt: Typing Γ (rec tr) S) :
  ∀ Tr, Sub Γ S (trec Tr) →
    ∀ l T, Tr l = Some T →
      ∃ t, tr l = Some t ∧ Typing Γ t T.
Proof.
  depind wt; simpl; intros Tr' subST l T Trl'.
  - apply sub_trec_inversion in subST; destruct subST as [[X]|[Sr [E subs]]].
    + discriminate.
    + inversion E; subst.
      destruct (subs l T Trl') as [S [Srl subST]].
      destruct (rtyping_trec_inversion H Srl) as [t [Et wt]].
      eauto using T_Sub.
  - eapply IHwt; eauto using sub_trans.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tvar {Γ t X} (v: Value t) (wt: Typing Γ t (tvar X)) : False.
Proof.
  depind wt; auto.
  depind H; eauto.
Qed.

Lemma can_form_tarr {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tarr T1 T2)) :
  ∃ T1' t2, t = abs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion H; subst; eauto.
    + elimtype False; eauto using can_form_tvar.
Qed.

Lemma can_form_tall {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tall T1 T2)) :
  ∃ T1' t2, t = tabs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion H; subst; eauto.
    + elimtype False; eauto using can_form_tvar.
Qed.

Lemma rtyping_lab_incl {Γ tr Tr} (wt: RTyping Γ tr Tr) :
  ∀ l T, Tr l = Some T → ∃ t, tr l = Some t.
Proof.
  induction wt; simpl; intros k Tk Trk; try discriminate;
     destruct (eq_lab_dec k l); eauto.
Qed.

Lemma can_form_trec {Γ t Sr} (v : Value t) (wt: Typing Γ t (trec Sr)) :
  ∃ vr, t = rec vr ∧ ∀ l T, Sr l = Some T → ∃ s, vr l = Some s.
Proof.
  depind wt; try contradiction.
  - eauto using rtyping_lab_incl.
  - inversion H; subst; eauto.
    + elimtype False; eauto using can_form_tvar.
    + destruct (IHwt Sr0 v eq_refl) as (vr & eq & inc').
      exists vr; split; auto; intros ? ? Srl.
      destruct (incl _ _ Srl) as [S0 Sr0l]; eauto.
Qed.

Lemma get_value {tr : Rec} {k t} :
  tr k = Some t -> RValue tr -> Value t.
Proof.
  induction tr; simpl; intros; try discriminate; destruct (eq_lab_dec k l);
    destruct_conjs; inversion H; subst; auto.
Qed.

Lemma matching_defined {Γ p S Δ} (wp: PTyping Γ p S Δ) :
  ∀ {v}, Value v → Typing Γ v S → ∀ t, ∃ t', Match p v t t'.
Proof.
  induction wp using ind_ptyping with
  (P0 := fun Γ pr (Sr : TRec) Δ wpr =>
           ∀ {vr}, RValue vr →
             (∀ l S, Sr l = Some S → ∃ v, vr l = Some v ∧ Typing Γ v S) →
             ∀ t, ∃ t', RMatch pr vr t t').
  - intros v val_v wv t.
    exists (substTm X0 v t).
    refine M_Var.
  - intros v val_v wv t.
    destruct (can_form_trec val_v wv) as (vr & eq & inc); subst.
    pose proof (typing_rec_inversion wv (sub_refl (typing_wf wv))).
    destruct (IHwp vr val_v H t) as [t' m].
    exists t'; constructor; auto.
  - rename e into Trl; intros vr val_vr wvr t.
    assert ((∀ (l0 : Lab) (S : Ty),
           (weakenTRec Tr (domainEnv Δp)) l0 = Some S
           → ∃ v : Tm,
             (weakenRec vr (domainEnv Δp)) l0 = Some v
             ∧ Typing (appendEnv Γ Δp) v S)).
    { intros k Sk; generalize (wvr k); simpl.
      rewrite get_weaken_trec.
      case (eq_lab_dec k l); intros; subst.
      - rewrite Trl in H0; discriminate.
      - remember (Tr k) as Trk; destruct Trk as [Tk|]; simpl in *.
        + inversion H0; subst; try discriminate.
          destruct (H Tk eq_refl) as [vk [eqvk wvk]].
          exists (weakenTm vk (domainEnv Δp)); split; auto.
          rewrite get_weaken_rec, eqvk; auto.
          eapply weaken_typing; eauto.
        + discriminate.
    }
    destruct (IHwp0 (weakenRec vr (domainEnv Δp))
                 (weaken_rvalue (domainEnv Δp) val_vr) H t) as [t' mr].
    simpl in wvr; pose proof (wvr l); destruct (eq_lab_dec l l); intuition.
    destruct (H0 _ eq_refl) as (vp, (vrl, wvp)).
    destruct (IHwp vp (get_value vrl val_vr) wvp t') as [t'' m].
    exists t''; econstructor; eauto.
    rewrite (PTyping_bindPat_domainEnv wp); eauto.
  - eauto using RMatch.
Qed.

Lemma progress {Γ t U} (wt: Typing Γ t U) :
  Γ = empty → Value t ∨ ∃ t', red t t'.
Proof with destruct_conjs; subst; simpl; eauto using red, rred.
  induction wt using ind_typing with
  (P0 := fun Γ tr Tr wtr => Γ = empty → RValue tr ∨ ∃ tr', rred tr tr');
    intros...
  - inversion l.
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  - destruct IHwt as [vt|[t1' r1]]...
    destruct (can_form_tall vt wt)...
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct (matching_defined p0 v1 wt1 t2)...
  - destruct IHwt as [vt|[t1' r1]]...
  - destruct IHwt as [vt|[t1' r1]]...
    destruct (can_form_trec vt wt)...
    destruct (H0 l T lIn) as [v H].
    pose proof (get_value H vt)...
  - destruct IHwt as [vt|[t1' r']]...
    destruct IHwt0 as [vr|[tr' rr]]...
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

Lemma local_preservation_lett {Γ p Tp Δp} (wp: PTyping Γ p Tp Δp) :
  ∀ {v u u' U}, Typing Γ v Tp →
    Typing (appendEnv Γ Δp) u (weakenTy U (domainEnv Δp)) →
    Match p v u u' → Typing Γ u' U.
Proof.
  induction wp using ind_ptyping with (P0 :=
      fun Γ pr Tr Δpr (wpr: PRTyping Γ pr Tr Δpr) =>
        ∀ (vr : Rec) u u' U,
          (∀ l S, Tr l = Some S → ∃ v, vr l = Some v ∧ Typing Γ v S) →
          Typing (appendEnv Γ Δpr) u (weakenTy U (domainEnv Δpr)) →
          RMatch pr vr u u' →
          Typing Γ u' U).
  - intros v u u' U wv wu m.
    dependent destruction m.
    eauto using subst_evar_typing with infra.
  - intros v u u' U wv wu m.
    dependent destruction m.
    eauto using typing_rec_inversion, sub_refl, typing_wf.
  - intros vr u u' U vtypes wu rm.
    dependent destruction rm.
    assert (∀ (l0 : Lab) (S : Ty),
        (weakenTRec Tr (domainEnv Δp)) l0 = Some S
        → ∃ v0 : Tm,
          (weakenRec vr (domainEnv Δp)) l0 = Some v0
          ∧ Typing (appendEnv Γ Δp) v0 S) as vtypes'.
    { intros k Sk; specialize (vtypes k); simpl in vtypes.
      rewrite get_weaken_trec, get_weaken_rec.
      destruct (eq_lab_dec k l); simpl; subst.
      * rewrite vIn, e; discriminate.
      * induction (Tr k); try discriminate; simpl.
        intro eqSk; inversion eqSk; subst; clear eqSk.
        destruct (vtypes a eq_refl) as [vk [eqvk wvk]].
        rewrite eqvk; simpl; eauto using weaken_typing.
    }
    rewrite appendEnv_assoc, domainEnv_appendEnv, <- weakenTy_append in wu.
    specialize (vtypes l Tp); simpl in vtypes.
    destruct (eq_lab_dec l l); intuition.
    destruct H0 as [v' [eqv wv']].
    rewrite (PTyping_bindPat_domainEnv wp) in rm.
    rewrite vIn in eqv; inversion eqv; subst; eauto.
  - intros; dependent destruction H1; eauto.
Qed.

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt using ind_typing
  with (P0 := fun Γ tr Tr wtr => ∀ {tr'}, rred tr tr' → RTyping Γ tr' Tr);
    intros t' rd; inversion rd; subst; eauto using Typing, RTyping.
  - destruct (t_abs_inversion wt1 (sub_refl (typing_wf wt1))).
    eauto using subst_evar_typing, T_Sub with subst.
  - destruct (t_tabs_inversion wt (sub_refl (typing_wf wt))).
    eauto using subst_etvar_typing, T_Sub with infra.
  - eauto using local_preservation_lett.
  - destruct (typing_rec_inversion wt (sub_refl (typing_wf wt)) _ lIn)
      as [t'' [eq'' wt'']].
    rewrite H3 in eq''; inversion eq''; subst; auto.
Qed.
