Require Export Coq.Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Specification.
Require Import Restrictions.
Require Import Substitutions.

Fixpoint Value (t: Tm) : Prop :=
  match t with
    | var       => False
    | abs _ _   => True
    | app _ _ _ => False
  end.

Reserved Notation "t₁ --> t₂" (at level 40).
Inductive red : Tm → Tm → Prop :=
  | red_abs {a t t'} :
      t --> t' →
      abs a t --> abs a t'
  | red_app₁ {p t1 t1' t2} :
      t1 --> t1' → app p t1 t2 --> app p t1' t2
  | red_app2 {p t1 t2 t2'} :
      t2 --> t2' → app p t1 t2 --> app p t1 t2'
  | red_beta {p a t1 t2} :
      app p (abs a t1) t2 --> subTm (subBeta t2 p) t1
where "t1 --> t2" := (red t1 t2).
Hint Constructors red : infra.

Lemma red_beta' {p a t₁ t₂ t'} :
  t' = subTm (subBeta t₂ p) t₁ →
  app p (abs a t₁) t₂ --> t'.
Proof.
  intros; subst; constructor.
Qed.

Section TypeSafety.

  Lemma can_form_tarr {Γ t a b}
    (v: Value t) (wt: ⟪ Γ ⊢ t : tarr a b ⟫) :
      ∃ t₂, t = abs a t₂.
  Proof. depind wt; try contradiction; eauto. Qed.

  Lemma progress {t a} (wt: ⟪ empty ⊢ t : a ⟫) :
    Value t ∨ ∃ t', t --> t'.
  Proof with crush.
    depind wt; simpl; auto.
    inversion H; subst.
    destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  Qed.

  Lemma preservation {Γ t a} (wt: ⟪ Γ ⊢ t : a ⟫) :
    ∀ {t'}, t --> t' → ⟪ Γ ⊢ t' : a ⟫.
  Proof.
    induction wt.
    - inversion 1.
    - intros t' r; inversion r; subst.
      econstructor; eauto.
    - intros t' r; inversion r; subst.
      + econstructor; eauto.
      + econstructor; eauto.
      + inversion wt1; subst; crush.
  Qed.

End TypeSafety.

Section StrongNormalization.

  Hint Resolve preservation : infra.

  Lemma red_subst {t t'} (r: t --> t') :
    ∀ a ζ Γ Δ,
      ⟪ Γ ⊢ t : a ⟫ → ⟪ ζ : Γ => Δ ⟫ →
      subTm ζ t --> subTm ζ t'.
  Proof.
    induction r; inversion 1; crush.
    - inversion H6; clear H H6; subst.
      eapply red_beta'.
      erewrite subTmComp; eauto with infra.
      erewrite subTmComp; eauto with infra.
      erewrite subBetaComm; crush.
  Qed.

  Definition Cand := Tm → Prop.
  Definition Neutral : Cand :=
    fun t =>
      match t with
        | abs _ _ => False
        | _       => True
      end.

  Inductive SN (t: Tm) : Prop :=
    | SNi : (∀ t', t --> t' → SN t') → SN t.

  Lemma SNd {t} (sn_t: SN t) : ∀ t', t --> t' → SN t'.
  Proof. destruct sn_t; auto. Qed.

  Lemma SNappl pΓ {t1} t2 :
    SN (app pΓ t1 t2) → SN t1.
  Proof.
    intro sn; depind sn; constructor; crush.
  Qed.

  Lemma SNvar {pΓa Γa Γ a t b} (peΓa: ⟪ pΓa ⊢ Γa = Γ ∘ (ε ▻ a) ⟫)
    (wt: ⟪ Γ ▻ a ⊢ t : b ⟫) (sn: SN (subTm (subBeta var pΓa) t)) : SN t.
  Proof.
    depind sn; constructor.
    - intros.
      eapply H0; eauto.
      eapply red_subst; eauto.
      eapply wtSubBeta; eauto.
      constructor.
      eapply preservation; eauto.
  Qed.

  (* Definition of reducibility candidates. *)
  Record CR (Γ: Env) (a: Ty) (P: Cand) : Prop :=
    { cr_sn : ∀ t, P t → SN t;
      cr_cl : ∀ t, P t → ∀ t', t --> t' → P t';
      cr_nt : ∀ t, (∀ t', t --> t' → P t') →
                   (* Linearity instead of typing should be enough. *)
                   ⟪ Γ ⊢ t : a ⟫ → Neutral t → P t
    }.
  Arguments cr_sn [_ _ _] _ [_] _.
  Arguments cr_cl [_ _ _] _ [_] _ [_] _.
  Arguments cr_nt [_ _ _] _ [_] _ _ _.

  Lemma CR_var {a P} (crP : CR [a] a P) : P var.
  Proof.
    intros; apply (cr_nt crP); simpl; auto; intros.
    - inversion H.
    - constructor.
  Qed.

  Lemma CR_SN : ∀ Γ a, CR Γ a SN.
  Proof. constructor; eauto using SNi, SNd. Qed.

  Definition ARR (a b: Ty) (P R: Env → Cand) : Env → Cand :=
    fun (Γ: Env) (t1: Tm) =>
      ∀ pΓΔ ΓΔ Δ t2,
        ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫ →
        ⟪ Δ ⊢ t2 : a ⟫ →
        P Δ t2 → R ΓΔ (app pΓΔ t1 t2).

  Lemma CR_ARR {a b P R} (CR_P: ∀ Δ, CR Δ a (P Δ)) (CR_R: ∀ ΓΔ, CR ΓΔ b (R ΓΔ)) Γ :
    CR Γ (tarr a b) (ARR a b P R Γ).
  Proof with simpl; eauto using red.
    constructor.
    - intros t ARR_t.
      (* This is soo ugly. *)
      eapply (SNappl (pright (plefts (dom Γ))) var).
      eapply (cr_sn (CR_R (Γ ▻ a))).
      eapply ARR_t; crush.
      eapply CR_var; eauto.
    - intros t ARR_t t' r.
      intros pΓΔ ΓΔ Δ t2 peΓΔ wt2 P_t2.
      eapply (cr_cl (CR_R ΓΔ))...
    - intros t1 Hyp wt1 neutral_t1.
      intros pΓΔ ΓΔ Δ t2 peΓΔ wt2 P_t2.
      assert (wt12: ⟪ ΓΔ ⊢ app pΓΔ t1 t2 : b ⟫)
        by (econstructor; eauto).
      apply (cr_nt (CR_R ΓΔ))...
      generalize (cr_sn (CR_P Δ) P_t2).
      induction 1 as [t2]; intros t12' r.
      inversion r; subst.
      * eapply Hyp...
      * apply (cr_nt (CR_R ΓΔ)); crush.
        eapply H0; crush.
        eapply (cr_cl (CR_P Δ))...
      * destruct neutral_t1.
  Qed.

  Lemma ARR_beta_exp {a b P R}
    (CR_P: ∀ Δ, CR Δ a (P Δ)) (CR_R: ∀ ΓΔ, CR ΓΔ b (R ΓΔ)) Γ :
    ∀ t1,
      ⟪ (Γ ▻ a) ⊢ t1 : b ⟫ →
      (∀ {pΓΔ ΓΔ Δ t2},
         ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫ →
         ⟪ Δ ⊢ t2 : a ⟫ →
         P Δ t2 → R ΓΔ (subTm (subBeta t2 pΓΔ) t1)) →
      ARR a b P R Γ (abs a t1).
  Proof.
    intros t1 wt1 H.
    assert (sn_t1: SN t1).
      apply (@SNvar (pright (plefts (dom Γ))) (Γ ▻ a) Γ a t1 b); crush.
      eapply (cr_sn (CR_R (Γ ▻ a))).
      apply (H (pright (plefts (dom Γ))) (Γ ▻ a) (ε ▻ a) var); crush.
      eapply CR_var; eauto.
    revert H.
    induction sn_t1; intro Hyp.
    intros pΓΔ ΓΔ Δ t2 peΓΔ wt2 P_t2.
    assert (SN_t2: SN t2)
      by (apply (cr_sn (CR_P Δ)); eauto).
    revert pΓΔ ΓΔ peΓΔ.
    induction SN_t2; intros.
    apply (cr_nt (CR_R ΓΔ)); simpl; auto.
    + intros ? r.
      depind r.
      * dependent destruction r; eauto.
        unfold ARR in *.
        eapply H0; eauto using preservation.
        intros.
        eapply (cr_cl (CR_R _)); eauto.
        eapply red_subst; crush.
      * eauto using (cr_cl (CR_P _)) with infra.
      * eapply Hyp; crush.
    + repeat econstructor; eauto.
  Qed.

  (* Type interpretation *)
  Fixpoint Int (a: Ty) (Γ: Env) : Cand :=
    fun t =>
      ⟪ Γ ⊢ t : a ⟫ ∧
      match a with
        | tbase    => SN t
        | tarr a b => ARR a b (Int a) (Int b) Γ t
      end.

  Lemma CR_Int (a: Ty) : ∀ Γ, CR Γ a (Int a Γ).
  Proof with simpl; eauto.
    induction a; simpl; intros;
      [ pose proof (CR_SN Γ tbase) as cr
      | pose proof (CR_ARR IHa1 IHa2 Γ) as cr
      ]; constructor; intros; destruct_conjs; split;
         eauto using (cr_sn cr), (cr_cl cr), preservation.
    - eapply (cr_nt cr); eauto.
      eapply H.
    - eapply (cr_nt cr); eauto.
      eapply H.
  Qed.

  Inductive IntSub : Sub → Env → Env → Prop :=
    | IntEmpty :
        IntSub snil ε ε
    | IntSnoc {ζ Γ pΔ Δ Δ₁ Δ₂ t a} :
        ⟪ pΔ ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ →
        ⟪ Δ₂ ⊢ t : a ⟫ →
        IntSub ζ Γ Δ₁ → Int a Δ₂ t →
        IntSub (snoc pΔ ζ t) (Γ ▻ a) Δ.

  Lemma IntSub_wt {ζ Γ Δ} (iζ: IntSub ζ Γ Δ) :
    ⟪ ζ : Γ => Δ ⟫.
  Proof. induction iζ; crush. Qed.
  Hint Resolve IntSub_wt : infra.

  Lemma Int_splitSubLeft {ζ Γ Δ} (iζ: IntSub ζ Γ Δ) :
    ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
      IntSub (splitSubLeft pΓ ζ) Γ₁ (splitSubEnvLeft pΓ Δ ζ).
  Proof. induction iζ; crush; econstructor; crush. Qed.
  Hint Resolve Int_splitSubLeft : infra.

  Lemma Int_splitSubRight {ζ Γ Δ} (iζ : IntSub ζ Γ Δ) :
    ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
      IntSub (splitSubRight pΓ ζ) Γ₂ (splitSubEnvRight pΓ Δ ζ).
  Proof. induction iζ; crush; econstructor; crush. Qed.
  Hint Resolve Int_splitSubRight : infra.

  Lemma IntSub_subId Γ :
    IntSub (subId (dom Γ)) Γ Γ.
  Proof.
    induction Γ; simpl; econstructor; crush.
    - eapply CR_var, CR_Int.
  Qed.

  Lemma fundamental {Γ t a} (wt: ⟪ Γ ⊢ t : a ⟫) :
    ∀ ζ Δ, IntSub ζ Γ Δ → Int a Δ (subTm ζ t).
  Proof.
    induction wt; intros ζ Δ iζ; simpl; auto.
    - inversion iζ; clear iζ; crush.
      inversion H4; clear H4; crush.
    - assert (⟪ ζ : Γ => Δ ⟫) by crush.
      split. econstructor; crush.
      apply ARR_beta_exp; crush; eauto using CR_Int.
      erewrite subTmComp; crush.
      erewrite splitSubPart_subId; crush.
      erewrite splitSubLeft_subId; crush.
      erewrite restrictLeftRightPart_part_plefts; crush.
      erewrite subCompIdRight; crush.
      apply IHwt; simpl; eauto.
      econstructor; eauto.
    - simpl in *; unfold ARR in *.
      eapply IHwt1; crush.
  Qed.

  Lemma fundamental_id {Γ t a} (wt: ⟪ Γ ⊢ t : a ⟫) : Int a Γ t.
  Proof.
    erewrite <- subTmId; eauto.
    apply (fundamental wt), IntSub_subId.
  Qed.

  Theorem strong_normalization {Γ t a} (wt: ⟪ Γ ⊢ t : a ⟫) : SN t.
  Proof.
    eauto using (cr_sn (CR_Int a Γ)), fundamental_id.
  Qed.

End StrongNormalization.
