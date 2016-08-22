Require Import Specification.
Require Import Restrictions.

Ltac crushRewriteH :=
  autorewrite with infra in *.

Ltac crushMatchH :=
  match goal with
    | [ H: ?x = ?x |- _ ] => clear H
    | [ H: ?x ≠ ?x |- _ ] => destruct H
    | [ H: _ ∧ _   |- _ ] => destruct H

    (* Domains *)
    | [ H: S _ = S _     |- _ ] => apply eq_add_S in H
    | [ |- S _ = S _ ] => f_equal

    (* Environments *)
    | [ H : _ ▻ _ = _ ▻ _ |- _ ] =>
      inversion H; clear H
    | [ H : [_] = _ ▻ _ |- _ ] =>
      unfold singleton in H; inversion H; clear H
    | [ H : _ ▻ _ = [_] |- _ ] =>
      unfold singleton in H; inversion H; clear H
    | [ |- _ ▻ _ = _ ▻ _ ] => f_equal

    (* Partitioning *)
    | [ H: match ?i with _ => _ end = inl _ |- _ ] =>
      destruct i eqn: ?
    | [ H: match ?i with _ => _ end = inr _ |- _ ] =>
      destruct i eqn: ?
    | [ |- pleft _ = pleft _ ] => f_equal
    | [ |- pright _ = pright _ ] => f_equal

    (* Env partitioning *)
    | [ pe: ⟪ _        ⊢ _       = ε ∘ _ ⟫ |- _ ] =>
      apply partEnv_leftEmpty in pe; destruct pe
    (* | [ pe: ⟪ _        ⊢ _       = _ ∘ ε ⟫ |- _ ] => *)
    (*   apply partEnv_rightEmpty in pe; destruct pe *)
    | [ pe: ⟪ _        ⊢ ε       = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
    | [ pe: ⟪ _        ⊢ _       = ε ∘ ε ⟫ |- _ ] => inversion pe; clear pe
    | [ pe: ⟪ pnil     ⊢ _       = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
    | [ pe: ⟪ _        ⊢ (_ ▻ _) = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
    | [ pe: ⟪ pleft _  ⊢ _       = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
    | [ pe: ⟪ pright _ ⊢ _       = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe

    | [ |- ⟪ pleft _   ⊢ _ = _ ∘ _ ⟫ ] => econstructor
    | [ |- ⟪ pright _  ⊢ _ = _ ∘ _ ⟫ ] => econstructor
    | [ |- ⟪ plefts _  ⊢ _ = _ ∘ _ ⟫ ] => eapply partEnv_plefts
    (* | [ |- ⟪ prights _ ⊢ _ = _ ∘ _ ⟫ ] => eapply partEnv_prights *)

    | [ H: ⟪ ?pΓΔ ⊢ ?ΓΔ = ?Γ ∘ _ ⟫ |- context[leftEnv ?pΓΔ ?ΓΔ] ] =>
      replace (leftEnv pΓΔ ΓΔ) with Γ by apply eq_sym, (leftEnv_sound H)
    (* | [ H: ⟪ ?pΓΔ ⊢ ?ΓΔ = _ ∘ ?Δ ⟫ |- context[rightEnv ?pΓΔ ?ΓΔ] ] => *)
    (*   replace (rightEnv pΓΔ ΓΔ) with Δ by apply eq_sym, (rightEnv_sound H) *)
    | [ H: ⟪ ?pΓΔ ⊢ ?ΓΔ = _ ∘ _ ⟫ |- context[domPart ?pΓΔ] ] =>
      replace (domPart pΓΔ) with (dom ΓΔ) by apply eq_sym, (domPart_sound H)
    | [ H: ⟪ ?pΓΔ ⊢ _ = ?Γ ∘ _ ⟫ |- context[domPartLeft ?pΓΔ] ] =>
      replace (domPartLeft pΓΔ) with (dom Γ) by apply eq_sym, (domPartLeft_sound H)
    (* | [ H: ⟪ ?pΓΔ ⊢ _ = _ ∘ ?Δ ⟫ |- context[domPartRight ?pΓΔ] ] => *)
    (*   replace (domPartRight pΓΔ) with (dom Δ) by apply eq_sym, (domPartRight_sound H) *)

    (* Substitution *)
    | [ w: ⟪ _ : ε     => _ ⟫ |- _ ] => inversion w; clear w
    | [ w: ⟪ _ : [_]   => _ ⟫ |- _ ] => inversion w; clear w
    | [ w: ⟪ _ : _ ▻ _ => _ ⟫ |- _ ] => inversion w; clear w
    | [ w: ⟪ ?ζ : _ => ?Δ ⟫ |- context[codSub ?ζ] ] =>
      replace (codSub ζ) with (dom Δ) by apply eq_sym, (codSub_sound w)
    | [ |- ⟪ _ : ε     => _ ⟫ ] => econstructor
    | [ |- ⟪ _ : [_]   => _ ⟫ ] => econstructor
    | [ |- ⟪ _ : _ ▻ _ => _ ⟫ ] => econstructor
    | [ |- snoc _ _ _ = snoc _ _ _ ] => f_equal

    (* Typing *)
    | [ |- ⟪ _ ⊢ var : _ ⟫ ] => econstructor
    | [ |- ⟪ _ ⊢ abs _ _ : _ ⟫ ] => econstructor
    | [ |- ⟪ _ ⊢ app _ _ _ : _ ⟫ ] => econstructor
  end.

Ltac crush :=
  intros;
  repeat
    (simpl in *;
     try crushRewriteH;
     try crushMatchH;
     crushRestrictH;
     try subst;
     try discriminate;
     eauto with infra
    ).

(******************************************************************************)

Fixpoint subCat (pΓ pΔ: Part) (ζ₁ ζ₂: Sub) : Sub :=
  match pΓ with
    | pnil  => snil
    | pleft pΓ =>
      match ζ₁ with
        | snil => snil (* IMPOSSIBLE *)
        | snoc pΣ ζ₁ t =>
          snoc
            (restrictLeftLeftPart pΔ pΣ)
            (subCat pΓ (restrictLeftLeftPart' pΔ pΣ) ζ₁ ζ₂)
            t
      end
    | pright pΓ =>
      match ζ₂ with
        | snil => snil (* IMPOSSIBLE *)
        | snoc pΣ ζ₂ t =>
          snoc
            (restrictRightLeftPart pΔ pΣ)
            (subCat pΓ (restrictRightLeftPart' pΔ pΣ) ζ₁ ζ₂)
            t
      end
  end.

Lemma wtSubCat {pΓ Γ Γ₁ Γ₂} (peΓ : ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ {pΔ Δ Δ₁ Δ₂ ζ₁ ζ₂},
  ⟪ pΔ ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ →
  ⟪ ζ₁ : Γ₁ => Δ₁⟫ →
  ⟪ ζ₂ : Γ₂ => Δ₂⟫ →
  ⟪ subCat pΓ pΔ ζ₁ ζ₂ : Γ => Δ ⟫.
Proof. induction peΓ; crush. Qed.
Hint Resolve wtSubCat : infra.


Fixpoint splitSubPart (pΓ: Part) (ζ: Sub) : Part :=
  match pΓ , ζ with
    | pnil        , _           => pnil
    | pleft pΓ    , snil        => pnil (* IMPOSSIBLE *)
    | pleft pΓ    , snoc pΔ ζ t => restrictLeftLeftPart pΔ (splitSubPart pΓ ζ)
    | pright pΓ   , snil        => pnil (* IMPOSSIBLE *)
    | pright pΓ   , snoc pΔ ζ t => restrictLeftRightPart pΔ (splitSubPart pΓ ζ)
  end.

Fixpoint splitSubEnvLeft (pΓ: Part) (Δ: Env) (ζ: Sub) : Env :=
  match pΓ , ζ with
    | pnil        , _           => ε
    | pleft pΓ    , snil        => ε (* IMPOSSIBLE *)
    | pleft pΓ    , snoc pΔ ζ t => restrictLeftLeftEnv pΔ (splitSubPart pΓ ζ) Δ
    | pright pΓ   , snil        => ε (* IMPOSSIBLE *)
    | pright pΓ   , snoc pΔ ζ t => splitSubEnvLeft pΓ (leftEnv pΔ Δ) ζ
  end.

Fixpoint splitSubEnvRight (pΓ: Part) (Δ: Env) (ζ: Sub) : Env :=
  match pΓ , ζ with
    | pnil        , _           => ε
    | pleft pΓ    , snil        => ε (* IMPOSSIBLE *)
    | pleft pΓ    , snoc pΔ ζ t => splitSubEnvRight pΓ (leftEnv pΔ Δ) ζ
    | pright pΓ   , snil        => ε (* IMPOSSIBLE *)
    | pright pΓ   , snoc pΔ ζ t => restrictLeftRightEnv pΔ (splitSubPart pΓ ζ) Δ
  end.

Lemma splitSubPart_sound {Γ Δ ζ} (wζ : ⟪ ζ : Γ => Δ ⟫) :
  ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  ⟪ splitSubPart pΓ ζ ⊢ Δ = splitSubEnvLeft pΓ Δ ζ ∘ splitSubEnvRight pΓ Δ ζ ⟫.
Proof. induction wζ; crush. Qed.
Hint Resolve splitSubPart_sound : infra.

Fixpoint splitSubLeft (pΓ: Part) (ζ: Sub) : Sub :=
  match pΓ , ζ with
    | pnil        , _           => snil
    | pleft pΓ    , snil        => snil (* IMPOSSIBLE *)
    | pleft pΓ    , snoc pΔ ζ t =>
      snoc
        (restrictLeftLeftPart' pΔ (splitSubPart pΓ ζ))
        (splitSubLeft pΓ ζ) t
    | pright pΓ   , snil        => snil (* IMPOSSIBLE *)
    | pright pΓ   , snoc pΔ ζ t => splitSubLeft pΓ ζ
  end.

Fixpoint splitSubRight (pΓ: Part) (ζ: Sub) : Sub :=
  match pΓ , ζ with
    | pnil        , _           => snil
    | pleft pΓ    , snil        => snil (* IMPOSSIBLE *)
    | pleft pΓ    , snoc pΔ ζ t => splitSubRight pΓ ζ
    | pright pΓ   , snil        => snil (* IMPOSSIBLE *)
    | pright pΓ   , snoc pΔ ζ t =>
      snoc
        (restrictLeftRightPart' pΔ (splitSubPart pΓ ζ))
        (splitSubRight pΓ ζ) t
  end.

Lemma splitSubLeft_sound {ζ Γ Δ} (wζ : ⟪ ζ : Γ => Δ ⟫) :
  ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
   ⟪ splitSubLeft pΓ ζ : Γ₁ => splitSubEnvLeft pΓ Δ ζ ⟫.
Proof. induction wζ; crush. Qed.
Hint Resolve splitSubLeft_sound : infra.

Lemma splitSubRight_sound {ζ Γ Δ} (wζ : ⟪ ζ : Γ => Δ ⟫) :
  ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
   ⟪ splitSubRight pΓ ζ : Γ₂ => splitSubEnvRight pΓ Δ ζ ⟫.
Proof. induction wζ; crush. Qed.
Hint Resolve splitSubRight_sound : infra.


Lemma splitSubPart_subCat {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ {pΔ Δ Δ₁ Δ₂ ζ₁ ζ₂},
    ⟪ pΔ ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ → ⟪ ζ₁ : Γ₁ => Δ₁ ⟫ → ⟪ ζ₂ : Γ₂ => Δ₂ ⟫ →
    splitSubPart pΓ (subCat pΓ pΔ ζ₁ ζ₂) = pΔ.
Proof.
  induction peΓ; crush.
  - erewrite IHpeΓ; crush.
  - erewrite IHpeΓ; crush.
Qed.

Lemma splitSubLeft_subCat_beta {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ {pΔ Δ Δ₁ Δ₂ ζ₁ ζ₂},
    ⟪ pΔ ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ → ⟪ ζ₁ : Γ₁ => Δ₁ ⟫ → ⟪ ζ₂ : Γ₂ => Δ₂ ⟫ →
    splitSubLeft pΓ (subCat pΓ pΔ ζ₁ ζ₂) = ζ₁.
Proof.
  induction peΓ; crush.
  erewrite splitSubPart_subCat; crush.
Qed.

Lemma splitSubRight_subCat_beta {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ {pΔ Δ Δ₁ Δ₂ ζ₁ ζ₂},
    ⟪ pΔ ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ → ⟪ ζ₁ : Γ₁ => Δ₁ ⟫ → ⟪ ζ₂ : Γ₂ => Δ₂ ⟫ →
    splitSubRight pΓ (subCat pΓ pΔ ζ₁ ζ₂) = ζ₂.
Proof.
  induction peΓ; crush.
  erewrite splitSubPart_subCat; crush.
Qed.

Lemma subCat_splitSub_eta {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ ζ Σ, ⟪ ζ : ΓΔ => Σ ⟫ →
    subCat pΓΔ (splitSubPart pΓΔ ζ)
      (splitSubLeft pΓΔ ζ) (splitSubRight pΓΔ ζ) = ζ.
Proof. induction peΓΔ; crush. Qed.

Lemma splitSubPart_plefts {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  splitSubPart (plefts (dom Γ)) ζ = plefts (dom Δ).
Proof.
  induction wζ; crush.
  - rewrite IHwζ.
    erewrite restrictLeftLeftPart_part_plefts; eauto.
Qed.

Lemma splitSubPart_prights {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  splitSubPart (prights (dom Γ)) ζ = prights (dom Δ).
Proof.
  induction wζ; crush.
  - rewrite IHwζ.
    erewrite restrictLeftRightPart_part_prights; eauto.
Qed.

Lemma splitSubLeft_plefts {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  splitSubLeft (plefts (dom Γ)) ζ = ζ.
Proof.
  induction wζ; crush.
  - erewrite splitSubPart_plefts; eauto.
    erewrite restrictLeftLeftPart'_part_plefts; eauto.
Qed.

Lemma splitSubLeft_prights {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  splitSubLeft (prights (dom Γ)) ζ = snil.
Proof. induction wζ; crush. Qed.

Lemma splitSubRight_prights {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  splitSubRight (prights (dom Γ)) ζ = ζ.
Proof.
  induction wζ; crush.
  - erewrite splitSubPart_prights; eauto.
    erewrite restrictLeftRightPart'_part_prights; eauto.
Qed.


Lemma splitSubPart_subId {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  splitSubPart pΓ (subId (dom Γ)) = pΓ.
Proof. induction peΓ; crush. Qed.

Lemma splitSubLeft_subId {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  splitSubLeft pΓΔ (subId (dom ΓΔ)) = subId (dom Γ).
Proof.
  induction peΓΔ; crush.
  - unfold subUp; crush.
    erewrite splitSubPart_subId; eauto.
    erewrite restrictLeftLeftPart'_plefts_part; eauto.
Qed.

Lemma splitSubRight_subId {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  splitSubRight pΓΔ (subId (dom ΓΔ)) = subId (dom Δ).
Proof.
  induction peΓΔ; crush.
  - unfold subUp; crush.
    erewrite splitSubPart_subId; eauto.
    erewrite restrictLeftRightPart'_plefts_part; eauto.
Qed.

Fixpoint subTm (ζ: Sub) (t: Tm) : Tm :=
  match t with
    | var => match ζ with
               | snil => var (* IMPOSSIBLE *)
               | snoc _ _ t => t
             end
    | abs a t =>
      abs a (subTm (subUp ζ) t)
    | app pΓ t₁ t₂ =>
      app
        (splitSubPart pΓ  ζ)
        (subTm (splitSubLeft pΓ ζ) t₁)
        (subTm (splitSubRight pΓ ζ) t₂)
  end.

(* The substitution lemma. *)
Lemma wtSubTm {Γ t a} (wt: ⟪ Γ ⊢ t : a ⟫) :
  ∀ ζ Δ, ⟪ ζ : Γ => Δ ⟫ → ⟪ Δ ⊢ subTm ζ t : a ⟫.
Proof. induction wt; crush. Qed.
Hint Resolve wtSubTm : infra.

Reserved Notation "σ₁ >=> σ₂" (at level 42, left associativity).
Fixpoint subComp (ξ ζ: Sub) : Sub :=
  match ξ with
    | snil        => ζ
    | snoc pΔ ξ t =>
      snoc
        (splitSubPart pΔ ζ)
        (ξ >=> splitSubLeft pΔ ζ)
        (subTm (splitSubRight pΔ ζ) t)
  end
where "ξ >=> ζ" := (subComp ξ ζ).

Lemma wtSubComp {ξ Γ Δ} (wξ: ⟪ ξ : Γ => Δ ⟫) :
  ∀ {ζ Σ}, ⟪ ζ : Δ => Σ ⟫ → ⟪ (ξ >=> ζ) : Γ => Σ ⟫.
Proof. induction wξ; crush. Qed.
Hint Resolve wtSubComp : infra.

Lemma subTmId {Γ t a} (wt: ⟪ Γ ⊢ t : a ⟫) :
  subTm (subId (dom Γ)) t = t.
Proof.
  induction wt; crush.
  - f_equal.
    eapply IHwt.
  - erewrite splitSubPart_subId; eauto.
    erewrite splitSubLeft_subId; eauto.
    erewrite splitSubRight_subId; eauto.
    f_equal; auto.
Qed.

Lemma subCompIdRight {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  ζ >=> subId (dom Δ) = ζ.
Proof.
  induction wζ; crush; simpl.
  eapply splitSubPart_subId; eauto.
  erewrite splitSubLeft_subId; eauto.
  erewrite splitSubRight_subId; eauto.
  erewrite subTmId; eauto.
Qed.

Lemma subCompIdLeft {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  subId (dom Γ) >=> ζ = ζ.
Proof.
  induction wζ; crush.
  - erewrite splitSubPart_plefts; eauto.
    erewrite restrictLeftRightPart_part_plefts; eauto.
  - erewrite splitSubLeft_plefts; eauto.
Qed.

Lemma domPart_restrictLeftLeftPart {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
    domPart (restrictLeftLeftPart pΓΔ pΓ) = dom ΓΔ.
Proof. induction peΓΔ; crush. Qed.

Lemma domPart_restrictLeftRightPart {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
    domPart (restrictLeftRightPart pΓΔ pΓ) = dom ΓΔ.
Proof. induction peΓΔ; crush. Qed.

Lemma domPart_splitSubPart {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂}, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
    domPart (splitSubPart pΓ ζ) = dom Δ.
Proof.
  induction wζ; crush.
  - erewrite domPart_restrictLeftLeftPart; crush.
  - erewrite domPart_restrictLeftRightPart; crush.
Qed.

Lemma codSub_subComp {Γ Δ ξ} (wξ: ⟪ ξ : Γ => Δ⟫) :
  ∀ ζ Σ, ⟪ ζ : Δ => Σ⟫ → codSub (ξ >=> ζ) = codSub ζ.
Proof.
  induction wξ; crush.
  eapply domPart_splitSubPart; eauto.
Qed.

Lemma subUpComp {Γ Δ Σ ζ₁ ζ₂} (wζ₁: ⟪ ζ₁ : Γ => Δ⟫) (wζ₂: ⟪ ζ₂ : Δ => Σ⟫) :
  subUp (ζ₁ >=> ζ₂) = subUp ζ₁ >=> subUp ζ₂.
Proof.
  unfold subUp; crush.
  - erewrite splitSubPart_plefts; crush.
    erewrite codSub_subComp; crush.
  - erewrite splitSubLeft_plefts; eauto.
Qed.

Lemma restrictLeftLeftPart_restrictLeftLeftPart
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂ pΓ₁ Γ₁₁ Γ₁₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ pΓ₁ ⊢ Γ₁ = Γ₁₁ ∘ Γ₁₂ ⟫ →
  restrictLeftLeftPart pΓΔ (restrictLeftLeftPart pΓ pΓ₁) =
  restrictLeftLeftPart (restrictLeftRightPart pΓΔ pΓ) pΓ₁.
Proof. induction peΓΔ; crushRestrict. Qed.

Lemma restrictLeftLeftPart_restrictLeftRightPart
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂ pΓ₁ Γ₁₁ Γ₁₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ pΓ₁ ⊢ Γ₁ = Γ₁₁ ∘ Γ₁₂ ⟫ →
    restrictLeftLeftPart pΓΔ (restrictLeftRightPart pΓ pΓ₁) =
    restrictLeftRightPart (restrictLeftLeftPart pΓΔ pΓ)
      (restrictLeftLeftPart (restrictLeftLeftPart' pΓΔ pΓ) pΓ₁).
Proof. induction peΓΔ; crushRestrict. Qed.

(* Lemma restrictLeftLeftPart'_restrictLeftRightPart *)
(*   {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   ∀ {pΓ Γ₁ Γ₂ pΓ₁ Γ₁₁ Γ₁₂}, *)
(*     ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ pΓ₁ ⊢ Γ₁ = Γ₁₁ ∘ Γ₁₂ ⟫ → *)
(*     restrictLeftLeftPart' pΓΔ (restrictLeftRightPart pΓ pΓ₁) = *)
(*     restrictLeftLeftPart' (restrictLeftLeftPart' pΓΔ pΓ) pΓ₁. *)
(* Proof. induction peΓΔ; crushRestrict. Qed. *)

Lemma restrictLeftRightPart_restrictLeftLeftPart
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂ pΓ₁ Γ₁₁ Γ₁₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ pΓ₁ ⊢ Γ₁ = Γ₁₁ ∘ Γ₁₂ ⟫ →
  restrictLeftRightPart pΓΔ (restrictLeftLeftPart pΓ pΓ₁) =
  restrictLeftLeftPart (restrictLeftLeftPart pΓΔ pΓ)
    (restrictLeftRightPart (restrictLeftLeftPart' pΓΔ pΓ) pΓ₁).
Proof. induction peΓΔ; crushRestrict. Qed.

Lemma restrictLeftRightPart_restrictLeftRightPart
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂ pΓ₁ Γ₁₁ Γ₁₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ pΓ₁ ⊢ Γ₁ = Γ₁₁ ∘ Γ₁₂ ⟫ →
    restrictLeftRightPart pΓΔ (restrictLeftRightPart pΓ pΓ₁) =
    restrictLeftRightPart (restrictLeftRightPart pΓΔ pΓ) pΓ₁.
Proof. induction peΓΔ; crushRestrict. Qed.

(* Lemma restrictLeftLeftPart_restrictLeftLeftPart' *)
(*   {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   ∀ {pΓ Γ₁ Γ₂ pΓ₁ Γ₁₁ Γ₁₂}, *)
(*     ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → *)
(*     ⟪ pΓ₁ ⊢ Γ₁ = Γ₁₁ ∘ Γ₁₂ ⟫ → *)
(*     restrictLeftLeftPart *)
(*       (restrictLeftLeftPart' pΓΔ (restrictLeftLeftPart pΓ pΓ₁)) *)
(*       (restrictLeftLeftPart' pΓ pΓ₁) = *)
(*     restrictLeftLeftPart' (restrictLeftLeftPart pΓΔ pΓ) *)
(*       (restrictLeftLeftPart (restrictLeftLeftPart' pΓΔ pΓ) pΓ₁). *)
(* Proof. induction peΓΔ; crushRestrict. Qed. *)

Lemma splitSubPart_restrictLeftLeftPart
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂ ξ Σ},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ ξ : ΓΔ => Σ ⟫ →
    splitSubPart (restrictLeftLeftPart pΓΔ pΓ) ξ =
    restrictLeftLeftPart (splitSubPart pΓΔ ξ)
      (splitSubPart pΓ (splitSubLeft pΓΔ ξ)).
Proof.
  induction peΓΔ; crush.
  - erewrite IHpeΓΔ; crush.
    erewrite restrictLeftLeftPart_restrictLeftLeftPart; crush.
    erewrite restrictLeftLeftPart_restrictLeftLeftPart; crush.
  - erewrite IHpeΓΔ; crush.
    erewrite restrictLeftRightPart_restrictLeftLeftPart; crush.
  - erewrite IHpeΓΔ; crush.
    erewrite restrictLeftLeftPart_restrictLeftLeftPart; crush.
Qed.

Lemma splitSubPart_restrictLeftRightPart
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂ ξ Σ},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ ξ : ΓΔ => Σ ⟫ →
    splitSubPart (restrictLeftRightPart pΓΔ pΓ) ξ =
    restrictLeftRightPart (splitSubPart pΓΔ ξ)
      (splitSubPart pΓ (splitSubLeft pΓΔ ξ)).
Proof.
  induction peΓΔ; crush.
  - erewrite IHpeΓΔ; crush.
    erewrite restrictLeftLeftPart_restrictLeftRightPart; crush.
  - erewrite IHpeΓΔ; crush.
    erewrite restrictLeftRightPart_restrictLeftRightPart; crush.
    erewrite restrictLeftRightPart_restrictLeftRightPart; crush.
  - erewrite IHpeΓΔ; crush.
    erewrite restrictLeftRightPart_restrictLeftRightPart; crush.
Qed.

(* Lemma splitSubLeft_restrictLeftRightPart *)
(*   {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   ∀ {pΓ Γ₁ Γ₂ ζ Σ}, *)
(*     ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ ζ : ΓΔ => Σ ⟫ → *)
(*   splitSubLeft (restrictLeftRightPart pΓΔ pΓ) ζ = *)
(*   splitSubLeft pΓ (splitSubLeft pΓΔ ζ). *)
(* Proof. *)
(*   induction peΓΔ; crush. *)
(*   erewrite splitSubPart_restrictLeftRightPart; crush. *)
(* Qed. *)

Lemma splitSubPartComp {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ⟫) :
  ∀ {pΓ Γ₁ Γ₂ ξ Σ},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ ξ : Δ => Σ ⟫ →
    splitSubPart (splitSubPart pΓ ζ) ξ  =
    splitSubPart pΓ (ζ >=> ξ).
Proof.
  induction wζ; crush.
  - erewrite splitSubPart_restrictLeftLeftPart; crush.
    erewrite IHwζ; crush.
  - erewrite splitSubPart_restrictLeftRightPart; crush.
    erewrite IHwζ; crush.
Qed.


(* Lemma restrictLeftLeftPart'_restrictLeftLeftPart *)
(*   {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   ∀ {pΓ Γ₁ Γ₂ pΓ₁ Γ₁₁ Γ₁₂}, *)
(*     ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → *)
(*     ⟪ pΓ₁ ⊢ Γ₁ = Γ₁₁ ∘ Γ₁₂ ⟫ → *)
(*     restrictLeftLeftPart' (restrictLeftLeftPart pΓΔ pΓ) *)
(*       (restrictLeftRightPart (restrictLeftLeftPart' pΓΔ pΓ) pΓ₁) = *)
(*     restrictLeftLeftPart' pΓ pΓ₁. *)
(* Proof. *)
(*   intros. *)
(*   erewrite restrictLeftLeftPart'_restrictLeftRightPart; eauto with infra. *)
(*   crush. *)
(* Qed. *)

(* Lemma splitSubPart_restrictLeftLeftPart' *)
(*   {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   ∀ {pΓ Γ₁ Γ₂ ζ Σ}, *)
(*     ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ ζ : ΓΔ => Σ ⟫ → *)
(*     splitSubPart (restrictLeftLeftPart' pΓΔ pΓ) *)
(*       (splitSubLeft (restrictLeftLeftPart pΓΔ pΓ) ζ) = *)
(*     restrictLeftLeftPart' (splitSubPart pΓΔ ζ) *)
(*       (splitSubPart pΓ (splitSubLeft pΓΔ ζ)). *)
(* Proof. *)
(*   induction peΓΔ; crush. *)
(*   - erewrite IHpeΓΔ; crush. *)
(*     erewrite splitSubPart_restrictLeftLeftPart; crush. *)
(*     erewrite restrictLeftLeftPart_restrictLeftLeftPart'; crush. *)
(*   - erewrite IHpeΓΔ; crush. *)
(*     erewrite restrictLeftLeftPart'_restrictLeftRightPart; crush. *)
(*   - erewrite IHpeΓΔ; crush. *)
(*     erewrite splitSubPart_restrictLeftLeftPart; crush. *)
(* Admitted. *)

Lemma splitSubLeftComp {Γ Δ ξ} (wξ: ⟪ ξ : Γ => Δ⟫) :
  ∀ {pΓ Γ₁ Γ₂ ζ Σ},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ ζ : Δ => Σ⟫ →
    splitSubLeft pΓ ξ >=> splitSubLeft (splitSubPart pΓ ξ) ζ =
    splitSubLeft pΓ (ξ >=> ζ).
Proof.
Admitted.

Lemma splitSubRightComp {Γ Δ ξ} (wξ: ⟪ ξ : Γ => Δ⟫) :
  ∀ {pΓ Γ₁ Γ₂ ζ Σ},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ ζ : Δ => Σ⟫ →
    splitSubRight pΓ ξ >=> splitSubRight (splitSubPart pΓ ξ) ζ =
    splitSubRight pΓ (ξ >=> ζ).
Proof.
  induction wξ; crush.
Admitted.

Lemma subTmComp {Γ t a} (wt : ⟪ Γ ⊢ t : a ⟫) :
  ∀ {Δ Σ ζ₁ ζ₂} (wζ₁: ⟪ ζ₁ : Γ => Δ ⟫) (wζ₂: ⟪ ζ₂ : Δ => Σ ⟫),
    subTm ζ₂ (subTm ζ₁ t) = subTm (ζ₁ >=> ζ₂) t.
Proof.
  induction wt; crush.
  - erewrite splitSubRight_prights; eauto.
  - erewrite subUpComp; crush.
    erewrite IHwt; crush.
  - f_equal.
    + eapply splitSubPartComp; eauto.
    + erewrite IHwt1; crush. f_equal.
      eapply splitSubLeftComp; eauto.
    + erewrite IHwt2; crush. f_equal.
      eapply splitSubRightComp; eauto.
Qed.

Definition subBeta (t: Tm) (pΓΔ: Part) : Sub :=
  snoc pΓΔ (subId (domPartLeft pΓΔ)) t.

Lemma wtSubBeta {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ t a, ⟪ Δ ⊢ t : a ⟫ →
    ⟪ subBeta t pΓΔ : (Γ ▻ a) => ΓΔ ⟫.
Proof. crush. Qed.
Hint Resolve wtSubBeta : infra.

Lemma subBetaComm {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {t a ζ Σ},
    ⟪ Δ ⊢ t : a ⟫ → ⟪ ζ : ΓΔ => Σ ⟫ →
    subBeta t pΓΔ >=> ζ =
    subUp (splitSubLeft pΓΔ ζ) >=>
    subBeta (subTm (splitSubRight pΓΔ ζ) t) (splitSubPart pΓΔ ζ).
Proof.
  unfold subBeta; crush.
  - erewrite domPartLeft_sound; crush.
    erewrite codSub_sound; crush.
    erewrite splitSubPart_subId; crush.
    erewrite restrictLeftRightPart_part_plefts; crush.
  - erewrite domPartLeft_sound; crush.
    erewrite codSub_sound; crush.
    erewrite splitSubLeft_subId; crush.
    erewrite subCompIdLeft; crush.
    erewrite subCompIdRight; crush.
Qed.

Lemma subBetaComm' {pΓΣ ΓΣ pΔΣ ΔΣ Γ Δ Σ ζ t a} (wζ: ⟪ ζ : Γ => Δ ⟫)
  (wt : ⟪ Σ ⊢ t : a ⟫) (peΓΣ : ⟪ pΓΣ ⊢ ΓΣ = Γ ∘ Σ ⟫) (peΔΣ : ⟪ pΔΣ ⊢ ΔΣ = Δ ∘ Σ ⟫) :
  subUp ζ >=> subBeta t pΔΣ =
  subBeta t pΓΣ >=> subCat pΓΣ pΔΣ ζ (subId (dom Σ)).
Proof.
  unfold subBeta; crush.
  - erewrite splitSubPart_subId; crush.
    erewrite restrictLeftRightPart_part_plefts; crush.
    erewrite splitSubPart_subCat; crush.
  - erewrite splitSubLeft_subCat_beta; crush.
    erewrite splitSubLeft_subId; crush.
    erewrite subCompIdLeft; crush.
    erewrite subCompIdRight; crush.
  - erewrite splitSubRight_subCat_beta; crush.
    erewrite subTmId; crush.
Qed.
