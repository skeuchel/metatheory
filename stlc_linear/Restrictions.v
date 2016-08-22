Require Import Specification.

(* Restriction

   Restrict one partitioning with another one. For example given the
   witnesses pΓΔ and pΓ for the partitionings

     pΓΔ ⊢ ΓΔ = Γ ∘ Δ
     pΓ ⊢ Γ = Γ₁ ∘ Γ₂

   there exists witnesses p and p' and environment Σ ⊆ ΓΔ s.t.

     p' ⊢ Σ   = Γ₁ ∘ Δ
     p  ⊢ ΓΔ  = Σ ∘ Δ₂

   We implement functions that calculate the env Σ and ΓΔ for this and
   similar cases. For this example:

     Σ  = restrictLeftLeftEnv pΓΔ pΓ ΓΔ
     p' = restrictLeftLeftPart' pΓΔ pΓ
     p  = restrictLeftLeftPart pΓΔ pΓ
*)

Ltac crushRestrictMatchH :=
  match goal with
    | [ H: S _ = S _     |- _ ] => apply eq_add_S in H
    | [ |- S _ = S _ ] => f_equal

    | [ pe: ⟪ _        ⊢ ε       = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
    | [ pe: ⟪ _        ⊢ (_ ▻ _) = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
    | [ |- _ ▻ _ = _ ▻ _ ] => f_equal
    | [ |- pleft _ = pleft _ ] => f_equal
    | [ |- pright _ = pright _ ] => f_equal
  end.

Ltac crushRestrict :=
  intros;
  repeat
    (simpl in *;
     try crushRestrictMatchH;
     try subst;
     try discriminate
    );
  eauto with infra.

Fixpoint restrictLeftLeftEnv (pΓΔ pΓ: Part) (ΓΔ: Env) : Env :=
  match pΓΔ , pΓ, ΓΔ with
    | pnil,       _         , _      => ε
    | pleft pΓΔ,  pnil      , _      => ε (* IMPOSSIBLE *)
    | pleft pΓΔ,  pleft pΓ  , ε      => ε (* IMPOSSIBLE *)
    | pleft pΓΔ,  pleft pΓ  , ΓΔ ▻ a => restrictLeftLeftEnv pΓΔ pΓ ΓΔ ▻ a
    | pleft pΓΔ,  pright pΓ , ε      => ε (* IMPOSSIBLE *)
    | pleft pΓΔ,  pright pΓ , ΓΔ ▻ a => restrictLeftLeftEnv pΓΔ pΓ ΓΔ
    | pright pΓΔ, pΓ        , ε      => ε (* IMPOSSIBLE *)
    | pright pΓΔ, pΓ        , ΓΔ ▻ a => restrictLeftLeftEnv pΓΔ pΓ ΓΔ ▻ a
  end.

Fixpoint restrictLeftLeftPart' (pΓΔ pΓ: Part) : Part :=
  match pΓΔ , pΓ with
    | pnil,       _         => pnil
    | pleft pΓΔ,  pnil      => pnil (* IMPOSSIBLE *)
    | pleft pΓΔ,  pleft pΓ  => pleft (restrictLeftLeftPart' pΓΔ pΓ)
    | pleft pΓΔ,  pright pΓ => restrictLeftLeftPart' pΓΔ pΓ
    | pright pΓΔ, pΓ        => pright (restrictLeftLeftPart' pΓΔ pΓ)
  end.

Lemma restrictLeftLeft' {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  ⟪ restrictLeftLeftPart' pΓΔ pΓ ⊢ restrictLeftLeftEnv pΓΔ pΓ ΓΔ = Γ₁ ∘ Δ ⟫.
Proof. induction peΓΔ; crushRestrict. Qed.
Hint Resolve restrictLeftLeft' : infra.

Fixpoint restrictLeftLeftPart (pΓΔ pΓ: Part) : Part :=
  match pΓΔ , pΓ with
    | pnil,       _         => pnil
    | pleft pΓΔ,  pnil      => pnil (* IMPOSSIBLE *)
    | pleft pΓΔ,  pleft pΓ  => pleft (restrictLeftLeftPart pΓΔ pΓ)
    | pleft pΓΔ,  pright pΓ => pright (restrictLeftLeftPart pΓΔ pΓ)
    | pright pΓΔ, pΓ        => pleft (restrictLeftLeftPart pΓΔ pΓ)
  end.

Lemma restrictLeftLeft {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  ⟪ restrictLeftLeftPart pΓΔ pΓ ⊢ ΓΔ = restrictLeftLeftEnv pΓΔ pΓ ΓΔ ∘ Γ₂ ⟫.
Proof. induction peΓΔ; crushRestrict. Qed.
Hint Resolve restrictLeftLeft : infra.


Fixpoint restrictLeftRightEnv (pΓΔ pΓ: Part) (ΓΔ: Env) : Env :=
  match pΓΔ , pΓ, ΓΔ with
    | pnil,       _         , _      => ε
    | pleft pΓΔ,  pnil      , _      => ε (* IMPOSSIBLE *)
    | pleft pΓΔ,  pleft pΓ  , ε      => ε (* IMPOSSIBLE *)
    | pleft pΓΔ,  pleft pΓ  , ΓΔ ▻ a => restrictLeftRightEnv pΓΔ pΓ ΓΔ
    | pleft pΓΔ,  pright pΓ , ε      => ε (* IMPOSSIBLE *)
    | pleft pΓΔ,  pright pΓ , ΓΔ ▻ a => restrictLeftRightEnv pΓΔ pΓ ΓΔ ▻ a
    | pright pΓΔ, pΓ        , ε      => ε (* IMPOSSIBLE *)
    | pright pΓΔ, pΓ        , ΓΔ ▻ a => restrictLeftRightEnv pΓΔ pΓ ΓΔ ▻ a
  end.

Fixpoint restrictLeftRightPart' (pΓΔ pΓ: Part) : Part :=
  match pΓΔ , pΓ with
    | pnil,       _         => pnil
    | pleft pΓΔ,  pnil      => pnil (* IMPOSSIBLE *)
    | pleft pΓΔ,  pleft pΓ  => restrictLeftRightPart' pΓΔ pΓ
    | pleft pΓΔ,  pright pΓ => pleft (restrictLeftRightPart' pΓΔ pΓ)
    | pright pΓΔ, pΓ        => pright (restrictLeftRightPart' pΓΔ pΓ)
  end.

Lemma restrictLeftRight' {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  ⟪ restrictLeftRightPart' pΓΔ pΓ ⊢ restrictLeftRightEnv pΓΔ pΓ ΓΔ = Γ₂ ∘ Δ ⟫.
Proof. induction peΓΔ; crushRestrict. Qed.
Hint Resolve restrictLeftRight' : infra.

Fixpoint restrictLeftRightPart (pΓΔ pΓ: Part) : Part :=
  match pΓΔ , pΓ with
    | pnil,       _         => pnil
    | pleft pΓΔ,  pnil      => pnil (* IMPOSSIBLE *)
    | pleft pΓΔ,  pleft pΓ  => pleft (restrictLeftRightPart pΓΔ pΓ)
    | pleft pΓΔ,  pright pΓ => pright (restrictLeftRightPart pΓΔ pΓ)
    | pright pΓΔ, pΓ        => pright (restrictLeftRightPart pΓΔ pΓ)
  end.

Lemma restrictLeftRight {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ pΓ Γ₁ Γ₂, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  ⟪ restrictLeftRightPart pΓΔ pΓ ⊢ ΓΔ = Γ₁ ∘ restrictLeftRightEnv pΓΔ pΓ ΓΔ ⟫.
Proof. induction peΓΔ; crushRestrict. Qed.
Hint Resolve restrictLeftRight : infra.



Fixpoint restrictRightLeftEnv (pΓΔ pΔ: Part) (ΓΔ: Env) : Env :=
  match pΓΔ , pΔ, ΓΔ with
    | pnil,       _         , _      => ε
    | pleft pΓΔ,  pΔ        , ε      => ε (* IMPOSSIBLE *)
    | pleft pΓΔ,  pΔ        , ΓΔ ▻ a => restrictRightLeftEnv pΓΔ pΔ ΓΔ ▻ a
    | pright pΓΔ, pnil      , _      => ε (* IMPOSSIBLE *)
    | pright pΓΔ, pleft pΔ  , ε      => ε (* IMPOSSIBLE *)
    | pright pΓΔ, pleft pΔ  , ΓΔ ▻ a => restrictRightLeftEnv pΓΔ pΔ ΓΔ ▻ a
    | pright pΓΔ, pright pΔ , ε      => ε (* IMPOSSIBLE *)
    | pright pΓΔ, pright pΔ , ΓΔ ▻ a => restrictRightLeftEnv pΓΔ pΔ ΓΔ
  end.

Fixpoint restrictRightLeftPart' (pΓΔ pΔ: Part) : Part :=
  match pΓΔ , pΔ with
    | pnil,       _         => pnil
    | pleft pΓΔ,  pΔ        => pleft (restrictRightLeftPart' pΓΔ pΔ)
    | pright pΓΔ, pnil      => pnil (* IMPOSSIBLE *)
    | pright pΓΔ, pleft pΔ  => pright (restrictRightLeftPart' pΓΔ pΔ)
    | pright pΓΔ, pright pΔ => restrictRightLeftPart' pΓΔ pΔ
  end.

Lemma restrictRightLeft' {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ pΔ Δ₁ Δ₂, ⟪ pΔ ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ →
  ⟪ restrictRightLeftPart' pΓΔ pΔ ⊢ restrictRightLeftEnv pΓΔ pΔ ΓΔ = Γ ∘ Δ₁ ⟫.
Proof. induction peΓΔ; crushRestrict. Qed.
Hint Resolve restrictRightLeft' : infra.

Fixpoint restrictRightLeftPart (pΓΔ pΔ: Part) : Part :=
  match pΓΔ , pΔ with
    | pnil,       _         => pnil
    | pleft pΓΔ,  pΔ        => pleft (restrictRightLeftPart pΓΔ pΔ)
    | pright pΓΔ, pnil      => pnil (* IMPOSSIBLE *)
    | pright pΓΔ, pleft pΔ  => pleft (restrictRightLeftPart pΓΔ pΔ)
    | pright pΓΔ, pright pΔ => pright (restrictRightLeftPart pΓΔ pΔ)
  end.

Lemma restrictRightLeft {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ pΔ Δ₁ Δ₂, ⟪ pΔ ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ →
  ⟪ restrictRightLeftPart pΓΔ pΔ ⊢ ΓΔ = restrictRightLeftEnv pΓΔ pΔ ΓΔ ∘ Δ₂ ⟫.
Proof. induction peΓΔ; crushRestrict. Qed.
Hint Resolve restrictRightLeft : infra.


(* Left Left *)
(* Lemma restrictLeftLeftEnv_plefts_part {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   restrictLeftLeftEnv (plefts (dom ΓΔ)) pΓΔ ΓΔ = Γ. *)
(* Proof. induction peΓΔ; crushRestrict. Qed. *)

(* Lemma restrictLeftLeftEnv_prights_part {p ΓΔ} : *)
(*   restrictLeftLeftEnv (prights (dom ΓΔ)) p ΓΔ = ΓΔ. *)
(* Proof. induction ΓΔ; crushRestrict. Qed. *)

(* Lemma restrictLeftLeftEnv_part_plefts {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   restrictLeftLeftEnv pΓΔ (plefts (dom Γ)) ΓΔ = ΓΔ. *)
(* Proof. induction peΓΔ; crushRestrict. Qed. *)

(* Lemma restrictLeftLeftEnv_part_prights {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   restrictLeftLeftEnv pΓΔ (prights (dom Γ)) ΓΔ = Δ. *)
(* Proof. induction peΓΔ; crushRestrict. Qed. *)

Lemma restrictLeftLeftPart'_plefts_part {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  restrictLeftLeftPart' (plefts (dom ΓΔ)) pΓΔ = plefts (dom Γ).
Proof. induction peΓΔ; crushRestrict. Qed.

(* Lemma restrictLeftLeftPart'_prights_part {p γδ} : *)
(*   restrictLeftLeftPart' (prights γδ) p = prights γδ. *)
(* Proof. induction γδ; crushRestrict. Qed. *)

Lemma restrictLeftLeftPart'_part_plefts {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  restrictLeftLeftPart' pΓΔ (plefts (dom Γ)) = pΓΔ.
Proof. induction peΓΔ; crushRestrict. Qed.

(* Lemma restrictLeftLeftPart'_part_prights {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   restrictLeftLeftPart' pΓΔ (prights (dom Γ)) = prights (dom Δ). *)
(* Proof. induction peΓΔ; crushRestrict. Qed. *)

Lemma restrictLeftLeftPart_plefts_part {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  restrictLeftLeftPart (plefts (dom ΓΔ)) pΓΔ = pΓΔ.
Proof. induction peΓΔ; crushRestrict. Qed.

(* Lemma restrictLeftLeftPart_prights_part δ p: *)
(*   restrictLeftLeftPart (prights δ) p = plefts δ . *)
(* Proof. induction δ; crushRestrict. Qed. *)

Lemma restrictLeftLeftPart_part_plefts {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  restrictLeftLeftPart pΓΔ (plefts (dom Γ)) = plefts (dom ΓΔ).
Proof. induction peΓΔ; crushRestrict. Qed.

(* Lemma restrictLeftLeftPart_part_prights {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   restrictLeftLeftPart pΓΔ (prights (dom Γ)) = ??. *)
(* Proof. *)
(* Admitted. *)


(* Left Right *)
(* Lemma restrictLeftRightEnv_plefts {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   restrictLeftRightEnv pΓΔ (plefts (dom Γ)) ΓΔ = Δ. *)
(* Proof. induction peΓΔ; crushRestrict. Qed. *)

(* Lemma restrictLeftRightPart'_part_plefts {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) : *)
(*   restrictLeftRightPart' pΓ (plefts (dom Γ₁)) = prights (dom Γ₂). *)
(* Proof. induction peΓ; crushRestrict. Qed. *)

Lemma restrictLeftRightPart'_plefts_part {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  restrictLeftRightPart' (plefts (dom Γ)) pΓ = plefts (dom Γ₂).
Proof. induction peΓ; crushRestrict. Qed.

Lemma restrictLeftRightPart'_part_prights {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  restrictLeftRightPart' pΓ (prights (dom Γ₁)) = pΓ.
Proof. induction peΓ; crushRestrict. Qed.

(* Lemma restrictLeftRightPart'_prights_part δ p : *)
(*   restrictLeftRightPart' (prights δ) p = prights δ. *)
(* Proof. induction δ; crushRestrict. Qed. *)

Lemma restrictLeftRightPart_plefts_part {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  restrictLeftRightPart (plefts (dom Γ)) pΓ = pΓ.
Proof. induction peΓ; crushRestrict. Qed.

Lemma restrictLeftRightPart_part_plefts {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  restrictLeftRightPart pΓ (plefts (dom Γ₁)) = pΓ.
Proof. induction peΓ; crushRestrict. Qed.

Lemma restrictLeftRightPart_part_prights {pΓ Γ Γ₁ Γ₂} (peΓ: ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  restrictLeftRightPart pΓ (prights (dom Γ₁)) = prights (dom Γ).
Proof. induction peΓ; crushRestrict. Qed.


Lemma restrictLeftLeftPart'_restrictLeftLeftPart_cancels
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂}, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  restrictLeftLeftPart'
    (restrictLeftLeftPart pΓΔ pΓ)
    (restrictLeftLeftPart' pΓΔ pΓ) = pΓ.
Proof. induction peΓΔ; crushRestrict. Qed.

Lemma restrictLeftLeftPart_restrictLeftLeftPart_cancels
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂}, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  restrictLeftLeftPart
    (restrictLeftLeftPart pΓΔ pΓ)
    (restrictLeftLeftPart' pΓΔ pΓ) = pΓΔ.
Proof. induction peΓΔ; crushRestrict. Qed.

Lemma restrictLeftRightPart'_restrictRightLeftPart_cancels
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΔ Δ₁ Δ₂}, ⟪ pΔ ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ →
  restrictLeftRightPart'
    (restrictRightLeftPart pΓΔ pΔ)
    (restrictRightLeftPart' pΓΔ pΔ) = pΔ.
Proof. induction peΓΔ; crushRestrict. Qed.

Lemma restrictLeftRightPart_restrictRightLeftPart_cancels
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΔ Δ₁ Δ₂}, ⟪ pΔ ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ →
  restrictLeftRightPart
    (restrictRightLeftPart pΓΔ pΔ)
    (restrictRightLeftPart' pΓΔ pΔ) = pΓΔ.
Proof. induction peΓΔ; crushRestrict. Qed.

Lemma restrictRightLeftPart_restrictLeftRightPart_cancels
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂}, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  restrictRightLeftPart
    (restrictLeftRightPart pΓΔ pΓ)
    (restrictLeftRightPart' pΓΔ pΓ) = pΓΔ.
Proof. induction peΓΔ; crushRestrict. Qed.

Lemma restrictRightLeftPart'_restrictLeftRightPart_cancels
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂}, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  restrictRightLeftPart'
    (restrictLeftRightPart pΓΔ pΓ)
    (restrictLeftRightPart' pΓΔ pΓ) = pΓ.
Proof. induction peΓΔ; crushRestrict. Qed.

Lemma restrictLeftRightPart_restrictLeftLeftPart_cancels
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂}, ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
  restrictLeftRightPart
    (restrictLeftLeftPart pΓΔ pΓ)
    (restrictLeftLeftPart' pΓΔ pΓ) =
  restrictLeftRightPart pΓΔ pΓ.
Proof. induction peΓΔ; crushRestrict. Qed.


(* Lemma restrictLeftLeftPart'_pnil *)
(*   {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   ∀ {pΓ Γ₁ Γ₂}, *)
(*     restrictLeftLeftPart' pΓΔ pΓ = pnil → *)
(*     ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → *)
(*     Γ₁ = ε ∧ Γ = Γ₂ ∧ pΓ = prights (dom Γ₂). *)
(* Proof. *)
(*   induction peΓΔ; crushRestrict. *)
(*   specialize (IHpeΓΔ _ _ _ H H6). *)
(*   destruct_conjs; subst. *)
(*   repeat split; eauto. *)
(* Qed. *)

Lemma restrictLeftLeftEnv_restrictLeftLeftPart'_comm
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂ pΓ₁ Γ₁₁ Γ₁₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ pΓ₁ ⊢ Γ₁ = Γ₁₁ ∘ Γ₁₂ ⟫ →
  restrictLeftLeftEnv (restrictLeftLeftPart' pΓΔ pΓ) pΓ₁
    (restrictLeftLeftEnv pΓΔ pΓ ΓΔ) =
  restrictLeftLeftEnv pΓΔ (restrictLeftRightPart pΓ pΓ₁) ΓΔ.
Proof. induction peΓΔ; crushRestrict. Qed.

Lemma restrictLeftLeftPart'_restrictLeftLeftPart'_comm
  {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂ pΓ₁ Γ₁₁ Γ₁₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ → ⟪ pΓ₁ ⊢ Γ₁ = Γ₁₁ ∘ Γ₁₂ ⟫ →
  restrictLeftLeftPart' (restrictLeftLeftPart' pΓΔ pΓ) pΓ₁ =
  restrictLeftLeftPart' pΓΔ (restrictLeftRightPart pΓ pΓ₁).
Proof. induction peΓΔ; crushRestrict. Qed.


Ltac crushRestrictH :=
  erewrite
    ?restrictLeftLeftPart_plefts_part,
    ?restrictLeftRightPart_plefts_part,
    ?restrictLeftLeftPart_restrictLeftLeftPart_cancels,
    ?restrictLeftLeftPart'_restrictLeftLeftPart_cancels,
    ?restrictLeftRightPart_restrictRightLeftPart_cancels,
    ?restrictLeftRightPart'_restrictRightLeftPart_cancels,
    ?restrictRightLeftPart_restrictLeftRightPart_cancels,
    ?restrictRightLeftPart'_restrictLeftRightPart_cancels,
    ?restrictLeftRightPart_restrictLeftLeftPart_cancels,
    ?restrictLeftLeftEnv_restrictLeftLeftPart'_comm,
    ?restrictLeftLeftPart'_restrictLeftLeftPart'_comm.
