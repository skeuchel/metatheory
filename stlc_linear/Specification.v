Require Export Coq.Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.

(* Types
   Meta-variables: a, b
 *)
Inductive Ty : Set :=
  | tbase
  | tarr (a b: Ty).

(* Typing environments mapping term indices to types.
   Meta-variables: Γ, Δ
 *)
Inductive Env : Set :=
  | empty
  | evar (Γ : Env) (a : Ty).
Notation "'ε'" := (empty).
Notation "Γ ▻ a" := (evar Γ a) (at level 56, left associativity).

Definition singleton (a: Ty) := empty ▻ a.
Notation "[ a ]" := (singleton a).

(* Environment concatenation. *)
Reserved Notation "Γ₁ ▻▻ Γ₂" (at level 56, left associativity).
Fixpoint ecat (Γ₁ Γ₂ : Env) {struct Γ₂} : Env :=
  match Γ₂ with
    | empty  => Γ₁
    | Γ₂ ▻ a => (Γ₁ ▻▻ Γ₂) ▻ a
  end
where "Γ₁ ▻▻ Γ₂" := (ecat Γ₁ Γ₂).

(* Lemma ecat_left_empty Δ : ε ▻▻ Δ = Δ. *)
(* Proof. induction Δ; simpl; congruence. Qed. *)

(* Lemma ecat_empty_left {Γ₁ Γ₂} : *)
(*   ε = Γ₁ ▻▻ Γ₂ → Γ₁ = ε. *)
(* Proof. induction Γ₂; inversion 1; auto. Qed. *)

(* Lemma ecat_empty_right {Γ₁ Γ₂} : *)
(*   ε = Γ₁ ▻▻ Γ₂ → Γ₂ = ε. *)
(* Proof. induction Γ₂; inversion 1; auto. Qed. *)


(* Domains represent a set of variables such as the variables
   bound in a typing environment or that can appear in a term.
   Meta-variables: γ, δ
 *)
Definition Dom : Set := nat.

Fixpoint dom (Γ: Env) : Dom :=
  match Γ with
    | ε     => O
    | Γ ▻ _ => S (dom Γ)
  end.

(* Just a copy of plus. *)
Fixpoint dunion (δ₁ δ₂ : Dom) {struct δ₂} : Dom :=
  match δ₂ with
    | O    => δ₁
    | S δ₂ => S (dunion δ₁ δ₂)
  end.
Notation "δ₁ ∪ δ₂" := (dunion δ₁ δ₂) (at level 56, left associativity).

(* Lemma dunion_left_zero δ : 0 ∪ δ = δ. *)
(* Proof. induction δ; simpl; congruence. Qed. *)

(* A partition of a context g is a pair of contexts (g1,g2) such that g is some
 * permutation of g1++g2, under the side condition that the domains of g1 and g2
 * are disjoint *)

Inductive Part : Set :=
  | pnil   : Part
  | pleft  : Part → Part
  | pright : Part → Part.

Reserved Notation "⟨ p ⊢ γ = γ₁ ∘ γ₂ ⟩"
 (at level 0, p at level 10, γ at level 10, γ₁ at level 10, γ₂ at level 10,
  format "⟨ p  ⊢  γ  =  γ₁  ∘  γ₂ ⟩").
Inductive PartDom : Part → Dom → Dom → Dom → Prop :=
  | PDNil : ⟨pnil ⊢ 0 = 0 ∘ 0⟩
  | PDLeft {p γ γ₁ γ₂} :
      ⟨p         ⊢  γ    =  γ₁   ∘ γ₂  ⟩ →
      ⟨pleft p   ⊢  S γ  =  S γ₁ ∘ γ₂  ⟩
  | PDRight {p γ γ₁ γ₂} :
      ⟨p         ⊢  γ    =  γ₁   ∘ γ₂  ⟩ →
      ⟨pright p  ⊢  S γ  =  γ₁   ∘ S γ₂⟩
where "⟨ p ⊢ γ = γ₁ ∘ γ₂ ⟩" := (PartDom p γ γ₁ γ₂).

(* Partition typing environments. *)
Reserved Notation "⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫"
  (at level 0, p at level 10, Γ at level 10, Γ₁ at level 10, Γ₂ at level 10).
Inductive PartEnv : Part → Env → Env → Env → Prop :=
  | PENil : ⟪ pnil ⊢ ε = ε ∘ ε ⟫
  | PELeft {p a Γ Γ₁ Γ₂} :
      ⟪ p         ⊢  Γ       =  Γ₁       ∘ Γ₂       ⟫ →
      ⟪ pleft p   ⊢  (Γ ▻ a) =  (Γ₁ ▻ a) ∘ Γ₂       ⟫
  | PERight {p a Γ Γ₁ Γ₂} :
      ⟪ p         ⊢  Γ       =  Γ₁       ∘ Γ₂       ⟫ →
      ⟪ pright p  ⊢  (Γ ▻ a) =  Γ₁       ∘ (Γ₂ ▻ a) ⟫
where "⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫" := (PartEnv p Γ Γ₁ Γ₂).

Fixpoint domPart (p: Part) : Dom :=
  match p with
    | pnil => O
    | pleft p => S (domPart p)
    | pright p => S (domPart p)
  end.

Fixpoint domPartLeft (p: Part) : Dom :=
  match p with
    | pnil => O
    | pleft p => S (domPartLeft p)
    | pright p => domPartLeft p
  end.

(* Fixpoint domPartRight (p: Part) : Dom := *)
(*   match p with *)
(*     | pnil => O *)
(*     | pleft p => domPartRight p *)
(*     | pright p => S (domPartRight p) *)
(*   end. *)

Lemma domPart_sound {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  domPart pΓΔ = dom ΓΔ.
Proof. induction peΓΔ; simpl; congruence. Qed.

Lemma domPartLeft_sound {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  domPartLeft pΓΔ = dom Γ.
Proof. induction peΓΔ; simpl; congruence. Qed.

(* Lemma domPartRight_sound {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   domPartRight pΓΔ = dom Δ. *)
(* Proof. induction peΓΔ; simpl; congruence. Qed. *)

Fixpoint plefts (δ : Dom) : Part :=
  match δ with
    | O   => pnil
    | S δ => pleft (plefts δ)
  end.

Fixpoint prights (δ: Dom) : Part :=
  match δ with
    | O   => pnil
    | S δ => pright (prights δ)
  end.

Lemma partEnv_plefts (Δ: Env) :
  ⟪ plefts (dom Δ) ⊢ Δ = Δ ∘ ε ⟫.
Proof. induction Δ; simpl; eauto using PartEnv. Qed.
Hint Resolve partEnv_plefts : infra.

(* Lemma partEnv_prights (Δ: Env) : *)
(*   ⟪ prights (dom Δ) ⊢ Δ = ε ∘ Δ ⟫. *)
(* Proof. induction Δ; simpl; eauto using PartEnv. Qed. *)
(* Hint Resolve partEnv_prights : infra. *)

Lemma domPart_plefts δ: domPart (plefts δ) = δ.
Proof. induction δ; simpl; congruence. Qed.

(* Lemma domPartLeft_plefts δ: domPartLeft (plefts δ) = δ. *)
(* Proof. induction δ; simpl; congruence. Qed. *)

(* Lemma domPartRight_plefts δ: domPartRight (plefts δ) = O. *)
(* Proof. induction δ; simpl; congruence. Qed. *)

Lemma partEnv_leftEmpty {pΓΔ ΓΔ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = ε ∘ Δ ⟫) :
  ΓΔ = Δ ∧ pΓΔ = prights (dom ΓΔ).
Proof. depind peΓΔ; simpl; destruct_conjs; split; congruence. Qed.

(* Lemma partEnv_rightEmpty {pΓΔ ΓΔ Γ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ ε ⟫) : *)
(*   ΓΔ = Γ ∧ pΓΔ = plefts (dom ΓΔ). *)
(* Proof. depind peΓΔ; simpl; destruct_conjs; split; congruence. Qed. *)

(* Terms.
   Meta-variables: s, t
 *)
Inductive Tm : Set :=
  | var
  | abs (a: Ty) (t: Tm)
  | app (p: Part) (t₁ t₂: Tm).

(* Linear scoping for terms. *)
Reserved Notation "⟨ γ ⊢ t ⟩"
  (at level 0, γ at level 10, t at level 10, format "⟨ γ  ⊢  t ⟩").
Inductive wsTm : Dom → Tm → Prop :=
  | WsVar :
      ⟨1 ⊢ var⟩
  | WsAbs {γ a t} :
      ⟨S γ ⊢ t⟩ →
      ⟨γ ⊢ abs a t⟩
  | WsApp {p γ γ₁ γ₂ t₁ t₂} :
      ⟨p ⊢ γ = γ₁ ∘ γ₂⟩ →
      ⟨γ₁ ⊢ t₁⟩ → ⟨γ₂ ⊢ t₂⟩ →
      ⟨γ ⊢ app p t₁ t₂⟩
where "⟨ γ ⊢ t ⟩" := (wsTm γ t).

(* Linear typing for terms *)
Reserved Notation "⟪  Γ ⊢ t : T  ⟫"
  (at level 0, Γ at level 10, t at level 10, T at level 10 ).
Inductive wtTm : Env → Tm → Ty → Prop :=
  | WtVar {a} :
      ⟪ [a] ⊢ var : a ⟫
  | WtAbs {Γ t a b} :
      ⟪ Γ ▻ a ⊢ t : b ⟫ →
      ⟪ Γ ⊢ abs a t : tarr a b ⟫
  | WtApp {p Γ Γ₁ Γ₂ t₁ t₂ a b} :
      ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
      ⟪ Γ₁ ⊢ t₁ : tarr a b ⟫ →
      ⟪ Γ₂ ⊢ t₂ : a ⟫ →
      ⟪ Γ ⊢ app p t₁ t₂ : b ⟫
where "⟪  Γ ⊢ t : T  ⟫" := (wtTm Γ t T).

(* Linear substitutions *)
Inductive Sub : Set :=
  | snil
  | snoc (p: Part) (ζ: Sub) (t: Tm).

Reserved Notation "⟪ ζ : Γ => Δ ⟫"
  (at level 0, ζ at level 10, Γ at level 10, Δ at level 10).
Inductive WtSub : Sub → Env → Env → Prop :=
  | WtSNil :
      ⟪ snil : ε => ε ⟫
  | WtSnoc {ζ Γ p Δ Δ₁ Δ₂ t a} :
      ⟪ p ⊢ Δ = Δ₁ ∘ Δ₂ ⟫ →
      ⟪ ζ : Γ => Δ₁ ⟫ →
      ⟪ Δ₂ ⊢ t : a ⟫ →
      ⟪ snoc p ζ t : Γ ▻ a => Δ ⟫
where "⟪ ζ : Γ => Δ ⟫" := (WtSub ζ Γ Δ).

Fixpoint leftEnv (pΓΔ: Part) (ΓΔ: Env) : Env :=
  match pΓΔ , ΓΔ with
    | pnil       , _      => ε
    | pleft pΓΔ  , ε      => ε (* IMPOSSIBLE *)
    | pleft pΓΔ  , ΓΔ ▻ a => leftEnv pΓΔ ΓΔ ▻ a
    | pright pΓΔ , ε      => ε (* IMPOSSIBLE *)
    | pright pΓΔ , ΓΔ ▻ a => leftEnv pΓΔ ΓΔ
  end.

(* Fixpoint rightEnv (pΓΔ: Part) (ΓΔ: Env) : Env := *)
(*   match pΓΔ , ΓΔ with *)
(*     | pnil       , _      => ε *)
(*     | pleft pΓΔ  , ε      => ε (* IMPOSSIBLE *) *)
(*     | pleft pΓΔ  , ΓΔ ▻ a => rightEnv pΓΔ ΓΔ *)
(*     | pright pΓΔ , ε      => ε (* IMPOSSIBLE *) *)
(*     | pright pΓΔ , ΓΔ ▻ a => rightEnv pΓΔ ΓΔ ▻ a *)
(*   end. *)

Lemma leftEnv_sound {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  leftEnv pΓΔ ΓΔ = Γ.
Proof. induction peΓΔ; simpl; eauto using f_equal2. Qed.

(* Lemma rightEnv_sound {pΓΔ ΓΔ Γ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) : *)
(*   rightEnv pΓΔ ΓΔ = Δ. *)
(* Proof. induction peΓΔ; simpl; eauto using f_equal2. Qed. *)


Definition codSub (ζ: Sub) : Dom :=
  match ζ with
    | snil => O
    | snoc pΔ _ _ => domPart pΔ
  end.

Lemma codSub_sound {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  codSub ζ = dom Δ.
Proof. inversion wζ; simpl; eauto using domPart_sound. Qed.

Hint Constructors PartDom : infra.
Hint Constructors PartEnv : infra.
Hint Constructors WtSub : infra.

Definition subUp (ζ: Sub) : Sub :=
  snoc (pright (plefts (codSub ζ))) ζ var.

Lemma wtSubUp {ζ Γ Δ} (wζ: ⟪ ζ : Γ => Δ ⟫) :
  ∀ a, ⟪ subUp ζ : (Γ ▻ a) => (Δ ▻ a) ⟫.
Proof.
  unfold subUp. rewrite (codSub_sound wζ).
  repeat econstructor; eauto with infra.
Qed.
Hint Resolve wtSubUp : infra.

Fixpoint subId (δ: Dom) : Sub :=
  match δ with
    | O   => snil
    | S δ => subUp (subId δ)
  end.

Lemma wtSubId Γ :
  ⟪ subId (dom Γ) : Γ => Γ ⟫.
Proof. induction Γ; simpl; eauto with infra. Qed.
Hint Resolve wtSubId : infra.

(* Lemma domPart_plefts δ : *)
(*   domPart (plefts δ) = δ. *)
(* Proof. induction δ; simpl; congruence. Qed. *)

(* Lemma codSub_subUp ζ : *)
(*   codSub (subUp ζ) = S (codSub ζ). *)
(* Proof. simpl; eauto using domPart_plefts. Qed. *)
(* Hint Rewrite codSub_subUp : infra. *)

Lemma codSub_subId δ :
  codSub (subId δ) = δ.
Proof.
  pose proof domPart_plefts.
  induction δ; simpl; congruence.
Qed.
Hint Rewrite codSub_subId : infra.
