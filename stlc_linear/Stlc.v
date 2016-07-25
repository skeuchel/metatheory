Require Export Coq.Unicode.Utf8.
Require Import Coq.Program.Equality.

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
Notation "Γ ▻ a" := (evar Γ a) (at level 55, left associativity).

Definition singleton (a: Ty) := empty ▻ a.
Notation "[ a ]" := (singleton a).

(* Environment concatenation. *)
Reserved Notation "Γ₁ ▻▻ Γ₂" (at level 55, left associativity).
Fixpoint ecat (Γ₁ Γ₂ : Env) {struct Γ₂} : Env :=
  match Γ₂ with
    | empty  => Γ₁
    | Γ₂ ▻ a => (Γ₁ ▻▻ Γ₂) ▻ a
  end
where "Γ₁ ▻▻ Γ₂" := (ecat Γ₁ Γ₂).

Lemma ecat_left_empty Δ : ε ▻▻ Δ = Δ.
Proof. induction Δ; simpl; congruence. Qed.

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
Notation "δ₁ ∪ δ₂" := (dunion δ₁ δ₂) (at level 55, left associativity).

Lemma dunion_left_zero δ : 0 ∪ δ = δ.
Proof. induction δ; simpl; congruence. Qed.

(* De Bruijn indices.
   Meta-variables: i, j
 *)
Definition Ix : Set := nat.

(* Well-scoping for indices, aka less-than. *)
Reserved Notation "⟨ i ∈ γ ⟩"
  (at level 0, i at level 10, γ at level 10, format "⟨ i  ∈  γ ⟩").
Inductive inDom : Dom → Ix → Prop :=
  | inDomO γ   :           ⟨O   ∈ S γ⟩
  | inDomS γ i : ⟨i ∈ γ⟩ → ⟨S i ∈ S γ⟩
where "⟨ i ∈ γ ⟩" := (inDom γ i).

Lemma inDomInvS (γ: Dom) (i: Ix) : ⟨S i ∈ S γ⟩ → ⟨i ∈ γ⟩.
Proof. inversion 1; auto. Qed.


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

(* Given a partition γ = γ₁ ∘ γ₂ map variables from γ₁ to γ. *)
Fixpoint fromLeft (p: Part) (i : Ix) : Ix :=
  match p with
    | pnil      => i
    | pleft p'  => match i with
                     | O    => O
                     | S i' => S (fromLeft p' i')
                   end
    | pright p' => S (fromLeft p' i)
  end.
(* Arguments fromLeft !p !i /. *)

(* Given a partition γ = γ₁ ∘ γ₂ map variables from γ₂ to γ. *)
Fixpoint fromRight (p: Part) (i : Ix) : Ix :=
  match p with
    | pnil      => i
    | pleft p'  => S (fromRight p' i)
    | pright p' => match i with
                     | O    => O
                     | S i' => S (fromRight p' i')
                   end
  end.
(* Arguments fromRight !p !i /. *)

Lemma fromLeft_inDom {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ (i: Ix) (wi: ⟨i ∈ γ₁⟩), ⟨fromLeft p i ∈ γ⟩.
Proof with simpl; eauto using inDom, inDomInvS.
  induction pd... destruct i...
Qed.

Lemma fromRight_inDom {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ (i: Ix) (wi: ⟨i ∈ γ₂⟩), ⟨fromRight p i ∈ γ⟩.
Proof with simpl; eauto using inDom, inDomInvS.
  induction pd... destruct i...
Qed.

Lemma fromLeft_inDomInv {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ (i: Ix), ⟨fromLeft p i ∈ γ⟩ → ⟨i ∈ γ₁⟩.
Proof with simpl; eauto using inDom, inDomInvS.
  induction pd... destruct i...
Qed.

Lemma fromRight_inDomInv {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ (i: Ix), ⟨fromRight p i ∈ γ⟩ → ⟨i ∈ γ₂⟩.
Proof with simpl; eauto using inDom, inDomInvS.
  induction pd... destruct i...
Qed.

(* Given a partition γ = γ₁ ∘ γ₂, decide for a variable in
   γ if it is in γ₁ or γ₂ and return an approporiate index. *)
Fixpoint isLeftOrRight (p: Part) (i: Ix) : Ix + Ix :=
  match p with
    | pnil    => inl i  (* IMPOSSIBLE *)
    | pleft p => match i with
                   | O   => inl 0
                   | S i => match isLeftOrRight p i with
                              | inl j => inl (S j)
                              | inr j => inr j
                            end
                 end
    | pright p => match i with
                   | O   => inr 0
                   | S i => match isLeftOrRight p i with
                              | inl j => inl j
                              | inr j => inr (S j)
                            end
                  end
  end.

Ltac crush :=
  intros;
  repeat
    (repeat
       match goal with
         | [ H: S _ = S _     |- _ ] => apply eq_add_S in H
         | [ H: inl _ = inl _ |- _ ] => inversion H; clear H; subst
         | [ H: inr _ = inr _ |- _ ] => inversion H; clear H; subst
         | [ H: inl _ = inr _ |- _ ] => inversion H
         | [ H: inr _ = inl _ |- _ ] => inversion H
         | [ H: ⟨_   ∈ O⟩     |- _ ] => inversion H
         | [ H: ⟨O   ∈ S _⟩   |- _ ] => clear H
         | [ H: ⟨S _ ∈ S _⟩   |- _ ] => apply inDomInvS in H
         | [ H: ⟨?i  ∈ S _⟩   |- context[match ?i with _ => _ end] ] =>
           destruct i
         | [ H: ⟨?i  ∈ S _⟩, H1: context[match ?i with _ => _ end] |- _ ] =>
           destruct i
         | [ |- S _ = S _ ] => f_equal
         | [ |- ⟨S _ ∈ S _⟩ ] => constructor
         | [ H: match ?i with _ => _ end = inl _ |- _ ] =>
           destruct i eqn: ?
         | [ H: match ?i with _ => _ end = inr _ |- _ ] =>
           destruct i eqn: ?
         | [ H: context[match isLeftOrRight ?p ?i with _ => _ end] |- _ ] =>
           destruct (isLeftOrRight p i) eqn: ?
         | [ |- context[match isLeftOrRight ?p ?i with _ => _ end] ] =>
           destruct (isLeftOrRight p i) eqn: ?
         | [ pd: ⟨?p ⊢ ?γ = _ ∘ _⟩, wi: ⟨ fromLeft ?p _ ∈ ?γ ⟩ |- _ ] =>
           apply (fromLeft_inDomInv pd) in wi
         | [ pd: ⟨?p ⊢ ?γ = _ ∘ _⟩, wi: ⟨ fromRight ?p _ ∈ ?γ ⟩ |- _ ] =>
           apply (fromRight_inDomInv pd) in wi
       end;
     simpl in *;
     subst;
     try discriminate;
     try rewrite dunion_left_zero in *;
     eauto using inDom).

Lemma isLeftOrRight_inl_sound p :
  ∀ i j, isLeftOrRight p i = inl j → i = fromLeft p j.
Proof. induction p; crush. Qed.

Lemma isLeftOrRight_inr_sound p :
  ∀ i j, isLeftOrRight p i = inr j → i = fromRight p j.
Proof. induction p; crush. Qed.

Lemma isLeftOrRight_inl_inDom {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ {i j}, ⟨i ∈ γ⟩ → isLeftOrRight p i = inl j → ⟨j ∈ γ₁⟩.
Proof. induction pd; crush. Qed.

Lemma isLeftOrRight_inr_inDom {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ {i j}, ⟨i ∈ γ⟩ → isLeftOrRight p i = inr j → ⟨j ∈ γ₂⟩.
Proof. induction pd; crush. Qed.

(* Replace a single binding for i by δ bindings. *)
Fixpoint insertDom (δ: Dom) (γ: Dom) (i: Ix) : Dom :=
  match γ , i with
    | O   , _   => O
    | S γ , O   => γ ∪ δ
    | S γ , S i => S (insertDom δ γ i)
  end.

Lemma insertDom_foo δ γ₁ γ₂ :
  insertDom δ (γ₁ ∪ 1 ∪ γ₂) γ₂ = γ₁ ∪ δ ∪ γ₂.
Proof. induction γ₂; crush. Qed.

Fixpoint plefts (p: Part) (δ: Dom) : Part :=
  match δ with
    | O   => p
    | S δ => pleft (plefts p δ)
  end.

Fixpoint prights (p: Part) (δ: Dom) : Part :=
  match δ with
    | O   => p
    | S δ => pright (prights p δ)
  end.

Lemma plefts_partdom δ {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ⟨plefts p δ ⊢ (γ ∪ δ) = (γ₁ ∪ δ) ∘ γ₂⟩.
Proof. induction δ; simpl; eauto using PartDom. Qed.

Lemma prights_partdom δ {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ⟨prights p δ ⊢ (γ ∪ δ) = γ₁ ∘ (γ₂ ∪ δ)⟩.
Proof. induction δ; simpl; eauto using PartDom. Qed.

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

Lemma plefts_partenv Δ {p Γ Γ₁ Γ₂} (pe: ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ⟪ plefts p (dom Δ) ⊢ (Γ ▻▻ Δ) = (Γ₁ ▻▻ Δ) ∘ Γ₂ ⟫.
Proof. induction Δ; simpl; eauto using PartEnv. Qed.

Lemma prights_partenv Δ {p Γ Γ₁ Γ₂} (pe: ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ⟪ prights p (dom Δ) ⊢ (Γ ▻▻ Δ) = Γ₁ ∘ (Γ₂ ▻▻ Δ) ⟫.
Proof. induction Δ; simpl; eauto using PartEnv. Qed.

Hint Constructors PartDom.
Hint Resolve plefts_partdom.
Hint Resolve prights_partdom.

Hint Constructors PartEnv.
Hint Resolve plefts_partenv.
Hint Resolve prights_partenv.

(* Type environment lookup. *)
Reserved Notation "⟪  i : a ∈ Γ  ⟫"
  (at level 0, i at level 10, Γ at level 10).
Inductive wtIx : Env → Ix → Ty → Prop :=
  | wt0 {Γ a} :
      ⟪   O : a ∈ Γ ▻ a  ⟫
  | wtS {Γ a a' i} :
      ⟪   i : a ∈ Γ      ⟫ →
      ⟪ S i : a ∈ Γ ▻ a' ⟫
where "⟪  i : a ∈ Γ  ⟫" := (wtIx Γ i a).

Lemma wtix_isLeftOrRight_inl {p Γ Γ₁ Γ₂} (pe: ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ {a i j}, ⟪ i : a ∈ Γ ⟫ → isLeftOrRight p i = inl j → ⟪ j : a ∈ Γ₁ ⟫.
Proof with crush.
  induction pe...
  - inversion H...
    constructor...
  - inversion H...
    constructor...
  - inversion H...
Qed.

Lemma wtix_isLeftOrRight_inr {p Γ Γ₁ Γ₂} (pe: ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ {a i j}, ⟪ i : a ∈ Γ ⟫ → isLeftOrRight p i = inr j → ⟪ j : a ∈ Γ₂ ⟫.
Proof with crush.
  induction pe...
  - inversion H...
  - inversion H...
    constructor...
  - inversion H...
    constructor...
Qed.

(* Terms.
   Meta-variables: s, t
 *)
Inductive Tm : Set :=
  | var (i: Ix)
  | abs (a: Ty) (t: Tm)
  | app (p: Part) (t₁ t₂: Tm).

(* Well-scoping for terms. *)
Reserved Notation "⟨ γ ⊢ t ⟩"
  (at level 0, γ at level 10, t at level 10, format "⟨ γ  ⊢  t ⟩").
Inductive wsTm : Dom → Tm → Prop :=
  | WsVar :
      ⟨1 ⊢ var 0⟩
  | WsAbs {γ a t} :
      ⟨S γ ⊢ t⟩ →
      ⟨γ ⊢ abs a t⟩
  | WsApp {p γ γ₁ γ₂ t₁ t₂} :
      ⟨p ⊢ γ = γ₁ ∘ γ₂⟩ →
      ⟨γ₁ ⊢ t₁⟩ → ⟨γ₂ ⊢ t₂⟩ →
      ⟨γ ⊢ app p t₁ t₂⟩
where "⟨ γ ⊢ t ⟩" := (wsTm γ t).

(* Well-typing for terms *)
Reserved Notation "⟪  Γ ⊢ t : T  ⟫"
  (at level 0, Γ at level 10, t at level 10, T at level 10 ).
Inductive wtTm : Env → Tm → Ty → Prop :=
  | WtVar {a} :
      ⟪ [a] ⊢ var 0 : a ⟫
  | WtAbs {Γ t a b} :
      ⟪ Γ ▻ a ⊢ t : b ⟫ →
      ⟪ Γ ⊢ abs a t : tarr a b ⟫
  | WtApp {p Γ Γ₁ Γ₂ t₁ t₂ a b} :
      ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
      ⟪ Γ₁ ⊢ t₁ : tarr a b ⟫ →
      ⟪ Γ₂ ⊢ t₂ : a ⟫ →
      ⟪ Γ ⊢ app p t₁ t₂ : b ⟫
where "⟪  Γ ⊢ t : T  ⟫" := (wtTm Γ t T).

(* Updates the partition witness when substituting index i for
   a term with δ free variables. *)
Fixpoint substPart (p: Part) (i: Ix) (δ: Dom): Part :=
  match p with
    | pnil    => pnil
    | pleft p =>
      match i with
        | O   => plefts p δ
        | S i => pleft (substPart p i δ)
      end
    | pright p =>
      match i with
        | O   => prights p δ
        | S i => pright (substPart p i δ)
      end
  end.

Lemma substPart_inl_partdom {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ i j δ,
    isLeftOrRight p i = inl j →
    ⟨substPart p i δ ⊢ insertDom δ γ i = insertDom δ γ₁ j ∘ γ₂⟩.
Proof. induction pd; crush. Qed.

Lemma substPart_inr_partdom {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ i j δ,
    isLeftOrRight p i = inr j →
    ⟨substPart p i δ ⊢ insertDom δ γ i = γ₁ ∘ insertDom δ γ₂ j⟩.
Proof. induction pd; crush. Qed.

Fixpoint insertEnv (Δ: Env) (Γ: Env) (i: Ix) : Env :=
  match Γ , i with
    | ε     , _   => ε
    | Γ ▻ a , O   => Γ ▻▻ Δ
    | Γ ▻ a , S i => insertEnv Δ Γ i ▻ a
  end.

Lemma insertEnv_foo a Δ Γ₁ Γ₂ :
  insertEnv Δ (Γ₁ ▻▻ [a] ▻▻ Γ₂) (dom Γ₂) = Γ₁ ▻▻ Δ ▻▻ Γ₂.
Proof. induction Γ₂; simpl in *; congruence. Qed.

Lemma substPart_inl_partenv {p Γ Γ₁ Γ₂} (pe: ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ i j Δ,
    isLeftOrRight p i = inl j →
    ⟪ substPart p i (dom Δ) ⊢ insertEnv Δ Γ i = insertEnv Δ Γ₁ j ∘ Γ₂ ⟫.
Proof. induction pe; crush. Qed.

Lemma substPart_inr_partenv {p Γ Γ₁ Γ₂} (pe: ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ i j Δ,
    isLeftOrRight p i = inr j →
    ⟪ substPart p i (dom Δ) ⊢ insertEnv Δ Γ i = Γ₁ ∘ insertEnv Δ Γ₂ j ⟫.
Proof. induction pe; crush. Qed.

(* Substitute index i in t by term s which has δ free variables. *)
Fixpoint subst (i: Ix) (s: Tm) (δ: Dom) (t: Tm) : Tm :=
  match t with
    | var _       => s
    | abs b t     => abs b (subst (S i) s δ t)
    | app p t₁ t₂ =>
      match isLeftOrRight p i with
        | inl i' => app (substPart p i δ) (subst i' s δ t₁) t₂
        | inr i' => app (substPart p i δ) t₁ (subst i' s δ t₂)
      end
  end.

Lemma subst_wsTm {γ t s δ} (ws: ⟨δ ⊢ s⟩) (wt: ⟨γ ⊢ t⟩) :
  ∀ i, ⟨i ∈ γ⟩ → ⟨insertDom δ γ i ⊢ subst i s δ t⟩.
Proof.
  induction wt; crush.
  - constructor.
    apply (IHwt (S i)); crush.
  - econstructor; eauto.
    eapply substPart_inl_partdom; eauto.
    apply isLeftOrRight_inl_sound in Heqs0; crush.
  - econstructor; eauto.
    eapply substPart_inr_partdom; eauto.
    apply isLeftOrRight_inr_sound in Heqs0; crush.
Qed.

Lemma subst_wtTm {Γ Δ s b t a} (ws: ⟪ Δ ⊢ s : b ⟫) (wt: ⟪ Γ ⊢ t : a ⟫) :
  ∀ i, ⟪ i : b ∈ Γ ⟫ → ⟪ insertEnv Δ Γ i ⊢ subst i s (dom Δ) t : a ⟫.
Proof.
  induction wt; crush.
  - inversion H; subst.
    + rewrite ecat_left_empty; auto.
    + inversion H4.
  - constructor.
    apply (IHwt (S i)); crush.
    constructor.
    eauto.
  - econstructor; crush.
    eapply substPart_inl_partenv; crush.
    eapply IHwt1.
    apply (wtix_isLeftOrRight_inl H H0 Heqs0).
  - econstructor; crush.
    eapply substPart_inr_partenv; crush.
    eapply IHwt2; crush.
    apply (wtix_isLeftOrRight_inr H H0 Heqs0).
Qed.

Lemma subst_wtTm_closed {s b t a} (ws: ⟪ ε ⊢ s : b ⟫) (wt: ⟪ [b] ⊢ t : a ⟫) :
  ⟪ ε ⊢ subst 0 s 0 t : a ⟫.
Proof. apply (subst_wtTm ws wt 0). constructor. Qed.

Fixpoint Value (t: Tm) : Prop :=
  match t with
    | var _     => False
    | abs _ _   => True
    | app _ _ _ => False
  end.

Reserved Notation "t₁ --> t₂" (at level 40).
Inductive red : Tm → Tm → Prop :=
  | red_beta {a t₁ t₂} :
      app pnil (abs a t₁) t₂ --> subst 0 t₂ 0 t₁
  | red_app₁ {t₁ t₁' t₂} :
      t₁ --> t₁' → app pnil t₁ t₂ --> app pnil t₁' t₂
  | red_app₂ {t₁ t₂ t₂'} :
      Value t₁ → t₂ --> t₂' → app pnil t₁ t₂ --> app pnil t₁ t₂'
where "t₁ --> t₂" := (red t₁ t₂).

Lemma can_form_tarr {Γ t a b}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tarr a b ⟫) :
    ∃ t₂, t = abs a t₂.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma progress {t a} (wt: ⟪ empty ⊢ t : a ⟫) :
  Value t ∨ ∃ t', t --> t'.
Proof with try (subst; eauto using red).
  depind wt; simpl; auto.
  inversion H; subst.
  destruct IHwt1 as [v1|[t1' r1]]...
  destruct IHwt2 as [v2|[t2' r2]]...
  destruct (can_form_tarr v1 wt1)...
Qed.

Lemma preservation {t a} (wt: ⟪ ε ⊢ t : a ⟫) :
  ∀ {t'}, t --> t' → ⟪ ε ⊢ t' : a ⟫.
Proof.
  depind wt.
  - inversion 1; crush.
  - inversion H; subst.
    specialize (IHwt1 eq_refl).
    specialize (IHwt2 eq_refl).
    clear H.
    inversion 1; subst.
    + inversion wt1; subst.
      eapply subst_wtTm_closed; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
Qed.
