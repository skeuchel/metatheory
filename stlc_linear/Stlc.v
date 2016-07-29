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

Lemma ecat_empty_left {Γ₁ Γ₂} :
  ε = Γ₁ ▻▻ Γ₂ → Γ₁ = ε.
Proof. induction Γ₂; inversion 1; auto. Qed.

Lemma ecat_empty_right {Γ₁ Γ₂} :
  ε = Γ₁ ▻▻ Γ₂ → Γ₂ = ε.
Proof. induction Γ₂; inversion 1; auto. Qed.


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

(* Type environment lookup. *)
Reserved Notation "⟪  i : a ∈ Γ  ⟫"
  (at level 0, i at level 10, Γ at level 10).
Inductive inEnv : Env → Ix → Ty → Prop :=
  | inEnvO {Γ a} :
      ⟪   O : a ∈ Γ ▻ a  ⟫
  | inEnvS {Γ a a' i} :
      ⟪   i : a ∈ Γ      ⟫ →
      ⟪ S i : a ∈ Γ ▻ a' ⟫
where "⟪  i : a ∈ Γ  ⟫" := (inEnv Γ i a).

Lemma inEnvInvS (Γ: Env) (i: Ix) (a b: Ty) :
  ⟪S i : a ∈ Γ ▻ b⟫ → ⟪ i : a ∈ Γ ⟫.
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


Lemma fromLeft_inEnv {p Γ Γ₁ Γ₂} (pe: ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂⟫) :
  ∀ (i: Ix) a, ⟪i : a ∈ Γ₁⟫ → ⟪fromLeft p i : a ∈ Γ⟫.
Proof with simpl; eauto using inEnv, inEnvInvS.
  induction pe... destruct i... inversion 1...
Qed.

Lemma fromRight_inEnv {p Γ Γ₁ Γ₂} (pe: ⟪p ⊢ Γ = Γ₁ ∘ Γ₂⟫) :
  ∀ (i: Ix) a, ⟪i : a ∈ Γ₂⟫ → ⟪fromRight p i :a ∈ Γ⟫.
Proof with simpl; eauto using inEnv, inEnvInvS.
  induction pe... destruct i... inversion 1...
Qed.

Lemma fromLeft_inEnvInv {p Γ Γ₁ Γ₂} (pe: ⟪p ⊢ Γ = Γ₁ ∘ Γ₂⟫) :
  ∀ (i: Ix) a, ⟪fromLeft p i : a ∈ Γ⟫ → ⟪i : a ∈ Γ₁⟫.
Proof with simpl; eauto using inEnv, inEnvInvS.
  induction pe... destruct i... inversion 1...
Qed.

Lemma fromRight_inEnvInv {p Γ Γ₁ Γ₂} (pe: ⟪p ⊢ Γ = Γ₁ ∘ Γ₂⟫) :
  ∀ (i: Ix) a, ⟪fromRight p i : a ∈ Γ⟫ → ⟪i : a ∈ Γ₂⟫.
Proof with simpl; eauto using inEnv, inEnvInvS.
  induction pe... destruct i... inversion 1...
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

Lemma partLeftEmpty {pΓΔ ΓΔ Δ} (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = ε ∘ Δ ⟫) : ΓΔ = Δ.
Proof. depind peΓΔ; simpl; congruence. Qed.

Ltac crush' :=
  intros; simpl in *;
  repeat
    (try match goal with
           | [ H: inl _ = inl _ |- _ ] => inversion H; clear H; subst
           | [ H: inr _ = inr _ |- _ ] => inversion H; clear H; subst
           | [ H: match ?i with _ => _ end = inl _ |- _ ] =>
             destruct i eqn: ?
           | [ H: match ?i with _ => _ end = inr _ |- _ ] =>
             destruct i eqn: ?
         end;
     subst;
     try discriminate;
     eauto).

Lemma isLeftOrRight_inl p :
  ∀ i j, isLeftOrRight p i = inl j → i = fromLeft p j.
Proof. induction p; crush'.
Qed.

Lemma isLeftOrRight_inr p :
  ∀ i j, isLeftOrRight p i = inr j → i = fromRight p j.
Proof. induction p; crush'. Qed.

Ltac crush :=
  intros;
  repeat
    (try
       match goal with
         | [ H: ?x = ?x |- _ ] => clear H
         | [ H: ?x ≠ ?x |- _ ] => destruct H

         (* Naturals (Domains, Indices) *)
         | [ H: S _ = S _     |- _ ] => apply eq_add_S in H
         | [ |- S _ = S _ ] => f_equal

         (* Coproducts *)
         | [ H: inl _ = inl _ |- _ ] => inversion H; clear H; subst
         | [ H: inr _ = inr _ |- _ ] => inversion H; clear H; subst
         | [ H: inl _ = inr _ |- _ ] => inversion H
         | [ H: inr _ = inl _ |- _ ] => inversion H
         | [ |- inl _ = inl _ ] => f_equal
         | [ |- inr _ = inr _ ] => f_equal

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
         | [ H: context[match isLeftOrRight ?p ?i with _ => _ end] |- _ ] =>
           destruct (isLeftOrRight p i) eqn: ?
         | [ |- context[match isLeftOrRight ?p ?i with _ => _ end] ] =>
           destruct (isLeftOrRight p i) eqn: ?
         | [ |- pleft _ = pleft _ ] => f_equal
         | [ |- pright _ = pright _ ] => f_equal
         | [ H: isLeftOrRight _ ?i = inl _, wi: ⟪ ?i : _ ∈ _ ⟫ |- _ ] =>
           apply isLeftOrRight_inl in H
         | [ H: isLeftOrRight _ ?i = inr _, wi: ⟪ ?i : _ ∈ _ ⟫ |- _ ] =>
           apply isLeftOrRight_inr in H
         (* | [ H: context[fromLeft (pright ?p) ?i] |- _ ] => *)
         (*   change (fromLeft (pright p) i) with (S (fromLeft p i)) in H *)
         (* | [ H: context[fromRight (pleft ?p) ?i] |- _ ] => *)
         (*   change (fromRight (pleft p) i) with (S (fromRight p i)) in H *)

         (* Dom containment *)
         | [ H: ⟨_   ∈ O⟩     |- _ ] => inversion H
         | [ H: ⟨O   ∈ S _⟩   |- _ ] => clear H
         | [ H: ⟨S _ ∈ S _⟩   |- _ ] => apply inDomInvS in H
         | [ H: ⟨?i  ∈ S _⟩   |- context[match ?i with _ => _ end] ] =>
           destruct i
         | [ H: ⟨?i  ∈ S _⟩, H1: context[match ?i with _ => _ end] |- _ ] =>
           destruct i
         | [ |- ⟨S _ ∈ S _⟩ ] => constructor
         | [ H: ⟨ match ?i with _ => _ end ∈ S _ ⟩ |- _ ] =>
           destruct i eqn: ?
         | [ H: ⟨fromLeft (pleft _) ?i ∈ S _⟩ |- _ ] =>
           destruct i eqn: ?
         | [ H: ⟨fromRight (pright _) ?i ∈ S _⟩ |- _ ] =>
           destruct i eqn: ?

         (* Env containment *)
         | [ H: ⟪_   : _ ∈ ε    ⟫ |- _ ] => inversion H
         | [ H: ⟪O   : _ ∈ _ ▻ _⟫ |- _ ] => inversion H; clear H
         | [ H: ⟪S _ : _ ∈ _ ▻ _⟫ |- _ ] => apply inEnvInvS in H
         | [ H: ⟪?i  : _ ∈ _ ▻ _⟫ |- context[match ?i with _ => _ end] ] =>
           destruct i
         | [ H: ⟪?i  : _ ∈ _ ▻ _⟫, H1: context[match ?i with _ => _ end] |- _ ] =>
           destruct i
         | [ |- ⟪S _ : _ ∈ _ ▻ _⟫ ] => econstructor
         | [ |- ⟪ 0 : ?a ∈ (_ ▻ ?a) ⟫ ] => constructor
         | [ H: ⟪_   : _ ∈ [_] ⟫ |- _ ] => inversion H; clear H
         | [ H: ⟪ match ?i with _ => _ end : _ ∈ _ ▻ _ ⟫ |- _ ] =>
           destruct i eqn: ?
         | [ H: ⟪fromLeft (pleft _) ?i : _ ∈ _ ▻ _⟫ |- _ ] =>
           destruct i eqn: ?
         | [ H: ⟪fromRight (pright _) ?i : _ ∈ _ ▻ _⟫ |- _ ] =>
           destruct i eqn: ?

         (* Dom partitioning *)
         | [ pd: ⟨?p ⊢ ?γ = _ ∘ _⟩, wi: ⟨ fromLeft ?p _ ∈ ?γ ⟩ |- _ ] =>
           apply (fromLeft_inDomInv pd) in wi
         | [ pd: ⟨?p ⊢ ?γ = _ ∘ _⟩, wi: ⟨ fromRight ?p _ ∈ ?γ ⟩ |- _ ] =>
           apply (fromRight_inDomInv pd) in wi

         (* Env partitioning *)
         | [ pe: ⟪ _        ⊢ _       = ε ∘ _ ⟫ |- _ ] => apply partLeftEmpty in pe
         | [ pe: ⟪ _        ⊢ ε       = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
         | [ pe: ⟪ pnil     ⊢ _       = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
         | [ pe: ⟪ _        ⊢ (_ ▻ _) = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
         | [ pe: ⟪ pleft _  ⊢ _       = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
         | [ pe: ⟪ pright _ ⊢ _       = _ ∘ _ ⟫ |- _ ] => inversion pe; clear pe
         | [ pe: ⟪?p ⊢ ?Γ = _ ∘ _⟫, wi: ⟪ fromLeft ?p _ : _ ∈ ?γ ⟫ |- _ ] =>
           apply (fromLeft_inEnvInv pe) in wi
         | [ pe: ⟪?p ⊢ ?Γ = _ ∘ _⟫, wi: ⟪ fromRight ?p _ : _ ∈ ?γ ⟫ |- _ ] =>
           apply (fromRight_inEnvInv pe) in wi

         | [ |- ⟪ pleft _  ⊢ _       = _ ∘ _ ⟫ ] => econstructor
         | [ |- ⟪ pright _ ⊢ _       = _ ∘ _ ⟫ ] => econstructor

       end;
     simpl in *;
     subst;
     try discriminate;
     try rewrite dunion_left_zero in *;
     eauto using inDom).

Lemma isLeftOrRight_inl_inDom {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ {i j}, ⟨i ∈ γ⟩ → isLeftOrRight p i = inl j → ⟨j ∈ γ₁⟩.
Proof. induction pd; crush. Qed.

Lemma isLeftOrRight_inr_inDom {p γ γ₁ γ₂} (pd: ⟨p ⊢ γ = γ₁ ∘ γ₂⟩) :
  ∀ {i j}, ⟨i ∈ γ⟩ → isLeftOrRight p i = inr j → ⟨j ∈ γ₂⟩.
Proof. induction pd; crush. Qed.

Lemma wtix_isLeftOrRight_inl {p Γ Γ₁ Γ₂} (pe: ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ {a i j}, ⟪ i : a ∈ Γ ⟫ → isLeftOrRight p i = inl j → ⟪ j : a ∈ Γ₁ ⟫.
Proof. induction pe; crush. Qed.

Lemma wtix_isLeftOrRight_inr {p Γ Γ₁ Γ₂} (pe: ⟪ p ⊢ Γ = Γ₁ ∘ Γ₂ ⟫) :
  ∀ {a i j}, ⟪ i : a ∈ Γ ⟫ → isLeftOrRight p i = inr j → ⟪ j : a ∈ Γ₂ ⟫.
Proof. induction pe; crush. Qed.

Hint Constructors PartDom.
Hint Constructors PartEnv.

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

(* The substitution function
     substTm (i: Ix) (p: Part) (s t: Tm) : Tm
   takes as inputs
     i: The index to be substituted.
     s: The term that substitutes the index.
     t: The term in which the substitution is performed.
     p: A partitioning witness that determines the final
        order of the indices.

   Assume Δ ⊢ s, Γ ⊢ t, i ∈ Γ and p ⊢ ΓΔ = Γ ∘ Δ. Then the final context will be
   ΓΔ with the index i removed (substResultEnv ΓΔ pΓΔ i). We call ΓΔ the input
   environment (which is not given at the term level) and p the input
   partition. At each split point with partition p' we have to decide whether to
   proceed left or right with the substitution. The following functions
   calculuate the input environment and partition and also the new result
   partition for the split point that replaces p'.
 *)

Fixpoint substLeftInputEnv (ΓΔ: Env) (pΓΔ pΓ: Part) : Env :=
  match ΓΔ , pΓΔ , pΓ with
    | ε      , _          , _         => ε
    | _      , pnil       , _         => ε
    | ΓΔ ▻ a , pleft pΓΔ  , pnil      => ε
    | ΓΔ ▻ a , pleft pΓΔ  , pleft pΓ  => substLeftInputEnv ΓΔ pΓΔ pΓ ▻ a
    | ΓΔ ▻ a , pleft pΓΔ  , pright pΓ => substLeftInputEnv ΓΔ pΓΔ pΓ
    | ΓΔ ▻ a , pright pΓΔ , pΓ        => substLeftInputEnv ΓΔ pΓΔ pΓ ▻ a
  end.

Fixpoint substLeftInputPart (pΓΔ pΓ: Part) : Part :=
  match pΓΔ , pΓ with
    | pnil       , _         => pnil
    | pleft _    , pnil      => pnil
    | pleft pΓΔ  , pleft pΓ  => pleft (substLeftInputPart pΓΔ pΓ)
    | pleft pΓΔ  , pright pΓ => substLeftInputPart pΓΔ pΓ
    | pright pΓΔ , pΓ        => pright (substLeftInputPart pΓΔ pΓ)
  end.

Lemma substLeftInput {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
    ⟪ substLeftInputPart pΓΔ pΓ
      ⊢ substLeftInputEnv ΓΔ pΓΔ pΓ
      = Γ₁ ∘ Δ
    ⟫.
Proof. induction peΓΔ; crush. Qed.
Hint Resolve substLeftInput.

Fixpoint substRightInputEnv (ΓΔ: Env) (pΓΔ pΓ: Part) : Env :=
  match ΓΔ , pΓΔ , pΓ with
    | ε      , _          , _         => ε
    | _      , pnil       , _         => ε
    | ΓΔ ▻ a , pleft pΓΔ  , pnil      => ε
    | ΓΔ ▻ a , pleft pΓΔ  , pleft pΓ  => substRightInputEnv ΓΔ pΓΔ pΓ
    | ΓΔ ▻ a , pleft pΓΔ  , pright pΓ => substRightInputEnv ΓΔ pΓΔ pΓ ▻ a
    | ΓΔ ▻ a , pright pΓΔ , pΓ        => substRightInputEnv ΓΔ pΓΔ pΓ ▻ a
  end.

Fixpoint substRightInputPart (pΓΔ pΓ: Part) : Part :=
  match pΓΔ , pΓ with
    | pnil       , _         => pnil
    | pleft _    , pnil      => pnil
    | pleft pΓΔ  , pleft pΓ  => substRightInputPart pΓΔ pΓ
    | pleft pΓΔ  , pright pΓ => pleft (substRightInputPart pΓΔ pΓ)
    | pright pΓΔ , pΓ        => pright (substRightInputPart pΓΔ pΓ)
  end.

Lemma substRightInput {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
    ⟪ substRightInputPart pΓΔ pΓ ⊢ substRightInputEnv ΓΔ pΓΔ pΓ = Γ₂ ∘ Δ ⟫.
Proof. induction peΓΔ; crush. Qed.
Hint Resolve substRightInput.

Fixpoint substLeftResultPart' (pΓΔ pΓ: Part) : Part :=
  match pΓΔ , pΓ with
    | pnil         , _         => pnil
    | pleft _      , pnil      => pnil
    | pleft pΓΔ    , pleft pΓ  => pleft (substLeftResultPart' pΓΔ pΓ)
    | pleft pΓΔ    , pright pΓ => pright (substLeftResultPart' pΓΔ pΓ)
    | pright pΓΔ   , pΓ        => pleft (substLeftResultPart' pΓΔ pΓ)
  end.

Lemma substLeftResult' {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
    ⟪ substLeftResultPart' pΓΔ pΓ ⊢ ΓΔ = substLeftInputEnv ΓΔ pΓΔ pΓ ∘ Γ₂ ⟫.
Proof. induction peΓΔ; crush. Qed.
Hint Resolve substLeftResult'.

Fixpoint substRightResultPart' (pΓΔ pΓ: Part) : Part :=
  match pΓΔ , pΓ with
    | pnil         , _         => pnil
    | pleft _      , pnil      => pnil
    | pleft pΓΔ    , pleft pΓ  => pleft (substRightResultPart' pΓΔ pΓ)
    | pleft pΓΔ    , pright pΓ => pright (substRightResultPart' pΓΔ pΓ)
    | pright pΓΔ   , pΓ        => pright (substRightResultPart' pΓΔ pΓ)
  end.

Lemma substRightResult' {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {pΓ Γ₁ Γ₂},
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
    ⟪ substRightResultPart' pΓΔ pΓ ⊢ ΓΔ = Γ₁ ∘ substRightInputEnv ΓΔ pΓΔ pΓ ⟫.
Proof. induction peΓΔ; crush. Qed.
Hint Resolve substRightResult'.

Fixpoint substResultEnv (ΓΔ: Env) (pΓΔ: Part) (i: Ix) : Env :=
  match ΓΔ , pΓΔ , i with
    | ε      , _          , _   => ε
    | _      , pnil       , _   => ε
    | ΓΔ ▻ a , pleft pΓΔ  , O   => ΓΔ
    | ΓΔ ▻ a , pleft pΓΔ  , S i => substResultEnv ΓΔ pΓΔ i ▻ a
    | ΓΔ ▻ a , pright pΓΔ , i   => substResultEnv ΓΔ pΓΔ i ▻ a
  end.

Fixpoint substLeftResultPart (pΓΔ pΓ: Part) (j: Ix) : Part :=
  match pΓΔ , pΓ , j with
    | pnil       , _          , _   => pnil
    | pleft _    , pnil       , _   => pnil
    | pleft pΓΔ  , pleft pΓ   , O   => substLeftResultPart' pΓΔ pΓ
    | pleft pΓΔ  , pleft pΓ   , S j => pleft (substLeftResultPart pΓΔ pΓ j)
    | pleft pΓΔ  , pright pΓ  , j   => pright (substLeftResultPart pΓΔ pΓ j)
    | pright pΓΔ , pΓ         , j   => pleft (substLeftResultPart pΓΔ pΓ j)
  end.

Lemma substLeftResult {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {j b pΓ Γ₁ Γ₂},
    ⟪ j : b ∈ Γ₁ ⟫ →
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
    ⟪ substLeftResultPart pΓΔ pΓ j ⊢ substResultEnv ΓΔ pΓΔ (fromLeft pΓ j) =
      substResultEnv (substLeftInputEnv ΓΔ pΓΔ pΓ) (substLeftInputPart pΓΔ pΓ) j ∘ Γ₂
    ⟫.
Proof. induction peΓΔ; crush. Qed.
Hint Resolve substLeftResult.

Fixpoint substRightResultPart (pΓΔ pΓ: Part) (j: Ix) : Part :=
  match pΓΔ , pΓ , j with
    | pnil       , _          , _   => pnil
    | pleft _    , pnil       , _   => pnil
    | pleft pΓΔ  , pleft pΓ   , j   => pleft (substRightResultPart pΓΔ pΓ j)
    | pleft pΓΔ  , pright pΓ  , O   => substRightResultPart' pΓΔ pΓ
    | pleft pΓΔ  , pright pΓ  , S j => pright (substRightResultPart pΓΔ pΓ j)
    | pright pΓΔ , pΓ         , j   => pright (substRightResultPart pΓΔ pΓ j)
  end.

Lemma substRightResult {pΓΔ ΓΔ Γ Δ} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ∀ {j b pΓ Γ₁ Γ₂},
    ⟪ j : b ∈ Γ₂ ⟫ →
    ⟪ pΓ ⊢ Γ = Γ₁ ∘ Γ₂ ⟫ →
    ⟪ substRightResultPart pΓΔ pΓ j ⊢ substResultEnv ΓΔ pΓΔ (fromRight pΓ j) =
      Γ₁ ∘ substResultEnv (substRightInputEnv ΓΔ pΓΔ pΓ) (substRightInputPart pΓΔ pΓ) j
    ⟫.
Proof. induction peΓΔ; crush. Qed.
Hint Resolve substRightResult.

Lemma substResultEnv_singleton {pΓΔ ΓΔ Δ b} (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = ε ▻ b ∘ Δ ⟫) :
  Δ = substResultEnv ΓΔ pΓΔ O.
Proof. depind peΓΔ; crush. Qed.

Fixpoint substTm (i: Ix) (pΓΔ: Part) (s t: Tm) : Tm :=
  match t with
    | var _       => s
    | abs a t     => abs a (substTm (S i) (pleft pΓΔ) s t)
    | app pΓ t₁ t₂ =>
      match isLeftOrRight pΓ i with
        | inl j => (* j ∈ γ₁ *)
          app (substLeftResultPart pΓΔ pΓ j) (substTm j (substLeftInputPart pΓΔ pΓ) s t₁) t₂
        | inr j => (* j ∈ γ₂ *)
          app (substRightResultPart pΓΔ pΓ j) t₁ (substTm j (substRightInputPart pΓΔ pΓ) s t₂)
      end
  end.

Lemma substWtTm {Δ s b Γ t a} (ws: ⟪ Δ ⊢ s : b⟫) (wt: ⟪ Γ ⊢ t : a ⟫) :
  ∀ {i pΓΔ ΓΔ} (wi : ⟪ i : b ∈ Γ⟫) (peΓΔ : ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫),
    ⟪ substResultEnv ΓΔ pΓΔ i ⊢ substTm i pΓΔ s t : a ⟫.
Proof.
  induction wt; simpl; intros.
  - apply substResultEnv_singleton in peΓΔ; crush.
  - constructor.
    apply (IHwt (S i) (pleft pΓΔ) (ΓΔ ▻ a)); crush.
  - crush; econstructor; crush.
Qed.


Lemma subst0_wtTm {pΓΔ ΓΔ Γ Δ s b t a}
  (ws: ⟪ Δ ⊢ s : b ⟫) (wt: ⟪ Γ ▻ b ⊢ t : a ⟫)
  (peΓΔ: ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫) :
  ⟪ ΓΔ ⊢ substTm 0 (pleft pΓΔ) s t : a ⟫.
Proof. apply (substWtTm ws wt inEnvO (PELeft peΓΔ)). Qed.

Inductive Substs : Set :=
  | SNil
  | SSnoc (σ: Substs) (p: Part) (s: Tm).

Fixpoint substsTm (σ: Substs) (t: Tm) : Tm :=
  match σ with
    | SNil          => t
    | SSnoc σ pΓΔ s => substsTm σ (substTm 0 (pleft pΓΔ) s t)
  end.

Inductive WtSubsts : Substs → Env → Env → Prop :=
  | WtSNil {Γ} :
      WtSubsts SNil Γ Γ
  | WtSSnoc {σ Σ ΓΔ Γ Δ pΓΔ s b} :
      WtSubsts σ ΓΔ Σ →
      ⟪ pΓΔ ⊢ ΓΔ = Γ ∘ Δ ⟫ →
      ⟪ Δ ⊢ s : b ⟫ →
      WtSubsts (SSnoc σ pΓΔ s) (Γ ▻ b) Σ.

Lemma substsWtTm {σ Γ Δ} (wσ: WtSubsts σ Γ Δ) :
  ∀ {t a}, ⟪ Γ ⊢ t : a ⟫ → ⟪ Δ ⊢ substsTm σ t : a ⟫.
Proof.
  induction wσ; simpl; intros.
  - eauto.
  - eapply IHwσ.
    eapply subst0_wtTm; eauto.
Qed.

(*  Γ,Δ₂,Δ₁   Γ,Δ₂,Δ₁              *)
(*    ⇓ σ₁                         *)
(*  Γ,Δ₂        ⇓ σ₁ >>= σ₂        *)
(*    ⇓ σ₂                         *)
(*  Γ         Γ                    *)
Fixpoint substsComp (σ₁ σ₂: Substs) : Substs :=
  match σ₁ with
    | SNil         => σ₂
    | SSnoc σ₁ p s => SSnoc (substsComp σ₁ σ₂) p s
  end.
Notation "σ₁ >>= σ₂" := (substsComp σ₁ σ₂) (at level 42, left associativity).

Lemma wtsubsts_comp {σ₁ Γ Δ} (wσ₁: WtSubsts σ₁ Γ Δ) :
  ∀ σ₂ Σ,
    WtSubsts σ₂ Δ Σ →
    WtSubsts (σ₁ >>= σ₂) Γ Σ.
Proof.
  induction wσ₁; simpl; try econstructor; eauto.
Qed.


Fixpoint Value (t: Tm) : Prop :=
  match t with
    | var _     => False
    | abs _ _   => True
    | app _ _ _ => False
  end.

Reserved Notation "t₁ --> t₂" (at level 40).
Inductive red : Tm → Tm → Prop :=
  | red_abs {a t t'} :
      t --> t' →
      abs a t --> abs a t'
  | red_app₁ {p t₁ t₁' t₂} :
      t₁ --> t₁' → app p t₁ t₂ --> app p t₁' t₂
  | red_app₂ {p t₁ t₂ t₂'} :
      t₂ --> t₂' → app p t₁ t₂ --> app p t₁ t₂'
  | red_beta {p a t₁ t₂} :
      app p (abs a t₁) t₂ --> substTm 0 (pleft p) t₂ t₁
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
    + inversion wt1; subst.
      eapply subst0_wtTm; eauto.
Qed.

Lemma red_subst i p s :
  ∀ {t t'}, t --> t' → substTm i p s t --> substTm i p s t'.
Proof.
Admitted.

Inductive SN (t : Tm) : Prop :=
  | SNi : (∀ t', t --> t' → SN t') → SN t.

Lemma SNd {t} (sn_t: SN t) : ∀ t', t --> t' → SN t'.
Proof. destruct sn_t; auto. Qed.

Lemma SNappl {t1} p t2 (sn: SN (app p t1 t2)) : SN t1.
Proof.
  depind sn; constructor; intros; subst.
  eapply H0; eauto using red.
Qed.

Lemma SNvar {t} p n (sn: SN (substTm 0 p (var n) t)) : SN t.
Proof. depind sn; constructor; eauto using red_subst. Qed.

Definition Cand := Tm → Prop.
Definition Neutral : Cand :=
  fun t => match t with
             | abs _ _ => False
             | _       => True
           end.

(* Definition of reducibility candidates. *)
Record CR (P: Cand) :=
  { cr_sn : ∀ t, P t → SN t;
    cr_cl : ∀ t, P t → ∀ t', t --> t' → P t';
    cr_nt : ∀ t, Neutral t → (∀ t', t --> t' → P t') → P t
  }.
Arguments cr_sn [_] _ [_] _.
Arguments cr_cl [_] _ [_] _ [_] _.
Arguments cr_nt [_] _ [_] _ _.

Lemma CR_var {P:Cand} (crP : CR P) : ∀ n, P (var n).
Proof.
  intros; apply cr_nt; simpl; auto; intros.
  inversion H.
Qed.

Lemma CR_SN : CR SN.
Proof. constructor; eauto using SNd, SNi. Qed.

Definition ARR (P R: Cand) : Cand :=
  fun (t1: Tm) => ∀ p t2, P t2 → R (app p t1 t2).

Lemma CR_ARR {P R} {CR_P: CR P} {CR_R: CR R} : CR (ARR P R).
Proof with simpl; eauto using red.
  constructor.
  - intros t ARR_t.
    (* This is soo ugly. *)
    eapply (SNappl pnil (var 0)).
    eapply (cr_sn CR_R), ARR_t, CR_var...
  - intros t ARR_t t' r p s P_s.
    eapply (cr_cl CR_R)...
  - intros t neutral_t Hyp p t' P_t'.
    apply (cr_nt CR_R)...
    generalize (cr_sn CR_P P_t').
    induction 1 as [t']; intros t'' r.
    inversion r; subst.
    + eapply Hyp...
    + eapply cr_nt...
      eapply H0...
      eapply cr_cl...
    + destruct neutral_t.
Qed.

Lemma Lam_Sound {P R} (crP: CR P) (crR: CR R) :
  ∀ T M, (∀ p N, P N → R (substTm 0 p N M)) →
    ARR P R (abs T M).
Proof.
  intros T M H.
  assert (SN_M : SN M) by eauto using (SNvar pnil 0), (cr_sn crR), (CR_var crP).
  revert H.
  induction SN_M; intros Hyp p1 L1 ?.
  assert (SN_L1: SN L1) by eauto using (cr_sn crP).
  induction SN_L1.
  apply (cr_nt crR); simpl; auto.
  intros ? r.
  depind r; eauto.
  * dependent destruction r; eauto.
    unfold ARR in *; eauto using (cr_cl crR), red_subst.
  * eauto using (cr_cl crP).
Qed.

(* Type interpretation *)
Fixpoint Int (T: Ty) : Cand :=
  match T with
    | tbase      => SN
    | tarr T1 T2 => ARR (Int T1) (Int T2)
  end.

Lemma CR_Int (T: Ty) : CR (Int T).
Proof.
  induction T; eauto using CR_SN, CR_ARR.
Qed.

(* Definition IntEnv Γ (σ: Substs) : Prop := *)
(*   ∀ x T, lookup_evar Γ x T → Int T (substsTm σ (var x)). *)

(* Lemma Int_sound {Γ M T} (wt: Typing Γ M T) : *)
(*   ∀ σ, IntEnv Γ σ → Int T (M[σ]). *)
(* Proof. *)
(*   induction wt; intros σ IntEnv_Γ; simpl; auto using SNtt. *)
(*   - apply Lam_Sound; simpl; intros; eauto using CR_Int. *)
(*     rewrite sub_inst_comp. *)
(*     apply IHwt; simpl. *)
(*     unfold IntEnv; intros. *)
(*     dependent destruction H0; simpl. *)
(*     + rewrite sub_up1_def; simpl. *)
(*       rewrite sub_comp_snoc; simpl. *)
(*       auto. *)
(*     + rewrite sub_up1_def; simpl. *)
(*       rewrite sub_comp_snoc; simpl. *)
(*       rewrite sub_comp_assoc; simpl. *)
(*       rewrite sub_comp_id_right; simpl. *)
(*       auto. *)
(*   - simpl in *; unfold ARR in *; auto. *)
(* Qed. *)

Lemma Int_sound_id {Γ M T} (wt: ⟪ Γ ⊢ M : T ⟫) : Int T M.
Proof.
Admitted.

Theorem strong_normalization {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : SN t.
Proof.
  eauto using (cr_sn (CR_Int T)), Int_sound_id.
Qed.
