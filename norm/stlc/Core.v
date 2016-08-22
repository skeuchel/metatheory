Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.

Inductive Ty : Set :=
  | tunit
  | tarr (T1 T2 : Ty).

Inductive Tm : Set :=
  | var (n : nat)
  | tt
  | abs (T: Ty) (t: Tm)
  | app (t1 t2: Tm).

Inductive Env : Set :=
  | empty
  | evar (Γ : Env) (T : Ty).

Inductive lookup_evar : Env → nat → Ty → Prop :=
  | lookup_evar_here {Γ T} :
      lookup_evar (evar Γ T) O T
  | lookup_evar_there_evar {Γ T T' X} :
      lookup_evar Γ X T →
      lookup_evar (evar Γ T') (S X) T.
Hint Constructors lookup_evar.

Inductive Typing (Γ: Env) : Tm → Ty → Prop :=
  | T_Var {y T} :
      lookup_evar Γ y T → Typing Γ (var y) T
  | T_Unit :
      Typing Γ tt tunit
  | T_Abs {t T1 T2} :
      Typing (evar Γ T1) t T2 →
      Typing Γ (abs T1 t) (tarr T1 T2)
  | T_App {t1 t2 T11 T12} :
      Typing Γ t1 (tarr T11 T12) → Typing Γ t2 T11 →
      Typing Γ (app t1 t2) T12.

Definition Cand := Tm → Prop.
Definition Neutral : Cand :=
  fun t => match t with
             | abs _ _ => False
             | _       => True
           end.

(******************************************************************************)

Definition snoc {A: Type} (ζ: nat → A) (x: A) : nat → A :=
  fun i => match i with
             | O   => x
             | S i => ζ i
           end.
Notation "ζ · x" := (snoc ζ x) (at level 55, left associativity).

(******************************************************************************)

Definition Ren : Set := nat → nat.
Bind Scope ren_scope with Ren.

Section Renaming.
  Local Open Scope ren_scope.

  Definition ren_id : Ren := @id _.
  Definition ren_comp (ρ₁ ρ₂: Ren) : Ren := fun i => ρ₂ (ρ₁ i).
  Notation "ρ₁ >=> ρ₂" := (ren_comp ρ₁ ρ₂) (at level 54) : ren_scope.
  Definition ren_up (ρ: Ren) : Ren := (ρ >=> S) · 0.
  Notation "ρ ⇑" := (ren_up ρ) (at level 53, left associativity) : ren_scope.

  Reserved Notation "t [ ρ ]" (at level 12).
  Fixpoint renTm (t : Tm) (ρ: Ren) : Tm :=
    match t with
      | var x        => var (ρ x)
      | tt           => tt
      | abs T t2     => abs T (t2[ρ⇑])
      | app t1 t2    => app (t1[ρ]) (t2[ρ])
    end
  where "t [ ρ ]" := (renTm t ρ) : ren_scope.

  Lemma ren_id_up : ren_id ⇑ = ren_id.
  Proof. extensionality i; destruct i; reflexivity. Qed.

  Lemma renTm_id t : t[ren_id] = t.
  Proof. induction t; simpl; f_equal; rewrite ?ren_id_up; auto. Qed.

  Lemma ren_eta ρ : (S >=> ρ) · ρ 0 = ρ.
  Proof. extensionality i; destruct i; reflexivity. Qed.

  Lemma ren_reflection ρ n : S >=> (ρ · n) = ρ.
  Proof. extensionality i; destruct i; reflexivity. Qed.

  Lemma ren_comp_id_left ρ : ren_id >=> ρ = ρ.
  Proof. extensionality i; destruct i; reflexivity. Qed.

  Lemma ren_comp_id_right ρ : ρ >=> ren_id = ρ.
  Proof. extensionality i; destruct i; reflexivity. Qed.

  Lemma ren_comp_assoc ρ₁ ρ₂ ρ₃ : (ρ₁ >=> ρ₂) >=> ρ₃ = ρ₁ >=> (ρ₂ >=> ρ₃).
  Proof. reflexivity. Qed.

  Lemma ren_comp_snoc ζ₁ ζ₂ n : (ζ₁ · n) >=> ζ₂ = (ζ₁ >=> ζ₂) · ζ₂ n.
  Proof. extensionality i; destruct i; reflexivity. Qed.

  Lemma ren_comp_up ζ₁ ζ₂ : ζ₁ ⇑ >=> ζ₂ ⇑ = (ζ₁ >=> ζ₂) ⇑.
  Proof. extensionality i; destruct i; reflexivity. Qed.

  Lemma ren_inst_comp s :
    forall ζ₁ ζ₂, s[ζ₁][ζ₂] = s[ζ₁>=>ζ₂].
  Proof.
    induction s; simpl; intros; f_equal;
      rewrite <- ?ren_comp_up; auto.
  Qed.

  (* Lemma ren_S_snoc : S · 0 = ren_id. *)
  (* Proof. extensionality i; destruct i; reflexivity. Qed. *)

End Renaming.

(******************************************************************************)

Definition Sub : Set := nat → Tm.
Bind Scope sub_scope with Sub.

Open Scope sub_scope.

Definition sub_id : Sub := var.
Definition sub_up (ζ: Sub) : Sub :=
  fun i => match i with
             | O   => var O
             | S i => renTm (ζ i) S
           end.
Notation "ζ ⇑" :=
  (sub_up ζ) (at level 53, left associativity, format "ζ '⇑'") : sub_scope.

Definition ren_to_sub (ρ: Ren) : Sub := fun i => var (ρ i).
Notation "'⌈' ρ '⌉'" := (ren_to_sub ρ) (format "'⌈' ρ '⌉'") : sub_scope.

Reserved Notation "t [ ζ ]" (at level 12, left associativity).
Fixpoint subTm (t: Tm) (ζ: Sub) : Tm :=
  match t with
  | var x        => ζ x
  | tt           => tt
  | abs T t      => abs T (t[ζ⇑])
  | app t1 t2    => app (t1[ζ]) (t2[ζ])
  end
where "t [ ζ ] " := (subTm t ζ) : sub_scope.

Definition sub_comp (ζ τ: Sub) : Sub := fun i => (ζ i)[τ].
Notation "ζ₁ >=> ζ₂" := (sub_comp ζ₁ ζ₂) (at level 54) : sub_scope.

Lemma sub_id_up : sub_id ⇑ = sub_id.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_inst_id t : t[sub_id] = t.
Proof. induction t; simpl; f_equal; rewrite ?sub_id_up; auto. Qed.

Lemma sub_eta (ζ: Sub) : (⌈S⌉ >=> ζ) · ζ 0 = ζ.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_reflection ζ s : ⌈ S ⌉ >=> (ζ · s) = ζ.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_comp_id_left ρ : sub_id >=> ρ = ρ.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_comp_id_right ρ : ρ >=> sub_id = ρ.
Proof.
  extensionality i; unfold sub_comp.
  rewrite sub_inst_id; reflexivity.
Qed.

Lemma sub_comp_snoc ζ₁ ζ₂ s : (ζ₁ · s) >=> ζ₂ = (ζ₁ >=> ζ₂) · s[ζ₂].
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma ren_up_to_sub_up ρ : ⌈ren_up ρ⌉ = ⌈ρ⌉ ⇑.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma renTm_to_subTm t :
  forall ρ, renTm t ρ  = subTm t ⌈ ρ ⌉.
Proof.
  induction t; simpl; intros; auto.
  - rewrite IHt, ren_up_to_sub_up; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma sub_up_def (ζ: Sub) : ζ⇑ = (ζ >=> ⌈ S ⌉) · var 0.
Proof.
  extensionality i; destruct i; simpl.
  - reflexivity.
  - rewrite renTm_to_subTm; reflexivity.
Qed.

Lemma sub_comp_ren_sub_up ρ ζ : ⌈ρ⌉⇑ >=> ζ⇑ = (⌈ρ⌉>=>ζ)⇑.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_comp_ren_sub s :
  forall ρ ζ,  s[⌈ρ⌉][ζ] = s[⌈ρ⌉>=>ζ].
Proof.
  induction s; simpl; intros; auto.
  - rewrite <- ren_up_to_sub_up, IHs, ren_up_to_sub_up,
      sub_comp_ren_sub_up; reflexivity.
  - rewrite IHs1, IHs2; auto.
Qed.

Lemma sub_comp_sub_ren_up ρ ζ : ζ⇑ >=> ⌈ρ⌉⇑ = (ζ>=>⌈ρ⌉)⇑.
Proof.
  extensionality i; destruct i; simpl.
  - reflexivity.
  - unfold sub_comp; simpl.
    repeat rewrite renTm_to_subTm, sub_comp_ren_sub; reflexivity.
Qed.

Lemma sub_comp_sub_ren s :
  forall ζ ρ, s[ζ][⌈ρ⌉] = s[ζ>=>⌈ρ⌉].
Proof.
  induction s; simpl; intros; f_equal; auto.
  - rewrite <- ren_up_to_sub_up, IHs, ren_up_to_sub_up,
      sub_comp_sub_ren_up; reflexivity.
Qed.

Lemma sub_comp_sub_up ζ₁ ζ₂: ζ₁⇑ >=> ζ₂⇑ = (ζ₁>=>ζ₂)⇑.
Proof.
  extensionality i; destruct i; simpl.
  - reflexivity.
  - unfold sub_comp; simpl.
    repeat rewrite renTm_to_subTm.
    rewrite sub_comp_ren_sub, sub_comp_sub_ren, sub_up_def, sub_reflection.
    reflexivity.
Qed.

Lemma sub_S_snoc : ⌈ S ⌉ · var 0 = sub_id.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_inst_comp s :
  forall ζ₁ ζ₂, s[ζ₁][ζ₂] = s[ζ₁>=>ζ₂].
Proof.
  induction s; simpl; intros; auto.
  - rewrite IHs, sub_comp_sub_up; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
Qed.

Lemma sub_comp_assoc ρ₁ ρ₂ ρ₃ :
  (ρ₁ >=> ρ₂) >=> ρ₃ = ρ₁ >=> (ρ₂ >=> ρ₃).
Proof.
  extensionality i; repeat unfold sub_comp; simpl.
  rewrite sub_inst_comp; reflexivity.
Qed.

Lemma sub_comm s ζ : ζ ⇑ >=> (sub_id · s [ζ]) = (sub_id · s) >=> ζ.
Proof.
  rewrite sub_comp_snoc.
  rewrite sub_comp_id_left.
  rewrite sub_up_def.
  rewrite sub_comp_snoc.
  rewrite sub_comp_assoc.
  rewrite sub_comp_id_right.
  reflexivity.
Qed.
