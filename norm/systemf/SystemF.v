Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.

(******************************************************************************)

Definition snoc {A: Type} (ζ: nat → A) (x: A) : nat → A :=
  fun i => match i with
             | O   => x
             | S i => ζ i
           end.
Notation "ζ · x" := (snoc ζ x) (at level 55, left associativity).

Definition Ren : Set := nat → nat.
Definition ren_id : Ren := @id _.
Definition ren_comp (ξ₁ ξ₂: Ren) : Ren := fun i => ξ₂ (ξ₁ i).
Notation "ξ₁ >-> ξ₂" := (ren_comp ξ₁ ξ₂) (at level 54).

Definition ren_up (ξ: Ren) : Ren := (ξ >-> S) · 0.
Notation "ξ ↑" := (ren_up ξ) (at level 53, left associativity).

Lemma ren_id_up : ren_id ↑ = ren_id.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma ren_eta ξ : (S >-> ξ) · ξ 0 = ξ.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma ren_reflection ξ n : S >-> (ξ · n) = ξ.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma ren_comp_id_left ξ : ren_id >-> ξ = ξ.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma ren_comp_id_right ξ : ξ >-> ren_id = ξ.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma ren_comp_assoc ξ₁ ξ₂ ξ₃ : (ξ₁ >-> ξ₂) >-> ξ₃ = ξ₁ >-> (ξ₂ >-> ξ₃).
Proof. reflexivity. Qed.

Lemma ren_comp_snoc ξ₁ ξ₂ n : (ξ₁ · n) >-> ξ₂ = (ξ₁ >-> ξ₂) · ξ₂ n.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma ren_comp_up ξ₁ ξ₂ : ξ₁ ↑ >-> ξ₂ ↑ = (ξ₁ >-> ξ₂) ↑.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma ren_S_snoc : S · 0 = ren_id.
Proof. extensionality i; destruct i; reflexivity. Qed.

Hint Rewrite ren_id_up ren_eta ren_reflection ren_comp_id_left ren_comp_snoc
  ren_comp_id_right ren_comp_assoc  ren_S_snoc ren_comp_up : infra.
Ltac rewriteHyp :=
  match goal with
    | H:_ |- _ => rewrite H by solve [ auto ]
  end.
Ltac isimpl := intros; simpl in *; autorewrite with infra in *.

(******************************************************************************)

Inductive Ty : Set :=
  | tvar (X : nat)
  | tarr (T1 T2 : Ty )
  | tall (T : Ty).

(******************************************************************************)

Reserved Notation "T [ ξ ]" (at level 14, left associativity).
Fixpoint renTy (T : Ty) (ξ: Ren) : Ty :=
  match T with
    | tvar X       => tvar (ξ X)
    | tarr T1 T2   => tarr (renTy T1 ξ) (renTy T2 ξ)
    | tall T       => tall (renTy T (ren_up ξ))
  end
where "T [ ξ ]" := (renTy T ξ).

Lemma renTy_id T : renTy T ren_id = T.
Proof. induction T; isimpl; f_equal; auto. Qed.

Lemma renTy_comp T : ∀ ξ₁ ξ₂, T[ξ₁][ξ₂] = T[ξ₁>->ξ₂].
Proof. induction T; isimpl; f_equal; rewriteHyp; isimpl; auto. Qed.

Hint Rewrite renTy_id : infra.
Hint Rewrite renTy_comp : infra.

(******************************************************************************)

Definition SubT : Set := nat → Ty.
Definition subt_id : SubT := tvar.
Definition subt_up (ζ: SubT) : SubT :=
  fun i => match i with
             | O   => tvar O
             | S i => renTy (ζ i) S
           end.
Notation "ζ ⇓" :=
  (subt_up ζ) (at level 53, left associativity, format "ζ '⇓'").

Definition ren_to_subt (ξ: Ren) : SubT := fun i => tvar (ξ i).
Notation "'⌊' ξ '⌋'" := (ren_to_subt ξ) (format "'⌊' ξ '⌋'").

Reserved Notation "t ⁅ ζ ⁆" (at level 14, left associativity).
Fixpoint subTy (T : Ty) (ζ: SubT) : Ty :=
  match T with
    | tvar X       => ζ X
    | tarr T1 T2   => tarr (T1⁅ζ⁆) (T2⁅ζ⁆)
    | tall T       => tall (T⁅ζ⇓⁆)
  end
where "T ⁅ ζ ⁆" := (subTy T ζ).

Definition subt_comp (ζT₁ ζT₂: SubT) : SubT := fun i => subTy (ζT₁ i) ζT₂.
Notation "ζ₁ >=> ζ₂" := (subt_comp ζ₁ ζ₂) (at level 54).

Lemma ren_id_to_subt : ⌊ren_id⌋ = subt_id.
Proof. reflexivity. Qed.
Hint Rewrite ren_id_to_subt : infra.

Lemma subt_id_up : subt_id ⇓ = subt_id.
Proof. extensionality i; destruct i; reflexivity. Qed.
Hint Rewrite subt_id_up : infra.

Lemma subTy_id t : t⁅subt_id⁆ = t.
Proof. induction t; isimpl; f_equal; auto. Qed.
Hint Rewrite subTy_id : infra.

Lemma subt_eta ζ : (⌊S⌋ >=> ζ) · ζ 0 = ζ.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma subt_reflection ζ s : ⌊S⌋ >=> (ζ · s) = ζ.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma subt_comp_id_left ξ : subt_id >=> ξ = ξ.
Proof. extensionality i; destruct i; reflexivity. Qed.
Hint Rewrite subt_comp_id_left : infra.

Lemma subt_comp_id_right ξ : ξ >=> subt_id = ξ.
Proof. extensionality i; unfold subt_comp; isimpl; auto. Qed.
Hint Rewrite subt_comp_id_right : infra.

Lemma subt_comp_snoc ζ₁ ζ₂ s : (ζ₁ · s) >=> ζ₂ = (ζ₁ >=> ζ₂) · s⁅ζ₂⁆.
Proof. extensionality i; destruct i; reflexivity. Qed.
Hint Rewrite subt_comp_snoc : infra.

Lemma ren_up_to_subt_up ξ : ⌊ren_up ξ⌋ = ⌊ξ⌋ ⇓.
Proof. extensionality i; destruct i; reflexivity. Qed.
Hint Rewrite ren_up_to_subt_up : infra.

Lemma renTy_to_subTy t : ∀ ξ, renTy t ξ  = subTy t ⌊ ξ ⌋.
Proof. induction t; isimpl; repeat rewriteHyp; isimpl; auto. Qed.
Hint Rewrite renTy_to_subTy : infra.

Lemma subt_up_def ζ : ζ⇓ = (ζ>=>⌊S⌋)·tvar 0.
Proof. extensionality i; destruct i; isimpl; auto. Qed.
Hint Rewrite subt_up_def.

Lemma subt_comp_ren_subt_up ξ ζ : ⌊ξ⌋⇓ >=> ζ⇓ = (⌊ξ⌋>=>ζ)⇓.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma subt_comp_ren_sub s : ∀ ξ ζ, s⁅⌊ξ⌋⁆⁅ζ⁆ = s⁅⌊ξ⌋>=>ζ⁆.
Proof.
  induction s; isimpl; repeat rewriteHyp; auto.
  - rewrite <- ren_up_to_subt_up, IHs, ren_up_to_subt_up,
      subt_comp_ren_subt_up; reflexivity.
Qed.

Lemma subt_comp_subt_ren_up ξ ζ : ζ⇓ >=> ⌊ξ⌋⇓ = (ζ>=>⌊ξ⌋)⇓.
Proof.
  extensionality i; destruct i; simpl.
  - reflexivity.
  - unfold subt_comp; simpl.
    repeat rewrite renTy_to_subTy, subt_comp_ren_sub; reflexivity.
Qed.

Lemma subt_comp_subt_ren s : ∀ ζ ξ, s⁅ζ⁆⁅⌊ξ⌋⁆ = s⁅ζ>=>⌊ξ⌋⁆.
Proof.
  induction s; simpl; intros; f_equal; auto.
  - rewrite <- ren_up_to_subt_up, IHs, ren_up_to_subt_up,
      subt_comp_subt_ren_up; reflexivity.
Qed.

Lemma subt_comp_subt_up ζ₁ ζ₂: ζ₁⇓ >=> ζ₂⇓ = (ζ₁>=>ζ₂)⇓.
Proof.
  extensionality i; destruct i; simpl.
  - reflexivity.
  - unfold subt_comp; simpl.
    repeat rewrite renTy_to_subTy.
    rewrite subt_comp_ren_sub, subt_comp_subt_ren, subt_up_def, subt_reflection.
    reflexivity.
Qed.
Hint Rewrite subt_comp_subt_up : infra.

Lemma subt_S_snoc : ⌊S⌋ · tvar 0 = subt_id.
Proof. extensionality i; destruct i; reflexivity. Qed.
Hint Rewrite subt_S_snoc : infra.

Lemma subt_inst_comp s : ∀ ζ₁ ζ₂, s⁅ζ₁⁆⁅ζ₂⁆ = s⁅ζ₁>=>ζ₂⁆.
Proof.
  induction s; simpl; intros; auto.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs, subt_comp_subt_up; reflexivity.
Qed.
Hint Rewrite subt_inst_comp : infra.

Lemma subt_comp_assoc ξ₁ ξ₂ ξ₃ : (ξ₁ >=> ξ₂) >=> ξ₃ = ξ₁ >=> (ξ₂ >=> ξ₃).
Proof.
  extensionality i; repeat unfold subt_comp; simpl.
  rewrite subt_inst_comp; reflexivity.
Qed.
Hint Rewrite subt_comp_assoc : infra.

Lemma subt_comp_up_id ζ T : ζ⇓ >=> (subt_id · T) = ζ · T.
Proof.
  extensionality i; destruct i; simpl.
  - reflexivity.
  - unfold subt_comp; isimpl; auto.
Qed.
Hint Rewrite subt_comp_up_id : infra.

(******************************************************************************)

Inductive Tm : Set :=
  | var (n : nat)
  | tt
  | abs (T: Ty) (t: Tm)
  | app (t1 t2: Tm)
  | tabs (t: Tm)
  | tapp (t: Tm) (T: Ty).

(******************************************************************************)

Reserved Notation "t ⦃ ξT , ξt ⦄" (at level 12).
Fixpoint renTm (t : Tm) (ξT: Ren) (ξt: Ren) : Tm :=
  match t with
    | var x        => var (ξt x)
    | tt           => tt
    | abs T1 t2    => abs (T1[ξT]) (t2 ⦃ ξT , ξt↑ ⦄ )
    | app t1 t2    => app (t1⦃ξT,ξt⦄) (t2⦃ξT,ξt⦄)
    | tabs t       => tabs (t⦃ξT↑,ξt⦄)
    | tapp t T     => tapp (t⦃ξT,ξt⦄) (T[ξT])
  end
where "t ⦃ ξT , ξt ⦄" := (renTm t ξT ξt).

Lemma renTm_id t : t⦃ren_id,ren_id⦄ = t.
Proof.
  induction t; simpl; f_equal; auto using renTy_id;
    rewrite ren_id_up; auto.
Qed.

Lemma renTm_comp t :
  forall ξT₁ ξt₁ ξT₂ ξt₂, t⦃ξT₁,ξt₁⦄⦃ξT₂,ξt₂⦄ = t⦃ξT₁>->ξT₂,ξt₁>->ξt₂⦄.
Proof.
  induction t; simpl; intros; auto; repeat rewrite renTy_comp; auto.
  - rewrite IHt, ren_comp_up; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt, ren_comp_up; reflexivity.
  - rewrite IHt; reflexivity.
Qed.

(******************************************************************************)

Definition Sub : Set := nat → Tm.
Bind Scope sub_scope with Sub.

Open Scope sub_scope.

Definition sub_id : Sub := var.
Definition sub_upT (ζ: Sub) : Sub :=
  fun i => renTm (ζ i) S ren_id.
Definition sub_upt (ζ: Sub) : Sub :=
  fun i => match i with
             | O   => var O
             | S i => renTm (ζ i) ren_id S
           end.

Notation "ζ ⇑" :=
  (sub_upt ζ) (at level 53, left associativity, format "ζ '⇑'").
Notation "ζ ↓" :=
  (sub_upT ζ) (at level 53, left associativity, format "ζ '↓'").

Lemma sub_id_up : sub_id ⇑ = sub_id.
Proof.
  extensionality i; destruct i; reflexivity.
Qed.

Lemma sub_id_upT : sub_id ↓ = sub_id.
Proof.
  extensionality i; destruct i; reflexivity.
Qed.

Definition ren_to_sub (ξ: Ren) : Sub := fun i => var (ξ i).
Notation "'⌈' ξ '⌉'" := (ren_to_sub ξ) (format "'⌈' ξ '⌉'").

Lemma ren_id_to_sub : ⌈ren_id⌉ = sub_id.
Proof. reflexivity. Qed.
Hint Rewrite ren_id_to_sub : infra.

Lemma ren_to_sub_id_upT ξ : ⌈ ξ ⌉ ↓ = ⌈ ξ ⌉.
Proof.
  extensionality i; destruct i; reflexivity.
Qed.
Hint Rewrite ren_to_sub_id_upT : infra.

Reserved Notation "t ⟦ ζT , ζt ⟧" (at level 14, left associativity).
Fixpoint subTm (t: Tm) (ζT: SubT) (ζt: Sub) : Tm :=
  match t with
  | var x        => ζt x
  | tt           => tt
  | abs T t      => abs (T⁅ζT⁆) (t⟦ζT,ζt⇑⟧)
  | app t1 t2    => app (t1⟦ζT,ζt⟧) (t2⟦ζT,ζt⟧)
  | tabs t       => tabs (t⟦subt_up ζT,ζt↓⟧)
  | tapp t T     => tapp (t⟦ζT,ζt⟧) (T⁅ζT⁆)
  end
where "t ⟦ ζT , ζt ⟧" := (subTm t ζT ζt).

Lemma subTm_id t : t⟦subt_id,sub_id⟧ = t.
Proof.
  induction t; simpl; f_equal; auto using subTy_id.
  - rewrite sub_id_up; auto.
  - rewrite subt_id_up; auto.
Qed.
Hint Rewrite subTm_id : infra.

Definition sub_comp (ζT₁ ζT₂: SubT) (ζt₁ ζt₂ : Sub) : Sub :=
  fun i => (ζt₁ i)⟦ζT₂,ζt₂⟧.
Notation "'⟦' ζT₁ ',' ζt₁ '⟧>=>⟦' ζT₂ ',' ζt₂ '⟧'" := (sub_comp ζT₁ ζT₂ ζt₁ ζt₂)
  (at level 54).

Lemma sub_eta (ζT:SubT) (ζt: Sub) : ⟦subt_id,⌈S⌉⟧>=>⟦ζT,ζt⟧ · ζt 0 = ζt.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_reflection (ζT:SubT) (ζt: Sub) s :
  ⟦subt_id,⌈S⌉⟧>=>⟦subt_id,ζt · s⟧ = ζt.
Proof.
  extensionality i; destruct i; reflexivity.
Qed.

Lemma sub_comp_id_left ξ : ⟦subt_id,sub_id⟧>=>⟦subt_id,ξ⟧ = ξ.
Proof.
  extensionality i; destruct i; reflexivity.
Qed.

Lemma sub_comp_snoc ζt₁ ζt₂ s :
  ⟦subt_id,ζt₁·s⟧>=>⟦subt_id,ζt₂⟧ = ⟦subt_id,ζt₁⟧>=>⟦subt_id,ζt₂⟧ · s⟦subt_id,ζt₂⟧.
Proof. extensionality i; destruct i; reflexivity. Qed.
Hint Rewrite sub_comp_snoc.

Lemma ren_up_to_sub_up ξ : ⌈ren_up ξ⌉ = ⌈ξ⌉ ⇑.
Proof.
  extensionality i; destruct i; reflexivity.
Qed.

Lemma sub_comp_id_right ζ : ⟦subt_id,ζ⟧>=>⟦subt_id,sub_id⟧ = ζ.
Proof.
  extensionality i; unfold sub_comp.
  rewrite subTm_id; reflexivity.
Qed.

Lemma renTm_to_subTm t :
  ∀ ξT ξt, t ⦃ ξT, ξt ⦄ = t ⟦ ren_to_subt ξT, ⌈ ξt ⌉ ⟧.
Proof.
  induction t; simpl; intros; auto.
  - rewrite IHt, renTy_to_subTy, ren_up_to_sub_up; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt, ren_up_to_subt_up; reflexivity.
  - rewrite IHt, renTy_to_subTy; reflexivity.
Qed.
Hint Rewrite renTm_to_subTm : infra.

Lemma sub_up_def (ζ: Sub) : ζ⇑ = ⟦subt_id,ζ⟧>=>⟦subt_id,⌈S⌉⟧ · var 0.
Proof.
  extensionality i; destruct i; simpl.
  - reflexivity.
  - rewrite renTm_to_subTm; reflexivity.
Qed.

Lemma sub_comp_ren_sub_up ζT₁ ζT₂ ξ ζ :
  ⟦ζT₁⇓,⌈ξ⌉⇑⟧>=>⟦ζT₂⇓,ζ⇑⟧ = ⟦ζT₁,⌈ξ⌉⟧>=>⟦ζT₂,ζ⟧⇑.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_comp_ren_sub_upT ζT₁ ζT₂ ξ ζ :
  ⟦ζT₁⇓,⌈ξ⌉↓⟧>=>⟦ζT₂⇓,ζ↓⟧ = ⟦ζT₁,⌈ξ⌉⟧>=>⟦ζT₂,ζ⟧↓.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_upT_ren_to_sub ξ : sub_upT (ren_to_sub ξ) = ren_to_sub ξ.
Proof. reflexivity. Qed.

Lemma sub_comp_ren_sub s :
  ∀ ζT₁ ζT₂ ξ ζ, s⟦ζT₁,⌈ξ⌉⟧⟦ζT₂,ζ⟧ = s⟦ζT₁>=>ζT₂,⟦ζT₁,⌈ξ⌉⟧>=>⟦subt_id,ζ⟧⟧.
Proof.
  induction s; isimpl; intros; repeat rewriteHyp; auto.
  - rewrite <- ren_up_to_sub_up.
    rewrite IHs.
    rewrite ren_up_to_sub_up.
    rewrite <- sub_comp_ren_sub_up.
    rewrite subt_id_up.
    reflexivity.
  - rewrite <- sub_comp_ren_sub_upT.
    isimpl; auto.
Qed.

Lemma sub_comp_sub_ren_up ζT₁ ζT₂ ξ ζ :
  ⟦ζT₁⇓,ζ⇑⟧>=>⟦ζT₂,⌈ξ⌉⇑⟧ = ⟦ζT₁,ζ⟧>=>⟦ζT₂,⌈ξ⌉⟧⇑.
Proof.
  extensionality i; destruct i; simpl.
  - reflexivity.
  - unfold sub_comp; simpl.
    repeat rewrite renTm_to_subTm.
    repeat rewrite sub_comp_ren_sub.
    isimpl.
    reflexivity.
Qed.

Lemma sub_comp_sub_ren_upT ζT₁ ζT₂ ξ ζ :
  ⟦ζT₁⇓,ζ↓⟧>=>⟦ζT₂⇓,⌈ξ⌉↓⟧ = ⟦ζT₁,ζ⟧>=>⟦ζT₂,⌈ξ⌉⟧↓.
Proof.
  extensionality i.
  unfold sub_upT, sub_comp; simpl.
  repeat rewrite renTm_to_subTm; simpl.
  repeat rewrite sub_comp_ren_sub; simpl.
  unfold sub_upT, sub_comp; simpl.
  isimpl.
  unfold ren_id, sub_id, id.
  f_equal.
  clear.
  extensionality i.
  unfold subt_comp; simpl.
  rewrite renTy_to_subTy.
  reflexivity.
Qed.

Lemma sub_comp_sub_ren s :
  ∀ ζT₁ ζT₂ ξ ζ, s⟦ζT₁,ζ⟧⟦ζT₂,⌈ξ⌉⟧ = s⟦ζT₁>=>ζT₂,⟦ζT₁,ζ⟧>=>⟦ζT₂,⌈ξ⌉⟧⟧.
Proof.
  induction s; isimpl; intros; repeat rewriteHyp; auto.
  - rewrite <- sub_comp_sub_ren_up.
    rewrite <- ren_up_to_sub_up.
    rewrite IHs.
    reflexivity.
  - rewrite <- sub_comp_sub_ren_upT.
    isimpl.
    reflexivity.
Qed.

Lemma subt_comp_S ζ : ⌊S⌋ >=> ζ⇓ = ζ >=> ⌊S⌋.
Proof.
  extensionality i.
  unfold subt_comp; simpl.
  rewrite renTy_to_subTy.
  reflexivity.
Qed.

Lemma sub_comp_sub_up ζT₁ ζT₂ ζt₁ ζt₂ :
  ⟦ζT₁⇓,ζt₁⇑⟧>=>⟦ζT₂,ζt₂⇑⟧ = ⟦ζT₁,ζt₁⟧>=>⟦ζT₂,ζt₂⟧⇑.
Proof.
  extensionality i; destruct i; simpl.
  - reflexivity.
  - unfold sub_upt, sub_comp; simpl.
    repeat rewrite renTm_to_subTm; simpl.
    repeat rewrite sub_comp_ren_sub; simpl.
    repeat rewrite sub_comp_sub_ren; simpl.
    unfold sub_upt, sub_comp; simpl.
    repeat rewrite renTm_to_subTm; simpl.
    repeat rewrite sub_comp_ren_sub; simpl.
    repeat rewrite sub_comp_sub_ren; simpl.
    isimpl.
    f_equal.
    clear.
    extensionality i.
    repeat rewrite renTm_to_subTm; simpl.
    reflexivity.
Qed.

Lemma sub_comp_sub_upT ζT₁ ζT₂ ζt₁ ζt₂ :
  ⟦ζT₁⇓,ζt₁↓⟧>=>⟦ζT₂⇓,ζt₂↓⟧ = ⟦ζT₁,ζt₁⟧>=>⟦ζT₂,ζt₂⟧↓.
Proof.
  extensionality i.
  unfold sub_upT, sub_comp; simpl.
  repeat rewrite renTm_to_subTm; simpl.
  repeat rewrite sub_comp_ren_sub; simpl.
  repeat rewrite sub_comp_sub_ren; simpl.
  unfold sub_upT, sub_comp; simpl.
  repeat rewrite renTm_to_subTm; simpl.
  repeat rewrite sub_comp_ren_sub; simpl.
  repeat rewrite sub_comp_sub_ren; simpl.
  isimpl.
  rewrite subt_comp_S.
  repeat rewrite renTm_to_subTm; simpl.
  repeat rewrite sub_comp_ren_sub; simpl.
  repeat rewrite sub_comp_sub_ren; simpl.
  f_equal.
  clear.
  extensionality i.
  repeat rewrite renTm_to_subTm; simpl.
  reflexivity.
Qed.

Lemma sub_comp_sub s :
  ∀ ζT₁ ζT₂ ζt₁ ζt₂, s⟦ζT₁,ζt₁⟧⟦ζT₂,ζt₂⟧ = s⟦ζT₁>=>ζT₂,⟦ζT₁,ζt₁⟧>=>⟦ζT₂,ζt₂⟧⟧.
Proof.
  induction s; isimpl; repeat rewriteHyp; auto.
  - f_equal.
    rewrite <- sub_comp_sub_up.
    reflexivity.
  - f_equal.
    rewrite <- sub_comp_sub_upT.
    isimpl.
    reflexivity.
Qed.
Hint Rewrite sub_comp_sub : infra.

(* Lemma subt_comp_assoc ξ₁ ξ₂ ξ₃ : (ξ₁ >=> ξ₂) >=> ξ₃ = ξ₁ >=> (ξ₂ >=> ξ₃). *)
(* Proof. *)
(*   extensionality i; repeat unfold subt_comp; simpl. *)
(*   rewrite subt_inst_comp; reflexivity. *)
(* Qed. *)

(******************************************************************************)

Inductive Env : Set :=
  | empty
  | etvar (Γ : Env)
  | evar  (Γ : Env) (T : Ty).

Inductive lookup_etvar : Env → nat → Prop :=
  | lookup_etvar_here {Γ: Env} :
      lookup_etvar (etvar Γ) O
  | lookup_etvar_there_evar {Γ: Env} {T X} :
      lookup_etvar Γ X →
      lookup_etvar (evar Γ T) X
  | lookup_etvar_there_etvar {Γ: Env} {X} :
      lookup_etvar Γ X →
      lookup_etvar (etvar Γ) (S X).
Hint Constructors lookup_etvar.

Inductive lookup_evar : Env → nat → Ty → Prop :=
  | lookup_evar_here {Γ: Env} {T} :
      lookup_evar (evar Γ T) O T
  | lookup_evar_there_evar {Γ: Env} {T T' X} :
      lookup_evar Γ X T →
      lookup_evar (evar Γ T') (S X) T
  | lookup_evar_there_etvar {Γ: Env} {T X} :
      lookup_evar Γ X T →
      lookup_evar (etvar Γ) X (renTy T S).
Hint Constructors lookup_evar.

(******************************************************************************)

Section StrongNormalization.

  Inductive red : Tm → Tm → Prop :=
    | red_beta {T11 t12 t2} :
        red (app (abs T11 t12) t2) (t12⟦subt_id,sub_id · t2⟧)
    | red_abs {T1 t2 t2'} :
        red t2 t2' → red (abs T1 t2) (abs T1 t2')
    | red_app1 {t1 t1' t2} :
        red t1 t1' → red (app t1 t2) (app t1' t2)
    | red_app2 {t1 t2 t2'} :
        red t2 t2' → red (app t1 t2) (app t1 t2')
    | red_tbeta {t11 T2} :
        red (tapp (tabs t11) T2) (t11⟦subt_id · T2,sub_id⟧)
    | red_tabs {t1 t1'} :
        red t1 t1' → red (tabs t1) (tabs t1')
    | red_tapp {t1 t1' T2} :
        red t1 t1' → red (tapp t1 T2) (tapp t1' T2).

  Lemma sub_snoc_comm ζT ζt t12 t2 :
    t12 ⟦ ζT,      ζt⇑         ⟧⟦ subt_id, sub_id · t2 ⟦ζT, ζt ⟧ ⟧ =
    t12 ⟦ subt_id, sub_id · t2 ⟧⟦ ζT     , ζt                    ⟧.
  Proof.
    isimpl.
    f_equal.
    extensionality i; destruct i; simpl.
    - reflexivity.
    - unfold sub_comp; isimpl; auto.
  Qed.

  Lemma subt_snoc_comm t11 ζT ζt T2 :
    t11 ⟦ subt_up ζT,  ζt↓    ⟧⟦ subt_id · subTy T2 ζT, sub_id ⟧ =
    t11 ⟦ subt_id · T2, sub_id ⟧⟦ ζT                   , ζt     ⟧.
  Proof.
    isimpl.
    f_equal.
    extensionality i.
    unfold sub_comp; isimpl; auto.
    unfold sub_upT; isimpl; auto.
  Qed.

  Lemma sub_up_snoc_cancel t s ζT ζt :
    t ⟦ ζT, ζt⇑    ⟧⟦ subt_id, sub_id · s ⟧ =
    t ⟦ ζT, ζt · s ⟧.
  Proof.
    isimpl.
    f_equal; extensionality i; destruct i; unfold sub_comp; isimpl; auto.
  Qed.

  Lemma subt_up_snoc_cancel t T ζT ζt :
    t ⟦ subt_up ζT, ζt↓ ⟧⟦ subt_id · T, sub_id ⟧ =
    t ⟦ ζT · T, ζt ⟧.
  Proof.
    isimpl.
    f_equal; extensionality i; destruct i; unfold sub_comp, sub_upT; isimpl; auto.
  Qed.

  Lemma red_subst {t t'} (r: red t t') :
    forall ζT ζt, red (t⟦ζT,ζt⟧) (t'⟦ζT,ζt⟧).
  Proof.
    induction r; intros; simpl; try constructor; auto.
    - rewrite <- sub_snoc_comm.
      constructor.
    - rewrite <- subt_snoc_comm.
      constructor.
  Qed.

  Inductive SN (t : Tm) : Prop :=
    SNi : (forall t', red t t' → SN t') → SN t.

  Lemma SNd {t} (sn_t: SN t) :
    forall t', red t t' → SN t'.
  Proof.
    destruct sn_t; auto.
  Qed.

  Lemma SNtt : SN tt.
  Proof.
    constructor; intros; inversion H.
  Qed.

  Lemma SNappl {t1} t2 (sn: SN (app t1 t2)) : SN t1.
  Proof.
    depind sn; constructor; intros; subst.
    eapply H0; eauto using red.
  Qed.

  Lemma SNtappl {t1} T2 (sn: SN (tapp t1 T2)) : SN t1.
  Proof.
    depind sn; constructor; intros; subst.
    eapply H0; eauto using red.
  Qed.

  Lemma SNvar {t} n (sn: SN (subTm t subt_id (sub_id · var n))) : SN t.
  Proof.
    depind sn; constructor; eauto using red_subst.
  Qed.

  Lemma SNtvar {t} n (sn: SN (subTm t (subt_id · tvar n) sub_id)) : SN t.
  Proof.
    depind sn; constructor; eauto using red_subst.
  Qed.

  Definition Cand := Tm → Prop.
  Definition Neutral : Cand :=
    fun t => match t with
               | abs _ _ | tabs _ => False
               | _                => True
             end.

  Record CR (P:Cand) :=
    { cr_sn : forall t, P t → SN t;
      cr_cl : forall t, P t → forall t', red t t' → P t';
      cr_nt : forall t, Neutral t → (forall t', red t t' → P t') → P t
    }.
  Arguments cr_sn [_] _ [_] _.
  Arguments cr_cl [_] _ [_] _ [_] _.
  Arguments cr_nt [_] _ [_] _ _.

  Lemma CR_var {P:Cand} (crP : CR P) : forall n, P (var n).
  Proof.
    intros; apply cr_nt; simpl; auto; intros.
    inversion H.
  Qed.

  Lemma CR_SN : CR SN.
  Proof.
    constructor; eauto using SNd, SNi.
  Qed.

  Definition ARR (P R: Cand) : Cand :=
    fun t1 => forall t2, P t2 → R (app t1 t2).
  Definition PI (F: Cand → Cand) : Cand :=
    fun M => forall T P, CR P → F P (tapp M T).

  Fixpoint Int (T: Ty) (e: nat → Cand) {struct T} : Cand :=
    match T with
      | tvar X     => e X
      | tarr T1 T2 => ARR (Int T1 e) (Int T2 e)
      | tall T     => PI (λ P, Int T (snoc e P))
    end.


  Lemma CR_ARR {P R} {CR_P: CR P} {CR_R: CR R} : CR (ARR P R).
  Proof with simpl; eauto using red.
    constructor.
    - intros t ARR_t; eapply (SNappl (var 0)), (cr_sn CR_R), ARR_t, CR_var...
    - intros t ARR_t t' r s P_s; eapply (cr_cl CR_R)...
    - intros t neutral_t Hyp t' P_t'; apply (cr_nt CR_R)...
      generalize (cr_sn CR_P P_t').
      induction 1 as [t']; intros t'' r.
      inversion r; subst.
      + destruct neutral_t.
      + eapply Hyp...
      + eapply cr_nt... eapply H0... eapply cr_cl...
  Qed.

  Lemma CR_PI {F} (CR_F: (forall P, CR P → CR (F P))) : CR (PI F).
  Proof with simpl; eauto using red.
    constructor; simpl.
    - intros t PI_t; apply (SNtappl (tvar 0)), (cr_sn (CR_F _ CR_SN)), PI_t, CR_SN.
    - intros t PI_t t' r T P CR_P; eapply (cr_cl (CR_F _ CR_P) (PI_t _ _ CR_P))...
    - intros t NT_t PI_t' T P CR_P; apply (cr_nt (CR_F _ CR_P))...
      intros t'' r.
      inversion r; subst.
      + destruct NT_t.
      + eapply cr_nt...
        eapply cr_cl...
        eapply PI_t'...
  Qed.

  Lemma ARR_abs {P R} (crP: CR P) (crR: CR R) :
    forall T M, (forall N, P N → R (subTm M subt_id (sub_id · N))) →
      ARR P R (abs T M).
  Proof.
    intros T M H.
    assert (SN_M : SN M) by eauto using (SNvar 0), (cr_sn crR), (CR_var crP).
    revert H.
    induction SN_M; intros Hyp L1 ?.
    assert (SN_L1: SN L1) by eauto using (cr_sn crP).
    induction SN_L1.
    apply (cr_nt crR); simpl; auto.
    intros ? r.
    depind r; eauto.
    * dependent destruction r; eauto.
      unfold ARR in *.
      eapply H0; eauto; intros.
      eapply (cr_cl crR).
      Focus 2.
      eapply red_subst.
      eauto.
      eauto using (cr_cl crR).
    * eauto using (cr_cl crP).
  Qed.

  Lemma PI_tabs {F} (CR_F: (forall P, CR P → CR (F P))) :
    forall M, (forall T P, CR P → F P (subTm M (subt_id · T) sub_id)) →
      PI F (tabs M).
  Proof.
    unfold PI in *.
    intros M H.
    cut (SN M).
    - intro SN_M.
      revert H.
      induction SN_M; intros Hyp T P CR_P.
      apply (cr_nt (CR_F P CR_P)); simpl; auto.
      intros ? r; revert P CR_P.
      depind r; eauto; intros.
      dependent destruction r; eauto.
      eapply H0; eauto; intros.
      eapply (cr_cl (CR_F P0 H1)).
      Focus 2.
      eapply red_subst.
      eauto.
      eauto using (cr_cl (CR_F P0 H1)).
    - specialize (H (tvar 0) SN CR_SN).
      apply (SNtvar 0).
      eapply (cr_sn (CR_F SN CR_SN)); eauto.
  Qed.


  Definition CRet (et : nat → Cand) :=
    forall X, CR (et X).

  Lemma CRet_snoc et P (CR_et: CRet et) (CR_P: CR P) : CRet (et · P).
  Proof.
    intro i; destruct i; simpl; auto.
  Qed.

  Lemma CR_Int (T: Ty) :
    forall et (CR_e: CRet et), CR (Int T et).
  Proof.
    induction T; eauto using CR_ARR, CR_PI, CRet_snoc.
  Qed.

  Lemma Int_exten T :
    forall et₁ et₂, (forall i t, et₁ i t <-> et₂ i t) →
      forall t, Int T et₁ t <-> Int T et₂ t.
  Proof.
    induction T; simpl; intros.
    - auto.
    - specialize (IHT1 _ _ H).
      specialize (IHT2 _ _ H).
      unfold ARR in *; split; intros; auto.
      + eapply IHT2; eauto.
        apply H0.
        apply IHT1; auto.
      + apply IHT2; auto.
        apply H0.
        apply IHT1; auto.
    - unfold PI in *; split; intros; auto; specialize (IHT (et₁ · P) (et₂ · P)).
      + eapply IHT.
        intros i; destruct i; simpl.
        * intros; split; auto.
        * auto.
        * apply H0; auto.
      + eapply IHT.
        intros i; destruct i; simpl.
        * intros; split; auto.
        * auto.
        * apply H0; auto.
  Qed.

  Lemma Int_rename T :
    forall ξ et t, Int (renTy T ξ) et t <-> Int T (fun i => et (ξ i)) t.
  Proof.
    induction T; simpl; intros.
    - split; auto.
    - unfold ARR in *.
      split; intros; auto.
      + apply IHT2.
        apply H.
        eapply IHT1.
        eauto.
      + eapply IHT2.
        apply H.
        eapply IHT1.
        eauto.
    - assert (Hyp : ∀ P (i : nat) (t0 : Tm),
                (et · P) (ren_up ξ i) t0 ↔
                ((λ i0 : nat, et (ξ i0)) · P) i t0)
        by (intros; destruct i; simpl; split; auto).
      assert (IHTa := fun ξ et t => proj1 (IHT ξ et t)).
      assert (IHTb := fun ξ et t => proj2 (IHT ξ et t)).
      split; intros H U P CR_P; specialize (H U P CR_P);
        destruct (Int_exten T _ _ (Hyp P) (tapp t U)); eauto.
  Qed.

  Lemma Int_subst T :
    forall ζ et t, Int (subTy T ζ) et t <-> Int T (fun i => Int (ζ i) et) t.
  Proof.
    induction T; simpl; intros.
    - split; auto.
    - unfold ARR in *; split; intros; auto.
      + eapply IHT2; eauto.
        apply H.
        apply IHT1; auto.
      + apply IHT2; auto.
        apply H.
        apply IHT1; auto.
    - unfold PI in *; split; intros H U P CR_P; auto.
      + specialize (H U P CR_P).
        apply IHT in H.
        refine (proj1 (@Int_exten T _ _ _ (tapp t U)) H).
        intros.
        destruct i; simpl; split; auto.
        * intros.
          apply (proj1 (Int_rename _ _ _ _)) in H0.
          apply H0.
        * intros.
          apply Int_rename.
          apply H0.
      + specialize (H U P CR_P).
        apply IHT.
        refine (proj1 (@Int_exten T _ _ _ (tapp t U)) H).
        intros.
        destruct i; simpl; split; auto.
        * intros.
          apply (proj2 (Int_rename _ _ _ _)).
          apply H0.
        * intros.
          apply (proj1 (Int_rename _ _ _ _)) in H0.
          apply H0.
  Qed.

  Definition IntEnv Γ (et: nat → Cand) (ζ: Sub) : Prop :=
    forall x T, lookup_evar Γ x T → Int T et (ζ x).

  Lemma IntEnv_snoc :
    ∀ (Γ : Env) (et : nat → Cand) (ζ : Sub) (P : Cand),
      IntEnv Γ et ζ → IntEnv (etvar Γ) (et · P) ζ.
  Proof.
    unfold IntEnv; simpl; intros.
    dependent destruction H0.
    apply Int_rename; auto.
  Qed.

(******************************************************************************)

Inductive Typing (Γ: Env) : Tm → Ty → Prop :=
  | T_Var {x T} :
      lookup_evar Γ x T → Typing Γ (var x) T
  | T_Abs {t2 T1 T2} :
      Typing (evar Γ T1) t2 T2 →
      Typing Γ (abs T1 t2) (tarr T1 T2)
  | T_App {t1 t2 T11 T12} :
      Typing Γ t1 (tarr T11 T12) → Typing Γ t2 T11 →
      Typing Γ (app t1 t2) T12
  | T_Tabs {t T} :
      Typing (etvar Γ) t T →
      Typing Γ (tabs t) (tall T)
  | T_Tapp {t1 T12 T2} :
      Typing Γ t1 (tall T12) →
      Typing Γ (tapp t1 T2) (subTy T12 (subt_id · T2)).

Theorem fundamental {Γ M T} (wt: Typing Γ M T) :
  forall et ζT ζt, CRet et → IntEnv Γ et ζt → Int T et (M⟦ζT,ζt⟧).
Proof.
  induction wt; intros et ζT ζt CRet_et IntEnv_Γ; simpl; auto using SNtt.
  - eapply ARR_abs; simpl; intros; eauto using CR_Int.
    rewrite sub_up_snoc_cancel.
    apply IHwt; simpl; auto.
    unfold IntEnv; intros.
    dependent destruction H0; simpl; eauto.
  - simpl in *; unfold ARR in *; auto.
  - eapply PI_tabs; simpl; intros; eauto using CR_Int, CRet_snoc.
    rewrite subt_up_snoc_cancel.
    apply IHwt; auto using CRet_snoc, IntEnv_snoc.
  - simpl in *; unfold PI in *.
    apply Int_subst.
    specialize (IHwt et ζT ζt CRet_et IntEnv_Γ (subTy T2 ζT) _ (CR_Int T2 _ CRet_et)).
    refine (proj1 (Int_exten _ _ _ _ _) IHwt).
    intros i; destruct i; simpl; split; auto.
Qed.

Lemma fundamental_id {Γ M T} (wt: Typing Γ M T) et (CR_et: CRet et) :
  Int T et M.
Proof.
  rewrite <- subTm_id; apply (fundamental wt); auto.
  intros ? ? ?; eapply CR_var, CR_Int; auto.
Qed.

Theorem strong_normalization {Γ t T} (wt: Typing Γ t T) : SN t.
Proof.
  assert (CRs: CRet (λ _ : nat, SN)) by (intro; apply CR_SN).
  apply (@cr_sn (Int T (λ _ : nat, SN))).
  apply CR_Int, CRs.
  apply (fundamental_id wt), CRs.
Qed.
