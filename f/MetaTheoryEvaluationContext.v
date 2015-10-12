Require Import MetaTheory.
Set Implicit Arguments.

(*************************************************************************)
(* Evaluation context based reduction                                    *)
(*************************************************************************)

Inductive Ctx : Set :=
  | c_hole
  | c_appfun (c: Ctx) (t: Tm)
  | c_apparg (t: Tm) (v: Value t) (c: Ctx)
  | c_typefun (c: Ctx) (T: Ty).

Fixpoint ctx_app (c : Ctx) (t : Tm) {struct c} : Tm :=
  match c with
    | c_hole           => t
    | c_appfun c' t'   => app (ctx_app c' t) t'
    | c_apparg t' _ c' => app t' (ctx_app c' t)
    | c_typefun c' T   => tapp (ctx_app c' t) T
  end.

Inductive red : Tm → Tm → Prop :=
  | E_AppAbs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm X0 t2 t12)
  | E_TappTabs {t11 T2} :
      red (tapp (tabs t11) T2) (tsubstTm X0 T2 t11)
  | E_Ctx {c t t'} :
      red t t' → red (ctx_app c t) (ctx_app c t').

(******************************************************************************)
(* Progress.                                                                  *)
(******************************************************************************)

Lemma local_progress (t : Tm) (U : Ty) (wt: Typing empty t U) :
  Value t ∨ ∃ c t0 t0', red t0 t0' ∧ t = ctx_app c t0.
Proof.
  depind wt; simpl; auto; right.
  - inversion H.
  - destruct IHwt1 as [v1|[c1 [s1 [s1' [r1 eq1]]]]]; subst.
    + destruct IHwt2 as [v2|[c2 [s2 [s2' [r2 eq2]]]]]; subst.
      * destruct (can_form_tarr v1 wt1) as [t12 eq_t2]; subst.
        exists c_hole, (app (abs T11 t12) t2), (substTm X0 t2 t12).
        split; auto; apply E_AppAbs; trivial.
      * exists (c_apparg _ v1 c2), s2, s2'; auto.
    + exists (c_appfun c1 t2), s1, s1'; split; trivial.
  - destruct IHwt as [v1|[c1 [s1 [s1' [r1 eq_t1]]]]]; subst.
    + destruct (can_form_tall v1 wt) as [t11 eq_t1]; subst.
      exists c_hole, (tapp (tabs t11) T2), (tsubstTm X0 T2 t11).
      split; trivial; apply E_TappTabs.
    + exists (c_typefun c1 T2), s1, s1'; split; trivial.
Qed.

Lemma progress (t : Tm) (U : Ty) (wt: Typing empty t U) :
  Value t ∨ ∃ t', red t t'.
Proof.
  destruct (local_progress wt) as [val_t|[c [s [s' [r eq]]]]]; auto.
  right; exists (ctx_app c s'); subst; apply E_Ctx; trivial.
Qed.

(******************************************************************************)
(* Preservation.                                                              *)
(******************************************************************************)

Lemma context_replacement {Γ : Env} {c : Ctx} {t t' T} :
   (∀ (T' : Ty), Typing Γ t T' → Typing Γ t' T') →
   Typing Γ (ctx_app c t) T → Typing Γ (ctx_app c t') T.
Proof.
  intros H wt; depind wt.
  - induction c; simpl in x; subst; try discriminate.
    eauto using T_Var.
  - induction c; simpl in x; subst; try discriminate.
    eauto using T_Abs.
  - induction c; simpl in x; subst; try discriminate;
      try (inversion x; subst); simpl; eauto using T_App.
  - induction c; simpl in x; subst; try discriminate.
    eauto using T_Tabs.
  - induction c; simpl in x; subst; try discriminate;
      try (inversion x; subst); simpl; eauto using T_Tapp.
Qed.

Lemma local_preservation_app {Γ} t12 t2 T11 U :
  Typing Γ (app (abs T11 t12) t2) U → Typing Γ (substTm X0 t2 t12) U.
Proof.
  intro wt; depind wt.
  dependent destruction wt1; subst.
   eauto using subst_evar_typing with subst.
Qed.

Lemma local_preservation_tapp {Γ} t11 T2 U :
  Typing Γ (tapp (tabs t11) T2) U → Typing Γ (tsubstTm X0 T2 t11) U.
Proof.
  intro wt; depind wt.
  dependent destruction wt; subst;
    eauto using subst_etvar_typing with subst.
Qed.

Lemma preservation {t t'} (r: red t t') :
  ∀ {Γ U}, Typing Γ t U → Typing Γ t' U.
Proof.
  induction r; intros Γ U wt;
    eauto using
      local_preservation_app,
      local_preservation_tapp,
      context_replacement.
Qed.
