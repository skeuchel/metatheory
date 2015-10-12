Require Export MetaTheory.
Set Implicit Arguments.

(******************************************************************************)
(* Evaluation context based reduction                                         *)
(******************************************************************************)

Inductive Ctx : Set :=
  | c_hole
  | c_appfun  (c: Ctx) (t: Tm)
  | c_apparg  (t: Tm)  (v: Value t) (c: Ctx)
  | c_typefun (c: Ctx) (T: Ty)
  | c_prodl   (c: Ctx) (t: Tm)
  | c_prodr   (t: Tm)  (v: Value t) (c: Ctx)
  | c_let     (p: Pat) (c: Ctx) (t: Tm).

Fixpoint ctx_app (c : Ctx) (t : Tm) {struct c} : Tm :=
  match c with
    | c_hole           => t
    | c_appfun c' t'   => app (ctx_app c' t) t'
    | c_apparg t' _ c' => app t' (ctx_app c' t)
    | c_typefun c' T   => tapp (ctx_app c' t) T
    | c_prodl c' t'    => prod (ctx_app c' t) t'
    | c_prodr t' _ c'  => prod t' (ctx_app c' t)
    | c_let p c' t'    => lett p (ctx_app c' t) t'
  end.

Inductive red : Tm → Tm → Prop :=
  | E_AppAbs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm X0 t2 t12)
  | E_TappTabs {T11 T2 t12} :
      red (tapp (tabs T11 t12) T2) (tsubstTm X0 T2 t12)
  | E_Let {t1 : Tm} {p} {t2 : Tm} {t3 : Tm} :
      Value t1 →
      Match p t1 t2 t3 →
      red (lett p t1 t2) t3
  | E_Ctx {c t t'} :
      red t t' → red (ctx_app c t) (ctx_app c t').

(******************************************************************************)
(* Progress.                                                                  *)
(******************************************************************************)

Lemma local_progress (t : Tm) (U : Ty) (wt: Typing empty t U) :
  Value t ∨ ∃ c t0 t0', red t0 t0' ∧ t = ctx_app c t0.
Proof.
  depind wt; simpl; auto.
  - inversion H.
  - right.
    destruct IHwt1 as [v1|[c1 [s1 [s1' [r1 eq1]]]]]; subst.
    + destruct IHwt2 as [v2|[c2 [s2 [s2' [r2 eq2]]]]]; subst.
      * destruct (can_form_tarr v1 wt1) as [T1' [t12 eq2]]; subst.
        exists c_hole, (app (abs T1' t12) t2), (substTm X0 t2 t12).
        split; auto; apply E_AppAbs; trivial.
      * exists (c_apparg _ v1 c2), s2, s2'; auto.
    + exists (c_appfun c1 t2), s1, s1'; split; auto.
  - right.
    destruct IHwt as [v1|[c1 [s1 [s1' [r1 eq1]]]]]; subst.
    + destruct (can_form_tall v1 wt) as [T1' [t12 eq2]]; subst.
      exists c_hole, (tapp (tabs T1' t12) T2), (tsubstTm X0 T2 t12).
      split; trivial; apply E_TappTabs.
    + exists (c_typefun c1 T2), s1, s1'; split; trivial.
  - destruct IHwt1 as [v1|[c1 [s1 [s1' [r1 eq1]]]]]; subst.
    + destruct IHwt2 as [v2|[c2 [s2 [s2' [r2 eq2]]]]]; subst.
      * left; auto.
      * right; exists (c_prodr _ v1 c2), s2, s2'; auto.
    + right; exists (c_prodl c1 t2), s1, s1'; auto.
  - right.
    destruct IHwt1 as [v1|[c1 [s1 [s1' [r1 eq1]]]]]; subst.
    + destruct (matching_defined H v1 wt1 t2) as [t2' m].
      exists c_hole, (lett p t1 t2), t2'; split; auto using E_Let.
    + exists (c_let p c1 t2), s1, s1'; auto.
Qed.

Lemma progress (t : Tm) (U : Ty) (wt: Typing empty t U) :
  Value t ∨ ∃ t', red t t'.
Proof.
  destruct (local_progress wt) as [val_t|(c & s & s' & r & eq)]; auto.
  right; exists (ctx_app c s'); subst; apply E_Ctx; auto.
Qed.

(******************************************************************************)
(* Preservation.                                                              *)
(******************************************************************************)

Lemma context_replacement {Γ c t t' T}
  (hyp: ∀ T', Typing Γ t T' → Typing Γ t' T') :
  Typing Γ (ctx_app c t) T → Typing Γ (ctx_app c t') T.
Proof.
  intro wt; depind wt; induction c; simpl in *; subst;
    try discriminate; try (inversion x; subst); eauto using Typing.
Qed.

Lemma local_preservation_app {Γ t12 t2 T11 U} :
  Typing Γ (app (abs T11 t12) t2) U → Typing Γ (substTm X0 t2 t12) U.
Proof.
  intro wt; depind wt.
  - destruct (t_abs_inversion wt1 (sub_refl (typing_wf wt1))).
    eauto using T_Sub, subst_evar_typing with infra.
  - eauto using T_Sub.
Qed.

Lemma local_preservation_tapp {Γ T11 t12 T2 U} :
  Typing Γ (tapp (tabs T11 t12) T2) U → Typing Γ (tsubstTm X0 T2 t12) U.
Proof.
  intro wt; depind wt.
  - destruct (t_tabs_inversion wt (sub_refl (typing_wf wt))).
    eauto using subst_etvar_typing with infra.
  - eauto using T_Sub.
Qed.

Lemma local_preservation_lett' {Γ} p t1 t2 U t3 :
  Typing Γ (lett p t1 t2) U → Match p t1 t2 t3 →
  Typing Γ t3 U.
Proof.
  intro wt; depind wt; eauto using T_Sub, local_preservation_lett.
Qed.

Lemma preservation {t t'} (r: red t t') :
  ∀ {Γ U}, Typing Γ t U → Typing Γ t' U.
Proof.
  induction r.
  - eauto using local_preservation_app.
  - eauto using local_preservation_tapp.
  - eauto using local_preservation_lett'.
  - eauto using context_replacement.
Qed.
