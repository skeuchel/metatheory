Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.
Section Namespace.
  Inductive Namespace : Type :=
    | tm 
    | ty .
  Lemma eq_namespace_dec (a : Namespace) (b : Namespace) :
    (sumbool (a =
    b) (not (a =
    b))).
  Proof.
    decide equality .
  Defined.
End Namespace.

Section HVarlist.
  Inductive Hvl : Type :=
    | H0 
    | HS (a : Namespace) (k : Hvl).
  
  Fixpoint appendHvl (k : Hvl) (k0 : Hvl) {struct k0} : Hvl :=
    match k0 with
      | (H0) => k
      | (HS a k0) => (HS a (appendHvl k k0))
    end.
  
  Lemma appendHvl_assoc  :
    (forall (k : Hvl) (k0 : Hvl) (k1 : Hvl) ,
      ((appendHvl (appendHvl k k0) k1) =
      (appendHvl k (appendHvl k0 k1)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End HVarlist.

Section Index.
  Inductive Index (a : Namespace) : Type :=
    | I0 
    | IS : (Index a) -> (Index a).
  
  Global Arguments I0 [a] .
  Global Arguments IS [a] _ .
  
  Lemma eq_index_dec {a : Namespace} (i : (Index a)) (j : (Index a)) :
    (sumbool (i =
    j) (not (i =
    j))).
  Proof.
    decide equality .
  Qed.
  
  Fixpoint weakenIndextm (x : (Index tm)) (k : Hvl) {struct k} : (Index tm) :=
    match k with
      | (H0) => x
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x k))
        | _ => (weakenIndextm x k)
      end
    end.
  Fixpoint weakenIndexty (X : (Index ty)) (k : Hvl) {struct k} : (Index ty) :=
    match k with
      | (H0) => X
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X k))
        | _ => (weakenIndexty X k)
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x k) k0) =
      (weakenIndextm x (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexty_append  :
    (forall (X : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X k) k0) =
      (weakenIndexty X (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | tvar (X : (Index ty))
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (T : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Decls : Set :=
    | dnil 
    | dcons (t : Tm) (d : Decls)
  with Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (t : Tm)
    | tapp (t : Tm) (T : Ty)
    | lett (d : Decls) (t : Tm).
  Scheme ind_Decls := Induction for Decls Sort Prop
  with ind_Tm := Induction for Tm Sort Prop.
  Combined Scheme ind_Decls_Tm from ind_Decls, ind_Tm.
End Terms.

Section Functions.
  Fixpoint bind (d : Decls) {struct d} : Hvl :=
    match d with
      | (dnil) => H0
      | (dcons t d) => (appendHvl (HS tm H0) (appendHvl (bind d) H0))
    end.
  Scheme ind_bind_Decls := Induction for Decls Sort Prop.
End Functions.

Section Shift.
  Inductive Cutoff (a : Namespace) : Type :=
    | C0 
    | CS : (Cutoff a) -> (Cutoff a).
  
  Global Arguments C0 {a} .
  Global Arguments CS {a} _ .
  Fixpoint weakenCutofftm (c : (Cutoff tm)) (k : Hvl) {struct k} : (Cutoff tm) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (tm) => (CS (weakenCutofftm c k))
        | _ => (weakenCutofftm c k)
      end
    end.
  Fixpoint weakenCutoffty (c : (Cutoff ty)) (k : Hvl) {struct k} : (Cutoff ty) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (ty) => (CS (weakenCutoffty c k))
        | _ => (weakenCutoffty c k)
      end
    end.
  
  Lemma weakenCutofftm_append  :
    (forall (c : (Cutoff tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutofftm (weakenCutofftm c k) k0) =
      (weakenCutofftm c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenCutoffty_append  :
    (forall (c : (Cutoff ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffty (weakenCutoffty c k) k0) =
      (weakenCutoffty c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shiftIndex (c : (Cutoff tm)) (x : (Index tm)) {struct c} : (Index tm) :=
    match c with
      | (C0) => (IS x)
      | (CS c) => match x with
        | (I0) => I0
        | (IS x) => (IS (shiftIndex c x))
      end
    end.
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X : (Index ty)) {struct c} : (Index ty) :=
    match c with
      | (C0) => (IS X)
      | (CS c) => match X with
        | (I0) => I0
        | (IS X) => (IS (tshiftIndex c X))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff ty)) (S0 : Ty) {struct S0} : Ty :=
    match S0 with
      | (tvar X) => (tvar (tshiftIndex c X))
      | (tarr T1 T2) => (tarr (tshiftTy (weakenCutoffty c H0) T1) (tshiftTy (weakenCutoffty c H0) T2))
      | (tall T) => (tall (tshiftTy (weakenCutoffty c (appendHvl (HS ty H0) H0)) T))
    end.
  Fixpoint shiftDecls (c : (Cutoff tm)) (d : Decls) {struct d} : Decls :=
    match d with
      | (dnil) => (dnil)
      | (dcons t d0) => (dcons (shiftTm (weakenCutofftm c H0) t) (shiftDecls (weakenCutofftm c (appendHvl (HS tm H0) H0)) d0))
    end
  with shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var (shiftIndex c x))
      | (abs T t) => (abs T (shiftTm (weakenCutofftm c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (shiftTm (weakenCutofftm c H0) t1) (shiftTm (weakenCutofftm c H0) t2))
      | (tabs t0) => (tabs (shiftTm (weakenCutofftm c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T0) => (tapp (shiftTm (weakenCutofftm c H0) t3) T0)
      | (lett d t4) => (lett (shiftDecls (weakenCutofftm c H0) d) (shiftTm (weakenCutofftm c (appendHvl (bind d) H0)) t4))
    end.
  Fixpoint tshiftDecls (c : (Cutoff ty)) (d : Decls) {struct d} : Decls :=
    match d with
      | (dnil) => (dnil)
      | (dcons t d0) => (dcons (tshiftTm (weakenCutoffty c H0) t) (tshiftDecls (weakenCutoffty c (appendHvl (HS tm H0) H0)) d0))
    end
  with tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tshiftTy (weakenCutoffty c H0) T) (tshiftTm (weakenCutoffty c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (tshiftTm (weakenCutoffty c H0) t1) (tshiftTm (weakenCutoffty c H0) t2))
      | (tabs t0) => (tabs (tshiftTm (weakenCutoffty c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T0) => (tapp (tshiftTm (weakenCutoffty c H0) t3) (tshiftTy (weakenCutoffty c H0) T0))
      | (lett d t4) => (lett (tshiftDecls (weakenCutoffty c H0) d) (tshiftTm (weakenCutoffty c (appendHvl (bind d) H0)) t4))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} : Ty :=
    match k with
      | (H0) => S0
      | (HS tm k) => (weakenTy S0 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S0 k))
    end.
  Fixpoint weakenDecls (d : Decls) (k : Hvl) {struct k} : Decls :=
    match k with
      | (H0) => d
      | (HS tm k) => (shiftDecls C0 (weakenDecls d k))
      | (HS ty k) => (tshiftDecls C0 (weakenDecls d k))
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} : Tm :=
    match k with
      | (H0) => s
      | (HS tm k) => (shiftTm C0 (weakenTm s k))
      | (HS ty k) => (tshiftTm C0 (weakenTm s k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x : (Trace a)) (k : Hvl) {struct k} : (Trace a) :=
    match k with
      | (H0) => x
      | (HS b k) => (XS b (weakenTrace x k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x k) k0) =
      (weakenTrace x (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint substIndex (d : (Trace tm)) (s : Tm) (x : (Index tm)) {struct d} : Tm :=
    match d with
      | (X0) => match x with
        | (I0) => s
        | (IS x) => (var x)
      end
      | (XS tm d) => match x with
        | (I0) => (var I0)
        | (IS x) => (shiftTm C0 (substIndex d s x))
      end
      | (XS ty d) => (tshiftTm C0 (substIndex d s x))
    end.
  Fixpoint tsubstIndex (d : (Trace ty)) (S0 : Ty) (X : (Index ty)) {struct d} : Ty :=
    match d with
      | (X0) => match X with
        | (I0) => S0
        | (IS X) => (tvar X)
      end
      | (XS tm d) => (tsubstIndex d S0 X)
      | (XS ty d) => match X with
        | (I0) => (tvar I0)
        | (IS X) => (tshiftTy C0 (tsubstIndex d S0 X))
      end
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S1} : Ty :=
    match S1 with
      | (tvar X) => (tsubstIndex d S0 X)
      | (tarr T1 T2) => (tarr (tsubstTy d S0 T1) (tsubstTy d S0 T2))
      | (tall T) => (tall (tsubstTy (XS ty d) S0 T))
    end.
  Fixpoint substDecls (d : (Trace tm)) (s : Tm) (d0 : Decls) {struct d0} : Decls :=
    match d0 with
      | (dnil) => (dnil)
      | (dcons t d1) => (dcons (substTm d s t) (substDecls (XS tm d) s d1))
    end
  with substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} : Tm :=
    match s0 with
      | (var x) => (substIndex d s x)
      | (abs T t) => (abs T (substTm (XS tm d) s t))
      | (app t1 t2) => (app (substTm d s t1) (substTm d s t2))
      | (tabs t0) => (tabs (substTm (XS ty d) s t0))
      | (tapp t3 T0) => (tapp (substTm d s t3) T0)
      | (lett d0 t4) => (lett (substDecls d s d0) (substTm (weakenTrace d (bind d0)) s t4))
    end.
  Fixpoint tsubstDecls (d : (Trace ty)) (S0 : Ty) (d0 : Decls) {struct d0} : Decls :=
    match d0 with
      | (dnil) => (dnil)
      | (dcons t d1) => (dcons (tsubstTm d S0 t) (tsubstDecls (XS tm d) S0 d1))
    end
  with tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tsubstTy d S0 T) (tsubstTm (XS tm d) S0 t))
      | (app t1 t2) => (app (tsubstTm d S0 t1) (tsubstTm d S0 t2))
      | (tabs t0) => (tabs (tsubstTm (XS ty d) S0 t0))
      | (tapp t3 T0) => (tapp (tsubstTm d S0 t3) (tsubstTy d S0 T0))
      | (lett d0 t4) => (lett (tsubstDecls d S0 d0) (tsubstTm (weakenTrace d (bind d0)) S0 t4))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftDecls C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftDecls C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : interaction.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : interaction.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_shift_bind  :
  (forall (d : Decls) ,
    (forall (c : (Cutoff tm)) ,
      ((bind (shiftDecls c d)) =
      (bind d)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
Lemma stability_tshift_bind  :
  (forall (d0 : Decls) ,
    (forall (c0 : (Cutoff ty)) ,
      ((bind (tshiftDecls c0 d0)) =
      (bind d0)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_shift_bind stability_tshift_bind : interaction.
 Hint Rewrite stability_shift_bind stability_tshift_bind : stability_shift.
Lemma stability_weaken_bind  :
  (forall (k : Hvl) (d1 : Decls) ,
    ((bind (weakenDecls d1 k)) =
    (bind d1))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bind : interaction.
 Hint Rewrite stability_weaken_bind : stability_weaken.
Lemma stability_subst_bind  :
  (forall (d1 : Decls) ,
    (forall (d2 : (Trace tm)) (s : Tm) ,
      ((bind (substDecls d2 s d1)) =
      (bind d1)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
Lemma stability_tsubst_bind  :
  (forall (d3 : Decls) ,
    (forall (d4 : (Trace ty)) (S0 : Ty) ,
      ((bind (tsubstDecls d4 S0 d3)) =
      (bind d3)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_subst_bind stability_tsubst_bind : interaction.
 Hint Rewrite stability_subst_bind stability_tsubst_bind : stability_subst.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s0 : Tm) :
    (forall (k4 : Hvl) (x13 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k4) s0 (shiftIndex (weakenCutofftm C0 k4) x13)) =
      (var x13))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S1 : Ty) :
    (forall (k4 : Hvl) (X8 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k4) S1 (tshiftIndex (weakenCutoffty C0 k4) X8)) =
      (tvar X8))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Definition tsubst0_tshift0_Ty_reflection_ind := (ind_Ty (fun (S3 : Ty) =>
    (forall (k7 : Hvl) (S4 : Ty) ,
      ((tsubstTy (weakenTrace X0 k7) S4 (tshiftTy (weakenCutoffty C0 k7) S3)) =
      S3))) (fun (X14 : (Index ty)) =>
    (fun (k7 : Hvl) (S3 : Ty) =>
      (tsubstIndex0_tshiftIndex0_reflection_ind S3 k7 X14))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tarr (IHT0 k7 S3) (IHT3 k7 S3))) (fun (T : Ty) IHT0 (k7 : Hvl) (S3 : Ty) =>
    (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHT0 (HS ty k7) S3))))).
  Definition subst0_shift0_Decls_Tm_reflection_ind := (ind_Decls_Tm (fun (d17 : Decls) =>
    (forall (k7 : Hvl) (s1 : Tm) ,
      ((substDecls (weakenTrace X0 k7) s1 (shiftDecls (weakenCutofftm C0 k7) d17)) =
      d17))) (fun (s1 : Tm) =>
    (forall (k7 : Hvl) (s2 : Tm) ,
      ((substTm (weakenTrace X0 k7) s2 (shiftTm (weakenCutofftm C0 k7) s1)) =
      s1))) (fun (k7 : Hvl) (s1 : Tm) =>
    eq_refl) (fun (t : Tm) IHt41 (d : Decls) IHd (k7 : Hvl) (s1 : Tm) =>
    (f_equal2 dcons (IHt41 k7 s1) (eq_trans (f_equal3 substDecls (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl) (IHd (HS tm k7) s1)))) (fun (x20 : (Index tm)) =>
    (fun (k7 : Hvl) (s1 : Tm) =>
      (substIndex0_shiftIndex0_reflection_ind s1 k7 x20))) (fun (T : Ty) (t : Tm) IHt41 (k7 : Hvl) (s1 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt41 (HS tm k7) s1)))) (fun (t1 : Tm) IHt41 (t2 : Tm) IHt42 (k7 : Hvl) (s1 : Tm) =>
    (f_equal2 app (IHt41 k7 s1) (IHt42 k7 s1))) (fun (t : Tm) IHt41 (k7 : Hvl) (s1 : Tm) =>
    (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt41 (HS ty k7) s1)))) (fun (t : Tm) IHt41 (T : Ty) (k7 : Hvl) (s1 : Tm) =>
    (f_equal2 tapp (IHt41 k7 s1) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt41 (k7 : Hvl) (s1 : Tm) =>
    (f_equal2 lett (IHd k7 s1) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_shift_bind _ _) (eq_refl H0))) (weakenTrace_append tm X0 k7 (bind d))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k7 (bind d)) eq_refl)) (IHt41 (appendHvl k7 (bind d)) s1))))).
  Lemma subst0_shift0_Decls_reflection_ind  :
    (forall (d17 : Decls) ,
      (forall (k7 : Hvl) (s1 : Tm) ,
        ((substDecls (weakenTrace X0 k7) s1 (shiftDecls (weakenCutofftm C0 k7) d17)) =
        d17))).
  Proof.
    pose proof (subst0_shift0_Decls_Tm_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Lemma subst0_shift0_Tm_reflection_ind  :
    (forall (s1 : Tm) ,
      (forall (k7 : Hvl) (s2 : Tm) ,
        ((substTm (weakenTrace X0 k7) s2 (shiftTm (weakenCutofftm C0 k7) s1)) =
        s1))).
  Proof.
    pose proof (subst0_shift0_Decls_Tm_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Definition tsubst0_tshift0_Decls_Tm_reflection_ind := (ind_Decls_Tm (fun (d17 : Decls) =>
    (forall (k7 : Hvl) (S3 : Ty) ,
      ((tsubstDecls (weakenTrace X0 k7) S3 (tshiftDecls (weakenCutoffty C0 k7) d17)) =
      d17))) (fun (s1 : Tm) =>
    (forall (k7 : Hvl) (S3 : Ty) ,
      ((tsubstTm (weakenTrace X0 k7) S3 (tshiftTm (weakenCutoffty C0 k7) s1)) =
      s1))) (fun (k7 : Hvl) (S3 : Ty) =>
    eq_refl) (fun (t : Tm) IHt41 (d : Decls) IHd (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 dcons (IHt41 k7 S3) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty X0 k7 (HS tm H0)) eq_refl eq_refl) (IHd (HS tm k7) S3)))) (fun (x20 : (Index tm)) =>
    (fun (k7 : Hvl) (S3 : Ty) =>
      eq_refl)) (fun (T : Ty) (t : Tm) IHt41 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 abs (let IHT0 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT0 k7 S3)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt41 (HS tm k7) S3)))) (fun (t1 : Tm) IHt41 (t2 : Tm) IHt42 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 app (IHt41 k7 S3) (IHt42 k7 S3))) (fun (t : Tm) IHt41 (k7 : Hvl) (S3 : Ty) =>
    (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt41 (HS ty k7) S3)))) (fun (t : Tm) IHt41 (T : Ty) (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tapp (IHt41 k7 S3) (let IHT0 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT0 k7 S3)))) (fun (d : Decls) IHd (t : Tm) IHt41 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 lett (IHd k7 S3) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bind _ _) (eq_refl H0))) (weakenTrace_append ty X0 k7 (bind d))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k7 (bind d)) eq_refl)) (IHt41 (appendHvl k7 (bind d)) S3))))).
  Lemma tsubst0_tshift0_Decls_reflection_ind  :
    (forall (d17 : Decls) ,
      (forall (k7 : Hvl) (S3 : Ty) ,
        ((tsubstDecls (weakenTrace X0 k7) S3 (tshiftDecls (weakenCutoffty C0 k7) d17)) =
        d17))).
  Proof.
    pose proof (tsubst0_tshift0_Decls_Tm_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Lemma tsubst0_tshift0_Tm_reflection_ind  :
    (forall (s1 : Tm) ,
      (forall (k7 : Hvl) (S3 : Ty) ,
        ((tsubstTm (weakenTrace X0 k7) S3 (tshiftTm (weakenCutoffty C0 k7) s1)) =
        s1))).
  Proof.
    pose proof (tsubst0_tshift0_Decls_Tm_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Definition tsubstTy0_tshiftTy0_reflection (S4 : Ty) : (forall (S3 : Ty) ,
    ((tsubstTy X0 S3 (tshiftTy C0 S4)) =
    S4)) := (tsubst0_tshift0_Ty_reflection_ind S4 H0).
  Definition substDecls0_shiftDecls0_reflection (d17 : Decls) : (forall (s1 : Tm) ,
    ((substDecls X0 s1 (shiftDecls C0 d17)) =
    d17)) := (subst0_shift0_Decls_reflection_ind d17 H0).
  Definition substTm0_shiftTm0_reflection (s2 : Tm) : (forall (s1 : Tm) ,
    ((substTm X0 s1 (shiftTm C0 s2)) =
    s2)) := (subst0_shift0_Tm_reflection_ind s2 H0).
  Definition tsubstDecls0_tshiftDecls0_reflection (d17 : Decls) : (forall (S3 : Ty) ,
    ((tsubstDecls X0 S3 (tshiftDecls C0 d17)) =
    d17)) := (tsubst0_tshift0_Decls_reflection_ind d17 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s1 : Tm) : (forall (S3 : Ty) ,
    ((tsubstTm X0 S3 (tshiftTm C0 s1)) =
    s1)) := (tsubst0_tshift0_Tm_reflection_ind s1 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c1 : (Cutoff tm)) (x : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c1) k) (shiftIndex (weakenCutofftm C0 k) x)) =
        (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c1 k) x)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c1 : (Cutoff ty)) (X : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c1) k) (tshiftIndex (weakenCutoffty C0 k) X)) =
        (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c1 k) X)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Definition tshift_tshift0_Ty_comm_ind := (ind_Ty (fun (S1 : Ty) =>
      (forall (k4 : Hvl) (c6 : (Cutoff ty)) ,
        ((tshiftTy (weakenCutoffty (CS c6) k4) (tshiftTy (weakenCutoffty C0 k4) S1)) =
        (tshiftTy (weakenCutoffty C0 k4) (tshiftTy (weakenCutoffty c6 k4) S1))))) (fun (X8 : (Index ty)) =>
      (fun (k4 : Hvl) (c6 : (Cutoff ty)) =>
        (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k4 c6 X8)))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 tarr (IHT0 k4 c6) (IHT3 k4 c6))) (fun (T : Ty) IHT0 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal tall (IHT0 (HS ty k4) c6)))).
    Definition shift_shift0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d13 : Decls) =>
      (forall (k4 : Hvl) (c6 : (Cutoff tm)) ,
        ((shiftDecls (weakenCutofftm (CS c6) k4) (shiftDecls (weakenCutofftm C0 k4) d13)) =
        (shiftDecls (weakenCutofftm C0 k4) (shiftDecls (weakenCutofftm c6 k4) d13))))) (fun (s0 : Tm) =>
      (forall (k4 : Hvl) (c6 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm (CS c6) k4) (shiftTm (weakenCutofftm C0 k4) s0)) =
        (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c6 k4) s0))))) (fun (k4 : Hvl) (c6 : (Cutoff tm)) =>
      eq_refl) (fun (t : Tm) IHt27 (d : Decls) IHd (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 dcons (IHt27 k4 c6) (IHd (HS tm k4) c6))) (fun (x13 : (Index tm)) =>
      (fun (k4 : Hvl) (c6 : (Cutoff tm)) =>
        (f_equal var (shiftIndex_shiftIndex0_comm_ind k4 c6 x13)))) (fun (T : Ty) (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt27 (HS tm k4) c6))) (fun (t1 : Tm) IHt27 (t2 : Tm) IHt28 (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 app (IHt27 k4 c6) (IHt28 k4 c6))) (fun (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal tabs (IHt27 (HS ty k4) c6))) (fun (t : Tm) IHt27 (T : Ty) (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt27 k4 c6) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 lett (IHd k4 c6) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (stability_shift_bind _ _) (eq_refl H0))) (weakenCutofftm_append (CS c6) k4 (bind d))) (f_equal2 shiftTm (weakenCutofftm_append C0 k4 (bind d)) eq_refl)) (eq_trans (IHt27 (appendHvl k4 (bind d)) c6) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k4 (bind d))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_shift_bind _ _)) (eq_refl H0)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c6 k4 (bind d))) eq_refl))))))).
    Lemma shift_shift0_Decls_comm_ind  :
      (forall (d13 : Decls) ,
        (forall (k4 : Hvl) (c6 : (Cutoff tm)) ,
          ((shiftDecls (weakenCutofftm (CS c6) k4) (shiftDecls (weakenCutofftm C0 k4) d13)) =
          (shiftDecls (weakenCutofftm C0 k4) (shiftDecls (weakenCutofftm c6 k4) d13))))).
    Proof.
      pose proof (shift_shift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma shift_shift0_Tm_comm_ind  :
      (forall (s0 : Tm) ,
        (forall (k4 : Hvl) (c6 : (Cutoff tm)) ,
          ((shiftTm (weakenCutofftm (CS c6) k4) (shiftTm (weakenCutofftm C0 k4) s0)) =
          (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c6 k4) s0))))).
    Proof.
      pose proof (shift_shift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition shift_tshift0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d13 : Decls) =>
      (forall (k4 : Hvl) (c6 : (Cutoff tm)) ,
        ((shiftDecls (weakenCutofftm c6 k4) (tshiftDecls (weakenCutoffty C0 k4) d13)) =
        (tshiftDecls (weakenCutoffty C0 k4) (shiftDecls (weakenCutofftm c6 k4) d13))))) (fun (s0 : Tm) =>
      (forall (k4 : Hvl) (c6 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm c6 k4) (tshiftTm (weakenCutoffty C0 k4) s0)) =
        (tshiftTm (weakenCutoffty C0 k4) (shiftTm (weakenCutofftm c6 k4) s0))))) (fun (k4 : Hvl) (c6 : (Cutoff tm)) =>
      eq_refl) (fun (t : Tm) IHt27 (d : Decls) IHd (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 dcons (IHt27 k4 c6) (IHd (HS tm k4) c6))) (fun (x13 : (Index tm)) =>
      (fun (k4 : Hvl) (c6 : (Cutoff tm)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt27 (HS tm k4) c6))) (fun (t1 : Tm) IHt27 (t2 : Tm) IHt28 (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 app (IHt27 k4 c6) (IHt28 k4 c6))) (fun (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal tabs (IHt27 (HS ty k4) c6))) (fun (t : Tm) IHt27 (T : Ty) (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt27 k4 c6) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff tm)) =>
      (f_equal2 lett (IHd k4 c6) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (stability_tshift_bind _ _) (eq_refl H0))) (weakenCutofftm_append c6 k4 (bind d))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k4 (bind d)) eq_refl)) (eq_trans (IHt27 (appendHvl k4 (bind d)) c6) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k4 (bind d))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_sym (stability_shift_bind _ _)) (eq_refl H0)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c6 k4 (bind d))) eq_refl))))))).
    Lemma shift_tshift0_Decls_comm_ind  :
      (forall (d13 : Decls) ,
        (forall (k4 : Hvl) (c6 : (Cutoff tm)) ,
          ((shiftDecls (weakenCutofftm c6 k4) (tshiftDecls (weakenCutoffty C0 k4) d13)) =
          (tshiftDecls (weakenCutoffty C0 k4) (shiftDecls (weakenCutofftm c6 k4) d13))))).
    Proof.
      pose proof (shift_tshift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma shift_tshift0_Tm_comm_ind  :
      (forall (s0 : Tm) ,
        (forall (k4 : Hvl) (c6 : (Cutoff tm)) ,
          ((shiftTm (weakenCutofftm c6 k4) (tshiftTm (weakenCutoffty C0 k4) s0)) =
          (tshiftTm (weakenCutoffty C0 k4) (shiftTm (weakenCutofftm c6 k4) s0))))).
    Proof.
      pose proof (shift_tshift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_shift0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d13 : Decls) =>
      (forall (k4 : Hvl) (c6 : (Cutoff ty)) ,
        ((tshiftDecls (weakenCutoffty c6 k4) (shiftDecls (weakenCutofftm C0 k4) d13)) =
        (shiftDecls (weakenCutofftm C0 k4) (tshiftDecls (weakenCutoffty c6 k4) d13))))) (fun (s0 : Tm) =>
      (forall (k4 : Hvl) (c6 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty c6 k4) (shiftTm (weakenCutofftm C0 k4) s0)) =
        (shiftTm (weakenCutofftm C0 k4) (tshiftTm (weakenCutoffty c6 k4) s0))))) (fun (k4 : Hvl) (c6 : (Cutoff ty)) =>
      eq_refl) (fun (t : Tm) IHt27 (d : Decls) IHd (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 dcons (IHt27 k4 c6) (IHd (HS tm k4) c6))) (fun (x13 : (Index tm)) =>
      (fun (k4 : Hvl) (c6 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 abs eq_refl (IHt27 (HS tm k4) c6))) (fun (t1 : Tm) IHt27 (t2 : Tm) IHt28 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 app (IHt27 k4 c6) (IHt28 k4 c6))) (fun (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal tabs (IHt27 (HS ty k4) c6))) (fun (t : Tm) IHt27 (T : Ty) (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt27 k4 c6) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 lett (IHd k4 c6) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (stability_shift_bind _ _) (eq_refl H0))) (weakenCutoffty_append c6 k4 (bind d))) (f_equal2 shiftTm (weakenCutofftm_append C0 k4 (bind d)) eq_refl)) (eq_trans (IHt27 (appendHvl k4 (bind d)) c6) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k4 (bind d))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bind _ _)) (eq_refl H0)))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c6 k4 (bind d))) eq_refl))))))).
    Lemma tshift_shift0_Decls_comm_ind  :
      (forall (d13 : Decls) ,
        (forall (k4 : Hvl) (c6 : (Cutoff ty)) ,
          ((tshiftDecls (weakenCutoffty c6 k4) (shiftDecls (weakenCutofftm C0 k4) d13)) =
          (shiftDecls (weakenCutofftm C0 k4) (tshiftDecls (weakenCutoffty c6 k4) d13))))).
    Proof.
      pose proof (tshift_shift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_shift0_Tm_comm_ind  :
      (forall (s0 : Tm) ,
        (forall (k4 : Hvl) (c6 : (Cutoff ty)) ,
          ((tshiftTm (weakenCutoffty c6 k4) (shiftTm (weakenCutofftm C0 k4) s0)) =
          (shiftTm (weakenCutofftm C0 k4) (tshiftTm (weakenCutoffty c6 k4) s0))))).
    Proof.
      pose proof (tshift_shift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_tshift0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d13 : Decls) =>
      (forall (k4 : Hvl) (c6 : (Cutoff ty)) ,
        ((tshiftDecls (weakenCutoffty (CS c6) k4) (tshiftDecls (weakenCutoffty C0 k4) d13)) =
        (tshiftDecls (weakenCutoffty C0 k4) (tshiftDecls (weakenCutoffty c6 k4) d13))))) (fun (s0 : Tm) =>
      (forall (k4 : Hvl) (c6 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty (CS c6) k4) (tshiftTm (weakenCutoffty C0 k4) s0)) =
        (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c6 k4) s0))))) (fun (k4 : Hvl) (c6 : (Cutoff ty)) =>
      eq_refl) (fun (t : Tm) IHt27 (d : Decls) IHd (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 dcons (IHt27 k4 c6) (IHd (HS tm k4) c6))) (fun (x13 : (Index tm)) =>
      (fun (k4 : Hvl) (c6 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 abs (let IHT0 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT0 k4 c6)) (IHt27 (HS tm k4) c6))) (fun (t1 : Tm) IHt27 (t2 : Tm) IHt28 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 app (IHt27 k4 c6) (IHt28 k4 c6))) (fun (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal tabs (IHt27 (HS ty k4) c6))) (fun (t : Tm) IHt27 (T : Ty) (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt27 k4 c6) (let IHT0 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT0 k4 c6)))) (fun (d : Decls) IHd (t : Tm) IHt27 (k4 : Hvl) (c6 : (Cutoff ty)) =>
      (f_equal2 lett (IHd k4 c6) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (stability_tshift_bind _ _) (eq_refl H0))) (weakenCutoffty_append (CS c6) k4 (bind d))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k4 (bind d)) eq_refl)) (eq_trans (IHt27 (appendHvl k4 (bind d)) c6) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k4 (bind d))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bind _ _)) (eq_refl H0)))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c6 k4 (bind d))) eq_refl))))))).
    Lemma tshift_tshift0_Decls_comm_ind  :
      (forall (d13 : Decls) ,
        (forall (k4 : Hvl) (c6 : (Cutoff ty)) ,
          ((tshiftDecls (weakenCutoffty (CS c6) k4) (tshiftDecls (weakenCutoffty C0 k4) d13)) =
          (tshiftDecls (weakenCutoffty C0 k4) (tshiftDecls (weakenCutoffty c6 k4) d13))))).
    Proof.
      pose proof (tshift_tshift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_tshift0_Tm_comm_ind  :
      (forall (s0 : Tm) ,
        (forall (k4 : Hvl) (c6 : (Cutoff ty)) ,
          ((tshiftTm (weakenCutoffty (CS c6) k4) (tshiftTm (weakenCutoffty C0 k4) s0)) =
          (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c6 k4) s0))))).
    Proof.
      pose proof (tshift_tshift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S1 : Ty) : (forall (c6 : (Cutoff ty)) ,
      ((tshiftTy (CS c6) (tshiftTy C0 S1)) =
      (tshiftTy C0 (tshiftTy c6 S1)))) := (tshift_tshift0_Ty_comm_ind S1 H0).
    Definition shift_shift0_Decls_comm (d13 : Decls) : (forall (c6 : (Cutoff tm)) ,
      ((shiftDecls (CS c6) (shiftDecls C0 d13)) =
      (shiftDecls C0 (shiftDecls c6 d13)))) := (shift_shift0_Decls_comm_ind d13 H0).
    Definition shift_shift0_Tm_comm (s0 : Tm) : (forall (c6 : (Cutoff tm)) ,
      ((shiftTm (CS c6) (shiftTm C0 s0)) =
      (shiftTm C0 (shiftTm c6 s0)))) := (shift_shift0_Tm_comm_ind s0 H0).
    Definition shift_tshift0_Decls_comm (d13 : Decls) : (forall (c6 : (Cutoff tm)) ,
      ((shiftDecls c6 (tshiftDecls C0 d13)) =
      (tshiftDecls C0 (shiftDecls c6 d13)))) := (shift_tshift0_Decls_comm_ind d13 H0).
    Definition shift_tshift0_Tm_comm (s0 : Tm) : (forall (c6 : (Cutoff tm)) ,
      ((shiftTm c6 (tshiftTm C0 s0)) =
      (tshiftTm C0 (shiftTm c6 s0)))) := (shift_tshift0_Tm_comm_ind s0 H0).
    Definition tshift_shift0_Decls_comm (d13 : Decls) : (forall (c6 : (Cutoff ty)) ,
      ((tshiftDecls c6 (shiftDecls C0 d13)) =
      (shiftDecls C0 (tshiftDecls c6 d13)))) := (tshift_shift0_Decls_comm_ind d13 H0).
    Definition tshift_shift0_Tm_comm (s0 : Tm) : (forall (c6 : (Cutoff ty)) ,
      ((tshiftTm c6 (shiftTm C0 s0)) =
      (shiftTm C0 (tshiftTm c6 s0)))) := (tshift_shift0_Tm_comm_ind s0 H0).
    Definition tshift_tshift0_Decls_comm (d13 : Decls) : (forall (c6 : (Cutoff ty)) ,
      ((tshiftDecls (CS c6) (tshiftDecls C0 d13)) =
      (tshiftDecls C0 (tshiftDecls c6 d13)))) := (tshift_tshift0_Decls_comm_ind d13 H0).
    Definition tshift_tshift0_Tm_comm (s0 : Tm) : (forall (c6 : (Cutoff ty)) ,
      ((tshiftTm (CS c6) (tshiftTm C0 s0)) =
      (tshiftTm C0 (tshiftTm c6 s0)))) := (tshift_tshift0_Tm_comm_ind s0 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Decls_comm shift_tshift0_Decls_comm tshift_shift0_Decls_comm tshift_tshift0_Decls_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite shift_shift0_Decls_comm shift_tshift0_Decls_comm tshift_shift0_Decls_comm tshift_tshift0_Decls_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k61 : Hvl) (c11 : (Cutoff ty)) (S40 : Ty) ,
      ((weakenTy (tshiftTy c11 S40) k61) =
      (tshiftTy (weakenCutoffty c11 k61) (weakenTy S40 k61)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenDecls_shiftDecls  :
    (forall (k61 : Hvl) (c11 : (Cutoff tm)) (d88 : Decls) ,
      ((weakenDecls (shiftDecls c11 d88) k61) =
      (shiftDecls (weakenCutofftm c11 k61) (weakenDecls d88 k61)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k61 : Hvl) (c11 : (Cutoff tm)) (s21 : Tm) ,
      ((weakenTm (shiftTm c11 s21) k61) =
      (shiftTm (weakenCutofftm c11 k61) (weakenTm s21 k61)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenDecls_tshiftDecls  :
    (forall (k61 : Hvl) (c11 : (Cutoff ty)) (d88 : Decls) ,
      ((weakenDecls (tshiftDecls c11 d88) k61) =
      (tshiftDecls (weakenCutoffty c11 k61) (weakenDecls d88 k61)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k61 : Hvl) (c11 : (Cutoff ty)) (s21 : Tm) ,
      ((weakenTm (tshiftTm c11 s21) k61) =
      (tshiftTm (weakenCutoffty c11 k61) (weakenTm s21 k61)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c6 : (Cutoff tm)) (s1 : Tm) :
      (forall (k7 : Hvl) (x20 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c6 k7) (substIndex (weakenTrace X0 k7) s1 x20)) =
        (substIndex (weakenTrace X0 k7) (shiftTm c6 s1) (shiftIndex (weakenCutofftm (CS c6) k7) x20)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c6 : (Cutoff ty)) (s1 : Tm) :
      (forall (k7 : Hvl) (x20 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c6 k7) (substIndex (weakenTrace X0 k7) s1 x20)) =
        (substIndex (weakenTrace X0 k7) (tshiftTm c6 s1) x20))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c6 : (Cutoff ty)) (S3 : Ty) :
      (forall (k7 : Hvl) (X14 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c6 k7) (tsubstIndex (weakenTrace X0 k7) S3 X14)) =
        (tsubstIndex (weakenTrace X0 k7) (tshiftTy c6 S3) (tshiftIndex (weakenCutoffty (CS c6) k7) X14)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Definition tshift_tsubst0_Ty_comm_ind := (ind_Ty (fun (S6 : Ty) =>
      (forall (k12 : Hvl) (c11 : (Cutoff ty)) (S7 : Ty) ,
        ((tshiftTy (weakenCutoffty c11 k12) (tsubstTy (weakenTrace X0 k12) S7 S6)) =
        (tsubstTy (weakenTrace X0 k12) (tshiftTy c11 S7) (tshiftTy (weakenCutoffty (CS c11) k12) S6))))) (fun (X21 : (Index ty)) =>
      (fun (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
        (tshiftTy_tsubstIndex0_comm_ind c11 S6 k12 X21))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tarr (IHT0 k12 c11 S6) (IHT3 k12 c11 S6))) (fun (T : Ty) IHT0 (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal tall (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT0 (HS ty k12) c11 S6) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl)))))).
    Definition shift_subst0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d25 : Decls) =>
      (forall (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) ,
        ((shiftDecls (weakenCutofftm c11 k12) (substDecls (weakenTrace X0 k12) s3 d25)) =
        (substDecls (weakenTrace X0 k12) (shiftTm c11 s3) (shiftDecls (weakenCutofftm (CS c11) k12) d25))))) (fun (s3 : Tm) =>
      (forall (k12 : Hvl) (c11 : (Cutoff tm)) (s4 : Tm) ,
        ((shiftTm (weakenCutofftm c11 k12) (substTm (weakenTrace X0 k12) s4 s3)) =
        (substTm (weakenTrace X0 k12) (shiftTm c11 s4) (shiftTm (weakenCutofftm (CS c11) k12) s3))))) (fun (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) =>
      eq_refl) (fun (t : Tm) IHt69 (d : Decls) IHd (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) =>
      (f_equal2 dcons (IHt69 k12 c11 s3) (eq_trans (f_equal2 shiftDecls eq_refl (f_equal3 substDecls (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHd (HS tm k12) c11 s3) (f_equal3 substDecls (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (x36 : (Index tm)) =>
      (fun (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) =>
        (shiftTm_substIndex0_comm_ind c11 s3 k12 x36))) (fun (T : Ty) (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt69 (HS tm k12) c11 s3) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) =>
      (f_equal2 app (IHt69 k12 c11 s3) (IHt70 k12 c11 s3))) (fun (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) =>
      (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt69 (HS ty k12) c11 s3) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt69 (T : Ty) (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) =>
      (f_equal2 tapp (IHt69 k12 c11 s3) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) =>
      (f_equal2 lett (IHd k12 c11 s3) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (stability_subst_bind _ _ _) (eq_refl H0))) (weakenCutofftm_append c11 k12 (bind d))) (f_equal3 substTm (weakenTrace_append tm X0 k12 (bind d)) eq_refl eq_refl)) (eq_trans (IHt69 (appendHvl k12 (bind d)) c11 s3) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k12 (bind d))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_shift_bind _ _)) (eq_refl H0)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c11) k12 (bind d))) eq_refl))))))).
    Lemma shift_subst0_Decls_comm_ind  :
      (forall (d25 : Decls) ,
        (forall (k12 : Hvl) (c11 : (Cutoff tm)) (s3 : Tm) ,
          ((shiftDecls (weakenCutofftm c11 k12) (substDecls (weakenTrace X0 k12) s3 d25)) =
          (substDecls (weakenTrace X0 k12) (shiftTm c11 s3) (shiftDecls (weakenCutofftm (CS c11) k12) d25))))).
    Proof.
      pose proof (shift_subst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma shift_subst0_Tm_comm_ind  :
      (forall (s3 : Tm) ,
        (forall (k12 : Hvl) (c11 : (Cutoff tm)) (s4 : Tm) ,
          ((shiftTm (weakenCutofftm c11 k12) (substTm (weakenTrace X0 k12) s4 s3)) =
          (substTm (weakenTrace X0 k12) (shiftTm c11 s4) (shiftTm (weakenCutofftm (CS c11) k12) s3))))).
    Proof.
      pose proof (shift_subst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition shift_tsubst0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d25 : Decls) =>
      (forall (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) ,
        ((shiftDecls (weakenCutofftm c11 k12) (tsubstDecls (weakenTrace X0 k12) S6 d25)) =
        (tsubstDecls (weakenTrace X0 k12) S6 (shiftDecls (weakenCutofftm c11 k12) d25))))) (fun (s3 : Tm) =>
      (forall (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) ,
        ((shiftTm (weakenCutofftm c11 k12) (tsubstTm (weakenTrace X0 k12) S6 s3)) =
        (tsubstTm (weakenTrace X0 k12) S6 (shiftTm (weakenCutofftm c11 k12) s3))))) (fun (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) =>
      eq_refl) (fun (t : Tm) IHt69 (d : Decls) IHd (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 dcons (IHt69 k12 c11 S6) (eq_trans (f_equal2 shiftDecls eq_refl (f_equal3 tsubstDecls (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHd (HS tm k12) c11 S6) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (x36 : (Index tm)) =>
      (fun (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt69 (HS tm k12) c11 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 app (IHt69 k12 c11 S6) (IHt70 k12 c11 S6))) (fun (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt69 (HS ty k12) c11 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt69 (T : Ty) (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 tapp (IHt69 k12 c11 S6) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 lett (IHd k12 c11 S6) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0))) (weakenCutofftm_append c11 k12 (bind d))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (bind d)) eq_refl eq_refl)) (eq_trans (IHt69 (appendHvl k12 (bind d)) c11 S6) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k12 (bind d))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_shift_bind _ _)) (eq_refl H0)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c11 k12 (bind d))) eq_refl))))))).
    Lemma shift_tsubst0_Decls_comm_ind  :
      (forall (d25 : Decls) ,
        (forall (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) ,
          ((shiftDecls (weakenCutofftm c11 k12) (tsubstDecls (weakenTrace X0 k12) S6 d25)) =
          (tsubstDecls (weakenTrace X0 k12) S6 (shiftDecls (weakenCutofftm c11 k12) d25))))).
    Proof.
      pose proof (shift_tsubst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma shift_tsubst0_Tm_comm_ind  :
      (forall (s3 : Tm) ,
        (forall (k12 : Hvl) (c11 : (Cutoff tm)) (S6 : Ty) ,
          ((shiftTm (weakenCutofftm c11 k12) (tsubstTm (weakenTrace X0 k12) S6 s3)) =
          (tsubstTm (weakenTrace X0 k12) S6 (shiftTm (weakenCutofftm c11 k12) s3))))).
    Proof.
      pose proof (shift_tsubst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_subst0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d25 : Decls) =>
      (forall (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) ,
        ((tshiftDecls (weakenCutoffty c11 k12) (substDecls (weakenTrace X0 k12) s3 d25)) =
        (substDecls (weakenTrace X0 k12) (tshiftTm c11 s3) (tshiftDecls (weakenCutoffty c11 k12) d25))))) (fun (s3 : Tm) =>
      (forall (k12 : Hvl) (c11 : (Cutoff ty)) (s4 : Tm) ,
        ((tshiftTm (weakenCutoffty c11 k12) (substTm (weakenTrace X0 k12) s4 s3)) =
        (substTm (weakenTrace X0 k12) (tshiftTm c11 s4) (tshiftTm (weakenCutoffty c11 k12) s3))))) (fun (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) =>
      eq_refl) (fun (t : Tm) IHt69 (d : Decls) IHd (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) =>
      (f_equal2 dcons (IHt69 k12 c11 s3) (eq_trans (f_equal2 tshiftDecls eq_refl (f_equal3 substDecls (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHd (HS tm k12) c11 s3) (f_equal3 substDecls (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (x36 : (Index tm)) =>
      (fun (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) =>
        (tshiftTm_substIndex0_comm_ind c11 s3 k12 x36))) (fun (T : Ty) (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt69 (HS tm k12) c11 s3) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) =>
      (f_equal2 app (IHt69 k12 c11 s3) (IHt70 k12 c11 s3))) (fun (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) =>
      (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt69 (HS ty k12) c11 s3) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt69 (T : Ty) (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) =>
      (f_equal2 tapp (IHt69 k12 c11 s3) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) =>
      (f_equal2 lett (IHd k12 c11 s3) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (stability_subst_bind _ _ _) (eq_refl H0))) (weakenCutoffty_append c11 k12 (bind d))) (f_equal3 substTm (weakenTrace_append tm X0 k12 (bind d)) eq_refl eq_refl)) (eq_trans (IHt69 (appendHvl k12 (bind d)) c11 s3) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k12 (bind d))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bind _ _)) (eq_refl H0)))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c11 k12 (bind d))) eq_refl))))))).
    Lemma tshift_subst0_Decls_comm_ind  :
      (forall (d25 : Decls) ,
        (forall (k12 : Hvl) (c11 : (Cutoff ty)) (s3 : Tm) ,
          ((tshiftDecls (weakenCutoffty c11 k12) (substDecls (weakenTrace X0 k12) s3 d25)) =
          (substDecls (weakenTrace X0 k12) (tshiftTm c11 s3) (tshiftDecls (weakenCutoffty c11 k12) d25))))).
    Proof.
      pose proof (tshift_subst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_subst0_Tm_comm_ind  :
      (forall (s3 : Tm) ,
        (forall (k12 : Hvl) (c11 : (Cutoff ty)) (s4 : Tm) ,
          ((tshiftTm (weakenCutoffty c11 k12) (substTm (weakenTrace X0 k12) s4 s3)) =
          (substTm (weakenTrace X0 k12) (tshiftTm c11 s4) (tshiftTm (weakenCutoffty c11 k12) s3))))).
    Proof.
      pose proof (tshift_subst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_tsubst0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d25 : Decls) =>
      (forall (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) ,
        ((tshiftDecls (weakenCutoffty c11 k12) (tsubstDecls (weakenTrace X0 k12) S6 d25)) =
        (tsubstDecls (weakenTrace X0 k12) (tshiftTy c11 S6) (tshiftDecls (weakenCutoffty (CS c11) k12) d25))))) (fun (s3 : Tm) =>
      (forall (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) ,
        ((tshiftTm (weakenCutoffty c11 k12) (tsubstTm (weakenTrace X0 k12) S6 s3)) =
        (tsubstTm (weakenTrace X0 k12) (tshiftTy c11 S6) (tshiftTm (weakenCutoffty (CS c11) k12) s3))))) (fun (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
      eq_refl) (fun (t : Tm) IHt69 (d : Decls) IHd (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 dcons (IHt69 k12 c11 S6) (eq_trans (f_equal2 tshiftDecls eq_refl (f_equal3 tsubstDecls (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHd (HS tm k12) c11 S6) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (x36 : (Index tm)) =>
      (fun (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 abs (let IHT0 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT0 k12 c11 S6)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt69 (HS tm k12) c11 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 app (IHt69 k12 c11 S6) (IHt70 k12 c11 S6))) (fun (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt69 (HS ty k12) c11 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt69 (T : Ty) (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tapp (IHt69 k12 c11 S6) (let IHT0 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT0 k12 c11 S6)))) (fun (d : Decls) IHd (t : Tm) IHt69 (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 lett (IHd k12 c11 S6) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0))) (weakenCutoffty_append c11 k12 (bind d))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (bind d)) eq_refl eq_refl)) (eq_trans (IHt69 (appendHvl k12 (bind d)) c11 S6) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k12 (bind d))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bind _ _)) (eq_refl H0)))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append (CS c11) k12 (bind d))) eq_refl))))))).
    Lemma tshift_tsubst0_Decls_comm_ind  :
      (forall (d25 : Decls) ,
        (forall (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) ,
          ((tshiftDecls (weakenCutoffty c11 k12) (tsubstDecls (weakenTrace X0 k12) S6 d25)) =
          (tsubstDecls (weakenTrace X0 k12) (tshiftTy c11 S6) (tshiftDecls (weakenCutoffty (CS c11) k12) d25))))).
    Proof.
      pose proof (tshift_tsubst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_tsubst0_Tm_comm_ind  :
      (forall (s3 : Tm) ,
        (forall (k12 : Hvl) (c11 : (Cutoff ty)) (S6 : Ty) ,
          ((tshiftTm (weakenCutoffty c11 k12) (tsubstTm (weakenTrace X0 k12) S6 s3)) =
          (tsubstTm (weakenTrace X0 k12) (tshiftTy c11 S6) (tshiftTm (weakenCutoffty (CS c11) k12) s3))))).
    Proof.
      pose proof (tshift_tsubst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S7 : Ty) : (forall (c11 : (Cutoff ty)) (S6 : Ty) ,
      ((tshiftTy c11 (tsubstTy X0 S6 S7)) =
      (tsubstTy X0 (tshiftTy c11 S6) (tshiftTy (CS c11) S7)))) := (tshift_tsubst0_Ty_comm_ind S7 H0).
    Definition shiftDecls_substDecls0_comm (d25 : Decls) : (forall (c11 : (Cutoff tm)) (s3 : Tm) ,
      ((shiftDecls c11 (substDecls X0 s3 d25)) =
      (substDecls X0 (shiftTm c11 s3) (shiftDecls (CS c11) d25)))) := (shift_subst0_Decls_comm_ind d25 H0).
    Definition shiftTm_substTm0_comm (s4 : Tm) : (forall (c11 : (Cutoff tm)) (s3 : Tm) ,
      ((shiftTm c11 (substTm X0 s3 s4)) =
      (substTm X0 (shiftTm c11 s3) (shiftTm (CS c11) s4)))) := (shift_subst0_Tm_comm_ind s4 H0).
    Definition shiftDecls_tsubstDecls0_comm (d25 : Decls) : (forall (c11 : (Cutoff tm)) (S6 : Ty) ,
      ((shiftDecls c11 (tsubstDecls X0 S6 d25)) =
      (tsubstDecls X0 S6 (shiftDecls c11 d25)))) := (shift_tsubst0_Decls_comm_ind d25 H0).
    Definition shiftTm_tsubstTm0_comm (s3 : Tm) : (forall (c11 : (Cutoff tm)) (S6 : Ty) ,
      ((shiftTm c11 (tsubstTm X0 S6 s3)) =
      (tsubstTm X0 S6 (shiftTm c11 s3)))) := (shift_tsubst0_Tm_comm_ind s3 H0).
    Definition tshiftDecls_substDecls0_comm (d25 : Decls) : (forall (c11 : (Cutoff ty)) (s3 : Tm) ,
      ((tshiftDecls c11 (substDecls X0 s3 d25)) =
      (substDecls X0 (tshiftTm c11 s3) (tshiftDecls c11 d25)))) := (tshift_subst0_Decls_comm_ind d25 H0).
    Definition tshiftTm_substTm0_comm (s4 : Tm) : (forall (c11 : (Cutoff ty)) (s3 : Tm) ,
      ((tshiftTm c11 (substTm X0 s3 s4)) =
      (substTm X0 (tshiftTm c11 s3) (tshiftTm c11 s4)))) := (tshift_subst0_Tm_comm_ind s4 H0).
    Definition tshiftDecls_tsubstDecls0_comm (d25 : Decls) : (forall (c11 : (Cutoff ty)) (S6 : Ty) ,
      ((tshiftDecls c11 (tsubstDecls X0 S6 d25)) =
      (tsubstDecls X0 (tshiftTy c11 S6) (tshiftDecls (CS c11) d25)))) := (tshift_tsubst0_Decls_comm_ind d25 H0).
    Definition tshiftTm_tsubstTm0_comm (s3 : Tm) : (forall (c11 : (Cutoff ty)) (S6 : Ty) ,
      ((tshiftTm c11 (tsubstTm X0 S6 s3)) =
      (tsubstTm X0 (tshiftTy c11 S6) (tshiftTm (CS c11) s3)))) := (tshift_tsubst0_Tm_comm_ind s3 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d25 : (Trace tm)) (s3 : Tm) :
      (forall (k12 : Hvl) (x36 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d25) k12) s3 (shiftIndex (weakenCutofftm C0 k12) x36)) =
        (shiftTm (weakenCutofftm C0 k12) (substIndex (weakenTrace d25 k12) s3 x36)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d25 : (Trace tm)) (s3 : Tm) :
      (forall (k12 : Hvl) (x36 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d25) k12) s3 x36) =
        (tshiftTm (weakenCutoffty C0 k12) (substIndex (weakenTrace d25 k12) s3 x36)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d25 : (Trace ty)) (S6 : Ty) :
      (forall (k12 : Hvl) (X21 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d25) k12) S6 X21) =
        (tsubstIndex (weakenTrace d25 k12) S6 X21))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d25 : (Trace ty)) (S6 : Ty) :
      (forall (k12 : Hvl) (X21 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d25) k12) S6 (tshiftIndex (weakenCutoffty C0 k12) X21)) =
        (tshiftTy (weakenCutoffty C0 k12) (tsubstIndex (weakenTrace d25 k12) S6 X21)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Definition tsubst_tshift0_Ty_comm_ind := (ind_Ty (fun (S25 : Ty) =>
      (forall (k47 : Hvl) (d68 : (Trace ty)) (S26 : Ty) ,
        ((tsubstTy (weakenTrace (XS ty d68) k47) S26 (tshiftTy (weakenCutoffty C0 k47) S25)) =
        (tshiftTy (weakenCutoffty C0 k47) (tsubstTy (weakenTrace d68 k47) S26 S25))))) (fun (X28 : (Index ty)) =>
      (fun (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
        (tsubstIndex_tshiftTy0_comm_ind d68 S25 k47 X28))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 tarr (IHT0 k47 d68 S25) (IHT3 k47 d68 S25))) (fun (T : Ty) IHT0 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d68) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT0 (HS ty k47) d68 S25) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d68 k47 (HS ty H0))) eq_refl eq_refl))))))).
    Definition subst_shift0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d68 : Decls) =>
      (forall (k47 : Hvl) (d69 : (Trace tm)) (s19 : Tm) ,
        ((substDecls (weakenTrace (XS tm d69) k47) s19 (shiftDecls (weakenCutofftm C0 k47) d68)) =
        (shiftDecls (weakenCutofftm C0 k47) (substDecls (weakenTrace d69 k47) s19 d68))))) (fun (s19 : Tm) =>
      (forall (k47 : Hvl) (d68 : (Trace tm)) (s20 : Tm) ,
        ((substTm (weakenTrace (XS tm d68) k47) s20 (shiftTm (weakenCutofftm C0 k47) s19)) =
        (shiftTm (weakenCutofftm C0 k47) (substTm (weakenTrace d68 k47) s20 s19))))) (fun (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      eq_refl) (fun (t : Tm) IHt97 (d : Decls) IHd (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 dcons (IHt97 k47 d68 s19) (eq_trans (f_equal3 substDecls (weakenTrace_append tm (XS tm d68) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHd (HS tm k47) d68 s19) (f_equal2 shiftDecls eq_refl (f_equal3 substDecls (eq_sym (weakenTrace_append tm d68 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (x52 : (Index tm)) =>
      (fun (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
        (substIndex_shiftTm0_comm_ind d68 s19 k47 x52))) (fun (T : Ty) (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d68) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt97 (HS tm k47) d68 s19) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d68 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt97 (t2 : Tm) IHt98 (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 app (IHt97 k47 d68 s19) (IHt98 k47 d68 s19))) (fun (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d68) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt97 (HS ty k47) d68 s19) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d68 k47 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt97 (T : Ty) (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 tapp (IHt97 k47 d68 s19) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 lett (IHd k47 d68 s19) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_shift_bind _ _) (eq_refl H0))) (weakenTrace_append tm (XS tm d68) k47 (bind d))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k47 (bind d)) eq_refl)) (eq_trans (IHt97 (appendHvl k47 (bind d)) d68 s19) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k47 (bind d))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d68 k47 (bind d))) eq_refl eq_refl))))))).
    Lemma subst_shift0_Decls_comm_ind  :
      (forall (d68 : Decls) ,
        (forall (k47 : Hvl) (d69 : (Trace tm)) (s19 : Tm) ,
          ((substDecls (weakenTrace (XS tm d69) k47) s19 (shiftDecls (weakenCutofftm C0 k47) d68)) =
          (shiftDecls (weakenCutofftm C0 k47) (substDecls (weakenTrace d69 k47) s19 d68))))).
    Proof.
      pose proof (subst_shift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma subst_shift0_Tm_comm_ind  :
      (forall (s19 : Tm) ,
        (forall (k47 : Hvl) (d69 : (Trace tm)) (s20 : Tm) ,
          ((substTm (weakenTrace (XS tm d69) k47) s20 (shiftTm (weakenCutofftm C0 k47) s19)) =
          (shiftTm (weakenCutofftm C0 k47) (substTm (weakenTrace d69 k47) s20 s19))))).
    Proof.
      pose proof (subst_shift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition subst_tshift0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d68 : Decls) =>
      (forall (k47 : Hvl) (d69 : (Trace tm)) (s19 : Tm) ,
        ((substDecls (weakenTrace (XS ty d69) k47) s19 (tshiftDecls (weakenCutoffty C0 k47) d68)) =
        (tshiftDecls (weakenCutoffty C0 k47) (substDecls (weakenTrace d69 k47) s19 d68))))) (fun (s19 : Tm) =>
      (forall (k47 : Hvl) (d68 : (Trace tm)) (s20 : Tm) ,
        ((substTm (weakenTrace (XS ty d68) k47) s20 (tshiftTm (weakenCutoffty C0 k47) s19)) =
        (tshiftTm (weakenCutoffty C0 k47) (substTm (weakenTrace d68 k47) s20 s19))))) (fun (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      eq_refl) (fun (t : Tm) IHt97 (d : Decls) IHd (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 dcons (IHt97 k47 d68 s19) (eq_trans (f_equal3 substDecls (weakenTrace_append tm (XS ty d68) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHd (HS tm k47) d68 s19) (f_equal2 tshiftDecls eq_refl (f_equal3 substDecls (eq_sym (weakenTrace_append tm d68 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (x52 : (Index tm)) =>
      (fun (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
        (substIndex_tshiftTm0_comm_ind d68 s19 k47 x52))) (fun (T : Ty) (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d68) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt97 (HS tm k47) d68 s19) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d68 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt97 (t2 : Tm) IHt98 (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 app (IHt97 k47 d68 s19) (IHt98 k47 d68 s19))) (fun (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d68) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt97 (HS ty k47) d68 s19) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d68 k47 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt97 (T : Ty) (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 tapp (IHt97 k47 d68 s19) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace tm)) (s19 : Tm) =>
      (f_equal2 lett (IHd k47 d68 s19) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bind _ _) (eq_refl H0))) (weakenTrace_append tm (XS ty d68) k47 (bind d))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k47 (bind d)) eq_refl)) (eq_trans (IHt97 (appendHvl k47 (bind d)) d68 s19) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k47 (bind d))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d68 k47 (bind d))) eq_refl eq_refl))))))).
    Lemma subst_tshift0_Decls_comm_ind  :
      (forall (d68 : Decls) ,
        (forall (k47 : Hvl) (d69 : (Trace tm)) (s19 : Tm) ,
          ((substDecls (weakenTrace (XS ty d69) k47) s19 (tshiftDecls (weakenCutoffty C0 k47) d68)) =
          (tshiftDecls (weakenCutoffty C0 k47) (substDecls (weakenTrace d69 k47) s19 d68))))).
    Proof.
      pose proof (subst_tshift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma subst_tshift0_Tm_comm_ind  :
      (forall (s19 : Tm) ,
        (forall (k47 : Hvl) (d69 : (Trace tm)) (s20 : Tm) ,
          ((substTm (weakenTrace (XS ty d69) k47) s20 (tshiftTm (weakenCutoffty C0 k47) s19)) =
          (tshiftTm (weakenCutoffty C0 k47) (substTm (weakenTrace d69 k47) s20 s19))))).
    Proof.
      pose proof (subst_tshift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_shift0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d68 : Decls) =>
      (forall (k47 : Hvl) (d69 : (Trace ty)) (S25 : Ty) ,
        ((tsubstDecls (weakenTrace d69 k47) S25 (shiftDecls (weakenCutofftm C0 k47) d68)) =
        (shiftDecls (weakenCutofftm C0 k47) (tsubstDecls (weakenTrace d69 k47) S25 d68))))) (fun (s19 : Tm) =>
      (forall (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) ,
        ((tsubstTm (weakenTrace d68 k47) S25 (shiftTm (weakenCutofftm C0 k47) s19)) =
        (shiftTm (weakenCutofftm C0 k47) (tsubstTm (weakenTrace d68 k47) S25 s19))))) (fun (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      eq_refl) (fun (t : Tm) IHt97 (d : Decls) IHd (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 dcons (IHt97 k47 d68 S25) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty d68 k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHd (HS tm k47) d68 S25) (f_equal2 shiftDecls eq_refl (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty d68 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (x52 : (Index tm)) =>
      (fun (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d68 k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt97 (HS tm k47) d68 S25) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d68 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt97 (t2 : Tm) IHt98 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 app (IHt97 k47 d68 S25) (IHt98 k47 d68 S25))) (fun (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d68 k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt97 (HS ty k47) d68 S25) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d68 k47 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt97 (T : Ty) (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 tapp (IHt97 k47 d68 S25) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 lett (IHd k47 d68 S25) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_shift_bind _ _) (eq_refl H0))) (weakenTrace_append ty d68 k47 (bind d))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k47 (bind d)) eq_refl)) (eq_trans (IHt97 (appendHvl k47 (bind d)) d68 S25) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k47 (bind d))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0)))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d68 k47 (bind d))) eq_refl eq_refl))))))).
    Lemma tsubst_shift0_Decls_comm_ind  :
      (forall (d68 : Decls) ,
        (forall (k47 : Hvl) (d69 : (Trace ty)) (S25 : Ty) ,
          ((tsubstDecls (weakenTrace d69 k47) S25 (shiftDecls (weakenCutofftm C0 k47) d68)) =
          (shiftDecls (weakenCutofftm C0 k47) (tsubstDecls (weakenTrace d69 k47) S25 d68))))).
    Proof.
      pose proof (tsubst_shift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_shift0_Tm_comm_ind  :
      (forall (s19 : Tm) ,
        (forall (k47 : Hvl) (d69 : (Trace ty)) (S25 : Ty) ,
          ((tsubstTm (weakenTrace d69 k47) S25 (shiftTm (weakenCutofftm C0 k47) s19)) =
          (shiftTm (weakenCutofftm C0 k47) (tsubstTm (weakenTrace d69 k47) S25 s19))))).
    Proof.
      pose proof (tsubst_shift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_tshift0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d68 : Decls) =>
      (forall (k47 : Hvl) (d69 : (Trace ty)) (S25 : Ty) ,
        ((tsubstDecls (weakenTrace (XS ty d69) k47) S25 (tshiftDecls (weakenCutoffty C0 k47) d68)) =
        (tshiftDecls (weakenCutoffty C0 k47) (tsubstDecls (weakenTrace d69 k47) S25 d68))))) (fun (s19 : Tm) =>
      (forall (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) ,
        ((tsubstTm (weakenTrace (XS ty d68) k47) S25 (tshiftTm (weakenCutoffty C0 k47) s19)) =
        (tshiftTm (weakenCutoffty C0 k47) (tsubstTm (weakenTrace d68 k47) S25 s19))))) (fun (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      eq_refl) (fun (t : Tm) IHt97 (d : Decls) IHd (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 dcons (IHt97 k47 d68 S25) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty (XS ty d68) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHd (HS tm k47) d68 S25) (f_equal2 tshiftDecls eq_refl (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty d68 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (x52 : (Index tm)) =>
      (fun (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 abs (let IHT0 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT0 k47 d68 S25)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d68) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt97 (HS tm k47) d68 S25) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d68 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt97 (t2 : Tm) IHt98 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 app (IHt97 k47 d68 S25) (IHt98 k47 d68 S25))) (fun (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d68) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt97 (HS ty k47) d68 S25) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d68 k47 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt97 (T : Ty) (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 tapp (IHt97 k47 d68 S25) (let IHT0 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT0 k47 d68 S25)))) (fun (d : Decls) IHd (t : Tm) IHt97 (k47 : Hvl) (d68 : (Trace ty)) (S25 : Ty) =>
      (f_equal2 lett (IHd k47 d68 S25) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bind _ _) (eq_refl H0))) (weakenTrace_append ty (XS ty d68) k47 (bind d))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k47 (bind d)) eq_refl)) (eq_trans (IHt97 (appendHvl k47 (bind d)) d68 S25) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k47 (bind d))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0)))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d68 k47 (bind d))) eq_refl eq_refl))))))).
    Lemma tsubst_tshift0_Decls_comm_ind  :
      (forall (d68 : Decls) ,
        (forall (k47 : Hvl) (d69 : (Trace ty)) (S25 : Ty) ,
          ((tsubstDecls (weakenTrace (XS ty d69) k47) S25 (tshiftDecls (weakenCutoffty C0 k47) d68)) =
          (tshiftDecls (weakenCutoffty C0 k47) (tsubstDecls (weakenTrace d69 k47) S25 d68))))).
    Proof.
      pose proof (tsubst_tshift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tshift0_Tm_comm_ind  :
      (forall (s19 : Tm) ,
        (forall (k47 : Hvl) (d69 : (Trace ty)) (S25 : Ty) ,
          ((tsubstTm (weakenTrace (XS ty d69) k47) S25 (tshiftTm (weakenCutoffty C0 k47) s19)) =
          (tshiftTm (weakenCutoffty C0 k47) (tsubstTm (weakenTrace d69 k47) S25 s19))))).
    Proof.
      pose proof (tsubst_tshift0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S37 : Ty) : (forall (d81 : (Trace ty)) (S36 : Ty) ,
      ((tsubstTy (XS ty d81) S36 (tshiftTy C0 S37)) =
      (tshiftTy C0 (tsubstTy d81 S36 S37)))) := (tsubst_tshift0_Ty_comm_ind S37 H0).
    Definition substDecls_shiftDecls0_comm (d82 : Decls) : (forall (d81 : (Trace tm)) (s19 : Tm) ,
      ((substDecls (XS tm d81) s19 (shiftDecls C0 d82)) =
      (shiftDecls C0 (substDecls d81 s19 d82)))) := (subst_shift0_Decls_comm_ind d82 H0).
    Definition substTm_shiftTm0_comm (s20 : Tm) : (forall (d81 : (Trace tm)) (s19 : Tm) ,
      ((substTm (XS tm d81) s19 (shiftTm C0 s20)) =
      (shiftTm C0 (substTm d81 s19 s20)))) := (subst_shift0_Tm_comm_ind s20 H0).
    Definition substDecls_tshiftDecls0_comm (d82 : Decls) : (forall (d81 : (Trace tm)) (s19 : Tm) ,
      ((substDecls (XS ty d81) s19 (tshiftDecls C0 d82)) =
      (tshiftDecls C0 (substDecls d81 s19 d82)))) := (subst_tshift0_Decls_comm_ind d82 H0).
    Definition substTm_tshiftTm0_comm (s20 : Tm) : (forall (d81 : (Trace tm)) (s19 : Tm) ,
      ((substTm (XS ty d81) s19 (tshiftTm C0 s20)) =
      (tshiftTm C0 (substTm d81 s19 s20)))) := (subst_tshift0_Tm_comm_ind s20 H0).
    Definition tsubstDecls_shiftDecls0_comm (d82 : Decls) : (forall (d81 : (Trace ty)) (S36 : Ty) ,
      ((tsubstDecls d81 S36 (shiftDecls C0 d82)) =
      (shiftDecls C0 (tsubstDecls d81 S36 d82)))) := (tsubst_shift0_Decls_comm_ind d82 H0).
    Definition tsubstTm_shiftTm0_comm (s19 : Tm) : (forall (d81 : (Trace ty)) (S36 : Ty) ,
      ((tsubstTm d81 S36 (shiftTm C0 s19)) =
      (shiftTm C0 (tsubstTm d81 S36 s19)))) := (tsubst_shift0_Tm_comm_ind s19 H0).
    Definition tsubstDecls_tshiftDecls0_comm (d82 : Decls) : (forall (d81 : (Trace ty)) (S36 : Ty) ,
      ((tsubstDecls (XS ty d81) S36 (tshiftDecls C0 d82)) =
      (tshiftDecls C0 (tsubstDecls d81 S36 d82)))) := (tsubst_tshift0_Decls_comm_ind d82 H0).
    Definition tsubstTm_tshiftTm0_comm (s19 : Tm) : (forall (d81 : (Trace ty)) (S36 : Ty) ,
      ((tsubstTm (XS ty d81) S36 (tshiftTm C0 s19)) =
      (tshiftTm C0 (tsubstTm d81 S36 s19)))) := (tsubst_tshift0_Tm_comm_ind s19 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Definition tsubst_tm_Ty_ind := (ind_Ty (fun (S36 : Ty) =>
      (forall (k58 : Hvl) (d81 : (Trace ty)) (S37 : Ty) ,
        ((tsubstTy (weakenTrace (XS tm d81) k58) S37 S36) =
        (tsubstTy (weakenTrace d81 k58) S37 S36)))) (fun (X32 : (Index ty)) =>
      (fun (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
        (tsubstIndex_shiftTy0_comm_ind d81 S36 k58 X32))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
      (f_equal2 tarr (IHT0 k58 d81 S36) (IHT3 k58 d81 S36))) (fun (T : Ty) IHT0 (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
      (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d81) k58 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT0 (HS ty k58) d81 S36) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d81 k58 (HS ty H0))) eq_refl eq_refl)))))).
    Definition tsubst_tm_Decls_Tm_ind := (ind_Decls_Tm (fun (d81 : Decls) =>
      (forall (k58 : Hvl) (d82 : (Trace ty)) (S36 : Ty) ,
        ((tsubstDecls (weakenTrace (XS tm d82) k58) S36 d81) =
        (tsubstDecls (weakenTrace d82 k58) S36 d81)))) (fun (s19 : Tm) =>
      (forall (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) ,
        ((tsubstTm (weakenTrace (XS tm d81) k58) S36 s19) =
        (tsubstTm (weakenTrace d81 k58) S36 s19)))) (fun (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
      eq_refl) (fun (t : Tm) IHt104 (d : Decls) IHd (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
      (f_equal2 dcons (IHt104 k58 d81 S36) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty (XS tm d81) k58 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHd (HS tm k58) d81 S36) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty d81 k58 (HS tm H0))) eq_refl eq_refl))))) (fun (x56 : (Index tm)) =>
      (fun (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt104 (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
      (f_equal2 abs (let IHT0 := (tsubst_tm_Ty_ind T) in
      (IHT0 k58 d81 S36)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d81) k58 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt104 (HS tm k58) d81 S36) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d81 k58 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt104 (t2 : Tm) IHt105 (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
      (f_equal2 app (IHt104 k58 d81 S36) (IHt105 k58 d81 S36))) (fun (t : Tm) IHt104 (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d81) k58 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt104 (HS ty k58) d81 S36) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d81 k58 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt104 (T : Ty) (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
      (f_equal2 tapp (IHt104 k58 d81 S36) (let IHT0 := (tsubst_tm_Ty_ind T) in
      (IHT0 k58 d81 S36)))) (fun (d : Decls) IHd (t : Tm) IHt104 (k58 : Hvl) (d81 : (Trace ty)) (S36 : Ty) =>
      (f_equal2 lett (IHd k58 d81 S36) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d81) k58 (bind d)) eq_refl eq_refl) (eq_trans (IHt104 (appendHvl k58 (bind d)) d81 S36) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d81 k58 (bind d))) eq_refl eq_refl)))))).
    Lemma tsubst_tm_Decls_ind  :
      (forall (d81 : Decls) ,
        (forall (k58 : Hvl) (d82 : (Trace ty)) (S36 : Ty) ,
          ((tsubstDecls (weakenTrace (XS tm d82) k58) S36 d81) =
          (tsubstDecls (weakenTrace d82 k58) S36 d81)))).
    Proof.
      pose proof (tsubst_tm_Decls_Tm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tm_Tm_ind  :
      (forall (s19 : Tm) ,
        (forall (k58 : Hvl) (d82 : (Trace ty)) (S36 : Ty) ,
          ((tsubstTm (weakenTrace (XS tm d82) k58) S36 s19) =
          (tsubstTm (weakenTrace d82 k58) S36 s19)))).
    Proof.
      pose proof (tsubst_tm_Decls_Tm_ind).
      destruct_conjs .
      easy .
    Qed.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S37 : Ty) : (forall (d81 : (Trace ty)) (S36 : Ty) ,
      ((tsubstTy (XS tm d81) S36 S37) =
      (tsubstTy d81 S36 S37))) := (tsubst_tm_Ty_ind S37 H0).
    Definition tsubstDecls_tm (d82 : Decls) : (forall (d81 : (Trace ty)) (S36 : Ty) ,
      ((tsubstDecls (XS tm d81) S36 d82) =
      (tsubstDecls d81 S36 d82))) := (tsubst_tm_Decls_ind d82 H0).
    Definition tsubstTm_tm (s19 : Tm) : (forall (d81 : (Trace ty)) (S36 : Ty) ,
      ((tsubstTm (XS tm d81) S36 s19) =
      (tsubstTm d81 S36 s19))) := (tsubst_tm_Tm_ind s19 H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substDecls0_shiftDecls0_reflection tsubstDecls0_tshiftDecls0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite substDecls0_shiftDecls0_reflection tsubstDecls0_tshiftDecls0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite substDecls_shiftDecls0_comm substDecls_tshiftDecls0_comm tsubstDecls_shiftDecls0_comm tsubstDecls_tshiftDecls0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite substDecls_shiftDecls0_comm substDecls_tshiftDecls0_comm tsubstDecls_shiftDecls0_comm tsubstDecls_tshiftDecls0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstDecls_tm tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstDecls_tm tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite shiftDecls_substDecls0_comm shiftDecls_tsubstDecls0_comm tshiftDecls_substDecls0_comm tshiftDecls_tsubstDecls0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite shiftDecls_substDecls0_comm shiftDecls_tsubstDecls0_comm tshiftDecls_substDecls0_comm tshiftDecls_tsubstDecls0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d81 : (Trace tm)) (s19 : Tm) (s20 : Tm) :
      (forall (k58 : Hvl) (x56 : (Index tm)) ,
        ((substTm (weakenTrace d81 k58) s19 (substIndex (weakenTrace X0 k58) s20 x56)) =
        (substTm (weakenTrace X0 k58) (substTm d81 s19 s20) (substIndex (weakenTrace (XS tm d81) k58) s19 x56)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d81 : (Trace ty)) (S36 : Ty) (s19 : Tm) :
      (forall (k58 : Hvl) (x56 : (Index tm)) ,
        ((tsubstTm (weakenTrace d81 k58) S36 (substIndex (weakenTrace X0 k58) s19 x56)) =
        (substIndex (weakenTrace X0 k58) (tsubstTm d81 S36 s19) x56))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d81 : (Trace ty)) (S36 : Ty) (S37 : Ty) :
      (forall (k58 : Hvl) (X32 : (Index ty)) ,
        ((tsubstTy (weakenTrace d81 k58) S36 (tsubstIndex (weakenTrace X0 k58) S37 X32)) =
        (tsubstTy (weakenTrace X0 k58) (tsubstTy d81 S36 S37) (tsubstIndex (weakenTrace (XS ty d81) k58) S36 X32)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d81 : (Trace tm)) (s19 : Tm) (S36 : Ty) :
      (forall (k58 : Hvl) (x56 : (Index tm)) ,
        ((substIndex (weakenTrace d81 k58) s19 x56) =
        (tsubstTm (weakenTrace X0 k58) S36 (substIndex (weakenTrace (XS ty d81) k58) s19 x56)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition tsubst_tsubst0_Ty_comm_ind := (ind_Ty (fun (S40 : Ty) =>
      (forall (k61 : Hvl) (d88 : (Trace ty)) (S41 : Ty) (S42 : Ty) ,
        ((tsubstTy (weakenTrace d88 k61) S41 (tsubstTy (weakenTrace X0 k61) S42 S40)) =
        (tsubstTy (weakenTrace X0 k61) (tsubstTy d88 S41 S42) (tsubstTy (weakenTrace (XS ty d88) k61) S41 S40))))) (fun (X37 : (Index ty)) =>
      (fun (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
        (tsubstTy_tsubstIndex0_commright_ind d88 S40 S41 k61 X37))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
      (f_equal2 tarr (IHT0 k61 d88 S40 S41) (IHT3 k61 d88 S40 S41))) (fun (T : Ty) IHT0 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
      (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d88 k61 (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k61 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT0 (HS ty k61) d88 S40 S41) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k61 (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d88) k61 (HS ty H0))) eq_refl eq_refl))))))).
    Definition subst_subst0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d88 : Decls) =>
      (forall (k61 : Hvl) (d89 : (Trace tm)) (s21 : Tm) (s22 : Tm) ,
        ((substDecls (weakenTrace d89 k61) s21 (substDecls (weakenTrace X0 k61) s22 d88)) =
        (substDecls (weakenTrace X0 k61) (substTm d89 s21 s22) (substDecls (weakenTrace (XS tm d89) k61) s21 d88))))) (fun (s21 : Tm) =>
      (forall (k61 : Hvl) (d88 : (Trace tm)) (s22 : Tm) (s23 : Tm) ,
        ((substTm (weakenTrace d88 k61) s22 (substTm (weakenTrace X0 k61) s23 s21)) =
        (substTm (weakenTrace X0 k61) (substTm d88 s22 s23) (substTm (weakenTrace (XS tm d88) k61) s22 s21))))) (fun (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) =>
      eq_refl) (fun (t : Tm) IHt118 (d : Decls) IHd (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) =>
      (f_equal2 dcons (IHt118 k61 d88 s21 s22) (eq_trans (f_equal3 substDecls (weakenTrace_append tm d88 k61 (HS tm H0)) eq_refl (f_equal3 substDecls (weakenTrace_append tm X0 k61 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHd (HS tm k61) d88 s21 s22) (f_equal3 substDecls (eq_sym (weakenTrace_append tm X0 k61 (HS tm H0))) eq_refl (f_equal3 substDecls (eq_sym (weakenTrace_append tm (XS tm d88) k61 (HS tm H0))) eq_refl eq_refl)))))) (fun (x64 : (Index tm)) =>
      (fun (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) =>
        (substTm_substIndex0_commright_ind d88 s21 s22 k61 x64))) (fun (T : Ty) (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d88 k61 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k61 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt118 (HS tm k61) d88 s21 s22) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k61 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d88) k61 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt118 (t2 : Tm) IHt119 (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) =>
      (f_equal2 app (IHt118 k61 d88 s21 s22) (IHt119 k61 d88 s21 s22))) (fun (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d88 k61 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k61 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt118 (HS ty k61) d88 s21 s22) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k61 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d88) k61 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt118 (T : Ty) (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) =>
      (f_equal2 tapp (IHt118 k61 d88 s21 s22) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) =>
      (f_equal2 lett (IHd k61 d88 s21 s22) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_subst_bind _ _ _) (eq_refl H0))) (weakenTrace_append tm d88 k61 (bind d))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k61 (bind d)) eq_refl eq_refl)) (eq_trans (IHt118 (appendHvl k61 (bind d)) d88 s21 s22) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k61 (bind d))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d88) k61 (bind d))) eq_refl eq_refl))))))).
    Lemma subst_subst0_Decls_comm_ind  :
      (forall (d88 : Decls) ,
        (forall (k61 : Hvl) (d89 : (Trace tm)) (s21 : Tm) (s22 : Tm) ,
          ((substDecls (weakenTrace d89 k61) s21 (substDecls (weakenTrace X0 k61) s22 d88)) =
          (substDecls (weakenTrace X0 k61) (substTm d89 s21 s22) (substDecls (weakenTrace (XS tm d89) k61) s21 d88))))).
    Proof.
      pose proof (subst_subst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma subst_subst0_Tm_comm_ind  :
      (forall (s21 : Tm) ,
        (forall (k61 : Hvl) (d89 : (Trace tm)) (s22 : Tm) (s23 : Tm) ,
          ((substTm (weakenTrace d89 k61) s22 (substTm (weakenTrace X0 k61) s23 s21)) =
          (substTm (weakenTrace X0 k61) (substTm d89 s22 s23) (substTm (weakenTrace (XS tm d89) k61) s22 s21))))).
    Proof.
      pose proof (subst_subst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition subst_tsubst0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d88 : Decls) =>
      (forall (k61 : Hvl) (d89 : (Trace tm)) (s21 : Tm) (S40 : Ty) ,
        ((substDecls (weakenTrace d89 k61) s21 (tsubstDecls (weakenTrace X0 k61) S40 d88)) =
        (tsubstDecls (weakenTrace X0 k61) S40 (substDecls (weakenTrace (XS ty d89) k61) s21 d88))))) (fun (s21 : Tm) =>
      (forall (k61 : Hvl) (d88 : (Trace tm)) (s22 : Tm) (S40 : Ty) ,
        ((substTm (weakenTrace d88 k61) s22 (tsubstTm (weakenTrace X0 k61) S40 s21)) =
        (tsubstTm (weakenTrace X0 k61) S40 (substTm (weakenTrace (XS ty d88) k61) s22 s21))))) (fun (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) =>
      eq_refl) (fun (t : Tm) IHt118 (d : Decls) IHd (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) =>
      (f_equal2 dcons (IHt118 k61 d88 s21 S40) (eq_trans (f_equal3 substDecls (weakenTrace_append tm d88 k61 (HS tm H0)) eq_refl (f_equal3 tsubstDecls (weakenTrace_append ty X0 k61 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHd (HS tm k61) d88 s21 S40) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty X0 k61 (HS tm H0))) eq_refl (f_equal3 substDecls (eq_sym (weakenTrace_append tm (XS ty d88) k61 (HS tm H0))) eq_refl eq_refl)))))) (fun (x64 : (Index tm)) =>
      (fun (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) =>
        (substTy_tsubstIndex0_commleft_ind d88 s21 S40 k61 x64))) (fun (T : Ty) (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d88 k61 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k61 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt118 (HS tm k61) d88 s21 S40) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k61 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d88) k61 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt118 (t2 : Tm) IHt119 (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) =>
      (f_equal2 app (IHt118 k61 d88 s21 S40) (IHt119 k61 d88 s21 S40))) (fun (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d88 k61 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k61 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt118 (HS ty k61) d88 s21 S40) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k61 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d88) k61 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt118 (T : Ty) (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) =>
      (f_equal2 tapp (IHt118 k61 d88 s21 S40) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) =>
      (f_equal2 lett (IHd k61 d88 s21 S40) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0))) (weakenTrace_append tm d88 k61 (bind d))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k61 (bind d)) eq_refl eq_refl)) (eq_trans (IHt118 (appendHvl k61 (bind d)) d88 s21 S40) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k61 (bind d))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d88) k61 (bind d))) eq_refl eq_refl))))))).
    Lemma subst_tsubst0_Decls_comm_ind  :
      (forall (d88 : Decls) ,
        (forall (k61 : Hvl) (d89 : (Trace tm)) (s21 : Tm) (S40 : Ty) ,
          ((substDecls (weakenTrace d89 k61) s21 (tsubstDecls (weakenTrace X0 k61) S40 d88)) =
          (tsubstDecls (weakenTrace X0 k61) S40 (substDecls (weakenTrace (XS ty d89) k61) s21 d88))))).
    Proof.
      pose proof (subst_tsubst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma subst_tsubst0_Tm_comm_ind  :
      (forall (s21 : Tm) ,
        (forall (k61 : Hvl) (d89 : (Trace tm)) (s22 : Tm) (S40 : Ty) ,
          ((substTm (weakenTrace d89 k61) s22 (tsubstTm (weakenTrace X0 k61) S40 s21)) =
          (tsubstTm (weakenTrace X0 k61) S40 (substTm (weakenTrace (XS ty d89) k61) s22 s21))))).
    Proof.
      pose proof (subst_tsubst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_subst0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d88 : Decls) =>
      (forall (k61 : Hvl) (d89 : (Trace ty)) (S40 : Ty) (s21 : Tm) ,
        ((tsubstDecls (weakenTrace d89 k61) S40 (substDecls (weakenTrace X0 k61) s21 d88)) =
        (substDecls (weakenTrace X0 k61) (tsubstTm d89 S40 s21) (tsubstDecls (weakenTrace d89 k61) S40 d88))))) (fun (s21 : Tm) =>
      (forall (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s22 : Tm) ,
        ((tsubstTm (weakenTrace d88 k61) S40 (substTm (weakenTrace X0 k61) s22 s21)) =
        (substTm (weakenTrace X0 k61) (tsubstTm d88 S40 s22) (tsubstTm (weakenTrace d88 k61) S40 s21))))) (fun (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) =>
      eq_refl) (fun (t : Tm) IHt118 (d : Decls) IHd (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) =>
      (f_equal2 dcons (IHt118 k61 d88 S40 s21) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty d88 k61 (HS tm H0)) eq_refl (f_equal3 substDecls (weakenTrace_append tm X0 k61 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHd (HS tm k61) d88 S40 s21) (f_equal3 substDecls (eq_sym (weakenTrace_append tm X0 k61 (HS tm H0))) eq_refl (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty d88 k61 (HS tm H0))) eq_refl eq_refl)))))) (fun (x64 : (Index tm)) =>
      (fun (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) =>
        (tsubstTm_substIndex0_commright_ind d88 S40 s21 k61 x64))) (fun (T : Ty) (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d88 k61 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k61 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt118 (HS tm k61) d88 S40 s21) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k61 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d88 k61 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt118 (t2 : Tm) IHt119 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) =>
      (f_equal2 app (IHt118 k61 d88 S40 s21) (IHt119 k61 d88 S40 s21))) (fun (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d88 k61 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k61 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt118 (HS ty k61) d88 S40 s21) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k61 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d88 k61 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt118 (T : Ty) (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) =>
      (f_equal2 tapp (IHt118 k61 d88 S40 s21) eq_refl)) (fun (d : Decls) IHd (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) =>
      (f_equal2 lett (IHd k61 d88 S40 s21) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_subst_bind _ _ _) (eq_refl H0))) (weakenTrace_append ty d88 k61 (bind d))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k61 (bind d)) eq_refl eq_refl)) (eq_trans (IHt118 (appendHvl k61 (bind d)) d88 S40 s21) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k61 (bind d))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d88 k61 (bind d))) eq_refl eq_refl))))))).
    Lemma tsubst_subst0_Decls_comm_ind  :
      (forall (d88 : Decls) ,
        (forall (k61 : Hvl) (d89 : (Trace ty)) (S40 : Ty) (s21 : Tm) ,
          ((tsubstDecls (weakenTrace d89 k61) S40 (substDecls (weakenTrace X0 k61) s21 d88)) =
          (substDecls (weakenTrace X0 k61) (tsubstTm d89 S40 s21) (tsubstDecls (weakenTrace d89 k61) S40 d88))))).
    Proof.
      pose proof (tsubst_subst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_subst0_Tm_comm_ind  :
      (forall (s21 : Tm) ,
        (forall (k61 : Hvl) (d89 : (Trace ty)) (S40 : Ty) (s22 : Tm) ,
          ((tsubstTm (weakenTrace d89 k61) S40 (substTm (weakenTrace X0 k61) s22 s21)) =
          (substTm (weakenTrace X0 k61) (tsubstTm d89 S40 s22) (tsubstTm (weakenTrace d89 k61) S40 s21))))).
    Proof.
      pose proof (tsubst_subst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_tsubst0_Decls_Tm_comm_ind := (ind_Decls_Tm (fun (d88 : Decls) =>
      (forall (k61 : Hvl) (d89 : (Trace ty)) (S40 : Ty) (S41 : Ty) ,
        ((tsubstDecls (weakenTrace d89 k61) S40 (tsubstDecls (weakenTrace X0 k61) S41 d88)) =
        (tsubstDecls (weakenTrace X0 k61) (tsubstTy d89 S40 S41) (tsubstDecls (weakenTrace (XS ty d89) k61) S40 d88))))) (fun (s21 : Tm) =>
      (forall (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) ,
        ((tsubstTm (weakenTrace d88 k61) S40 (tsubstTm (weakenTrace X0 k61) S41 s21)) =
        (tsubstTm (weakenTrace X0 k61) (tsubstTy d88 S40 S41) (tsubstTm (weakenTrace (XS ty d88) k61) S40 s21))))) (fun (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
      eq_refl) (fun (t : Tm) IHt118 (d : Decls) IHd (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
      (f_equal2 dcons (IHt118 k61 d88 S40 S41) (eq_trans (f_equal3 tsubstDecls (weakenTrace_append ty d88 k61 (HS tm H0)) eq_refl (f_equal3 tsubstDecls (weakenTrace_append ty X0 k61 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHd (HS tm k61) d88 S40 S41) (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty X0 k61 (HS tm H0))) eq_refl (f_equal3 tsubstDecls (eq_sym (weakenTrace_append ty (XS ty d88) k61 (HS tm H0))) eq_refl eq_refl)))))) (fun (x64 : (Index tm)) =>
      (fun (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
      (f_equal2 abs (let IHT0 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT0 k61 d88 S40 S41)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d88 k61 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k61 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt118 (HS tm k61) d88 S40 S41) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k61 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d88) k61 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt118 (t2 : Tm) IHt119 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
      (f_equal2 app (IHt118 k61 d88 S40 S41) (IHt119 k61 d88 S40 S41))) (fun (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d88 k61 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k61 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt118 (HS ty k61) d88 S40 S41) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k61 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d88) k61 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt118 (T : Ty) (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
      (f_equal2 tapp (IHt118 k61 d88 S40 S41) (let IHT0 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT0 k61 d88 S40 S41)))) (fun (d : Decls) IHd (t : Tm) IHt118 (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) =>
      (f_equal2 lett (IHd k61 d88 S40 S41) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0))) (weakenTrace_append ty d88 k61 (bind d))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k61 (bind d)) eq_refl eq_refl)) (eq_trans (IHt118 (appendHvl k61 (bind d)) d88 S40 S41) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k61 (bind d))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d88) k61 (bind d))) eq_refl eq_refl))))))).
    Lemma tsubst_tsubst0_Decls_comm_ind  :
      (forall (d88 : Decls) ,
        (forall (k61 : Hvl) (d89 : (Trace ty)) (S40 : Ty) (S41 : Ty) ,
          ((tsubstDecls (weakenTrace d89 k61) S40 (tsubstDecls (weakenTrace X0 k61) S41 d88)) =
          (tsubstDecls (weakenTrace X0 k61) (tsubstTy d89 S40 S41) (tsubstDecls (weakenTrace (XS ty d89) k61) S40 d88))))).
    Proof.
      pose proof (tsubst_tsubst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tsubst0_Tm_comm_ind  :
      (forall (s21 : Tm) ,
        (forall (k61 : Hvl) (d89 : (Trace ty)) (S40 : Ty) (S41 : Ty) ,
          ((tsubstTm (weakenTrace d89 k61) S40 (tsubstTm (weakenTrace X0 k61) S41 s21)) =
          (tsubstTm (weakenTrace X0 k61) (tsubstTy d89 S40 S41) (tsubstTm (weakenTrace (XS ty d89) k61) S40 s21))))).
    Proof.
      pose proof (tsubst_tsubst0_Decls_Tm_comm_ind).
      destruct_conjs .
      easy .
    Qed.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S42 : Ty) : (forall (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) ,
      ((tsubstTy d88 S40 (tsubstTy X0 S41 S42)) =
      (tsubstTy X0 (tsubstTy d88 S40 S41) (tsubstTy (XS ty d88) S40 S42)))) := (tsubst_tsubst0_Ty_comm_ind S42 H0).
    Definition substDecls_substDecls0_comm (d89 : Decls) : (forall (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) ,
      ((substDecls d88 s21 (substDecls X0 s22 d89)) =
      (substDecls X0 (substTm d88 s21 s22) (substDecls (XS tm d88) s21 d89)))) := (subst_subst0_Decls_comm_ind d89 H0).
    Definition substTm_substTm0_comm (s23 : Tm) : (forall (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) ,
      ((substTm d88 s21 (substTm X0 s22 s23)) =
      (substTm X0 (substTm d88 s21 s22) (substTm (XS tm d88) s21 s23)))) := (subst_subst0_Tm_comm_ind s23 H0).
    Definition substDecls_tsubstDecls0_comm (d89 : Decls) : (forall (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) ,
      ((substDecls d88 s21 (tsubstDecls X0 S40 d89)) =
      (tsubstDecls X0 S40 (substDecls (XS ty d88) s21 d89)))) := (subst_tsubst0_Decls_comm_ind d89 H0).
    Definition substTm_tsubstTm0_comm (s22 : Tm) : (forall (d88 : (Trace tm)) (s21 : Tm) (S40 : Ty) ,
      ((substTm d88 s21 (tsubstTm X0 S40 s22)) =
      (tsubstTm X0 S40 (substTm (XS ty d88) s21 s22)))) := (subst_tsubst0_Tm_comm_ind s22 H0).
    Definition tsubstDecls_substDecls0_comm (d89 : Decls) : (forall (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) ,
      ((tsubstDecls d88 S40 (substDecls X0 s21 d89)) =
      (substDecls X0 (tsubstTm d88 S40 s21) (tsubstDecls d88 S40 d89)))) := (tsubst_subst0_Decls_comm_ind d89 H0).
    Definition tsubstTm_substTm0_comm (s22 : Tm) : (forall (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) ,
      ((tsubstTm d88 S40 (substTm X0 s21 s22)) =
      (substTm X0 (tsubstTm d88 S40 s21) (tsubstTm d88 S40 s22)))) := (tsubst_subst0_Tm_comm_ind s22 H0).
    Definition tsubstDecls_tsubstDecls0_comm (d89 : Decls) : (forall (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) ,
      ((tsubstDecls d88 S40 (tsubstDecls X0 S41 d89)) =
      (tsubstDecls X0 (tsubstTy d88 S40 S41) (tsubstDecls (XS ty d88) S40 d89)))) := (tsubst_tsubst0_Decls_comm_ind d89 H0).
    Definition tsubstTm_tsubstTm0_comm (s21 : Tm) : (forall (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) ,
      ((tsubstTm d88 S40 (tsubstTm X0 S41 s21)) =
      (tsubstTm X0 (tsubstTy d88 S40 S41) (tsubstTm (XS ty d88) S40 s21)))) := (tsubst_tsubst0_Tm_comm_ind s21 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (S41 : Ty) ,
        ((weakenTy (tsubstTy d88 S40 S41) k61) =
        (tsubstTy (weakenTrace d88 k61) S40 (weakenTy S41 k61)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenDecls_substDecls  :
      (forall (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (d89 : Decls) ,
        ((weakenDecls (substDecls d88 s21 d89) k61) =
        (substDecls (weakenTrace d88 k61) s21 (weakenDecls d89 k61)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k61 : Hvl) (d88 : (Trace tm)) (s21 : Tm) (s22 : Tm) ,
        ((weakenTm (substTm d88 s21 s22) k61) =
        (substTm (weakenTrace d88 k61) s21 (weakenTm s22 k61)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenDecls_tsubstDecls  :
      (forall (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (d89 : Decls) ,
        ((weakenDecls (tsubstDecls d88 S40 d89) k61) =
        (tsubstDecls (weakenTrace d88 k61) S40 (weakenDecls d89 k61)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k61 : Hvl) (d88 : (Trace ty)) (S40 : Ty) (s21 : Tm) ,
        ((weakenTm (tsubstTm d88 S40 s21) k61) =
        (tsubstTm (weakenTrace d88 k61) S40 (weakenTm s21 k61)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenTy_append  :
      (forall (S40 : Ty) (k61 : Hvl) (k62 : Hvl) ,
        ((weakenTy (weakenTy S40 k61) k62) =
        (weakenTy S40 (appendHvl k61 k62)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenDecls_append  :
      (forall (d88 : Decls) (k61 : Hvl) (k62 : Hvl) ,
        ((weakenDecls (weakenDecls d88 k61) k62) =
        (weakenDecls d88 (appendHvl k61 k62)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s21 : Tm) (k61 : Hvl) (k62 : Hvl) ,
        ((weakenTm (weakenTm s21 k61) k62) =
        (weakenTm s21 (appendHvl k61 k62)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
  End WeakenAppend.
End SubstSubstInteraction.
 Hint Rewrite substDecls_substDecls0_comm tsubstDecls_tsubstDecls0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite substDecls_substDecls0_comm tsubstDecls_tsubstDecls0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenDecls_shiftDecls weakenDecls_tshiftDecls weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenDecls_substDecls weakenDecls_tsubstDecls weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
Section WellFormed.
  Fixpoint wfindex {a : Namespace} (k61 : Hvl) (i : (Index a)) {struct k61} : Prop :=
    match k61 with
      | (H0) => False
      | (HS b k61) => match (eq_namespace_dec a b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k61 i)
        end
        | (right n) => (wfindex k61 i)
      end
    end.
  Inductive wfTy (k61 : Hvl) : Ty -> Prop :=
    | wfTy_tvar {X43 : (Index ty)}
        (wfi : (wfindex k61 X43)) :
        (wfTy k61 (tvar X43))
    | wfTy_tarr {T58 : Ty}
        (wf : (wfTy k61 T58)) {T59 : Ty}
        (wf0 : (wfTy k61 T59)) :
        (wfTy k61 (tarr T58 T59))
    | wfTy_tall {T60 : Ty}
        (wf : (wfTy (HS ty k61) T60)) :
        (wfTy k61 (tall T60)).
  Inductive wfDecls (k61 : Hvl) : Decls -> Prop :=
    | wfDecls_dnil :
        (wfDecls k61 (dnil))
    | wfDecls_dcons {t132 : Tm}
        (wf : (wfTm k61 t132))
        {d92 : Decls}
        (wf0 : (wfDecls (HS tm k61) d92))
        : (wfDecls k61 (dcons t132 d92))
  with wfTm (k61 : Hvl) : Tm -> Prop :=
    | wfTm_var {x71 : (Index tm)}
        (wfi : (wfindex k61 x71)) :
        (wfTm k61 (var x71))
    | wfTm_abs {T58 : Ty}
        (wf : (wfTy k61 T58))
        {t132 : Tm}
        (wf0 : (wfTm (HS tm k61) t132))
        : (wfTm k61 (abs T58 t132))
    | wfTm_app {t133 : Tm}
        (wf : (wfTm k61 t133))
        {t134 : Tm}
        (wf0 : (wfTm k61 t134)) :
        (wfTm k61 (app t133 t134))
    | wfTm_tabs {t135 : Tm}
        (wf : (wfTm (HS ty k61) t135)) :
        (wfTm k61 (tabs t135))
    | wfTm_tapp {t136 : Tm}
        (wf : (wfTm k61 t136))
        {T59 : Ty}
        (wf0 : (wfTy k61 T59)) :
        (wfTm k61 (tapp t136 T59))
    | wfTm_lett {d92 : Decls}
        (wf : (wfDecls k61 d92))
        {t137 : Tm}
        (wf0 : (wfTm (appendHvl k61 (bind d92)) t137))
        : (wfTm k61 (lett d92 t137)).
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfDecls := Induction for wfDecls Sort Prop
  with ind_wfTm := Induction for wfTm Sort Prop.
  Combined Scheme ind_wfDecls_Tm from ind_wfDecls, ind_wfTm.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c14 : (Cutoff tm)) (k61 : Hvl) (k62 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k61 : Hvl)
        :
        (shifthvl_tm C0 k61 (HS tm k61))
    | shifthvl_tm_there_tm
        (c14 : (Cutoff tm)) (k61 : Hvl)
        (k62 : Hvl) :
        (shifthvl_tm c14 k61 k62) -> (shifthvl_tm (CS c14) (HS tm k61) (HS tm k62))
    | shifthvl_tm_there_ty
        (c14 : (Cutoff tm)) (k61 : Hvl)
        (k62 : Hvl) :
        (shifthvl_tm c14 k61 k62) -> (shifthvl_tm c14 (HS ty k61) (HS ty k62)).
  Inductive shifthvl_ty : (forall (c14 : (Cutoff ty)) (k61 : Hvl) (k62 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k61 : Hvl)
        :
        (shifthvl_ty C0 k61 (HS ty k61))
    | shifthvl_ty_there_tm
        (c14 : (Cutoff ty)) (k61 : Hvl)
        (k62 : Hvl) :
        (shifthvl_ty c14 k61 k62) -> (shifthvl_ty c14 (HS tm k61) (HS tm k62))
    | shifthvl_ty_there_ty
        (c14 : (Cutoff ty)) (k61 : Hvl)
        (k62 : Hvl) :
        (shifthvl_ty c14 k61 k62) -> (shifthvl_ty (CS c14) (HS ty k61) (HS ty k62)).
  Lemma weaken_shifthvl_tm  :
    (forall (k61 : Hvl) {c14 : (Cutoff tm)} {k62 : Hvl} {k63 : Hvl} ,
      (shifthvl_tm c14 k62 k63) -> (shifthvl_tm (weakenCutofftm c14 k61) (appendHvl k62 k61) (appendHvl k63 k61))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k61 : Hvl) {c14 : (Cutoff ty)} {k62 : Hvl} {k63 : Hvl} ,
      (shifthvl_ty c14 k62 k63) -> (shifthvl_ty (weakenCutoffty c14 k61) (appendHvl k62 k61) (appendHvl k63 k61))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c14 : (Cutoff tm)) (k61 : Hvl) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) (x71 : (Index tm)) ,
      (wfindex k61 x71) -> (wfindex k62 (shiftIndex c14 x71))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c14 : (Cutoff tm)) (k61 : Hvl) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) (X43 : (Index ty)) ,
      (wfindex k61 X43) -> (wfindex k62 X43)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c14 : (Cutoff ty)) (k61 : Hvl) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) (x71 : (Index tm)) ,
      (wfindex k61 x71) -> (wfindex k62 x71)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c14 : (Cutoff ty)) (k61 : Hvl) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) (X43 : (Index ty)) ,
      (wfindex k61 X43) -> (wfindex k62 (tshiftIndex c14 X43))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k61 : Hvl) ,
    (forall (S40 : Ty) (wf : (wfTy k61 S40)) ,
      (forall (c14 : (Cutoff tm)) (k62 : Hvl) ,
        (shifthvl_tm c14 k61 k62) -> (wfTy k62 S40)))) := (ind_wfTy (fun (k61 : Hvl) (S40 : Ty) (wf : (wfTy k61 S40)) =>
    (forall (c14 : (Cutoff tm)) (k62 : Hvl) ,
      (shifthvl_tm c14 k61 k62) -> (wfTy k62 S40))) (fun (k61 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k61 X43)) (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfTy_tvar k62 (shift_wfindex_ty c14 k61 k62 ins X43 wfi))) (fun (k61 : Hvl) (T1 : Ty) (wf : (wfTy k61 T1)) IHT0 (T2 : Ty) (wf0 : (wfTy k61 T2)) IHT3 (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfTy_tarr k62 (IHT0 c14 k62 (weaken_shifthvl_tm H0 ins)) (IHT3 c14 k62 (weaken_shifthvl_tm H0 ins)))) (fun (k61 : Hvl) (T : Ty) (wf : (wfTy (HS ty k61) T)) IHT0 (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfTy_tall k62 (IHT0 c14 (HS ty k62) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k61 : Hvl) ,
    (forall (S40 : Ty) (wf : (wfTy k61 S40)) ,
      (forall (c14 : (Cutoff ty)) (k62 : Hvl) ,
        (shifthvl_ty c14 k61 k62) -> (wfTy k62 (tshiftTy c14 S40))))) := (ind_wfTy (fun (k61 : Hvl) (S40 : Ty) (wf : (wfTy k61 S40)) =>
    (forall (c14 : (Cutoff ty)) (k62 : Hvl) ,
      (shifthvl_ty c14 k61 k62) -> (wfTy k62 (tshiftTy c14 S40)))) (fun (k61 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k61 X43)) (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfTy_tvar k62 (tshift_wfindex_ty c14 k61 k62 ins X43 wfi))) (fun (k61 : Hvl) (T1 : Ty) (wf : (wfTy k61 T1)) IHT0 (T2 : Ty) (wf0 : (wfTy k61 T2)) IHT3 (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfTy_tarr k62 (IHT0 c14 k62 (weaken_shifthvl_ty H0 ins)) (IHT3 c14 k62 (weaken_shifthvl_ty H0 ins)))) (fun (k61 : Hvl) (T : Ty) (wf : (wfTy (HS ty k61) T)) IHT0 (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfTy_tall k62 (IHT0 (CS c14) (HS ty k62) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfDecls_Tm : (forall (k61 : Hvl) ,
    (forall (d92 : Decls) (wf : (wfDecls k61 d92)) ,
      (forall (c14 : (Cutoff tm)) (k62 : Hvl) ,
        (shifthvl_tm c14 k61 k62) -> (wfDecls k62 (shiftDecls c14 d92)))) /\
    (forall (s21 : Tm) (wf : (wfTm k61 s21)) ,
      (forall (c14 : (Cutoff tm)) (k62 : Hvl) ,
        (shifthvl_tm c14 k61 k62) -> (wfTm k62 (shiftTm c14 s21))))) := (ind_wfDecls_Tm (fun (k61 : Hvl) (d92 : Decls) (wf : (wfDecls k61 d92)) =>
    (forall (c14 : (Cutoff tm)) (k62 : Hvl) ,
      (shifthvl_tm c14 k61 k62) -> (wfDecls k62 (shiftDecls c14 d92)))) (fun (k61 : Hvl) (s21 : Tm) (wf : (wfTm k61 s21)) =>
    (forall (c14 : (Cutoff tm)) (k62 : Hvl) ,
      (shifthvl_tm c14 k61 k62) -> (wfTm k62 (shiftTm c14 s21)))) (fun (k61 : Hvl) (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfDecls_dnil k62)) (fun (k61 : Hvl) (t : Tm) (wf : (wfTm k61 t)) IHt132 (d : Decls) (wf0 : (wfDecls (HS tm k61) d)) IHd (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfDecls_dcons k62 (IHt132 c14 k62 (weaken_shifthvl_tm H0 ins)) (IHd (CS c14) (HS tm k62) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k61 : Hvl) (x71 : (Index tm)) (wfi : (wfindex k61 x71)) (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfTm_var k62 (shift_wfindex_tm c14 k61 k62 ins x71 wfi))) (fun (k61 : Hvl) (T : Ty) (wf : (wfTy k61 T)) (t : Tm) (wf0 : (wfTm (HS tm k61) t)) IHt132 (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfTm_abs k62 (shift_wfTy k61 T wf c14 k62 (weaken_shifthvl_tm H0 ins)) (IHt132 (CS c14) (HS tm k62) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k61 : Hvl) (t1 : Tm) (wf : (wfTm k61 t1)) IHt132 (t2 : Tm) (wf0 : (wfTm k61 t2)) IHt133 (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfTm_app k62 (IHt132 c14 k62 (weaken_shifthvl_tm H0 ins)) (IHt133 c14 k62 (weaken_shifthvl_tm H0 ins)))) (fun (k61 : Hvl) (t : Tm) (wf : (wfTm (HS ty k61) t)) IHt132 (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfTm_tabs k62 (IHt132 c14 (HS ty k62) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k61 : Hvl) (t : Tm) (wf : (wfTm k61 t)) IHt132 (T : Ty) (wf0 : (wfTy k61 T)) (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfTm_tapp k62 (IHt132 c14 k62 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k61 T wf0 c14 k62 (weaken_shifthvl_tm H0 ins)))) (fun (k61 : Hvl) (d : Decls) (wf : (wfDecls k61 d)) IHd (t : Tm) (wf0 : (wfTm (appendHvl k61 (bind d)) t)) IHt132 (c14 : (Cutoff tm)) (k62 : Hvl) (ins : (shifthvl_tm c14 k61 k62)) =>
    (wfTm_lett k62 (IHd c14 k62 (weaken_shifthvl_tm H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k62) (f_equal2 appendHvl (eq_sym (stability_shift_bind _ _)) (eq_refl H0))) eq_refl (IHt132 (weakenCutofftm c14 (bind d)) (appendHvl k62 (bind d)) (weaken_shifthvl_tm (bind d) ins)))))).
  Lemma shift_wfDecls (k61 : Hvl) :
    (forall (d92 : Decls) (wf : (wfDecls k61 d92)) ,
      (forall (c14 : (Cutoff tm)) (k62 : Hvl) ,
        (shifthvl_tm c14 k61 k62) -> (wfDecls k62 (shiftDecls c14 d92)))).
  Proof.
    pose proof ((shift_wfDecls_Tm k61)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_wfTm (k61 : Hvl) :
    (forall (s21 : Tm) (wf0 : (wfTm k61 s21)) ,
      (forall (c15 : (Cutoff tm)) (k63 : Hvl) ,
        (shifthvl_tm c15 k61 k63) -> (wfTm k63 (shiftTm c15 s21)))).
  Proof.
    pose proof ((shift_wfDecls_Tm k61)).
    destruct_conjs .
    easy .
  Qed.
  Definition tshift_wfDecls_Tm : (forall (k61 : Hvl) ,
    (forall (d92 : Decls) (wf : (wfDecls k61 d92)) ,
      (forall (c14 : (Cutoff ty)) (k62 : Hvl) ,
        (shifthvl_ty c14 k61 k62) -> (wfDecls k62 (tshiftDecls c14 d92)))) /\
    (forall (s21 : Tm) (wf : (wfTm k61 s21)) ,
      (forall (c14 : (Cutoff ty)) (k62 : Hvl) ,
        (shifthvl_ty c14 k61 k62) -> (wfTm k62 (tshiftTm c14 s21))))) := (ind_wfDecls_Tm (fun (k61 : Hvl) (d92 : Decls) (wf : (wfDecls k61 d92)) =>
    (forall (c14 : (Cutoff ty)) (k62 : Hvl) ,
      (shifthvl_ty c14 k61 k62) -> (wfDecls k62 (tshiftDecls c14 d92)))) (fun (k61 : Hvl) (s21 : Tm) (wf : (wfTm k61 s21)) =>
    (forall (c14 : (Cutoff ty)) (k62 : Hvl) ,
      (shifthvl_ty c14 k61 k62) -> (wfTm k62 (tshiftTm c14 s21)))) (fun (k61 : Hvl) (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfDecls_dnil k62)) (fun (k61 : Hvl) (t : Tm) (wf : (wfTm k61 t)) IHt132 (d : Decls) (wf0 : (wfDecls (HS tm k61) d)) IHd (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfDecls_dcons k62 (IHt132 c14 k62 (weaken_shifthvl_ty H0 ins)) (IHd c14 (HS tm k62) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k61 : Hvl) (x71 : (Index tm)) (wfi : (wfindex k61 x71)) (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfTm_var k62 (tshift_wfindex_tm c14 k61 k62 ins x71 wfi))) (fun (k61 : Hvl) (T : Ty) (wf : (wfTy k61 T)) (t : Tm) (wf0 : (wfTm (HS tm k61) t)) IHt132 (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfTm_abs k62 (tshift_wfTy k61 T wf c14 k62 (weaken_shifthvl_ty H0 ins)) (IHt132 c14 (HS tm k62) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k61 : Hvl) (t1 : Tm) (wf : (wfTm k61 t1)) IHt132 (t2 : Tm) (wf0 : (wfTm k61 t2)) IHt133 (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfTm_app k62 (IHt132 c14 k62 (weaken_shifthvl_ty H0 ins)) (IHt133 c14 k62 (weaken_shifthvl_ty H0 ins)))) (fun (k61 : Hvl) (t : Tm) (wf : (wfTm (HS ty k61) t)) IHt132 (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfTm_tabs k62 (IHt132 (CS c14) (HS ty k62) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k61 : Hvl) (t : Tm) (wf : (wfTm k61 t)) IHt132 (T : Ty) (wf0 : (wfTy k61 T)) (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfTm_tapp k62 (IHt132 c14 k62 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k61 T wf0 c14 k62 (weaken_shifthvl_ty H0 ins)))) (fun (k61 : Hvl) (d : Decls) (wf : (wfDecls k61 d)) IHd (t : Tm) (wf0 : (wfTm (appendHvl k61 (bind d)) t)) IHt132 (c14 : (Cutoff ty)) (k62 : Hvl) (ins : (shifthvl_ty c14 k61 k62)) =>
    (wfTm_lett k62 (IHd c14 k62 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k62) (f_equal2 appendHvl (eq_sym (stability_tshift_bind _ _)) (eq_refl H0))) eq_refl (IHt132 (weakenCutoffty c14 (bind d)) (appendHvl k62 (bind d)) (weaken_shifthvl_ty (bind d) ins)))))).
  Lemma tshift_wfDecls (k61 : Hvl) :
    (forall (d92 : Decls) (wf : (wfDecls k61 d92)) ,
      (forall (c14 : (Cutoff ty)) (k62 : Hvl) ,
        (shifthvl_ty c14 k61 k62) -> (wfDecls k62 (tshiftDecls c14 d92)))).
  Proof.
    pose proof ((tshift_wfDecls_Tm k61)).
    destruct_conjs .
    easy .
  Qed.
  Lemma tshift_wfTm (k61 : Hvl) :
    (forall (s21 : Tm) (wf0 : (wfTm k61 s21)) ,
      (forall (c15 : (Cutoff ty)) (k63 : Hvl) ,
        (shifthvl_ty c15 k61 k63) -> (wfTm k63 (tshiftTm c15 s21)))).
  Proof.
    pose proof ((tshift_wfDecls_Tm k61)).
    destruct_conjs .
    easy .
  Qed.
End ShiftWellFormed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfDecls shift_wfTm shift_wfTy tshift_wfDecls tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfDecls shift_wfTm shift_wfTy tshift_wfDecls tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfDecls shift_wfTm shift_wfTy tshift_wfDecls tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfDecls shift_wfTm shift_wfTy tshift_wfDecls tshift_wfTm tshift_wfTy : wf.
 Hint Constructors shifthvl_tm shifthvl_ty : infra.
 Hint Constructors shifthvl_tm shifthvl_ty : shift.
 Hint Constructors shifthvl_tm shifthvl_ty : shift_wf.
 Hint Constructors shifthvl_tm shifthvl_ty : wf.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : infra.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : shift.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : shift_wf.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : weaken.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : wf.
Section SubstWellFormed.
  Inductive substhvl_tm (k61 : Hvl) : (forall (d92 : (Trace tm)) (k62 : Hvl) (k63 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k61 X0 (HS tm k61) k61)
    | substhvl_tm_there_tm
        {d92 : (Trace tm)} {k62 : Hvl}
        {k63 : Hvl} :
        (substhvl_tm k61 d92 k62 k63) -> (substhvl_tm k61 (XS tm d92) (HS tm k62) (HS tm k63))
    | substhvl_tm_there_ty
        {d92 : (Trace tm)} {k62 : Hvl}
        {k63 : Hvl} :
        (substhvl_tm k61 d92 k62 k63) -> (substhvl_tm k61 (XS ty d92) (HS ty k62) (HS ty k63)).
  Inductive substhvl_ty (k61 : Hvl) : (forall (d92 : (Trace ty)) (k62 : Hvl) (k63 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k61 X0 (HS ty k61) k61)
    | substhvl_ty_there_tm
        {d92 : (Trace ty)} {k62 : Hvl}
        {k63 : Hvl} :
        (substhvl_ty k61 d92 k62 k63) -> (substhvl_ty k61 (XS tm d92) (HS tm k62) (HS tm k63))
    | substhvl_ty_there_ty
        {d92 : (Trace ty)} {k62 : Hvl}
        {k63 : Hvl} :
        (substhvl_ty k61 d92 k62 k63) -> (substhvl_ty k61 (XS ty d92) (HS ty k62) (HS ty k63)).
  Lemma weaken_substhvl_tm  :
    (forall {k62 : Hvl} (k61 : Hvl) {d92 : (Trace tm)} {k63 : Hvl} {k64 : Hvl} ,
      (substhvl_tm k62 d92 k63 k64) -> (substhvl_tm k62 (weakenTrace d92 k61) (appendHvl k63 k61) (appendHvl k64 k61))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k62 : Hvl} (k61 : Hvl) {d92 : (Trace ty)} {k63 : Hvl} {k64 : Hvl} ,
      (substhvl_ty k62 d92 k63 k64) -> (substhvl_ty k62 (weakenTrace d92 k61) (appendHvl k63 k61) (appendHvl k64 k61))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k63 : Hvl} {s21 : Tm} (wft : (wfTm k63 s21)) :
    (forall {d92 : (Trace tm)} {k64 : Hvl} {k65 : Hvl} ,
      (substhvl_tm k63 d92 k64 k65) -> (forall {x71 : (Index tm)} ,
        (wfindex k64 x71) -> (wfTm k65 (substIndex d92 s21 x71)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k63 : Hvl} {S41 : Ty} (wft : (wfTy k63 S41)) :
    (forall {d92 : (Trace ty)} {k64 : Hvl} {k65 : Hvl} ,
      (substhvl_ty k63 d92 k64 k65) -> (forall {X43 : (Index ty)} ,
        (wfindex k64 X43) -> (wfTy k65 (tsubstIndex d92 S41 X43)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k63 : Hvl} :
    (forall {d92 : (Trace tm)} {k64 : Hvl} {k65 : Hvl} ,
      (substhvl_tm k63 d92 k64 k65) -> (forall {X43 : (Index ty)} ,
        (wfindex k64 X43) -> (wfindex k65 X43))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k63 : Hvl} :
    (forall {d92 : (Trace ty)} {k64 : Hvl} {k65 : Hvl} ,
      (substhvl_ty k63 d92 k64 k65) -> (forall {x71 : (Index tm)} ,
        (wfindex k64 x71) -> (wfindex k65 x71))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k63 : Hvl} : (forall (k64 : Hvl) ,
    (forall (S41 : Ty) (wf0 : (wfTy k64 S41)) ,
      (forall {d92 : (Trace tm)} {k65 : Hvl} ,
        (substhvl_tm k63 d92 k64 k65) -> (wfTy k65 S41)))) := (ind_wfTy (fun (k64 : Hvl) (S41 : Ty) (wf0 : (wfTy k64 S41)) =>
    (forall {d92 : (Trace tm)} {k65 : Hvl} ,
      (substhvl_tm k63 d92 k64 k65) -> (wfTy k65 S41))) (fun (k64 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k64 X43)) {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfTy_tvar k65 (substhvl_tm_wfindex_ty del wfi))) (fun (k64 : Hvl) (T1 : Ty) (wf0 : (wfTy k64 T1)) IHT0 (T2 : Ty) (wf1 : (wfTy k64 T2)) IHT3 {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfTy_tarr k65 (IHT0 (weakenTrace d92 H0) k65 (weaken_substhvl_tm H0 del)) (IHT3 (weakenTrace d92 H0) k65 (weaken_substhvl_tm H0 del)))) (fun (k64 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k64) T)) IHT0 {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfTy_tall k65 (IHT0 (weakenTrace d92 (HS ty H0)) (HS ty k65) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k63 : Hvl} {S41 : Ty} (wf : (wfTy k63 S41)) : (forall (k64 : Hvl) ,
    (forall (S42 : Ty) (wf0 : (wfTy k64 S42)) ,
      (forall {d92 : (Trace ty)} {k65 : Hvl} ,
        (substhvl_ty k63 d92 k64 k65) -> (wfTy k65 (tsubstTy d92 S41 S42))))) := (ind_wfTy (fun (k64 : Hvl) (S42 : Ty) (wf0 : (wfTy k64 S42)) =>
    (forall {d92 : (Trace ty)} {k65 : Hvl} ,
      (substhvl_ty k63 d92 k64 k65) -> (wfTy k65 (tsubstTy d92 S41 S42)))) (fun (k64 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k64 X43)) {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k64 : Hvl) (T1 : Ty) (wf0 : (wfTy k64 T1)) IHT0 (T2 : Ty) (wf1 : (wfTy k64 T2)) IHT3 {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfTy_tarr k65 (IHT0 (weakenTrace d92 H0) k65 (weaken_substhvl_ty H0 del)) (IHT3 (weakenTrace d92 H0) k65 (weaken_substhvl_ty H0 del)))) (fun (k64 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k64) T)) IHT0 {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfTy_tall k65 (IHT0 (weakenTrace d92 (HS ty H0)) (HS ty k65) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfDecls_Tm {k63 : Hvl} {s21 : Tm} (wf : (wfTm k63 s21)) : (forall (k64 : Hvl) ,
    (forall (d92 : Decls) (wf0 : (wfDecls k64 d92)) ,
      (forall {d93 : (Trace tm)} {k65 : Hvl} ,
        (substhvl_tm k63 d93 k64 k65) -> (wfDecls k65 (substDecls d93 s21 d92)))) /\
    (forall (s22 : Tm) (wf0 : (wfTm k64 s22)) ,
      (forall {d92 : (Trace tm)} {k65 : Hvl} ,
        (substhvl_tm k63 d92 k64 k65) -> (wfTm k65 (substTm d92 s21 s22))))) := (ind_wfDecls_Tm (fun (k64 : Hvl) (d92 : Decls) (wf0 : (wfDecls k64 d92)) =>
    (forall {d93 : (Trace tm)} {k65 : Hvl} ,
      (substhvl_tm k63 d93 k64 k65) -> (wfDecls k65 (substDecls d93 s21 d92)))) (fun (k64 : Hvl) (s22 : Tm) (wf0 : (wfTm k64 s22)) =>
    (forall {d92 : (Trace tm)} {k65 : Hvl} ,
      (substhvl_tm k63 d92 k64 k65) -> (wfTm k65 (substTm d92 s21 s22)))) (fun (k64 : Hvl) {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfDecls_dnil k65)) (fun (k64 : Hvl) (t : Tm) (wf0 : (wfTm k64 t)) IHt132 (d : Decls) (wf1 : (wfDecls (HS tm k64) d)) IHd {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfDecls_dcons k65 (IHt132 (weakenTrace d92 H0) k65 (weaken_substhvl_tm H0 del)) (IHd (weakenTrace d92 (HS tm H0)) (HS tm k65) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k64 : Hvl) {x71 : (Index tm)} (wfi : (wfindex k64 x71)) {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k64 : Hvl) (T : Ty) (wf0 : (wfTy k64 T)) (t : Tm) (wf1 : (wfTm (HS tm k64) t)) IHt132 {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfTm_abs k65 (substhvl_tm_wfTy k64 T wf0 (weaken_substhvl_tm H0 del)) (IHt132 (weakenTrace d92 (HS tm H0)) (HS tm k65) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k64 : Hvl) (t1 : Tm) (wf0 : (wfTm k64 t1)) IHt132 (t2 : Tm) (wf1 : (wfTm k64 t2)) IHt133 {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfTm_app k65 (IHt132 (weakenTrace d92 H0) k65 (weaken_substhvl_tm H0 del)) (IHt133 (weakenTrace d92 H0) k65 (weaken_substhvl_tm H0 del)))) (fun (k64 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k64) t)) IHt132 {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfTm_tabs k65 (IHt132 (weakenTrace d92 (HS ty H0)) (HS ty k65) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k64 : Hvl) (t : Tm) (wf0 : (wfTm k64 t)) IHt132 (T : Ty) (wf1 : (wfTy k64 T)) {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfTm_tapp k65 (IHt132 (weakenTrace d92 H0) k65 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k64 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k64 : Hvl) (d : Decls) (wf0 : (wfDecls k64 d)) IHd (t : Tm) (wf1 : (wfTm (appendHvl k64 (bind d)) t)) IHt132 {d92 : (Trace tm)} {k65 : Hvl} (del : (substhvl_tm k63 d92 k64 k65)) =>
    (wfTm_lett k65 (IHd (weakenTrace d92 H0) k65 (weaken_substhvl_tm H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k65) (f_equal2 appendHvl (eq_sym (stability_subst_bind _ _ _)) (eq_refl H0))) eq_refl (IHt132 (weakenTrace d92 (bind d)) (appendHvl k65 (bind d)) (weaken_substhvl_tm (bind d) del)))))).
  Lemma substhvl_tm_wfDecls {k63 : Hvl} {s21 : Tm} (wf : (wfTm k63 s21)) (k64 : Hvl) (d92 : Decls) (wf0 : (wfDecls k64 d92)) :
    (forall {d93 : (Trace tm)} {k65 : Hvl} ,
      (substhvl_tm k63 d93 k64 k65) -> (wfDecls k65 (substDecls d93 s21 d92))).
  Proof.
    apply ((substhvl_tm_wfDecls_Tm wf k64)).
    auto .
  Qed.
  Lemma substhvl_tm_wfTm {k63 : Hvl} {s21 : Tm} (wf : (wfTm k63 s21)) (k64 : Hvl) (s22 : Tm) (wf1 : (wfTm k64 s22)) :
    (forall {d94 : (Trace tm)} {k66 : Hvl} ,
      (substhvl_tm k63 d94 k64 k66) -> (wfTm k66 (substTm d94 s21 s22))).
  Proof.
    apply ((substhvl_tm_wfDecls_Tm wf k64)).
    auto .
  Qed.
  Definition substhvl_ty_wfDecls_Tm {k63 : Hvl} {S41 : Ty} (wf : (wfTy k63 S41)) : (forall (k64 : Hvl) ,
    (forall (d92 : Decls) (wf0 : (wfDecls k64 d92)) ,
      (forall {d93 : (Trace ty)} {k65 : Hvl} ,
        (substhvl_ty k63 d93 k64 k65) -> (wfDecls k65 (tsubstDecls d93 S41 d92)))) /\
    (forall (s21 : Tm) (wf0 : (wfTm k64 s21)) ,
      (forall {d92 : (Trace ty)} {k65 : Hvl} ,
        (substhvl_ty k63 d92 k64 k65) -> (wfTm k65 (tsubstTm d92 S41 s21))))) := (ind_wfDecls_Tm (fun (k64 : Hvl) (d92 : Decls) (wf0 : (wfDecls k64 d92)) =>
    (forall {d93 : (Trace ty)} {k65 : Hvl} ,
      (substhvl_ty k63 d93 k64 k65) -> (wfDecls k65 (tsubstDecls d93 S41 d92)))) (fun (k64 : Hvl) (s21 : Tm) (wf0 : (wfTm k64 s21)) =>
    (forall {d92 : (Trace ty)} {k65 : Hvl} ,
      (substhvl_ty k63 d92 k64 k65) -> (wfTm k65 (tsubstTm d92 S41 s21)))) (fun (k64 : Hvl) {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfDecls_dnil k65)) (fun (k64 : Hvl) (t : Tm) (wf0 : (wfTm k64 t)) IHt132 (d : Decls) (wf1 : (wfDecls (HS tm k64) d)) IHd {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfDecls_dcons k65 (IHt132 (weakenTrace d92 H0) k65 (weaken_substhvl_ty H0 del)) (IHd (weakenTrace d92 (HS tm H0)) (HS tm k65) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k64 : Hvl) {x71 : (Index tm)} (wfi : (wfindex k64 x71)) {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfTm_var k65 (substhvl_ty_wfindex_tm del wfi))) (fun (k64 : Hvl) (T : Ty) (wf0 : (wfTy k64 T)) (t : Tm) (wf1 : (wfTm (HS tm k64) t)) IHt132 {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfTm_abs k65 (substhvl_ty_wfTy wf k64 T wf0 (weaken_substhvl_ty H0 del)) (IHt132 (weakenTrace d92 (HS tm H0)) (HS tm k65) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k64 : Hvl) (t1 : Tm) (wf0 : (wfTm k64 t1)) IHt132 (t2 : Tm) (wf1 : (wfTm k64 t2)) IHt133 {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfTm_app k65 (IHt132 (weakenTrace d92 H0) k65 (weaken_substhvl_ty H0 del)) (IHt133 (weakenTrace d92 H0) k65 (weaken_substhvl_ty H0 del)))) (fun (k64 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k64) t)) IHt132 {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfTm_tabs k65 (IHt132 (weakenTrace d92 (HS ty H0)) (HS ty k65) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k64 : Hvl) (t : Tm) (wf0 : (wfTm k64 t)) IHt132 (T : Ty) (wf1 : (wfTy k64 T)) {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfTm_tapp k65 (IHt132 (weakenTrace d92 H0) k65 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k64 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k64 : Hvl) (d : Decls) (wf0 : (wfDecls k64 d)) IHd (t : Tm) (wf1 : (wfTm (appendHvl k64 (bind d)) t)) IHt132 {d92 : (Trace ty)} {k65 : Hvl} (del : (substhvl_ty k63 d92 k64 k65)) =>
    (wfTm_lett k65 (IHd (weakenTrace d92 H0) k65 (weaken_substhvl_ty H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k65) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))) eq_refl (IHt132 (weakenTrace d92 (bind d)) (appendHvl k65 (bind d)) (weaken_substhvl_ty (bind d) del)))))).
  Lemma substhvl_ty_wfDecls {k63 : Hvl} {S41 : Ty} (wf : (wfTy k63 S41)) (k64 : Hvl) (d92 : Decls) (wf0 : (wfDecls k64 d92)) :
    (forall {d93 : (Trace ty)} {k65 : Hvl} ,
      (substhvl_ty k63 d93 k64 k65) -> (wfDecls k65 (tsubstDecls d93 S41 d92))).
  Proof.
    apply ((substhvl_ty_wfDecls_Tm wf k64)).
    auto .
  Qed.
  Lemma substhvl_ty_wfTm {k63 : Hvl} {S41 : Ty} (wf : (wfTy k63 S41)) (k64 : Hvl) (s21 : Tm) (wf1 : (wfTm k64 s21)) :
    (forall {d94 : (Trace ty)} {k66 : Hvl} ,
      (substhvl_ty k63 d94 k64 k66) -> (wfTm k66 (tsubstTm d94 S41 s21))).
  Proof.
    apply ((substhvl_ty_wfDecls_Tm wf k64)).
    auto .
  Qed.
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfDecls substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfDecls substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfDecls substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfDecls substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfDecls substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfDecls substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfDecls substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfDecls substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Fixpoint subhvl_tm (k63 : Hvl) {struct k63} : Prop :=
  match k63 with
    | (H0) => True
    | (HS a k63) => match a with
      | (tm) => (subhvl_tm k63)
      | _ => False
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k63 : Hvl) (k64 : Hvl) ,
    (subhvl_tm k63) -> (subhvl_tm k64) -> (subhvl_tm (appendHvl k63 k64))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k62 : Hvl) (k61 : Hvl) (S40 : Ty) ,
    (subhvl_tm k62) -> (wfTy (appendHvl k61 k62) (weakenTy S40 k62)) -> (wfTy k61 S40)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_tm) in H
end : infra wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | etvar (G : Env)
    | evar (G : Env) (T : Ty).
  Fixpoint appendEnv (G : Env) (G0 : Env) : Env :=
    match G0 with
      | (empty) => G
      | (etvar G1) => (etvar (appendEnv G G1))
      | (evar G1 T) => (evar (appendEnv G G1) T)
    end.
  Fixpoint domainEnv (G : Env) : Hvl :=
    match G with
      | (empty) => H0
      | (etvar G0) => (HS ty (domainEnv G0))
      | (evar G0 T) => (HS tm (domainEnv G0))
    end.
  Lemma appendEnv_assoc  :
    (forall (G : Env) (G0 : Env) (G1 : Env) ,
      ((appendEnv G (appendEnv G0 G1)) =
      (appendEnv (appendEnv G G0) G1))).
  Proof.
    needleGenericAppendEnvAssoc .
  Qed.
  Lemma domainEnv_appendEnv  :
    (forall (G : Env) (G0 : Env) ,
      ((domainEnv (appendEnv G G0)) =
      (appendHvl (domainEnv G) (domainEnv G0)))).
  Proof.
    needleGenericDomainEnvAppendEnv .
  Qed.
  Fixpoint tshiftEnv (c14 : (Cutoff ty)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (etvar G0) => (etvar (tshiftEnv c14 G0))
      | (evar G0 T) => (evar (tshiftEnv c14 G0) (tshiftTy (weakenCutoffty c14 (domainEnv G0)) T))
    end.
  Fixpoint shiftEnv (c14 : (Cutoff tm)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (etvar G0) => (etvar (shiftEnv c14 G0))
      | (evar G0 T) => (evar (shiftEnv c14 G0) T)
    end.
  Fixpoint tsubstEnv (d92 : (Trace ty)) (S41 : Ty) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (etvar G0) => (etvar (tsubstEnv d92 S41 G0))
      | (evar G0 T) => (evar (tsubstEnv d92 S41 G0) (tsubstTy (weakenTrace d92 (domainEnv G0)) S41 T))
    end.
  Fixpoint substEnv (d92 : (Trace tm)) (s21 : Tm) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (etvar G0) => (etvar (substEnv d92 s21 G0))
      | (evar G0 T) => (evar (substEnv d92 s21 G0) T)
    end.
  Lemma domainEnv_tshiftEnv  :
    (forall (c14 : (Cutoff ty)) (G : Env) ,
      ((domainEnv (tshiftEnv c14 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_shiftEnv  :
    (forall (c14 : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c14 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d92 : (Trace ty)) (S41 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d92 S41 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d92 : (Trace tm)) (s21 : Tm) (G : Env) ,
      ((domainEnv (substEnv d92 s21 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma tshiftEnv_appendEnv  :
      (forall (c14 : (Cutoff ty)) (G : Env) (G0 : Env) ,
        ((tshiftEnv c14 (appendEnv G G0)) =
        (appendEnv (tshiftEnv c14 G) (tshiftEnv (weakenCutoffty c14 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma shiftEnv_appendEnv  :
      (forall (c14 : (Cutoff tm)) (G : Env) (G0 : Env) ,
        ((shiftEnv c14 (appendEnv G G0)) =
        (appendEnv (shiftEnv c14 G) (shiftEnv (weakenCutofftm c14 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma tsubstEnv_appendEnv  :
      (forall (d92 : (Trace ty)) (S41 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d92 S41 (appendEnv G G0)) =
        (appendEnv (tsubstEnv d92 S41 G) (tsubstEnv (weakenTrace d92 (domainEnv G)) S41 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma substEnv_appendEnv  :
      (forall (d92 : (Trace tm)) (s21 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d92 s21 (appendEnv G G0)) =
        (appendEnv (substEnv d92 s21 G) (substEnv (weakenTrace d92 (domainEnv G)) s21 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Section Lookups.
    Inductive lookup_etvar : Env -> (Index ty) -> Prop :=
      | lookup_etvar_here {G : Env}
          : (lookup_etvar (etvar G) I0)
      | lookup_etvar_there_etvar
          {G : Env} {X43 : (Index ty)} :
          (lookup_etvar G X43) -> (lookup_etvar (etvar G) (IS X43))
      | lookup_etvar_there_evar
          {G : Env} {X43 : (Index ty)}
          {T58 : Ty} :
          (lookup_etvar G X43) -> (lookup_etvar (evar G T58) X43).
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          {T58 : Ty} :
          (wfTy (domainEnv G) T58) -> (lookup_evar (evar G T58) I0 T58)
      | lookup_evar_there_etvar
          {G : Env} {x71 : (Index tm)}
          {T58 : Ty} :
          (lookup_evar G x71 T58) -> (lookup_evar (etvar G) x71 (tshiftTy C0 T58))
      | lookup_evar_there_evar
          {G : Env} {x71 : (Index tm)}
          {T58 : Ty} {T59 : Ty} :
          (lookup_evar G x71 T58) -> (lookup_evar (evar G T59) (IS x71) T58).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (S41 : Ty) (S42 : Ty) ,
        (lookup_evar (evar G S41) I0 S42) -> (S41 =
        S42)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x71 : (Index tm)} ,
        (forall {S41 : Ty} ,
          (lookup_evar G x71 S41) -> (forall {S42 : Ty} ,
            (lookup_evar G x71 S42) -> (S41 =
            S42)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x71 : (Index tm)} {S41 : Ty} ,
        (lookup_evar G x71 S41) -> (wfTy (domainEnv G) S41)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X43 : (Index ty)} ,
        (lookup_etvar G X43) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X43 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x71 : (Index tm)} {T58 : Ty} ,
        (lookup_evar G x71 T58) -> (lookup_evar (appendEnv G G0) (weakenIndextm x71 (domainEnv G0)) (weakenTy T58 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X43 : (Index ty)} ,
        (lookup_etvar G X43) -> (wfindex (domainEnv G) X43)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x71 : (Index tm)} {S41 : Ty} ,
        (lookup_evar G x71 S41) -> (wfindex (domainEnv G) x71)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env} :
        (shift_etvar C0 G (etvar G))
    | shiftetvar_there_etvar
        {c14 : (Cutoff ty)} {G : Env}
        {G0 : Env} :
        (shift_etvar c14 G G0) -> (shift_etvar (CS c14) (etvar G) (etvar G0))
    | shiftetvar_there_evar
        {c14 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c14 G G0) -> (shift_etvar c14 (evar G T) (evar G0 (tshiftTy c14 T))).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c14 : (Cutoff ty)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c14 G0 G1) -> (shift_etvar (weakenCutoffty c14 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (tshiftEnv c14 G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T58 : Ty} :
        (shift_evar C0 G (evar G T58))
    | shiftevar_there_etvar
        {c14 : (Cutoff tm)} {G : Env}
        {G0 : Env} :
        (shift_evar c14 G G0) -> (shift_evar c14 (etvar G) (etvar G0))
    | shiftevar_there_evar
        {c14 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c14 G G0) -> (shift_evar (CS c14) (evar G T) (evar G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c14 : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c14 G0 G1) -> (shift_evar (weakenCutofftm c14 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c14 : (Cutoff ty)} {G : Env} {G0 : Env} ,
      (shift_etvar c14 G G0) -> (shifthvl_ty c14 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c14 : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c14 G G0) -> (shifthvl_tm c14 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_etvar (G : Env) (S41 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G S41 X0 (etvar G) G)
    | subst_etvar_there_etvar
        {d92 : (Trace ty)} {G0 : Env}
        {G1 : Env} :
        (subst_etvar G S41 d92 G0 G1) -> (subst_etvar G S41 (XS ty d92) (etvar G0) (etvar G1))
    | subst_etvar_there_evar
        {d92 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G S41 d92 G0 G1) -> (subst_etvar G S41 (XS tm d92) (evar G0 T) (evar G1 (tsubstTy d92 S41 T))).
  Lemma weaken_subst_etvar {G : Env} {S41 : Ty} :
    (forall (G0 : Env) {d92 : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G S41 d92 G1 G2) -> (subst_etvar G S41 (weakenTrace d92 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d92 S41 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_evar (G : Env) (T58 : Ty) (s21 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T58 s21 X0 (evar G T58) G)
    | subst_evar_there_etvar
        {d92 : (Trace tm)} {G0 : Env}
        {G1 : Env} :
        (subst_evar G T58 s21 d92 G0 G1) -> (subst_evar G T58 s21 (XS ty d92) (etvar G0) (etvar G1))
    | subst_evar_there_evar
        {d92 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T58 s21 d92 G0 G1) -> (subst_evar G T58 s21 (XS tm d92) (evar G0 T) (evar G1 T)).
  Lemma weaken_subst_evar {G : Env} {T58 : Ty} {s21 : Tm} :
    (forall (G0 : Env) {d92 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T58 s21 d92 G1 G2) -> (subst_evar G T58 s21 (weakenTrace d92 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S41 : Ty} :
    (forall {d92 : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G S41 d92 G0 G1) -> (substhvl_ty (domainEnv G) d92 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s21 : Tm} {T58 : Ty} :
    (forall {d92 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T58 s21 d92 G0 G1) -> (substhvl_tm (domainEnv G) d92 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Rewrite domainEnv_tshiftEnv : interaction.
 Hint Rewrite domainEnv_tshiftEnv : env_domain_shift.
 Hint Rewrite domainEnv_tsubstEnv : interaction.
 Hint Rewrite domainEnv_tsubstEnv : env_domain_subst.
 Hint Rewrite tshiftEnv_appendEnv : interaction.
 Hint Rewrite tshiftEnv_appendEnv : env_shift_append.
 Hint Rewrite tsubstEnv_appendEnv : interaction.
 Hint Rewrite tsubstEnv_appendEnv : env_shift_append.
 Hint Constructors lookup_evar lookup_etvar : infra.
 Hint Constructors lookup_evar lookup_etvar : lookup.
 Hint Constructors lookup_evar lookup_etvar : shift.
 Hint Constructors lookup_evar lookup_etvar : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : weaken.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) ,
    (lookup_etvar (appendEnv (etvar G) G0) (weakenIndexty I0 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_evar_here  :
  (forall {G : Env} (G0 : Env) {T58 : Ty} (wf : (wfTy (domainEnv G) T58)) ,
    (lookup_evar (appendEnv (evar G T58) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T58 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfDecls wfTm wfTy : infra.
 Hint Constructors wfDecls wfTm wfTy : wf.
 Hint Extern 10 ((wfDecls _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H : (wfTy _ (tvar _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tarr _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tall _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfDecls _ _)) => match goal with
  | H : (wfDecls _ (dnil)) |- _ => inversion H; subst; clear H
  | H : (wfDecls _ (dcons _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H : (wfTm _ (var _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (abs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (app _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tabs _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tapp _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (lett _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Resolve lookup_evar_wf : infra.
 Hint Resolve lookup_evar_wf : wf.
 Hint Resolve lookup_evar_wfindex lookup_etvar_wfindex : infra.
 Hint Resolve lookup_evar_wfindex lookup_etvar_wfindex : lookup.
 Hint Resolve lookup_evar_wfindex lookup_etvar_wfindex : wf.
 Hint Constructors shift_evar shift_etvar : infra.
 Hint Constructors shift_evar shift_etvar : shift.
 Hint Constructors shift_evar shift_etvar : subst.
 Hint Resolve weaken_shift_evar weaken_shift_etvar : infra.
 Hint Resolve weaken_shift_evar weaken_shift_etvar : shift.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : infra.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : shift.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : shift_wf.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : wf.
 Hint Constructors subst_evar subst_etvar : infra.
 Hint Constructors subst_evar subst_etvar : subst.
 Hint Resolve weaken_subst_evar weaken_subst_etvar : infra.
 Hint Resolve weaken_subst_evar weaken_subst_etvar : subst.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : infra.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : subst.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : subst_wf.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : wf.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : substenv_substhvl.
Lemma shift_etvar_lookup_etvar  :
  (forall {c14 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c14 G G0)) {X43 : (Index ty)} ,
    (lookup_etvar G X43) -> (lookup_etvar G0 (tshiftIndex c14 X43))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c14 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c14 G G0)) {x71 : (Index tm)} {T58 : Ty} ,
    (lookup_evar G x71 T58) -> (lookup_evar G0 x71 (tshiftTy c14 T58))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c14 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c14 G G0)) {X43 : (Index ty)} ,
    (lookup_etvar G X43) -> (lookup_etvar G0 X43)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_evar  :
  (forall {c14 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c14 G G0)) {x71 : (Index tm)} {T58 : Ty} ,
    (lookup_evar G x71 T58) -> (lookup_evar G0 (shiftIndex c14 x71) T58)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_etvar_lookup_evar {G : Env} {S41 : Ty} (wf : (wfTy (domainEnv G) S41)) :
  (forall {d92 : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G S41 d92 G0 G1)) {x71 : (Index tm)} {T59 : Ty} ,
    (lookup_evar G0 x71 T59) -> (lookup_evar G1 x71 (tsubstTy d92 S41 T59))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_evar_lookup_etvar {G : Env} {T59 : Ty} {s21 : Tm} :
  (forall {d92 : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T59 s21 d92 G0 G1)) {X43 : (Index ty)} ,
    (lookup_etvar G0 X43) -> (lookup_etvar G1 X43)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} : nat :=
  match S0 with
    | (tvar X) => 1
    | (tarr T1 T2) => (plus 1 (plus (size_Ty T1) (size_Ty T2)))
    | (tall T) => (plus 1 (size_Ty T))
  end.
Fixpoint size_Decls (d : Decls) {struct d} : nat :=
  match d with
    | (dnil) => 1
    | (dcons t d0) => (plus 1 (plus (size_Tm t) (size_Decls d0)))
  end
with size_Tm (s : Tm) {struct s} : nat :=
  match s with
    | (var x) => 1
    | (abs T t) => (plus 1 (plus (size_Ty T) (size_Tm t)))
    | (app t1 t2) => (plus 1 (plus (size_Tm t1) (size_Tm t2)))
    | (tabs t0) => (plus 1 (size_Tm t0))
    | (tapp t3 T0) => (plus 1 (plus (size_Tm t3) (size_Ty T0)))
    | (lett d t4) => (plus 1 (plus (size_Decls d) (size_Tm t4)))
  end.
Lemma tshift_size_Ty  :
  (forall (S40 : Ty) (c11 : (Cutoff ty)) ,
    ((size_Ty (tshiftTy c11 S40)) =
    (size_Ty S40))).
Proof.
  apply_mutual_ind ind_Ty.
  - intros X38 c11.
  reflexivity.
  - intros T51 IHT51 T52 IHT52.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT51 c12)).
  + exact ((IHT52 c12)).
  - intros T53 IHT53.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT53 (CS c12))).
Qed.

Lemma shift_size_Decls_Tm  :
  (forall (d88 : Decls) (c12 : (Cutoff tm)) ,
    ((size_Decls (shiftDecls c12 d88)) =
    (size_Decls d88))) /\
  (forall (s21 : Tm) (c12 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c12 s21)) =
    (size_Tm s21))).
Proof.
  apply_mutual_ind ind_Decls_Tm.
  - intros c12; simpl; apply ((f_equal S)); reflexivity.
  - intros t118 IHt118 d88 IHd88.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt118 c12)).
  + exact ((IHd88 (CS c12))).
  - intros x66 c12.
  reflexivity.
  - intros T54 t119 IHt119.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt119 (CS c13))).
  - intros t120 IHt120 t121 IHt121.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt120 c13)).
  + exact ((IHt121 c13)).
  - intros t122 IHt122.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt122 c13)).
  - intros t123 IHt123 T55.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt123 c13)).
  + reflexivity.
  - intros d89 IHd89 t124 IHt124.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHd89 c13)).
  + exact ((IHt124 (weakenCutofftm c13 (bind d89)))).
Qed.

Lemma shift_size_Decls  :
  (forall (d90 : Decls) (c13 : (Cutoff tm)) ,
    ((size_Decls (shiftDecls c13 d90)) =
    (size_Decls d90))).
Proof.
  pose proof (shift_size_Decls_Tm).
  destruct_conjs .
  easy .
Qed.
Lemma shift_size_Tm  :
  (forall (s21 : Tm) (c13 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c13 s21)) =
    (size_Tm s21))).
Proof.
  pose proof (shift_size_Decls_Tm).
  destruct_conjs .
  easy .
Qed.
Lemma tshift_size_Decls_Tm  :
  (forall (d90 : Decls) (c13 : (Cutoff ty)) ,
    ((size_Decls (tshiftDecls c13 d90)) =
    (size_Decls d90))) /\
  (forall (s21 : Tm) (c13 : (Cutoff ty)) ,
    ((size_Tm (tshiftTm c13 s21)) =
    (size_Tm s21))).
Proof.
  apply_mutual_ind ind_Decls_Tm.
  - intros c13; simpl; apply ((f_equal S)); reflexivity.
  - intros t125 IHt125 d90 IHd90.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt125 c13)).
  + exact ((IHd90 c13)).
  - intros X41 c13.
  reflexivity.
  - intros T56 t126 IHt126.
  pose proof ((tshift_size_Ty T56)) as IHT56.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT56 c14)).
  + exact ((IHt126 c14)).
  - intros t127 IHt127 t128 IHt128.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt127 c14)).
  + exact ((IHt128 c14)).
  - intros t129 IHt129.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt129 (CS c14))).
  - intros t130 IHt130 T57.
  pose proof ((tshift_size_Ty T57)) as IHT57.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt130 c14)).
  + exact ((IHT57 c14)).
  - intros d91 IHd91 t131 IHt131.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHd91 c14)).
  + exact ((IHt131 (weakenCutoffty c14 (bind d91)))).
Qed.

Lemma tshift_size_Decls  :
  (forall (d92 : Decls) (c14 : (Cutoff ty)) ,
    ((size_Decls (tshiftDecls c14 d92)) =
    (size_Decls d92))).
Proof.
  pose proof (tshift_size_Decls_Tm).
  destruct_conjs .
  easy .
Qed.
Lemma tshift_size_Tm  :
  (forall (s21 : Tm) (c14 : (Cutoff ty)) ,
    ((size_Tm (tshiftTm c14 s21)) =
    (size_Tm s21))).
Proof.
  pose proof (tshift_size_Decls_Tm).
  destruct_conjs .
  easy .
Qed.
 Hint Rewrite shift_size_Decls tshift_size_Decls shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Decls tshift_size_Decls shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Decls  :
  (forall (k61 : Hvl) (d92 : Decls) ,
    ((size_Decls (weakenDecls d92 k61)) =
    (size_Decls d92))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k61 : Hvl) (s21 : Tm) ,
    ((size_Tm (weakenTm s21 k61)) =
    (size_Tm s21))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k61 : Hvl) (S40 : Ty) ,
    ((size_Ty (weakenTy S40 k61)) =
    (size_Ty S40))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Decls weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Decls weaken_size_Tm weaken_size_Ty : weaken_size.