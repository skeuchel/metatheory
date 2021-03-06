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
    | top 
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (T1 : Ty) (T2 : Ty)
    | tprod (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Pat : Set :=
    | pvar (T : Ty)
    | pprod (p1 : Pat) (p2 : Pat).
  Scheme ind_Pat := Induction for Pat Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (T : Ty) (t : Tm)
    | tapp (t : Tm) (T : Ty)
    | prod (t1 : Tm) (t2 : Tm)
    | lett (p : Pat) (t1 : Tm)
        (t2 : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  Fixpoint bindPat (p : Pat) {struct p} : Hvl :=
    match p with
      | (pvar T) => (appendHvl (HS tm H0) H0)
      | (pprod p1 p2) => (appendHvl (bindPat p1) (appendHvl (bindPat p2) H0))
    end.
  Scheme ind_bindPat_Pat := Induction for Pat Sort Prop.
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
      | (top) => (top)
      | (tarr T1 T2) => (tarr (tshiftTy (weakenCutoffty c H0) T1) (tshiftTy (weakenCutoffty c H0) T2))
      | (tall T0 T3) => (tall (tshiftTy (weakenCutoffty c H0) T0) (tshiftTy (weakenCutoffty c (appendHvl (HS ty H0) H0)) T3))
      | (tprod T4 T5) => (tprod (tshiftTy (weakenCutoffty c H0) T4) (tshiftTy (weakenCutoffty c H0) T5))
    end.
  Fixpoint tshiftPat (c : (Cutoff ty)) (p : Pat) {struct p} : Pat :=
    match p with
      | (pvar T) => (pvar (tshiftTy (weakenCutoffty c H0) T))
      | (pprod p1 p2) => (pprod (tshiftPat (weakenCutoffty c H0) p1) (tshiftPat (weakenCutoffty c H0) p2))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var (shiftIndex c x))
      | (abs T t) => (abs T (shiftTm (weakenCutofftm c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (shiftTm (weakenCutofftm c H0) t1) (shiftTm (weakenCutofftm c H0) t2))
      | (tabs T0 t0) => (tabs T0 (shiftTm (weakenCutofftm c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T1) => (tapp (shiftTm (weakenCutofftm c H0) t3) T1)
      | (prod t4 t5) => (prod (shiftTm (weakenCutofftm c H0) t4) (shiftTm (weakenCutofftm c H0) t5))
      | (lett p t6 t7) => (lett p (shiftTm (weakenCutofftm c H0) t6) (shiftTm (weakenCutofftm c (appendHvl (bindPat p) H0)) t7))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tshiftTy (weakenCutoffty c H0) T) (tshiftTm (weakenCutoffty c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (tshiftTm (weakenCutoffty c H0) t1) (tshiftTm (weakenCutoffty c H0) t2))
      | (tabs T0 t0) => (tabs (tshiftTy (weakenCutoffty c H0) T0) (tshiftTm (weakenCutoffty c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T1) => (tapp (tshiftTm (weakenCutoffty c H0) t3) (tshiftTy (weakenCutoffty c H0) T1))
      | (prod t4 t5) => (prod (tshiftTm (weakenCutoffty c H0) t4) (tshiftTm (weakenCutoffty c H0) t5))
      | (lett p t6 t7) => (lett (tshiftPat (weakenCutoffty c H0) p) (tshiftTm (weakenCutoffty c H0) t6) (tshiftTm (weakenCutoffty c (appendHvl (bindPat p) H0)) t7))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} : Ty :=
    match k with
      | (H0) => S0
      | (HS tm k) => (weakenTy S0 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S0 k))
    end.
  Fixpoint weakenPat (p : Pat) (k : Hvl) {struct k} : Pat :=
    match k with
      | (H0) => p
      | (HS tm k) => (weakenPat p k)
      | (HS ty k) => (tshiftPat C0 (weakenPat p k))
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
      | (top) => (top)
      | (tarr T1 T2) => (tarr (tsubstTy d S0 T1) (tsubstTy d S0 T2))
      | (tall T0 T3) => (tall (tsubstTy d S0 T0) (tsubstTy (XS ty d) S0 T3))
      | (tprod T4 T5) => (tprod (tsubstTy d S0 T4) (tsubstTy d S0 T5))
    end.
  Fixpoint tsubstPat (d : (Trace ty)) (S0 : Ty) (p : Pat) {struct p} : Pat :=
    match p with
      | (pvar T) => (pvar (tsubstTy d S0 T))
      | (pprod p1 p2) => (pprod (tsubstPat d S0 p1) (tsubstPat d S0 p2))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} : Tm :=
    match s0 with
      | (var x) => (substIndex d s x)
      | (abs T t) => (abs T (substTm (XS tm d) s t))
      | (app t1 t2) => (app (substTm d s t1) (substTm d s t2))
      | (tabs T0 t0) => (tabs T0 (substTm (XS ty d) s t0))
      | (tapp t3 T1) => (tapp (substTm d s t3) T1)
      | (prod t4 t5) => (prod (substTm d s t4) (substTm d s t5))
      | (lett p t6 t7) => (lett p (substTm d s t6) (substTm (weakenTrace d (bindPat p)) s t7))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tsubstTy d S0 T) (tsubstTm (XS tm d) S0 t))
      | (app t1 t2) => (app (tsubstTm d S0 t1) (tsubstTm d S0 t2))
      | (tabs T0 t0) => (tabs (tsubstTy d S0 T0) (tsubstTm (XS ty d) S0 t0))
      | (tapp t3 T1) => (tapp (tsubstTm d S0 t3) (tsubstTy d S0 T1))
      | (prod t4 t5) => (prod (tsubstTm d S0 t4) (tsubstTm d S0 t5))
      | (lett p t6 t7) => (lett (tsubstPat d S0 p) (tsubstTm d S0 t6) (tsubstTm (weakenTrace d (bindPat p)) S0 t7))
    end.
End Subst.

Global Hint Resolve (f_equal (tshiftPat C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : interaction.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : interaction.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_tshift_bindPat  :
  (forall (p : Pat) ,
    (forall (c : (Cutoff ty)) ,
      ((bindPat (tshiftPat c p)) =
      (bindPat p)))).
Proof.
  apply_mutual_ind (ind_bindPat_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tshift_bindPat : interaction.
 Hint Rewrite stability_tshift_bindPat : stability_shift.
Lemma stability_weaken_bindPat  :
  (forall (k : Hvl) (p0 : Pat) ,
    ((bindPat (weakenPat p0 k)) =
    (bindPat p0))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bindPat : interaction.
 Hint Rewrite stability_weaken_bindPat : stability_weaken.
Lemma stability_tsubst_bindPat  :
  (forall (p0 : Pat) ,
    (forall (d : (Trace ty)) (S0 : Ty) ,
      ((bindPat (tsubstPat d S0 p0)) =
      (bindPat p0)))).
Proof.
  apply_mutual_ind (ind_bindPat_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tsubst_bindPat : interaction.
 Hint Rewrite stability_tsubst_bindPat : stability_subst.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k4 : Hvl) (x10 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k4) s (shiftIndex (weakenCutofftm C0 k4) x10)) =
      (var x10))).
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
      (tsubstIndex0_tshiftIndex0_reflection_ind S3 k7 X14))) (fun (k7 : Hvl) (S3 : Ty) =>
    eq_refl) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tarr (IHT6 k7 S3) (IHT7 k7 S3))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tall (IHT6 k7 S3) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHT7 (HS ty k7) S3)))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tprod (IHT6 k7 S3) (IHT7 k7 S3)))).
  Definition tsubst0_tshift0_Pat_reflection_ind := (ind_Pat (fun (p11 : Pat) =>
    (forall (k7 : Hvl) (S3 : Ty) ,
      ((tsubstPat (weakenTrace X0 k7) S3 (tshiftPat (weakenCutoffty C0 k7) p11)) =
      p11))) (fun (T : Ty) (k7 : Hvl) (S3 : Ty) =>
    (f_equal pvar (let IHT6 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT6 k7 S3)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 pprod (IHp0 k7 S3) (IHp3 k7 S3)))).
  Definition subst0_shift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (s1 : Tm) ,
      ((substTm (weakenTrace X0 k7) s1 (shiftTm (weakenCutofftm C0 k7) s0)) =
      s0))) (fun (x16 : (Index tm)) =>
    (fun (k7 : Hvl) (s0 : Tm) =>
      (substIndex0_shiftIndex0_reflection_ind s0 k7 x16))) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt53 (HS tm k7) s0)))) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 app (IHt53 k7 s0) (IHt54 k7 s0))) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt53 (HS ty k7) s0)))) (fun (t : Tm) IHt53 (T : Ty) (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tapp (IHt53 k7 s0) eq_refl)) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 prod (IHt53 k7 s0) (IHt54 k7 s0))) (fun (p : Pat) (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (s0 : Tm) =>
    (f_equal3 lett eq_refl (IHt53 k7 s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k7 (bindPat p)) eq_refl)) (IHt54 (appendHvl k7 (bindPat p)) s0))))).
  Definition tsubst0_tshift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (S3 : Ty) ,
      ((tsubstTm (weakenTrace X0 k7) S3 (tshiftTm (weakenCutoffty C0 k7) s0)) =
      s0))) (fun (x16 : (Index tm)) =>
    (fun (k7 : Hvl) (S3 : Ty) =>
      eq_refl)) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 abs (let IHT6 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT6 k7 S3)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt53 (HS tm k7) S3)))) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 app (IHt53 k7 S3) (IHt54 k7 S3))) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tabs (let IHT6 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT6 k7 S3)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt53 (HS ty k7) S3)))) (fun (t : Tm) IHt53 (T : Ty) (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tapp (IHt53 k7 S3) (let IHT6 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT6 k7 S3)))) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 prod (IHt53 k7 S3) (IHt54 k7 S3))) (fun (p : Pat) (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (S3 : Ty) =>
    (f_equal3 lett (let IHp := (tsubst0_tshift0_Pat_reflection_ind p) in
    (IHp k7 S3)) (IHt53 k7 S3) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenTrace_append ty X0 k7 (bindPat p))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k7 (bindPat p)) eq_refl)) (IHt54 (appendHvl k7 (bindPat p)) S3))))).
  Definition tsubstTy0_tshiftTy0_reflection (S4 : Ty) : (forall (S3 : Ty) ,
    ((tsubstTy X0 S3 (tshiftTy C0 S4)) =
    S4)) := (tsubst0_tshift0_Ty_reflection_ind S4 H0).
  Definition tsubstPat0_tshiftPat0_reflection (p11 : Pat) : (forall (S3 : Ty) ,
    ((tsubstPat X0 S3 (tshiftPat C0 p11)) =
    p11)) := (tsubst0_tshift0_Pat_reflection_ind p11 H0).
  Definition substTm0_shiftTm0_reflection (s1 : Tm) : (forall (s0 : Tm) ,
    ((substTm X0 s0 (shiftTm C0 s1)) =
    s1)) := (subst0_shift0_Tm_reflection_ind s1 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s0 : Tm) : (forall (S3 : Ty) ,
    ((tsubstTm X0 S3 (tshiftTm C0 s0)) =
    s0)) := (tsubst0_tshift0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff tm)) (x : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c0) k) (shiftIndex (weakenCutofftm C0 k) x)) =
        (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c0 k) x)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff ty)) (X : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c0) k) (tshiftIndex (weakenCutoffty C0 k) X)) =
        (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c0 k) X)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Definition tshift_tshift0_Ty_comm_ind := (ind_Ty (fun (S1 : Ty) =>
      (forall (k4 : Hvl) (c5 : (Cutoff ty)) ,
        ((tshiftTy (weakenCutoffty (CS c5) k4) (tshiftTy (weakenCutoffty C0 k4) S1)) =
        (tshiftTy (weakenCutoffty C0 k4) (tshiftTy (weakenCutoffty c5 k4) S1))))) (fun (X8 : (Index ty)) =>
      (fun (k4 : Hvl) (c5 : (Cutoff ty)) =>
        (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k4 c5 X8)))) (fun (k4 : Hvl) (c5 : (Cutoff ty)) =>
      eq_refl) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tarr (IHT6 k4 c5) (IHT7 k4 c5))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tall (IHT6 k4 c5) (IHT7 (HS ty k4) c5))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tprod (IHT6 k4 c5) (IHT7 k4 c5)))).
    Definition tshift_tshift0_Pat_comm_ind := (ind_Pat (fun (p7 : Pat) =>
      (forall (k4 : Hvl) (c5 : (Cutoff ty)) ,
        ((tshiftPat (weakenCutoffty (CS c5) k4) (tshiftPat (weakenCutoffty C0 k4) p7)) =
        (tshiftPat (weakenCutoffty C0 k4) (tshiftPat (weakenCutoffty c5 k4) p7))))) (fun (T : Ty) (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal pvar (let IHT6 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT6 k4 c5)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 pprod (IHp0 k4 c5) (IHp3 k4 c5)))).
    Definition shift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c5 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm (CS c5) k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c5 k4) s))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c5 : (Cutoff tm)) =>
        (f_equal var (shiftIndex_shiftIndex0_comm_ind k4 c5 x10)))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt35 (HS tm k4) c5))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 app (IHt35 k4 c5) (IHt36 k4 c5))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 tabs eq_refl (IHt35 (HS ty k4) c5))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt35 k4 c5) eq_refl)) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 prod (IHt35 k4 c5) (IHt36 k4 c5))) (fun (p : Pat) (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal3 lett eq_refl (IHt35 k4 c5) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append (CS c5) k4 (bindPat p)) (f_equal2 shiftTm (weakenCutofftm_append C0 k4 (bindPat p)) eq_refl)) (eq_trans (IHt36 (appendHvl k4 (bindPat p)) c5) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k4 (bindPat p))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c5 k4 (bindPat p))) eq_refl))))))).
    Definition shift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c5 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm c5 k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (shiftTm (weakenCutofftm c5 k4) s))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c5 : (Cutoff tm)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt35 (HS tm k4) c5))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 app (IHt35 k4 c5) (IHt36 k4 c5))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 tabs eq_refl (IHt35 (HS ty k4) c5))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt35 k4 c5) eq_refl)) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 prod (IHt35 k4 c5) (IHt36 k4 c5))) (fun (p : Pat) (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal3 lett eq_refl (IHt35 k4 c5) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenCutofftm_append c5 k4 (bindPat p))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k4 (bindPat p)) eq_refl)) (eq_trans (IHt36 (appendHvl k4 (bindPat p)) c5) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k4 (bindPat p))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c5 k4 (bindPat p))) eq_refl))))))).
    Definition tshift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c5 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty c5 k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (tshiftTm (weakenCutoffty c5 k4) s))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c5 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 abs eq_refl (IHt35 (HS tm k4) c5))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 app (IHt35 k4 c5) (IHt36 k4 c5))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tabs eq_refl (IHt35 (HS ty k4) c5))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt35 k4 c5) eq_refl)) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 prod (IHt35 k4 c5) (IHt36 k4 c5))) (fun (p : Pat) (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal3 lett eq_refl (IHt35 k4 c5) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c5 k4 (bindPat p)) (f_equal2 shiftTm (weakenCutofftm_append C0 k4 (bindPat p)) eq_refl)) (eq_trans (IHt36 (appendHvl k4 (bindPat p)) c5) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k4 (bindPat p))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c5 k4 (bindPat p))) eq_refl))))))).
    Definition tshift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c5 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty (CS c5) k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c5 k4) s))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c5 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 abs (let IHT6 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT6 k4 c5)) (IHt35 (HS tm k4) c5))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 app (IHt35 k4 c5) (IHt36 k4 c5))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tabs (let IHT6 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT6 k4 c5)) (IHt35 (HS ty k4) c5))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt35 k4 c5) (let IHT6 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT6 k4 c5)))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 prod (IHt35 k4 c5) (IHt36 k4 c5))) (fun (p : Pat) (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal3 lett (let IHp := (tshift_tshift0_Pat_comm_ind p) in
      (IHp k4 c5)) (IHt35 k4 c5) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenCutoffty_append (CS c5) k4 (bindPat p))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k4 (bindPat p)) eq_refl)) (eq_trans (IHt36 (appendHvl k4 (bindPat p)) c5) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k4 (bindPat p))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c5 k4 (bindPat p))) eq_refl))))))).
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S1 : Ty) : (forall (c5 : (Cutoff ty)) ,
      ((tshiftTy (CS c5) (tshiftTy C0 S1)) =
      (tshiftTy C0 (tshiftTy c5 S1)))) := (tshift_tshift0_Ty_comm_ind S1 H0).
    Definition tshift_tshift0_Pat_comm (p7 : Pat) : (forall (c5 : (Cutoff ty)) ,
      ((tshiftPat (CS c5) (tshiftPat C0 p7)) =
      (tshiftPat C0 (tshiftPat c5 p7)))) := (tshift_tshift0_Pat_comm_ind p7 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c5 : (Cutoff tm)) ,
      ((shiftTm (CS c5) (shiftTm C0 s)) =
      (shiftTm C0 (shiftTm c5 s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c5 : (Cutoff tm)) ,
      ((shiftTm c5 (tshiftTm C0 s)) =
      (tshiftTm C0 (shiftTm c5 s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c5 : (Cutoff ty)) ,
      ((tshiftTm c5 (shiftTm C0 s)) =
      (shiftTm C0 (tshiftTm c5 s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c5 : (Cutoff ty)) ,
      ((tshiftTm (CS c5) (tshiftTm C0 s)) =
      (tshiftTm C0 (tshiftTm c5 s)))) := (tshift_tshift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite tshift_tshift0_Pat_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite tshift_tshift0_Pat_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k64 : Hvl) (c10 : (Cutoff ty)) (S45 : Ty) ,
      ((weakenTy (tshiftTy c10 S45) k64) =
      (tshiftTy (weakenCutoffty c10 k64) (weakenTy S45 k64)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenPat_tshiftPat  :
    (forall (k64 : Hvl) (c10 : (Cutoff ty)) (p30 : Pat) ,
      ((weakenPat (tshiftPat c10 p30) k64) =
      (tshiftPat (weakenCutoffty c10 k64) (weakenPat p30 k64)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k64 : Hvl) (c10 : (Cutoff tm)) (s18 : Tm) ,
      ((weakenTm (shiftTm c10 s18) k64) =
      (shiftTm (weakenCutofftm c10 k64) (weakenTm s18 k64)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k64 : Hvl) (c10 : (Cutoff ty)) (s18 : Tm) ,
      ((weakenTm (tshiftTm c10 s18) k64) =
      (tshiftTm (weakenCutoffty c10 k64) (weakenTm s18 k64)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c5 : (Cutoff tm)) (s0 : Tm) :
      (forall (k7 : Hvl) (x16 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c5 k7) (substIndex (weakenTrace X0 k7) s0 x16)) =
        (substIndex (weakenTrace X0 k7) (shiftTm c5 s0) (shiftIndex (weakenCutofftm (CS c5) k7) x16)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c5 : (Cutoff ty)) (s0 : Tm) :
      (forall (k7 : Hvl) (x16 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c5 k7) (substIndex (weakenTrace X0 k7) s0 x16)) =
        (substIndex (weakenTrace X0 k7) (tshiftTm c5 s0) x16))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c5 : (Cutoff ty)) (S3 : Ty) :
      (forall (k7 : Hvl) (X14 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c5 k7) (tsubstIndex (weakenTrace X0 k7) S3 X14)) =
        (tsubstIndex (weakenTrace X0 k7) (tshiftTy c5 S3) (tshiftIndex (weakenCutoffty (CS c5) k7) X14)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Definition tshift_tsubst0_Ty_comm_ind := (ind_Ty (fun (S6 : Ty) =>
      (forall (k12 : Hvl) (c10 : (Cutoff ty)) (S7 : Ty) ,
        ((tshiftTy (weakenCutoffty c10 k12) (tsubstTy (weakenTrace X0 k12) S7 S6)) =
        (tsubstTy (weakenTrace X0 k12) (tshiftTy c10 S7) (tshiftTy (weakenCutoffty (CS c10) k12) S6))))) (fun (X21 : (Index ty)) =>
      (fun (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
        (tshiftTy_tsubstIndex0_comm_ind c10 S6 k12 X21))) (fun (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tarr (IHT6 k12 c10 S6) (IHT7 k12 c10 S6))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tall (IHT6 k12 c10 S6) (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT7 (HS ty k12) c10 S6) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tprod (IHT6 k12 c10 S6) (IHT7 k12 c10 S6)))).
    Definition tshift_tsubst0_Pat_comm_ind := (ind_Pat (fun (p17 : Pat) =>
      (forall (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) ,
        ((tshiftPat (weakenCutoffty c10 k12) (tsubstPat (weakenTrace X0 k12) S6 p17)) =
        (tsubstPat (weakenTrace X0 k12) (tshiftTy c10 S6) (tshiftPat (weakenCutoffty (CS c10) k12) p17))))) (fun (T : Ty) (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal pvar (let IHT6 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT6 k12 c10 S6)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 pprod (IHp0 k12 c10 S6) (IHp3 k12 c10 S6)))).
    Definition shift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c10 : (Cutoff tm)) (s3 : Tm) ,
        ((shiftTm (weakenCutofftm c10 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (shiftTm c10 s3) (shiftTm (weakenCutofftm (CS c10) k12) s2))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
        (shiftTm_substIndex0_comm_ind c10 s2 k12 x29))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c10 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 app (IHt89 k12 c10 s2) (IHt90 k12 c10 s2))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c10 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 tapp (IHt89 k12 c10 s2) eq_refl)) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 prod (IHt89 k12 c10 s2) (IHt90 k12 c10 s2))) (fun (p : Pat) (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal3 lett eq_refl (IHt89 k12 c10 s2) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append c10 k12 (bindPat p)) (f_equal3 substTm (weakenTrace_append tm X0 k12 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt90 (appendHvl k12 (bindPat p)) c10 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (bindPat p))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c10) k12 (bindPat p))) eq_refl))))))).
    Definition shift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) ,
        ((shiftTm (weakenCutofftm c10 k12) (tsubstTm (weakenTrace X0 k12) S6 s2)) =
        (tsubstTm (weakenTrace X0 k12) S6 (shiftTm (weakenCutofftm c10 k12) s2))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c10 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 app (IHt89 k12 c10 S6) (IHt90 k12 c10 S6))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c10 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 tapp (IHt89 k12 c10 S6) eq_refl)) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal2 prod (IHt89 k12 c10 S6) (IHt90 k12 c10 S6))) (fun (p : Pat) (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal3 lett eq_refl (IHt89 k12 c10 S6) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenCutofftm_append c10 k12 (bindPat p))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt90 (appendHvl k12 (bindPat p)) c10 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (bindPat p))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c10 k12 (bindPat p))) eq_refl))))))).
    Definition tshift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c10 : (Cutoff ty)) (s3 : Tm) ,
        ((tshiftTm (weakenCutoffty c10 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (tshiftTm c10 s3) (tshiftTm (weakenCutoffty c10 k12) s2))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
        (tshiftTm_substIndex0_comm_ind c10 s2 k12 x29))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c10 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 app (IHt89 k12 c10 s2) (IHt90 k12 c10 s2))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c10 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tapp (IHt89 k12 c10 s2) eq_refl)) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 prod (IHt89 k12 c10 s2) (IHt90 k12 c10 s2))) (fun (p : Pat) (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal3 lett eq_refl (IHt89 k12 c10 s2) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c10 k12 (bindPat p)) (f_equal3 substTm (weakenTrace_append tm X0 k12 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt90 (appendHvl k12 (bindPat p)) c10 s2) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k12 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c10 k12 (bindPat p))) eq_refl))))))).
    Definition tshift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) ,
        ((tshiftTm (weakenCutoffty c10 k12) (tsubstTm (weakenTrace X0 k12) S6 s2)) =
        (tsubstTm (weakenTrace X0 k12) (tshiftTy c10 S6) (tshiftTm (weakenCutoffty (CS c10) k12) s2))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 abs (let IHT6 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT6 k12 c10 S6)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c10 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 app (IHt89 k12 c10 S6) (IHt90 k12 c10 S6))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tabs (let IHT6 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT6 k12 c10 S6)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c10 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tapp (IHt89 k12 c10 S6) (let IHT6 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT6 k12 c10 S6)))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 prod (IHt89 k12 c10 S6) (IHt90 k12 c10 S6))) (fun (p : Pat) (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal3 lett (let IHp := (tshift_tsubst0_Pat_comm_ind p) in
      (IHp k12 c10 S6)) (IHt89 k12 c10 S6) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenCutoffty_append c10 k12 (bindPat p))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt90 (appendHvl k12 (bindPat p)) c10 S6) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k12 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append (CS c10) k12 (bindPat p))) eq_refl))))))).
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S7 : Ty) : (forall (c10 : (Cutoff ty)) (S6 : Ty) ,
      ((tshiftTy c10 (tsubstTy X0 S6 S7)) =
      (tsubstTy X0 (tshiftTy c10 S6) (tshiftTy (CS c10) S7)))) := (tshift_tsubst0_Ty_comm_ind S7 H0).
    Definition tshiftPat_tsubstPat0_comm (p17 : Pat) : (forall (c10 : (Cutoff ty)) (S6 : Ty) ,
      ((tshiftPat c10 (tsubstPat X0 S6 p17)) =
      (tsubstPat X0 (tshiftTy c10 S6) (tshiftPat (CS c10) p17)))) := (tshift_tsubst0_Pat_comm_ind p17 H0).
    Definition shiftTm_substTm0_comm (s3 : Tm) : (forall (c10 : (Cutoff tm)) (s2 : Tm) ,
      ((shiftTm c10 (substTm X0 s2 s3)) =
      (substTm X0 (shiftTm c10 s2) (shiftTm (CS c10) s3)))) := (shift_subst0_Tm_comm_ind s3 H0).
    Definition shiftTm_tsubstTm0_comm (s2 : Tm) : (forall (c10 : (Cutoff tm)) (S6 : Ty) ,
      ((shiftTm c10 (tsubstTm X0 S6 s2)) =
      (tsubstTm X0 S6 (shiftTm c10 s2)))) := (shift_tsubst0_Tm_comm_ind s2 H0).
    Definition tshiftTm_substTm0_comm (s3 : Tm) : (forall (c10 : (Cutoff ty)) (s2 : Tm) ,
      ((tshiftTm c10 (substTm X0 s2 s3)) =
      (substTm X0 (tshiftTm c10 s2) (tshiftTm c10 s3)))) := (tshift_subst0_Tm_comm_ind s3 H0).
    Definition tshiftTm_tsubstTm0_comm (s2 : Tm) : (forall (c10 : (Cutoff ty)) (S6 : Ty) ,
      ((tshiftTm c10 (tsubstTm X0 S6 s2)) =
      (tsubstTm X0 (tshiftTy c10 S6) (tshiftTm (CS c10) s2)))) := (tshift_tsubst0_Tm_comm_ind s2 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d0 : (Trace tm)) (s2 : Tm) :
      (forall (k12 : Hvl) (x29 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d0) k12) s2 (shiftIndex (weakenCutofftm C0 k12) x29)) =
        (shiftTm (weakenCutofftm C0 k12) (substIndex (weakenTrace d0 k12) s2 x29)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d0 : (Trace tm)) (s2 : Tm) :
      (forall (k12 : Hvl) (x29 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d0) k12) s2 x29) =
        (tshiftTm (weakenCutoffty C0 k12) (substIndex (weakenTrace d0 k12) s2 x29)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d0 : (Trace ty)) (S6 : Ty) :
      (forall (k12 : Hvl) (X21 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d0) k12) S6 X21) =
        (tsubstIndex (weakenTrace d0 k12) S6 X21))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d0 : (Trace ty)) (S6 : Ty) :
      (forall (k12 : Hvl) (X21 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d0) k12) S6 (tshiftIndex (weakenCutoffty C0 k12) X21)) =
        (tshiftTy (weakenCutoffty C0 k12) (tsubstIndex (weakenTrace d0 k12) S6 X21)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Definition tsubst_tshift0_Ty_comm_ind := (ind_Ty (fun (S27 : Ty) =>
      (forall (k47 : Hvl) (d35 : (Trace ty)) (S28 : Ty) ,
        ((tsubstTy (weakenTrace (XS ty d35) k47) S28 (tshiftTy (weakenCutoffty C0 k47) S27)) =
        (tshiftTy (weakenCutoffty C0 k47) (tsubstTy (weakenTrace d35 k47) S28 S27))))) (fun (X28 : (Index ty)) =>
      (fun (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
        (tsubstIndex_tshiftTy0_comm_ind d35 S27 k47 X28))) (fun (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 tarr (IHT6 k47 d35 S27) (IHT7 k47 d35 S27))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 tall (IHT6 k47 d35 S27) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d35) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT7 (HS ty k47) d35 S27) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d35 k47 (HS ty H0))) eq_refl eq_refl)))))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 tprod (IHT6 k47 d35 S27) (IHT7 k47 d35 S27)))).
    Definition tsubst_tshift0_Pat_comm_ind := (ind_Pat (fun (p23 : Pat) =>
      (forall (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) ,
        ((tsubstPat (weakenTrace (XS ty d35) k47) S27 (tshiftPat (weakenCutoffty C0 k47) p23)) =
        (tshiftPat (weakenCutoffty C0 k47) (tsubstPat (weakenTrace d35 k47) S27 p23))))) (fun (T : Ty) (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal pvar (let IHT6 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT6 k47 d35 S27)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 pprod (IHp0 k47 d35 S27) (IHp3 k47 d35 S27)))).
    Definition subst_shift0_Tm_comm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k47 : Hvl) (d35 : (Trace tm)) (s17 : Tm) ,
        ((substTm (weakenTrace (XS tm d35) k47) s17 (shiftTm (weakenCutofftm C0 k47) s16)) =
        (shiftTm (weakenCutofftm C0 k47) (substTm (weakenTrace d35 k47) s17 s16))))) (fun (x42 : (Index tm)) =>
      (fun (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
        (substIndex_shiftTm0_comm_ind d35 s16 k47 x42))) (fun (T : Ty) (t : Tm) IHt125 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d35) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k47) d35 s16) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d35 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 app (IHt125 k47 d35 s16) (IHt126 k47 d35 s16))) (fun (T : Ty) (t : Tm) IHt125 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d35) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k47) d35 s16) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d35 k47 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 tapp (IHt125 k47 d35 s16) eq_refl)) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 prod (IHt125 k47 d35 s16) (IHt126 k47 d35 s16))) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal3 lett eq_refl (IHt125 k47 d35 s16) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d35) k47 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k47 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k47 (bindPat p)) d35 s16) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k47 (bindPat p))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d35 k47 (bindPat p))) eq_refl eq_refl))))))).
    Definition subst_tshift0_Tm_comm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k47 : Hvl) (d35 : (Trace tm)) (s17 : Tm) ,
        ((substTm (weakenTrace (XS ty d35) k47) s17 (tshiftTm (weakenCutoffty C0 k47) s16)) =
        (tshiftTm (weakenCutoffty C0 k47) (substTm (weakenTrace d35 k47) s17 s16))))) (fun (x42 : (Index tm)) =>
      (fun (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
        (substIndex_tshiftTm0_comm_ind d35 s16 k47 x42))) (fun (T : Ty) (t : Tm) IHt125 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d35) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k47) d35 s16) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d35 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 app (IHt125 k47 d35 s16) (IHt126 k47 d35 s16))) (fun (T : Ty) (t : Tm) IHt125 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d35) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k47) d35 s16) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d35 k47 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 tapp (IHt125 k47 d35 s16) eq_refl)) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 prod (IHt125 k47 d35 s16) (IHt126 k47 d35 s16))) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace tm)) (s16 : Tm) =>
      (f_equal3 lett eq_refl (IHt125 k47 d35 s16) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenTrace_append tm (XS ty d35) k47 (bindPat p))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k47 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k47 (bindPat p)) d35 s16) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k47 (bindPat p))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d35 k47 (bindPat p))) eq_refl eq_refl))))))).
    Definition tsubst_shift0_Tm_comm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) ,
        ((tsubstTm (weakenTrace d35 k47) S27 (shiftTm (weakenCutofftm C0 k47) s16)) =
        (shiftTm (weakenCutofftm C0 k47) (tsubstTm (weakenTrace d35 k47) S27 s16))))) (fun (x42 : (Index tm)) =>
      (fun (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt125 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d35 k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k47) d35 S27) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d35 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 app (IHt125 k47 d35 S27) (IHt126 k47 d35 S27))) (fun (T : Ty) (t : Tm) IHt125 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d35 k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k47) d35 S27) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d35 k47 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 tapp (IHt125 k47 d35 S27) eq_refl)) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 prod (IHt125 k47 d35 S27) (IHt126 k47 d35 S27))) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal3 lett eq_refl (IHt125 k47 d35 S27) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d35 k47 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k47 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k47 (bindPat p)) d35 S27) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k47 (bindPat p))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d35 k47 (bindPat p))) eq_refl eq_refl))))))).
    Definition tsubst_tshift0_Tm_comm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) ,
        ((tsubstTm (weakenTrace (XS ty d35) k47) S27 (tshiftTm (weakenCutoffty C0 k47) s16)) =
        (tshiftTm (weakenCutoffty C0 k47) (tsubstTm (weakenTrace d35 k47) S27 s16))))) (fun (x42 : (Index tm)) =>
      (fun (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt125 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 abs (let IHT6 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT6 k47 d35 S27)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d35) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k47) d35 S27) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d35 k47 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 app (IHt125 k47 d35 S27) (IHt126 k47 d35 S27))) (fun (T : Ty) (t : Tm) IHt125 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 tabs (let IHT6 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT6 k47 d35 S27)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d35) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k47) d35 S27) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d35 k47 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 tapp (IHt125 k47 d35 S27) (let IHT6 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT6 k47 d35 S27)))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal2 prod (IHt125 k47 d35 S27) (IHt126 k47 d35 S27))) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k47 : Hvl) (d35 : (Trace ty)) (S27 : Ty) =>
      (f_equal3 lett (let IHp := (tsubst_tshift0_Pat_comm_ind p) in
      (IHp k47 d35 S27)) (IHt125 k47 d35 S27) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenTrace_append ty (XS ty d35) k47 (bindPat p))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k47 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k47 (bindPat p)) d35 S27) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k47 (bindPat p))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d35 k47 (bindPat p))) eq_refl eq_refl))))))).
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S42 : Ty) : (forall (d49 : (Trace ty)) (S41 : Ty) ,
      ((tsubstTy (XS ty d49) S41 (tshiftTy C0 S42)) =
      (tshiftTy C0 (tsubstTy d49 S41 S42)))) := (tsubst_tshift0_Ty_comm_ind S42 H0).
    Definition tsubstPat_tshiftPat0_comm (p26 : Pat) : (forall (d49 : (Trace ty)) (S41 : Ty) ,
      ((tsubstPat (XS ty d49) S41 (tshiftPat C0 p26)) =
      (tshiftPat C0 (tsubstPat d49 S41 p26)))) := (tsubst_tshift0_Pat_comm_ind p26 H0).
    Definition substTm_shiftTm0_comm (s17 : Tm) : (forall (d49 : (Trace tm)) (s16 : Tm) ,
      ((substTm (XS tm d49) s16 (shiftTm C0 s17)) =
      (shiftTm C0 (substTm d49 s16 s17)))) := (subst_shift0_Tm_comm_ind s17 H0).
    Definition substTm_tshiftTm0_comm (s17 : Tm) : (forall (d49 : (Trace tm)) (s16 : Tm) ,
      ((substTm (XS ty d49) s16 (tshiftTm C0 s17)) =
      (tshiftTm C0 (substTm d49 s16 s17)))) := (subst_tshift0_Tm_comm_ind s17 H0).
    Definition tsubstTm_shiftTm0_comm (s16 : Tm) : (forall (d49 : (Trace ty)) (S41 : Ty) ,
      ((tsubstTm d49 S41 (shiftTm C0 s16)) =
      (shiftTm C0 (tsubstTm d49 S41 s16)))) := (tsubst_shift0_Tm_comm_ind s16 H0).
    Definition tsubstTm_tshiftTm0_comm (s16 : Tm) : (forall (d49 : (Trace ty)) (S41 : Ty) ,
      ((tsubstTm (XS ty d49) S41 (tshiftTm C0 s16)) =
      (tshiftTm C0 (tsubstTm d49 S41 s16)))) := (tsubst_tshift0_Tm_comm_ind s16 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Definition tsubst_tm_Ty_ind := (ind_Ty (fun (S41 : Ty) =>
      (forall (k61 : Hvl) (d49 : (Trace ty)) (S42 : Ty) ,
        ((tsubstTy (weakenTrace (XS tm d49) k61) S42 S41) =
        (tsubstTy (weakenTrace d49 k61) S42 S41)))) (fun (X32 : (Index ty)) =>
      (fun (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
        (tsubstIndex_shiftTy0_comm_ind d49 S41 k61 X32))) (fun (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal2 tarr (IHT6 k61 d49 S41) (IHT7 k61 d49 S41))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal2 tall (IHT6 k61 d49 S41) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d49) k61 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT7 (HS ty k61) d49 S41) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d49 k61 (HS ty H0))) eq_refl eq_refl))))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal2 tprod (IHT6 k61 d49 S41) (IHT7 k61 d49 S41)))).
    Definition tsubst_tm_Pat_ind := (ind_Pat (fun (p26 : Pat) =>
      (forall (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) ,
        ((tsubstPat (weakenTrace (XS tm d49) k61) S41 p26) =
        (tsubstPat (weakenTrace d49 k61) S41 p26)))) (fun (T : Ty) (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal pvar (let IHT6 := (tsubst_tm_Ty_ind T) in
      (IHT6 k61 d49 S41)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal2 pprod (IHp0 k61 d49 S41) (IHp3 k61 d49 S41)))).
    Definition tsubst_tm_Tm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) ,
        ((tsubstTm (weakenTrace (XS tm d49) k61) S41 s16) =
        (tsubstTm (weakenTrace d49 k61) S41 s16)))) (fun (x46 : (Index tm)) =>
      (fun (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt134 (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal2 abs (let IHT6 := (tsubst_tm_Ty_ind T) in
      (IHT6 k61 d49 S41)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d49) k61 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt134 (HS tm k61) d49 S41) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d49 k61 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt134 (t2 : Tm) IHt135 (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal2 app (IHt134 k61 d49 S41) (IHt135 k61 d49 S41))) (fun (T : Ty) (t : Tm) IHt134 (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal2 tabs (let IHT6 := (tsubst_tm_Ty_ind T) in
      (IHT6 k61 d49 S41)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d49) k61 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt134 (HS ty k61) d49 S41) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d49 k61 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt134 (T : Ty) (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal2 tapp (IHt134 k61 d49 S41) (let IHT6 := (tsubst_tm_Ty_ind T) in
      (IHT6 k61 d49 S41)))) (fun (t1 : Tm) IHt134 (t2 : Tm) IHt135 (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal2 prod (IHt134 k61 d49 S41) (IHt135 k61 d49 S41))) (fun (p : Pat) (t1 : Tm) IHt134 (t2 : Tm) IHt135 (k61 : Hvl) (d49 : (Trace ty)) (S41 : Ty) =>
      (f_equal3 lett (let IHp := (tsubst_tm_Pat_ind p) in
      (IHp k61 d49 S41)) (IHt134 k61 d49 S41) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d49) k61 (bindPat p)) eq_refl eq_refl) (eq_trans (IHt135 (appendHvl k61 (bindPat p)) d49 S41) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d49 k61 (bindPat p))) eq_refl eq_refl)))))).
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S42 : Ty) : (forall (d49 : (Trace ty)) (S41 : Ty) ,
      ((tsubstTy (XS tm d49) S41 S42) =
      (tsubstTy d49 S41 S42))) := (tsubst_tm_Ty_ind S42 H0).
    Definition tsubstPat_tm (p26 : Pat) : (forall (d49 : (Trace ty)) (S41 : Ty) ,
      ((tsubstPat (XS tm d49) S41 p26) =
      (tsubstPat d49 S41 p26))) := (tsubst_tm_Pat_ind p26 H0).
    Definition tsubstTm_tm (s16 : Tm) : (forall (d49 : (Trace ty)) (S41 : Ty) ,
      ((tsubstTm (XS tm d49) S41 s16) =
      (tsubstTm d49 S41 s16))) := (tsubst_tm_Tm_ind s16 H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite tsubstPat0_tshiftPat0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite tsubstPat0_tshiftPat0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite tsubstPat_tshiftPat0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite tsubstPat_tshiftPat0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstPat_tm tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstPat_tm tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite tshiftPat_tsubstPat0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite tshiftPat_tsubstPat0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d49 : (Trace tm)) (s16 : Tm) (s17 : Tm) :
      (forall (k61 : Hvl) (x46 : (Index tm)) ,
        ((substTm (weakenTrace d49 k61) s16 (substIndex (weakenTrace X0 k61) s17 x46)) =
        (substTm (weakenTrace X0 k61) (substTm d49 s16 s17) (substIndex (weakenTrace (XS tm d49) k61) s16 x46)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d49 : (Trace ty)) (S41 : Ty) (s16 : Tm) :
      (forall (k61 : Hvl) (x46 : (Index tm)) ,
        ((tsubstTm (weakenTrace d49 k61) S41 (substIndex (weakenTrace X0 k61) s16 x46)) =
        (substIndex (weakenTrace X0 k61) (tsubstTm d49 S41 s16) x46))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d49 : (Trace ty)) (S41 : Ty) (S42 : Ty) :
      (forall (k61 : Hvl) (X32 : (Index ty)) ,
        ((tsubstTy (weakenTrace d49 k61) S41 (tsubstIndex (weakenTrace X0 k61) S42 X32)) =
        (tsubstTy (weakenTrace X0 k61) (tsubstTy d49 S41 S42) (tsubstIndex (weakenTrace (XS ty d49) k61) S41 X32)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d49 : (Trace tm)) (s16 : Tm) (S41 : Ty) :
      (forall (k61 : Hvl) (x46 : (Index tm)) ,
        ((substIndex (weakenTrace d49 k61) s16 x46) =
        (tsubstTm (weakenTrace X0 k61) S41 (substIndex (weakenTrace (XS ty d49) k61) s16 x46)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition tsubst_tsubst0_Ty_comm_ind := (ind_Ty (fun (S45 : Ty) =>
      (forall (k64 : Hvl) (d52 : (Trace ty)) (S46 : Ty) (S47 : Ty) ,
        ((tsubstTy (weakenTrace d52 k64) S46 (tsubstTy (weakenTrace X0 k64) S47 S45)) =
        (tsubstTy (weakenTrace X0 k64) (tsubstTy d52 S46 S47) (tsubstTy (weakenTrace (XS ty d52) k64) S46 S45))))) (fun (X37 : (Index ty)) =>
      (fun (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
        (tsubstTy_tsubstIndex0_commright_ind d52 S45 S46 k64 X37))) (fun (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal2 tarr (IHT6 k64 d52 S45 S46) (IHT7 k64 d52 S45 S46))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal2 tall (IHT6 k64 d52 S45 S46) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d52 k64 (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k64 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT7 (HS ty k64) d52 S45 S46) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k64 (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d52) k64 (HS ty H0))) eq_refl eq_refl)))))) (fun (T1 : Ty) IHT6 (T2 : Ty) IHT7 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal2 tprod (IHT6 k64 d52 S45 S46) (IHT7 k64 d52 S45 S46)))).
    Definition tsubst_tsubst0_Pat_comm_ind := (ind_Pat (fun (p30 : Pat) =>
      (forall (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) ,
        ((tsubstPat (weakenTrace d52 k64) S45 (tsubstPat (weakenTrace X0 k64) S46 p30)) =
        (tsubstPat (weakenTrace X0 k64) (tsubstTy d52 S45 S46) (tsubstPat (weakenTrace (XS ty d52) k64) S45 p30))))) (fun (T : Ty) (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal pvar (let IHT6 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT6 k64 d52 S45 S46)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal2 pprod (IHp0 k64 d52 S45 S46) (IHp3 k64 d52 S45 S46)))).
    Definition subst_subst0_Tm_comm_ind := (ind_Tm (fun (s18 : Tm) =>
      (forall (k64 : Hvl) (d52 : (Trace tm)) (s19 : Tm) (s20 : Tm) ,
        ((substTm (weakenTrace d52 k64) s19 (substTm (weakenTrace X0 k64) s20 s18)) =
        (substTm (weakenTrace X0 k64) (substTm d52 s19 s20) (substTm (weakenTrace (XS tm d52) k64) s19 s18))))) (fun (x53 : (Index tm)) =>
      (fun (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
        (substTm_substIndex0_commright_ind d52 s18 s19 k64 x53))) (fun (T : Ty) (t : Tm) IHt152 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d52 k64 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k64 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k64) d52 s18 s19) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k64 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d52) k64 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal2 app (IHt152 k64 d52 s18 s19) (IHt153 k64 d52 s18 s19))) (fun (T : Ty) (t : Tm) IHt152 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d52 k64 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k64 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k64) d52 s18 s19) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k64 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d52) k64 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal2 tapp (IHt152 k64 d52 s18 s19) eq_refl)) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal2 prod (IHt152 k64 d52 s18 s19) (IHt153 k64 d52 s18 s19))) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal3 lett eq_refl (IHt152 k64 d52 s18 s19) (eq_trans (f_equal3 substTm (weakenTrace_append tm d52 k64 (bindPat p)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k64 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k64 (bindPat p)) d52 s18 s19) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k64 (bindPat p))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d52) k64 (bindPat p))) eq_refl eq_refl))))))).
    Definition subst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s18 : Tm) =>
      (forall (k64 : Hvl) (d52 : (Trace tm)) (s19 : Tm) (S45 : Ty) ,
        ((substTm (weakenTrace d52 k64) s19 (tsubstTm (weakenTrace X0 k64) S45 s18)) =
        (tsubstTm (weakenTrace X0 k64) S45 (substTm (weakenTrace (XS ty d52) k64) s19 s18))))) (fun (x53 : (Index tm)) =>
      (fun (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (S45 : Ty) =>
        (substTy_tsubstIndex0_commleft_ind d52 s18 S45 k64 x53))) (fun (T : Ty) (t : Tm) IHt152 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (S45 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d52 k64 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k64 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k64) d52 s18 S45) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k64 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d52) k64 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (S45 : Ty) =>
      (f_equal2 app (IHt152 k64 d52 s18 S45) (IHt153 k64 d52 s18 S45))) (fun (T : Ty) (t : Tm) IHt152 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (S45 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d52 k64 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k64 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k64) d52 s18 S45) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k64 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d52) k64 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (S45 : Ty) =>
      (f_equal2 tapp (IHt152 k64 d52 s18 S45) eq_refl)) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (S45 : Ty) =>
      (f_equal2 prod (IHt152 k64 d52 s18 S45) (IHt153 k64 d52 s18 S45))) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (S45 : Ty) =>
      (f_equal3 lett eq_refl (IHt152 k64 d52 s18 S45) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenTrace_append tm d52 k64 (bindPat p))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k64 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k64 (bindPat p)) d52 s18 S45) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k64 (bindPat p))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d52) k64 (bindPat p))) eq_refl eq_refl))))))).
    Definition tsubst_subst0_Tm_comm_ind := (ind_Tm (fun (s18 : Tm) =>
      (forall (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (s19 : Tm) ,
        ((tsubstTm (weakenTrace d52 k64) S45 (substTm (weakenTrace X0 k64) s19 s18)) =
        (substTm (weakenTrace X0 k64) (tsubstTm d52 S45 s19) (tsubstTm (weakenTrace d52 k64) S45 s18))))) (fun (x53 : (Index tm)) =>
      (fun (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (s18 : Tm) =>
        (tsubstTm_substIndex0_commright_ind d52 S45 s18 k64 x53))) (fun (T : Ty) (t : Tm) IHt152 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (s18 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d52 k64 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k64 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k64) d52 S45 s18) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k64 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d52 k64 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (s18 : Tm) =>
      (f_equal2 app (IHt152 k64 d52 S45 s18) (IHt153 k64 d52 S45 s18))) (fun (T : Ty) (t : Tm) IHt152 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (s18 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d52 k64 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k64 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k64) d52 S45 s18) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k64 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d52 k64 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (s18 : Tm) =>
      (f_equal2 tapp (IHt152 k64 d52 S45 s18) eq_refl)) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (s18 : Tm) =>
      (f_equal2 prod (IHt152 k64 d52 S45 s18) (IHt153 k64 d52 S45 s18))) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (s18 : Tm) =>
      (f_equal3 lett eq_refl (IHt152 k64 d52 S45 s18) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d52 k64 (bindPat p)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k64 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k64 (bindPat p)) d52 S45 s18) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k64 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d52 k64 (bindPat p))) eq_refl eq_refl))))))).
    Definition tsubst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s18 : Tm) =>
      (forall (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) ,
        ((tsubstTm (weakenTrace d52 k64) S45 (tsubstTm (weakenTrace X0 k64) S46 s18)) =
        (tsubstTm (weakenTrace X0 k64) (tsubstTy d52 S45 S46) (tsubstTm (weakenTrace (XS ty d52) k64) S45 s18))))) (fun (x53 : (Index tm)) =>
      (fun (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt152 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal2 abs (let IHT6 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT6 k64 d52 S45 S46)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d52 k64 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k64 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k64) d52 S45 S46) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k64 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d52) k64 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal2 app (IHt152 k64 d52 S45 S46) (IHt153 k64 d52 S45 S46))) (fun (T : Ty) (t : Tm) IHt152 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal2 tabs (let IHT6 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT6 k64 d52 S45 S46)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d52 k64 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k64 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k64) d52 S45 S46) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k64 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d52) k64 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal2 tapp (IHt152 k64 d52 S45 S46) (let IHT6 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT6 k64 d52 S45 S46)))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal2 prod (IHt152 k64 d52 S45 S46) (IHt153 k64 d52 S45 S46))) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) =>
      (f_equal3 lett (let IHp := (tsubst_tsubst0_Pat_comm_ind p) in
      (IHp k64 d52 S45 S46)) (IHt152 k64 d52 S45 S46) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenTrace_append ty d52 k64 (bindPat p))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k64 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k64 (bindPat p)) d52 S45 S46) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k64 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d52) k64 (bindPat p))) eq_refl eq_refl))))))).
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S47 : Ty) : (forall (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) ,
      ((tsubstTy d52 S45 (tsubstTy X0 S46 S47)) =
      (tsubstTy X0 (tsubstTy d52 S45 S46) (tsubstTy (XS ty d52) S45 S47)))) := (tsubst_tsubst0_Ty_comm_ind S47 H0).
    Definition tsubstPat_tsubstPat0_comm (p30 : Pat) : (forall (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) ,
      ((tsubstPat d52 S45 (tsubstPat X0 S46 p30)) =
      (tsubstPat X0 (tsubstTy d52 S45 S46) (tsubstPat (XS ty d52) S45 p30)))) := (tsubst_tsubst0_Pat_comm_ind p30 H0).
    Definition substTm_substTm0_comm (s20 : Tm) : (forall (d52 : (Trace tm)) (s18 : Tm) (s19 : Tm) ,
      ((substTm d52 s18 (substTm X0 s19 s20)) =
      (substTm X0 (substTm d52 s18 s19) (substTm (XS tm d52) s18 s20)))) := (subst_subst0_Tm_comm_ind s20 H0).
    Definition substTm_tsubstTm0_comm (s19 : Tm) : (forall (d52 : (Trace tm)) (s18 : Tm) (S45 : Ty) ,
      ((substTm d52 s18 (tsubstTm X0 S45 s19)) =
      (tsubstTm X0 S45 (substTm (XS ty d52) s18 s19)))) := (subst_tsubst0_Tm_comm_ind s19 H0).
    Definition tsubstTm_substTm0_comm (s19 : Tm) : (forall (d52 : (Trace ty)) (S45 : Ty) (s18 : Tm) ,
      ((tsubstTm d52 S45 (substTm X0 s18 s19)) =
      (substTm X0 (tsubstTm d52 S45 s18) (tsubstTm d52 S45 s19)))) := (tsubst_subst0_Tm_comm_ind s19 H0).
    Definition tsubstTm_tsubstTm0_comm (s18 : Tm) : (forall (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) ,
      ((tsubstTm d52 S45 (tsubstTm X0 S46 s18)) =
      (tsubstTm X0 (tsubstTy d52 S45 S46) (tsubstTm (XS ty d52) S45 s18)))) := (tsubst_tsubst0_Tm_comm_ind s18 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (S46 : Ty) ,
        ((weakenTy (tsubstTy d52 S45 S46) k64) =
        (tsubstTy (weakenTrace d52 k64) S45 (weakenTy S46 k64)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPat_tsubstPat  :
      (forall (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (p30 : Pat) ,
        ((weakenPat (tsubstPat d52 S45 p30) k64) =
        (tsubstPat (weakenTrace d52 k64) S45 (weakenPat p30 k64)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k64 : Hvl) (d52 : (Trace tm)) (s18 : Tm) (s19 : Tm) ,
        ((weakenTm (substTm d52 s18 s19) k64) =
        (substTm (weakenTrace d52 k64) s18 (weakenTm s19 k64)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k64 : Hvl) (d52 : (Trace ty)) (S45 : Ty) (s18 : Tm) ,
        ((weakenTm (tsubstTm d52 S45 s18) k64) =
        (tsubstTm (weakenTrace d52 k64) S45 (weakenTm s18 k64)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenTy_append  :
      (forall (S45 : Ty) (k64 : Hvl) (k65 : Hvl) ,
        ((weakenTy (weakenTy S45 k64) k65) =
        (weakenTy S45 (appendHvl k64 k65)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenPat_append  :
      (forall (p30 : Pat) (k64 : Hvl) (k65 : Hvl) ,
        ((weakenPat (weakenPat p30 k64) k65) =
        (weakenPat p30 (appendHvl k64 k65)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s18 : Tm) (k64 : Hvl) (k65 : Hvl) ,
        ((weakenTm (weakenTm s18 k64) k65) =
        (weakenTm s18 (appendHvl k64 k65)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
  End WeakenAppend.
End SubstSubstInteraction.
 Hint Rewrite tsubstPat_tsubstPat0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite tsubstPat_tsubstPat0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenPat_tshiftPat weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenPat_tsubstPat weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
Section WellFormed.
  Fixpoint wfindex {a : Namespace} (k64 : Hvl) (i : (Index a)) {struct k64} : Prop :=
    match k64 with
      | (H0) => False
      | (HS b k64) => match (eq_namespace_dec a b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k64 i)
        end
        | (right n) => (wfindex k64 i)
      end
    end.
  Inductive wfTy (k64 : Hvl) : Ty -> Prop :=
    | wfTy_tvar {X43 : (Index ty)}
        (wfi : (wfindex k64 X43)) :
        (wfTy k64 (tvar X43))
    | wfTy_top : (wfTy k64 (top))
    | wfTy_tarr {T105 : Ty}
        (wf : (wfTy k64 T105))
        {T106 : Ty}
        (wf0 : (wfTy k64 T106)) :
        (wfTy k64 (tarr T105 T106))
    | wfTy_tall {T107 : Ty}
        (wf : (wfTy k64 T107))
        {T108 : Ty}
        (wf0 : (wfTy (HS ty k64) T108))
        : (wfTy k64 (tall T107 T108))
    | wfTy_tprod {T109 : Ty}
        (wf : (wfTy k64 T109))
        {T110 : Ty}
        (wf0 : (wfTy k64 T110)) :
        (wfTy k64 (tprod T109 T110)).
  Inductive wfPat (k64 : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T105 : Ty}
        (wf : (wfTy k64 T105)) :
        (wfPat k64 (pvar T105))
    | wfPat_pprod {p34 : Pat}
        (wf : (wfPat k64 p34))
        {p35 : Pat}
        (wf0 : (wfPat k64 p35)) :
        (wfPat k64 (pprod p34 p35)).
  Inductive wfTm (k64 : Hvl) : Tm -> Prop :=
    | wfTm_var {x59 : (Index tm)}
        (wfi : (wfindex k64 x59)) :
        (wfTm k64 (var x59))
    | wfTm_abs {T105 : Ty}
        (wf : (wfTy k64 T105))
        {t170 : Tm}
        (wf0 : (wfTm (HS tm k64) t170))
        : (wfTm k64 (abs T105 t170))
    | wfTm_app {t171 : Tm}
        (wf : (wfTm k64 t171))
        {t172 : Tm}
        (wf0 : (wfTm k64 t172)) :
        (wfTm k64 (app t171 t172))
    | wfTm_tabs {T106 : Ty}
        (wf : (wfTy k64 T106))
        {t173 : Tm}
        (wf0 : (wfTm (HS ty k64) t173))
        : (wfTm k64 (tabs T106 t173))
    | wfTm_tapp {t174 : Tm}
        (wf : (wfTm k64 t174))
        {T107 : Ty}
        (wf0 : (wfTy k64 T107)) :
        (wfTm k64 (tapp t174 T107))
    | wfTm_prod {t175 : Tm}
        (wf : (wfTm k64 t175))
        {t176 : Tm}
        (wf0 : (wfTm k64 t176)) :
        (wfTm k64 (prod t175 t176))
    | wfTm_lett {p34 : Pat}
        (wf : (wfPat k64 p34))
        {t177 : Tm}
        (wf0 : (wfTm k64 t177))
        {t178 : Tm}
        (wf1 : (wfTm (appendHvl k64 (bindPat p34)) t178))
        :
        (wfTm k64 (lett p34 t177 t178)).
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c13 : (Cutoff tm)) (k64 : Hvl) (k65 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k64 : Hvl)
        :
        (shifthvl_tm C0 k64 (HS tm k64))
    | shifthvl_tm_there_tm
        (c13 : (Cutoff tm)) (k64 : Hvl)
        (k65 : Hvl) :
        (shifthvl_tm c13 k64 k65) -> (shifthvl_tm (CS c13) (HS tm k64) (HS tm k65))
    | shifthvl_tm_there_ty
        (c13 : (Cutoff tm)) (k64 : Hvl)
        (k65 : Hvl) :
        (shifthvl_tm c13 k64 k65) -> (shifthvl_tm c13 (HS ty k64) (HS ty k65)).
  Inductive shifthvl_ty : (forall (c13 : (Cutoff ty)) (k64 : Hvl) (k65 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k64 : Hvl)
        :
        (shifthvl_ty C0 k64 (HS ty k64))
    | shifthvl_ty_there_tm
        (c13 : (Cutoff ty)) (k64 : Hvl)
        (k65 : Hvl) :
        (shifthvl_ty c13 k64 k65) -> (shifthvl_ty c13 (HS tm k64) (HS tm k65))
    | shifthvl_ty_there_ty
        (c13 : (Cutoff ty)) (k64 : Hvl)
        (k65 : Hvl) :
        (shifthvl_ty c13 k64 k65) -> (shifthvl_ty (CS c13) (HS ty k64) (HS ty k65)).
  Lemma weaken_shifthvl_tm  :
    (forall (k64 : Hvl) {c13 : (Cutoff tm)} {k65 : Hvl} {k66 : Hvl} ,
      (shifthvl_tm c13 k65 k66) -> (shifthvl_tm (weakenCutofftm c13 k64) (appendHvl k65 k64) (appendHvl k66 k64))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k64 : Hvl) {c13 : (Cutoff ty)} {k65 : Hvl} {k66 : Hvl} ,
      (shifthvl_ty c13 k65 k66) -> (shifthvl_ty (weakenCutoffty c13 k64) (appendHvl k65 k64) (appendHvl k66 k64))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c13 : (Cutoff tm)) (k64 : Hvl) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) (x59 : (Index tm)) ,
      (wfindex k64 x59) -> (wfindex k65 (shiftIndex c13 x59))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c13 : (Cutoff tm)) (k64 : Hvl) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) (X43 : (Index ty)) ,
      (wfindex k64 X43) -> (wfindex k65 X43)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c13 : (Cutoff ty)) (k64 : Hvl) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) (x59 : (Index tm)) ,
      (wfindex k64 x59) -> (wfindex k65 x59)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c13 : (Cutoff ty)) (k64 : Hvl) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) (X43 : (Index ty)) ,
      (wfindex k64 X43) -> (wfindex k65 (tshiftIndex c13 X43))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k64 : Hvl) ,
    (forall (S45 : Ty) (wf : (wfTy k64 S45)) ,
      (forall (c13 : (Cutoff tm)) (k65 : Hvl) ,
        (shifthvl_tm c13 k64 k65) -> (wfTy k65 S45)))) := (ind_wfTy (fun (k64 : Hvl) (S45 : Ty) (wf : (wfTy k64 S45)) =>
    (forall (c13 : (Cutoff tm)) (k65 : Hvl) ,
      (shifthvl_tm c13 k64 k65) -> (wfTy k65 S45))) (fun (k64 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k64 X43)) (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTy_tvar k65 (shift_wfindex_ty c13 k64 k65 ins X43 wfi))) (fun (k64 : Hvl) (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTy_top k65)) (fun (k64 : Hvl) (T1 : Ty) (wf : (wfTy k64 T1)) IHT6 (T2 : Ty) (wf0 : (wfTy k64 T2)) IHT7 (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTy_tarr k65 (IHT6 c13 k65 (weaken_shifthvl_tm H0 ins)) (IHT7 c13 k65 (weaken_shifthvl_tm H0 ins)))) (fun (k64 : Hvl) (T1 : Ty) (wf : (wfTy k64 T1)) IHT6 (T2 : Ty) (wf0 : (wfTy (HS ty k64) T2)) IHT7 (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTy_tall k65 (IHT6 c13 k65 (weaken_shifthvl_tm H0 ins)) (IHT7 c13 (HS ty k65) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k64 : Hvl) (T1 : Ty) (wf : (wfTy k64 T1)) IHT6 (T2 : Ty) (wf0 : (wfTy k64 T2)) IHT7 (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTy_tprod k65 (IHT6 c13 k65 (weaken_shifthvl_tm H0 ins)) (IHT7 c13 k65 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTy : (forall (k64 : Hvl) ,
    (forall (S45 : Ty) (wf : (wfTy k64 S45)) ,
      (forall (c13 : (Cutoff ty)) (k65 : Hvl) ,
        (shifthvl_ty c13 k64 k65) -> (wfTy k65 (tshiftTy c13 S45))))) := (ind_wfTy (fun (k64 : Hvl) (S45 : Ty) (wf : (wfTy k64 S45)) =>
    (forall (c13 : (Cutoff ty)) (k65 : Hvl) ,
      (shifthvl_ty c13 k64 k65) -> (wfTy k65 (tshiftTy c13 S45)))) (fun (k64 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k64 X43)) (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTy_tvar k65 (tshift_wfindex_ty c13 k64 k65 ins X43 wfi))) (fun (k64 : Hvl) (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTy_top k65)) (fun (k64 : Hvl) (T1 : Ty) (wf : (wfTy k64 T1)) IHT6 (T2 : Ty) (wf0 : (wfTy k64 T2)) IHT7 (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTy_tarr k65 (IHT6 c13 k65 (weaken_shifthvl_ty H0 ins)) (IHT7 c13 k65 (weaken_shifthvl_ty H0 ins)))) (fun (k64 : Hvl) (T1 : Ty) (wf : (wfTy k64 T1)) IHT6 (T2 : Ty) (wf0 : (wfTy (HS ty k64) T2)) IHT7 (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTy_tall k65 (IHT6 c13 k65 (weaken_shifthvl_ty H0 ins)) (IHT7 (CS c13) (HS ty k65) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k64 : Hvl) (T1 : Ty) (wf : (wfTy k64 T1)) IHT6 (T2 : Ty) (wf0 : (wfTy k64 T2)) IHT7 (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTy_tprod k65 (IHT6 c13 k65 (weaken_shifthvl_ty H0 ins)) (IHT7 c13 k65 (weaken_shifthvl_ty H0 ins))))).
  Definition shift_wfPat : (forall (k64 : Hvl) ,
    (forall (p34 : Pat) (wf : (wfPat k64 p34)) ,
      (forall (c13 : (Cutoff tm)) (k65 : Hvl) ,
        (shifthvl_tm c13 k64 k65) -> (wfPat k65 p34)))) := (fun (k64 : Hvl) =>
    (ind_wfPat k64 (fun (p34 : Pat) (wf : (wfPat k64 p34)) =>
      (forall (c13 : (Cutoff tm)) (k65 : Hvl) ,
        (shifthvl_tm c13 k64 k65) -> (wfPat k65 p34))) (fun (T : Ty) (wf : (wfTy k64 T)) (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
      (wfPat_pvar k65 (shift_wfTy k64 T wf c13 k65 (weaken_shifthvl_tm H0 ins)))) (fun (p1 : Pat) (wf : (wfPat k64 p1)) IHp0 (p2 : Pat) (wf0 : (wfPat k64 p2)) IHp3 (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
      (wfPat_pprod k65 (IHp0 c13 k65 (weaken_shifthvl_tm H0 ins)) (IHp3 c13 k65 (weaken_shifthvl_tm H0 ins)))))).
  Definition tshift_wfPat : (forall (k64 : Hvl) ,
    (forall (p34 : Pat) (wf : (wfPat k64 p34)) ,
      (forall (c13 : (Cutoff ty)) (k65 : Hvl) ,
        (shifthvl_ty c13 k64 k65) -> (wfPat k65 (tshiftPat c13 p34))))) := (fun (k64 : Hvl) =>
    (ind_wfPat k64 (fun (p34 : Pat) (wf : (wfPat k64 p34)) =>
      (forall (c13 : (Cutoff ty)) (k65 : Hvl) ,
        (shifthvl_ty c13 k64 k65) -> (wfPat k65 (tshiftPat c13 p34)))) (fun (T : Ty) (wf : (wfTy k64 T)) (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
      (wfPat_pvar k65 (tshift_wfTy k64 T wf c13 k65 (weaken_shifthvl_ty H0 ins)))) (fun (p1 : Pat) (wf : (wfPat k64 p1)) IHp0 (p2 : Pat) (wf0 : (wfPat k64 p2)) IHp3 (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
      (wfPat_pprod k65 (IHp0 c13 k65 (weaken_shifthvl_ty H0 ins)) (IHp3 c13 k65 (weaken_shifthvl_ty H0 ins)))))).
  Definition shift_wfTm : (forall (k64 : Hvl) ,
    (forall (s18 : Tm) (wf : (wfTm k64 s18)) ,
      (forall (c13 : (Cutoff tm)) (k65 : Hvl) ,
        (shifthvl_tm c13 k64 k65) -> (wfTm k65 (shiftTm c13 s18))))) := (ind_wfTm (fun (k64 : Hvl) (s18 : Tm) (wf : (wfTm k64 s18)) =>
    (forall (c13 : (Cutoff tm)) (k65 : Hvl) ,
      (shifthvl_tm c13 k64 k65) -> (wfTm k65 (shiftTm c13 s18)))) (fun (k64 : Hvl) (x59 : (Index tm)) (wfi : (wfindex k64 x59)) (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTm_var k65 (shift_wfindex_tm c13 k64 k65 ins x59 wfi))) (fun (k64 : Hvl) (T : Ty) (wf : (wfTy k64 T)) (t : Tm) (wf0 : (wfTm (HS tm k64) t)) IHt170 (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTm_abs k65 (shift_wfTy k64 T wf c13 k65 (weaken_shifthvl_tm H0 ins)) (IHt170 (CS c13) (HS tm k65) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k64 : Hvl) (t1 : Tm) (wf : (wfTm k64 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k64 t2)) IHt171 (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTm_app k65 (IHt170 c13 k65 (weaken_shifthvl_tm H0 ins)) (IHt171 c13 k65 (weaken_shifthvl_tm H0 ins)))) (fun (k64 : Hvl) (T : Ty) (wf : (wfTy k64 T)) (t : Tm) (wf0 : (wfTm (HS ty k64) t)) IHt170 (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTm_tabs k65 (shift_wfTy k64 T wf c13 k65 (weaken_shifthvl_tm H0 ins)) (IHt170 c13 (HS ty k65) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k64 : Hvl) (t : Tm) (wf : (wfTm k64 t)) IHt170 (T : Ty) (wf0 : (wfTy k64 T)) (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTm_tapp k65 (IHt170 c13 k65 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k64 T wf0 c13 k65 (weaken_shifthvl_tm H0 ins)))) (fun (k64 : Hvl) (t1 : Tm) (wf : (wfTm k64 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k64 t2)) IHt171 (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTm_prod k65 (IHt170 c13 k65 (weaken_shifthvl_tm H0 ins)) (IHt171 c13 k65 (weaken_shifthvl_tm H0 ins)))) (fun (k64 : Hvl) (p : Pat) (wf : (wfPat k64 p)) (t1 : Tm) (wf0 : (wfTm k64 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm (appendHvl k64 (bindPat p)) t2)) IHt171 (c13 : (Cutoff tm)) (k65 : Hvl) (ins : (shifthvl_tm c13 k64 k65)) =>
    (wfTm_lett k65 (shift_wfPat k64 p wf c13 k65 (weaken_shifthvl_tm H0 ins)) (IHt170 c13 k65 (weaken_shifthvl_tm H0 ins)) (IHt171 (weakenCutofftm c13 (bindPat p)) (appendHvl k65 (bindPat p)) (weaken_shifthvl_tm (bindPat p) ins))))).
  Definition tshift_wfTm : (forall (k64 : Hvl) ,
    (forall (s18 : Tm) (wf : (wfTm k64 s18)) ,
      (forall (c13 : (Cutoff ty)) (k65 : Hvl) ,
        (shifthvl_ty c13 k64 k65) -> (wfTm k65 (tshiftTm c13 s18))))) := (ind_wfTm (fun (k64 : Hvl) (s18 : Tm) (wf : (wfTm k64 s18)) =>
    (forall (c13 : (Cutoff ty)) (k65 : Hvl) ,
      (shifthvl_ty c13 k64 k65) -> (wfTm k65 (tshiftTm c13 s18)))) (fun (k64 : Hvl) (x59 : (Index tm)) (wfi : (wfindex k64 x59)) (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTm_var k65 (tshift_wfindex_tm c13 k64 k65 ins x59 wfi))) (fun (k64 : Hvl) (T : Ty) (wf : (wfTy k64 T)) (t : Tm) (wf0 : (wfTm (HS tm k64) t)) IHt170 (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTm_abs k65 (tshift_wfTy k64 T wf c13 k65 (weaken_shifthvl_ty H0 ins)) (IHt170 c13 (HS tm k65) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k64 : Hvl) (t1 : Tm) (wf : (wfTm k64 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k64 t2)) IHt171 (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTm_app k65 (IHt170 c13 k65 (weaken_shifthvl_ty H0 ins)) (IHt171 c13 k65 (weaken_shifthvl_ty H0 ins)))) (fun (k64 : Hvl) (T : Ty) (wf : (wfTy k64 T)) (t : Tm) (wf0 : (wfTm (HS ty k64) t)) IHt170 (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTm_tabs k65 (tshift_wfTy k64 T wf c13 k65 (weaken_shifthvl_ty H0 ins)) (IHt170 (CS c13) (HS ty k65) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k64 : Hvl) (t : Tm) (wf : (wfTm k64 t)) IHt170 (T : Ty) (wf0 : (wfTy k64 T)) (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTm_tapp k65 (IHt170 c13 k65 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k64 T wf0 c13 k65 (weaken_shifthvl_ty H0 ins)))) (fun (k64 : Hvl) (t1 : Tm) (wf : (wfTm k64 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k64 t2)) IHt171 (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTm_prod k65 (IHt170 c13 k65 (weaken_shifthvl_ty H0 ins)) (IHt171 c13 k65 (weaken_shifthvl_ty H0 ins)))) (fun (k64 : Hvl) (p : Pat) (wf : (wfPat k64 p)) (t1 : Tm) (wf0 : (wfTm k64 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm (appendHvl k64 (bindPat p)) t2)) IHt171 (c13 : (Cutoff ty)) (k65 : Hvl) (ins : (shifthvl_ty c13 k64 k65)) =>
    (wfTm_lett k65 (tshift_wfPat k64 p wf c13 k65 (weaken_shifthvl_ty H0 ins)) (IHt170 c13 k65 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k65) (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0))) eq_refl (IHt171 (weakenCutoffty c13 (bindPat p)) (appendHvl k65 (bindPat p)) (weaken_shifthvl_ty (bindPat p) ins)))))).
End ShiftWellFormed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_tm (k64 : Hvl) : (forall (d52 : (Trace tm)) (k65 : Hvl) (k66 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k64 X0 (HS tm k64) k64)
    | substhvl_tm_there_tm
        {d52 : (Trace tm)} {k65 : Hvl}
        {k66 : Hvl} :
        (substhvl_tm k64 d52 k65 k66) -> (substhvl_tm k64 (XS tm d52) (HS tm k65) (HS tm k66))
    | substhvl_tm_there_ty
        {d52 : (Trace tm)} {k65 : Hvl}
        {k66 : Hvl} :
        (substhvl_tm k64 d52 k65 k66) -> (substhvl_tm k64 (XS ty d52) (HS ty k65) (HS ty k66)).
  Inductive substhvl_ty (k64 : Hvl) : (forall (d52 : (Trace ty)) (k65 : Hvl) (k66 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k64 X0 (HS ty k64) k64)
    | substhvl_ty_there_tm
        {d52 : (Trace ty)} {k65 : Hvl}
        {k66 : Hvl} :
        (substhvl_ty k64 d52 k65 k66) -> (substhvl_ty k64 (XS tm d52) (HS tm k65) (HS tm k66))
    | substhvl_ty_there_ty
        {d52 : (Trace ty)} {k65 : Hvl}
        {k66 : Hvl} :
        (substhvl_ty k64 d52 k65 k66) -> (substhvl_ty k64 (XS ty d52) (HS ty k65) (HS ty k66)).
  Lemma weaken_substhvl_tm  :
    (forall {k65 : Hvl} (k64 : Hvl) {d52 : (Trace tm)} {k66 : Hvl} {k67 : Hvl} ,
      (substhvl_tm k65 d52 k66 k67) -> (substhvl_tm k65 (weakenTrace d52 k64) (appendHvl k66 k64) (appendHvl k67 k64))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k65 : Hvl} (k64 : Hvl) {d52 : (Trace ty)} {k66 : Hvl} {k67 : Hvl} ,
      (substhvl_ty k65 d52 k66 k67) -> (substhvl_ty k65 (weakenTrace d52 k64) (appendHvl k66 k64) (appendHvl k67 k64))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k68 : Hvl} {s18 : Tm} (wft : (wfTm k68 s18)) :
    (forall {d52 : (Trace tm)} {k69 : Hvl} {k70 : Hvl} ,
      (substhvl_tm k68 d52 k69 k70) -> (forall {x59 : (Index tm)} ,
        (wfindex k69 x59) -> (wfTm k70 (substIndex d52 s18 x59)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k68 : Hvl} {S46 : Ty} (wft : (wfTy k68 S46)) :
    (forall {d52 : (Trace ty)} {k69 : Hvl} {k70 : Hvl} ,
      (substhvl_ty k68 d52 k69 k70) -> (forall {X43 : (Index ty)} ,
        (wfindex k69 X43) -> (wfTy k70 (tsubstIndex d52 S46 X43)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k68 : Hvl} :
    (forall {d52 : (Trace tm)} {k69 : Hvl} {k70 : Hvl} ,
      (substhvl_tm k68 d52 k69 k70) -> (forall {X43 : (Index ty)} ,
        (wfindex k69 X43) -> (wfindex k70 X43))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k68 : Hvl} :
    (forall {d52 : (Trace ty)} {k69 : Hvl} {k70 : Hvl} ,
      (substhvl_ty k68 d52 k69 k70) -> (forall {x59 : (Index tm)} ,
        (wfindex k69 x59) -> (wfindex k70 x59))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k68 : Hvl} : (forall (k69 : Hvl) ,
    (forall (S46 : Ty) (wf0 : (wfTy k69 S46)) ,
      (forall {d52 : (Trace tm)} {k70 : Hvl} ,
        (substhvl_tm k68 d52 k69 k70) -> (wfTy k70 S46)))) := (ind_wfTy (fun (k69 : Hvl) (S46 : Ty) (wf0 : (wfTy k69 S46)) =>
    (forall {d52 : (Trace tm)} {k70 : Hvl} ,
      (substhvl_tm k68 d52 k69 k70) -> (wfTy k70 S46))) (fun (k69 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k69 X43)) {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTy_tvar k70 (substhvl_tm_wfindex_ty del wfi))) (fun (k69 : Hvl) {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTy_top k70)) (fun (k69 : Hvl) (T1 : Ty) (wf0 : (wfTy k69 T1)) IHT6 (T2 : Ty) (wf1 : (wfTy k69 T2)) IHT7 {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTy_tarr k70 (IHT6 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)) (IHT7 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)))) (fun (k69 : Hvl) (T1 : Ty) (wf0 : (wfTy k69 T1)) IHT6 (T2 : Ty) (wf1 : (wfTy (HS ty k69) T2)) IHT7 {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTy_tall k70 (IHT6 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)) (IHT7 (weakenTrace d52 (HS ty H0)) (HS ty k70) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k69 : Hvl) (T1 : Ty) (wf0 : (wfTy k69 T1)) IHT6 (T2 : Ty) (wf1 : (wfTy k69 T2)) IHT7 {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTy_tprod k70 (IHT6 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)) (IHT7 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTy {k68 : Hvl} {S46 : Ty} (wf : (wfTy k68 S46)) : (forall (k69 : Hvl) ,
    (forall (S47 : Ty) (wf0 : (wfTy k69 S47)) ,
      (forall {d52 : (Trace ty)} {k70 : Hvl} ,
        (substhvl_ty k68 d52 k69 k70) -> (wfTy k70 (tsubstTy d52 S46 S47))))) := (ind_wfTy (fun (k69 : Hvl) (S47 : Ty) (wf0 : (wfTy k69 S47)) =>
    (forall {d52 : (Trace ty)} {k70 : Hvl} ,
      (substhvl_ty k68 d52 k69 k70) -> (wfTy k70 (tsubstTy d52 S46 S47)))) (fun (k69 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k69 X43)) {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k69 : Hvl) {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTy_top k70)) (fun (k69 : Hvl) (T1 : Ty) (wf0 : (wfTy k69 T1)) IHT6 (T2 : Ty) (wf1 : (wfTy k69 T2)) IHT7 {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTy_tarr k70 (IHT6 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)) (IHT7 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)))) (fun (k69 : Hvl) (T1 : Ty) (wf0 : (wfTy k69 T1)) IHT6 (T2 : Ty) (wf1 : (wfTy (HS ty k69) T2)) IHT7 {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTy_tall k70 (IHT6 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)) (IHT7 (weakenTrace d52 (HS ty H0)) (HS ty k70) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k69 : Hvl) (T1 : Ty) (wf0 : (wfTy k69 T1)) IHT6 (T2 : Ty) (wf1 : (wfTy k69 T2)) IHT7 {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTy_tprod k70 (IHT6 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)) (IHT7 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del))))).
  Definition substhvl_tm_wfPat {k68 : Hvl} : (forall (k69 : Hvl) ,
    (forall (p35 : Pat) (wf0 : (wfPat k69 p35)) ,
      (forall {d52 : (Trace tm)} {k70 : Hvl} ,
        (substhvl_tm k68 d52 k69 k70) -> (wfPat k70 p35)))) := (fun (k69 : Hvl) =>
    (ind_wfPat k69 (fun (p35 : Pat) (wf0 : (wfPat k69 p35)) =>
      (forall {d52 : (Trace tm)} {k70 : Hvl} ,
        (substhvl_tm k68 d52 k69 k70) -> (wfPat k70 p35))) (fun (T : Ty) (wf0 : (wfTy k69 T)) {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
      (wfPat_pvar k70 (substhvl_tm_wfTy k69 T wf0 (weaken_substhvl_tm H0 del)))) (fun (p1 : Pat) (wf0 : (wfPat k69 p1)) IHp0 (p2 : Pat) (wf1 : (wfPat k69 p2)) IHp3 {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
      (wfPat_pprod k70 (IHp0 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)) (IHp3 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_ty_wfPat {k68 : Hvl} {S46 : Ty} (wf : (wfTy k68 S46)) : (forall (k69 : Hvl) ,
    (forall (p35 : Pat) (wf0 : (wfPat k69 p35)) ,
      (forall {d52 : (Trace ty)} {k70 : Hvl} ,
        (substhvl_ty k68 d52 k69 k70) -> (wfPat k70 (tsubstPat d52 S46 p35))))) := (fun (k69 : Hvl) =>
    (ind_wfPat k69 (fun (p35 : Pat) (wf0 : (wfPat k69 p35)) =>
      (forall {d52 : (Trace ty)} {k70 : Hvl} ,
        (substhvl_ty k68 d52 k69 k70) -> (wfPat k70 (tsubstPat d52 S46 p35)))) (fun (T : Ty) (wf0 : (wfTy k69 T)) {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
      (wfPat_pvar k70 (substhvl_ty_wfTy wf k69 T wf0 (weaken_substhvl_ty H0 del)))) (fun (p1 : Pat) (wf0 : (wfPat k69 p1)) IHp0 (p2 : Pat) (wf1 : (wfPat k69 p2)) IHp3 {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
      (wfPat_pprod k70 (IHp0 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)) (IHp3 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)))))).
  Definition substhvl_tm_wfTm {k68 : Hvl} {s18 : Tm} (wf : (wfTm k68 s18)) : (forall (k69 : Hvl) ,
    (forall (s19 : Tm) (wf0 : (wfTm k69 s19)) ,
      (forall {d52 : (Trace tm)} {k70 : Hvl} ,
        (substhvl_tm k68 d52 k69 k70) -> (wfTm k70 (substTm d52 s18 s19))))) := (ind_wfTm (fun (k69 : Hvl) (s19 : Tm) (wf0 : (wfTm k69 s19)) =>
    (forall {d52 : (Trace tm)} {k70 : Hvl} ,
      (substhvl_tm k68 d52 k69 k70) -> (wfTm k70 (substTm d52 s18 s19)))) (fun (k69 : Hvl) {x59 : (Index tm)} (wfi : (wfindex k69 x59)) {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k69 : Hvl) (T : Ty) (wf0 : (wfTy k69 T)) (t : Tm) (wf1 : (wfTm (HS tm k69) t)) IHt170 {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTm_abs k70 (substhvl_tm_wfTy k69 T wf0 (weaken_substhvl_tm H0 del)) (IHt170 (weakenTrace d52 (HS tm H0)) (HS tm k70) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k69 : Hvl) (t1 : Tm) (wf0 : (wfTm k69 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k69 t2)) IHt171 {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTm_app k70 (IHt170 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)) (IHt171 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)))) (fun (k69 : Hvl) (T : Ty) (wf0 : (wfTy k69 T)) (t : Tm) (wf1 : (wfTm (HS ty k69) t)) IHt170 {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTm_tabs k70 (substhvl_tm_wfTy k69 T wf0 (weaken_substhvl_tm H0 del)) (IHt170 (weakenTrace d52 (HS ty H0)) (HS ty k70) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k69 : Hvl) (t : Tm) (wf0 : (wfTm k69 t)) IHt170 (T : Ty) (wf1 : (wfTy k69 T)) {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTm_tapp k70 (IHt170 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k69 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k69 : Hvl) (t1 : Tm) (wf0 : (wfTm k69 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k69 t2)) IHt171 {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTm_prod k70 (IHt170 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)) (IHt171 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)))) (fun (k69 : Hvl) (p : Pat) (wf0 : (wfPat k69 p)) (t1 : Tm) (wf1 : (wfTm k69 t1)) IHt170 (t2 : Tm) (wf2 : (wfTm (appendHvl k69 (bindPat p)) t2)) IHt171 {d52 : (Trace tm)} {k70 : Hvl} (del : (substhvl_tm k68 d52 k69 k70)) =>
    (wfTm_lett k70 (substhvl_tm_wfPat k69 p wf0 (weaken_substhvl_tm H0 del)) (IHt170 (weakenTrace d52 H0) k70 (weaken_substhvl_tm H0 del)) (IHt171 (weakenTrace d52 (bindPat p)) (appendHvl k70 (bindPat p)) (weaken_substhvl_tm (bindPat p) del))))).
  Definition substhvl_ty_wfTm {k68 : Hvl} {S46 : Ty} (wf : (wfTy k68 S46)) : (forall (k69 : Hvl) ,
    (forall (s18 : Tm) (wf0 : (wfTm k69 s18)) ,
      (forall {d52 : (Trace ty)} {k70 : Hvl} ,
        (substhvl_ty k68 d52 k69 k70) -> (wfTm k70 (tsubstTm d52 S46 s18))))) := (ind_wfTm (fun (k69 : Hvl) (s18 : Tm) (wf0 : (wfTm k69 s18)) =>
    (forall {d52 : (Trace ty)} {k70 : Hvl} ,
      (substhvl_ty k68 d52 k69 k70) -> (wfTm k70 (tsubstTm d52 S46 s18)))) (fun (k69 : Hvl) {x59 : (Index tm)} (wfi : (wfindex k69 x59)) {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTm_var k70 (substhvl_ty_wfindex_tm del wfi))) (fun (k69 : Hvl) (T : Ty) (wf0 : (wfTy k69 T)) (t : Tm) (wf1 : (wfTm (HS tm k69) t)) IHt170 {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTm_abs k70 (substhvl_ty_wfTy wf k69 T wf0 (weaken_substhvl_ty H0 del)) (IHt170 (weakenTrace d52 (HS tm H0)) (HS tm k70) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k69 : Hvl) (t1 : Tm) (wf0 : (wfTm k69 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k69 t2)) IHt171 {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTm_app k70 (IHt170 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)) (IHt171 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)))) (fun (k69 : Hvl) (T : Ty) (wf0 : (wfTy k69 T)) (t : Tm) (wf1 : (wfTm (HS ty k69) t)) IHt170 {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTm_tabs k70 (substhvl_ty_wfTy wf k69 T wf0 (weaken_substhvl_ty H0 del)) (IHt170 (weakenTrace d52 (HS ty H0)) (HS ty k70) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k69 : Hvl) (t : Tm) (wf0 : (wfTm k69 t)) IHt170 (T : Ty) (wf1 : (wfTy k69 T)) {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTm_tapp k70 (IHt170 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k69 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k69 : Hvl) (t1 : Tm) (wf0 : (wfTm k69 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k69 t2)) IHt171 {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTm_prod k70 (IHt170 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)) (IHt171 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)))) (fun (k69 : Hvl) (p : Pat) (wf0 : (wfPat k69 p)) (t1 : Tm) (wf1 : (wfTm k69 t1)) IHt170 (t2 : Tm) (wf2 : (wfTm (appendHvl k69 (bindPat p)) t2)) IHt171 {d52 : (Trace ty)} {k70 : Hvl} (del : (substhvl_ty k68 d52 k69 k70)) =>
    (wfTm_lett k70 (substhvl_ty_wfPat wf k69 p wf0 (weaken_substhvl_ty H0 del)) (IHt170 (weakenTrace d52 H0) k70 (weaken_substhvl_ty H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k70) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))) eq_refl (IHt171 (weakenTrace d52 (bindPat p)) (appendHvl k70 (bindPat p)) (weaken_substhvl_ty (bindPat p) del)))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Fixpoint subhvl_tm (k68 : Hvl) {struct k68} : Prop :=
  match k68 with
    | (H0) => True
    | (HS a k68) => match a with
      | (tm) => (subhvl_tm k68)
      | _ => False
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k68 : Hvl) (k69 : Hvl) ,
    (subhvl_tm k68) -> (subhvl_tm k69) -> (subhvl_tm (appendHvl k68 k69))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfPat_strengthen_subhvl_tm  :
  (forall (k65 : Hvl) (k64 : Hvl) (p34 : Pat) ,
    (subhvl_tm k65) -> (wfPat (appendHvl k64 k65) (weakenPat p34 k65)) -> (wfPat k64 p34)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k67 : Hvl) (k66 : Hvl) (S45 : Ty) ,
    (subhvl_tm k67) -> (wfTy (appendHvl k66 k67) (weakenTy S45 k67)) -> (wfTy k66 S45)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_tm) in H
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H0 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_tm) in H0
end : infra wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G : Env) (T : Ty)
    | etvar (G : Env) (T : Ty).
  Fixpoint appendEnv (G : Env) (G0 : Env) : Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
      | (etvar G1 T) => (etvar (appendEnv G G1) T)
    end.
  Fixpoint domainEnv (G : Env) : Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS tm (domainEnv G0))
      | (etvar G0 T) => (HS ty (domainEnv G0))
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
  Fixpoint shiftEnv (c13 : (Cutoff tm)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftEnv c13 G0) T)
      | (etvar G0 T) => (etvar (shiftEnv c13 G0) T)
    end.
  Fixpoint tshiftEnv (c13 : (Cutoff ty)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c13 G0) (tshiftTy (weakenCutoffty c13 (domainEnv G0)) T))
      | (etvar G0 T) => (etvar (tshiftEnv c13 G0) (tshiftTy (weakenCutoffty c13 (domainEnv G0)) T))
    end.
  Fixpoint substEnv (d52 : (Trace tm)) (s18 : Tm) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d52 s18 G0) T)
      | (etvar G0 T) => (etvar (substEnv d52 s18 G0) T)
    end.
  Fixpoint tsubstEnv (d52 : (Trace ty)) (S46 : Ty) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d52 S46 G0) (tsubstTy (weakenTrace d52 (domainEnv G0)) S46 T))
      | (etvar G0 T) => (etvar (tsubstEnv d52 S46 G0) (tsubstTy (weakenTrace d52 (domainEnv G0)) S46 T))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c13 : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c13 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c13 : (Cutoff ty)) (G : Env) ,
      ((domainEnv (tshiftEnv c13 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d52 : (Trace tm)) (s18 : Tm) (G : Env) ,
      ((domainEnv (substEnv d52 s18 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d52 : (Trace ty)) (S46 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d52 S46 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c13 : (Cutoff tm)) (G : Env) (G0 : Env) ,
        ((shiftEnv c13 (appendEnv G G0)) =
        (appendEnv (shiftEnv c13 G) (shiftEnv (weakenCutofftm c13 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftEnv_appendEnv  :
      (forall (c13 : (Cutoff ty)) (G : Env) (G0 : Env) ,
        ((tshiftEnv c13 (appendEnv G G0)) =
        (appendEnv (tshiftEnv c13 G) (tshiftEnv (weakenCutoffty c13 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d52 : (Trace tm)) (s18 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d52 s18 (appendEnv G G0)) =
        (appendEnv (substEnv d52 s18 G) (substEnv (weakenTrace d52 (domainEnv G)) s18 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d52 : (Trace ty)) (S46 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d52 S46 (appendEnv G G0)) =
        (appendEnv (tsubstEnv d52 S46 G) (tsubstEnv (weakenTrace d52 (domainEnv G)) S46 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          {T105 : Ty} :
          (wfTy (domainEnv G) T105) -> (lookup_evar (evar G T105) I0 T105)
      | lookup_evar_there_evar
          {G : Env} {x59 : (Index tm)}
          {T105 : Ty} {T106 : Ty} :
          (lookup_evar G x59 T105) -> (lookup_evar (evar G T106) (IS x59) T105)
      | lookup_evar_there_etvar
          {G : Env} {x59 : (Index tm)}
          {T105 : Ty} {T106 : Ty} :
          (lookup_evar G x59 T105) -> (lookup_evar (etvar G T106) x59 (tshiftTy C0 T105)).
    Inductive lookup_etvar : Env -> (Index ty) -> Ty -> Prop :=
      | lookup_etvar_here {G : Env}
          {T105 : Ty} :
          (wfTy (domainEnv G) T105) -> (lookup_etvar (etvar G T105) I0 (tshiftTy C0 T105))
      | lookup_etvar_there_evar
          {G : Env} {X43 : (Index ty)}
          {T105 : Ty} {T106 : Ty} :
          (lookup_etvar G X43 T105) -> (lookup_etvar (evar G T106) X43 T105)
      | lookup_etvar_there_etvar
          {G : Env} {X43 : (Index ty)}
          {T105 : Ty} {T106 : Ty} :
          (lookup_etvar G X43 T105) -> (lookup_etvar (etvar G T106) (IS X43) (tshiftTy C0 T105)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (S46 : Ty) (S47 : Ty) ,
        (lookup_evar (evar G S46) I0 S47) -> (S46 =
        S47)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (S46 : Ty) (S47 : Ty) ,
        (lookup_etvar (etvar G S46) I0 S47) -> ((tshiftTy C0 S46) =
        S47)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x59 : (Index tm)} ,
        (forall {S46 : Ty} ,
          (lookup_evar G x59 S46) -> (forall {S47 : Ty} ,
            (lookup_evar G x59 S47) -> (S46 =
            S47)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X43 : (Index ty)} ,
        (forall {S46 : Ty} ,
          (lookup_etvar G X43 S46) -> (forall {S47 : Ty} ,
            (lookup_etvar G X43 S47) -> (S46 =
            S47)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x59 : (Index tm)} {S46 : Ty} ,
        (lookup_evar G x59 S46) -> (wfTy (domainEnv G) S46)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X43 : (Index ty)} {S46 : Ty} ,
        (lookup_etvar G X43 S46) -> (wfTy (domainEnv G) S46)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x59 : (Index tm)} {T105 : Ty} ,
        (lookup_evar G x59 T105) -> (lookup_evar (appendEnv G G0) (weakenIndextm x59 (domainEnv G0)) (weakenTy T105 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X43 : (Index ty)} {T105 : Ty} ,
        (lookup_etvar G X43 T105) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X43 (domainEnv G0)) (weakenTy T105 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x59 : (Index tm)} {S46 : Ty} ,
        (lookup_evar G x59 S46) -> (wfindex (domainEnv G) x59)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X43 : (Index ty)} {S46 : Ty} ,
        (lookup_etvar G X43 S46) -> (wfindex (domainEnv G) X43)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T105 : Ty} :
        (shift_evar C0 G (evar G T105))
    | shiftevar_there_evar
        {c13 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c13 G G0) -> (shift_evar (CS c13) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c13 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c13 G G0) -> (shift_evar c13 (etvar G T) (etvar G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c13 : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c13 G0 G1) -> (shift_evar (weakenCutofftm c13 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {T105 : Ty} :
        (shift_etvar C0 G (etvar G T105))
    | shiftetvar_there_evar
        {c13 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c13 G G0) -> (shift_etvar c13 (evar G T) (evar G0 (tshiftTy c13 T)))
    | shiftetvar_there_etvar
        {c13 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c13 G G0) -> (shift_etvar (CS c13) (etvar G T) (etvar G0 (tshiftTy c13 T))).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c13 : (Cutoff ty)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c13 G0 G1) -> (shift_etvar (weakenCutoffty c13 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (tshiftEnv c13 G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c13 : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c13 G G0) -> (shifthvl_tm c13 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c13 : (Cutoff ty)} {G : Env} {G0 : Env} ,
      (shift_etvar c13 G G0) -> (shifthvl_ty c13 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T105 : Ty) (s18 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T105 s18 X0 (evar G T105) G)
    | subst_evar_there_evar
        {d52 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T105 s18 d52 G0 G1) -> (subst_evar G T105 s18 (XS tm d52) (evar G0 T) (evar G1 T))
    | subst_evar_there_etvar
        {d52 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T105 s18 d52 G0 G1) -> (subst_evar G T105 s18 (XS ty d52) (etvar G0 T) (etvar G1 T)).
  Lemma weaken_subst_evar {G : Env} {T105 : Ty} {s18 : Tm} :
    (forall (G0 : Env) {d52 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T105 s18 d52 G1 G2) -> (subst_evar G T105 s18 (weakenTrace d52 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (T105 : Ty) (S46 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G T105 S46 X0 (etvar G T105) G)
    | subst_etvar_there_evar
        {d52 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G T105 S46 d52 G0 G1) -> (subst_etvar G T105 S46 (XS tm d52) (evar G0 T) (evar G1 (tsubstTy d52 S46 T)))
    | subst_etvar_there_etvar
        {d52 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G T105 S46 d52 G0 G1) -> (subst_etvar G T105 S46 (XS ty d52) (etvar G0 T) (etvar G1 (tsubstTy d52 S46 T))).
  Lemma weaken_subst_etvar {G : Env} {T105 : Ty} {S46 : Ty} :
    (forall (G0 : Env) {d52 : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G T105 S46 d52 G1 G2) -> (subst_etvar G T105 S46 (weakenTrace d52 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d52 S46 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s18 : Tm} {T105 : Ty} :
    (forall {d52 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T105 s18 d52 G0 G1) -> (substhvl_tm (domainEnv G) d52 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S46 : Ty} {T106 : Ty} :
    (forall {d52 : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G T106 S46 d52 G0 G1) -> (substhvl_ty (domainEnv G) d52 (domainEnv G0) (domainEnv G1))).
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
Lemma weaken_lookup_evar_here  :
  (forall {G : Env} (G0 : Env) {T105 : Ty} (wf : (wfTy (domainEnv G) T105)) ,
    (lookup_evar (appendEnv (evar G T105) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T105 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {T105 : Ty} (wf : (wfTy (domainEnv G) T105)) ,
    (lookup_etvar (appendEnv (etvar G T105) G0) (weakenIndexty I0 (domainEnv G0)) (weakenTy (tshiftTy C0 T105) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfPat wfTm wfTy : infra.
 Hint Constructors wfPat wfTm wfTy : wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H : (wfTy _ (tvar _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (top)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tarr _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tall _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tprod _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H : (wfPat _ (pvar _)) |- _ => inversion H; subst; clear H
  | H : (wfPat _ (pprod _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H : (wfTm _ (var _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (abs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (app _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tabs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tapp _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (prod _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (lett _ _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Resolve lookup_evar_wf lookup_etvar_wf : infra.
 Hint Resolve lookup_evar_wf lookup_etvar_wf : wf.
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
Lemma shift_evar_lookup_evar  :
  (forall {c13 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c13 G G0)) {x59 : (Index tm)} {T105 : Ty} ,
    (lookup_evar G x59 T105) -> (lookup_evar G0 (shiftIndex c13 x59) T105)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c13 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c13 G G0)) {X43 : (Index ty)} {T105 : Ty} ,
    (lookup_etvar G X43 T105) -> (lookup_etvar G0 X43 T105)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c13 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c13 G G0)) {x59 : (Index tm)} {T105 : Ty} ,
    (lookup_evar G x59 T105) -> (lookup_evar G0 x59 (tshiftTy c13 T105))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c13 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c13 G G0)) {X43 : (Index ty)} {T105 : Ty} ,
    (lookup_etvar G X43 T105) -> (lookup_etvar G0 (tshiftIndex c13 X43) (tshiftTy c13 T105))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} {T107 : Ty} {s18 : Tm} :
  (forall {d52 : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T107 s18 d52 G0 G1)) {X43 : (Index ty)} {T108 : Ty} ,
    (lookup_etvar G0 X43 T108) -> (lookup_etvar G1 X43 T108)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} {T107 : Ty} {S46 : Ty} (wf : (wfTy (domainEnv G) S46)) :
  (forall {d52 : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G T107 S46 d52 G0 G1)) {x59 : (Index tm)} {T108 : Ty} ,
    (lookup_evar G0 x59 T108) -> (lookup_evar G1 x59 (tsubstTy d52 S46 T108))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} : nat :=
  match S0 with
    | (tvar X) => 1
    | (top) => 1
    | (tarr T1 T2) => (plus 1 (plus (size_Ty T1) (size_Ty T2)))
    | (tall T0 T3) => (plus 1 (plus (size_Ty T0) (size_Ty T3)))
    | (tprod T4 T5) => (plus 1 (plus (size_Ty T4) (size_Ty T5)))
  end.
Fixpoint size_Pat (p : Pat) {struct p} : nat :=
  match p with
    | (pvar T) => (plus 1 (size_Ty T))
    | (pprod p1 p2) => (plus 1 (plus (size_Pat p1) (size_Pat p2)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} : nat :=
  match s with
    | (var x) => 1
    | (abs T t) => (plus 1 (plus (size_Ty T) (size_Tm t)))
    | (app t1 t2) => (plus 1 (plus (size_Tm t1) (size_Tm t2)))
    | (tabs T0 t0) => (plus 1 (plus (size_Ty T0) (size_Tm t0)))
    | (tapp t3 T1) => (plus 1 (plus (size_Tm t3) (size_Ty T1)))
    | (prod t4 t5) => (plus 1 (plus (size_Tm t4) (size_Tm t5)))
    | (lett p t6 t7) => (plus 1 (plus (size_Pat p) (plus (size_Tm t6) (size_Tm t7))))
  end.
Lemma tshift_size_Ty  :
  (forall (S45 : Ty) (c10 : (Cutoff ty)) ,
    ((size_Ty (tshiftTy c10 S45)) =
    (size_Ty S45))).
Proof.
  apply_mutual_ind ind_Ty.
  - intros X38 c10.
  reflexivity.
  - intros c11; simpl; apply ((f_equal S)); reflexivity.
  - intros T92 IHT92 T93 IHT93.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT92 c11)).
  + exact ((IHT93 c11)).
  - intros T94 IHT94 T95 IHT95.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT94 c11)).
  + exact ((IHT95 (CS c11))).
  - intros T96 IHT96 T97 IHT97.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT96 c11)).
  + exact ((IHT97 c11)).
Qed.

Lemma tshift_size_Pat  :
  (forall (p30 : Pat) (c11 : (Cutoff ty)) ,
    ((size_Pat (tshiftPat c11 p30)) =
    (size_Pat p30))).
Proof.
  apply_mutual_ind ind_Pat.
  - intros T98.
  pose proof ((tshift_size_Ty T98)) as IHT98.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT98 c11)).
  - intros p30 IHp30 p31 IHp31.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHp30 c11)).
  + exact ((IHp31 c11)).
Qed.

Lemma shift_size_Tm  :
  (forall (s18 : Tm) (c11 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c11 s18)) =
    (size_Tm s18))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros x55 c11.
  reflexivity.
  - intros T99 t152 IHt152.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt152 (CS c12))).
  - intros t153 IHt153 t154 IHt154.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt153 c12)).
  + exact ((IHt154 c12)).
  - intros T100 t155 IHt155.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt155 c12)).
  - intros t156 IHt156 T101.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt156 c12)).
  + reflexivity.
  - intros t157 IHt157 t158 IHt158.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt157 c12)).
  + exact ((IHt158 c12)).
  - intros p32 t159 IHt159 t160 IHt160.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt159 c12)).
  + exact ((IHt160 (weakenCutofftm c12 (bindPat p32)))).
Qed.

Lemma tshift_size_Tm  :
  (forall (s18 : Tm) (c12 : (Cutoff ty)) ,
    ((size_Tm (tshiftTm c12 s18)) =
    (size_Tm s18))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros X41 c12.
  reflexivity.
  - intros T102 t161 IHt161.
  pose proof ((tshift_size_Ty T102)) as IHT102.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT102 c13)).
  + exact ((IHt161 c13)).
  - intros t162 IHt162 t163 IHt163.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt162 c13)).
  + exact ((IHt163 c13)).
  - intros T103 t164 IHt164.
  pose proof ((tshift_size_Ty T103)) as IHT103.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT103 c13)).
  + exact ((IHt164 (CS c13))).
  - intros t165 IHt165 T104.
  pose proof ((tshift_size_Ty T104)) as IHT104.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt165 c13)).
  + exact ((IHT104 c13)).
  - intros t166 IHt166 t167 IHt167.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt166 c13)).
  + exact ((IHt167 c13)).
  - intros p33 t168 IHt168 t169 IHt169.
  pose proof ((tshift_size_Pat p33)) as IHp33.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHp33 c13)).
  + exact ((IHt168 c13)).
  + exact ((IHt169 (weakenCutoffty c13 (bindPat p33)))).
Qed.

 Hint Rewrite tshift_size_Pat shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite tshift_size_Pat shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Pat  :
  (forall (k64 : Hvl) (p34 : Pat) ,
    ((size_Pat (weakenPat p34 k64)) =
    (size_Pat p34))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k64 : Hvl) (s18 : Tm) ,
    ((size_Tm (weakenTm s18 k64)) =
    (size_Tm s18))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k64 : Hvl) (S45 : Ty) ,
    ((size_Ty (weakenTy S45 k64)) =
    (size_Ty S45))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : weaken_size.