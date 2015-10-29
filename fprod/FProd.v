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
    | tall (T : Ty)
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
    | tabs (t : Tm)
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
      | (tarr T1 T2) => (tarr (tshiftTy (weakenCutoffty c H0) T1) (tshiftTy (weakenCutoffty c H0) T2))
      | (tall T) => (tall (tshiftTy (weakenCutoffty c (appendHvl (HS ty H0) H0)) T))
      | (tprod T0 T3) => (tprod (tshiftTy (weakenCutoffty c H0) T0) (tshiftTy (weakenCutoffty c H0) T3))
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
      | (tabs t0) => (tabs (shiftTm (weakenCutofftm c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T0) => (tapp (shiftTm (weakenCutofftm c H0) t3) T0)
      | (prod t4 t5) => (prod (shiftTm (weakenCutofftm c H0) t4) (shiftTm (weakenCutofftm c H0) t5))
      | (lett p t6 t7) => (lett p (shiftTm (weakenCutofftm c H0) t6) (shiftTm (weakenCutofftm c (appendHvl (bindPat p) H0)) t7))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tshiftTy (weakenCutoffty c H0) T) (tshiftTm (weakenCutoffty c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (tshiftTm (weakenCutoffty c H0) t1) (tshiftTm (weakenCutoffty c H0) t2))
      | (tabs t0) => (tabs (tshiftTm (weakenCutoffty c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T0) => (tapp (tshiftTm (weakenCutoffty c H0) t3) (tshiftTy (weakenCutoffty c H0) T0))
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
      | (tarr T1 T2) => (tarr (tsubstTy d S0 T1) (tsubstTy d S0 T2))
      | (tall T) => (tall (tsubstTy (XS ty d) S0 T))
      | (tprod T0 T3) => (tprod (tsubstTy d S0 T0) (tsubstTy d S0 T3))
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
      | (tabs t0) => (tabs (substTm (XS ty d) s t0))
      | (tapp t3 T0) => (tapp (substTm d s t3) T0)
      | (prod t4 t5) => (prod (substTm d s t4) (substTm d s t5))
      | (lett p t6 t7) => (lett p (substTm d s t6) (substTm (weakenTrace d (bindPat p)) s t7))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tsubstTy d S0 T) (tsubstTm (XS tm d) S0 t))
      | (app t1 t2) => (app (tsubstTm d S0 t1) (tsubstTm d S0 t2))
      | (tabs t0) => (tabs (tsubstTm (XS ty d) S0 t0))
      | (tapp t3 T0) => (tapp (tsubstTm d S0 t3) (tsubstTy d S0 T0))
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
      (tsubstIndex0_tshiftIndex0_reflection_ind S3 k7 X14))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tarr (IHT5 k7 S3) (IHT6 k7 S3))) (fun (T : Ty) IHT5 (k7 : Hvl) (S3 : Ty) =>
    (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHT5 (HS ty k7) S3)))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tprod (IHT5 k7 S3) (IHT6 k7 S3)))).
  Definition tsubst0_tshift0_Pat_reflection_ind := (ind_Pat (fun (p11 : Pat) =>
    (forall (k7 : Hvl) (S3 : Ty) ,
      ((tsubstPat (weakenTrace X0 k7) S3 (tshiftPat (weakenCutoffty C0 k7) p11)) =
      p11))) (fun (T : Ty) (k7 : Hvl) (S3 : Ty) =>
    (f_equal pvar (let IHT5 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT5 k7 S3)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 pprod (IHp0 k7 S3) (IHp3 k7 S3)))).
  Definition subst0_shift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (s1 : Tm) ,
      ((substTm (weakenTrace X0 k7) s1 (shiftTm (weakenCutofftm C0 k7) s0)) =
      s0))) (fun (x16 : (Index tm)) =>
    (fun (k7 : Hvl) (s0 : Tm) =>
      (substIndex0_shiftIndex0_reflection_ind s0 k7 x16))) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt53 (HS tm k7) s0)))) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 app (IHt53 k7 s0) (IHt54 k7 s0))) (fun (t : Tm) IHt53 (k7 : Hvl) (s0 : Tm) =>
    (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt53 (HS ty k7) s0)))) (fun (t : Tm) IHt53 (T : Ty) (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tapp (IHt53 k7 s0) eq_refl)) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 prod (IHt53 k7 s0) (IHt54 k7 s0))) (fun (p : Pat) (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (s0 : Tm) =>
    (f_equal3 lett eq_refl (IHt53 k7 s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k7 (bindPat p)) eq_refl)) (IHt54 (appendHvl k7 (bindPat p)) s0))))).
  Definition tsubst0_tshift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (S3 : Ty) ,
      ((tsubstTm (weakenTrace X0 k7) S3 (tshiftTm (weakenCutoffty C0 k7) s0)) =
      s0))) (fun (x16 : (Index tm)) =>
    (fun (k7 : Hvl) (S3 : Ty) =>
      eq_refl)) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 abs (let IHT5 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT5 k7 S3)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt53 (HS tm k7) S3)))) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 app (IHt53 k7 S3) (IHt54 k7 S3))) (fun (t : Tm) IHt53 (k7 : Hvl) (S3 : Ty) =>
    (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt53 (HS ty k7) S3)))) (fun (t : Tm) IHt53 (T : Ty) (k7 : Hvl) (S3 : Ty) =>
    (f_equal2 tapp (IHt53 k7 S3) (let IHT5 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT5 k7 S3)))) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (S3 : Ty) =>
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
        (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k4 c5 X8)))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tarr (IHT5 k4 c5) (IHT6 k4 c5))) (fun (T : Ty) IHT5 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal tall (IHT5 (HS ty k4) c5))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tprod (IHT5 k4 c5) (IHT6 k4 c5)))).
    Definition tshift_tshift0_Pat_comm_ind := (ind_Pat (fun (p7 : Pat) =>
      (forall (k4 : Hvl) (c5 : (Cutoff ty)) ,
        ((tshiftPat (weakenCutoffty (CS c5) k4) (tshiftPat (weakenCutoffty C0 k4) p7)) =
        (tshiftPat (weakenCutoffty C0 k4) (tshiftPat (weakenCutoffty c5 k4) p7))))) (fun (T : Ty) (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal pvar (let IHT5 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT5 k4 c5)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 pprod (IHp0 k4 c5) (IHp3 k4 c5)))).
    Definition shift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c5 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm (CS c5) k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c5 k4) s))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c5 : (Cutoff tm)) =>
        (f_equal var (shiftIndex_shiftIndex0_comm_ind k4 c5 x10)))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt35 (HS tm k4) c5))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal2 app (IHt35 k4 c5) (IHt36 k4 c5))) (fun (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal tabs (IHt35 (HS ty k4) c5))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c5 : (Cutoff tm)) =>
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
      (f_equal2 app (IHt35 k4 c5) (IHt36 k4 c5))) (fun (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff tm)) =>
      (f_equal tabs (IHt35 (HS ty k4) c5))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c5 : (Cutoff tm)) =>
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
      (f_equal2 app (IHt35 k4 c5) (IHt36 k4 c5))) (fun (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal tabs (IHt35 (HS ty k4) c5))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt35 k4 c5) eq_refl)) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 prod (IHt35 k4 c5) (IHt36 k4 c5))) (fun (p : Pat) (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal3 lett eq_refl (IHt35 k4 c5) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c5 k4 (bindPat p)) (f_equal2 shiftTm (weakenCutofftm_append C0 k4 (bindPat p)) eq_refl)) (eq_trans (IHt36 (appendHvl k4 (bindPat p)) c5) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k4 (bindPat p))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c5 k4 (bindPat p))) eq_refl))))))).
    Definition tshift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c5 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty (CS c5) k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c5 k4) s))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c5 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 abs (let IHT5 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT5 k4 c5)) (IHt35 (HS tm k4) c5))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 app (IHt35 k4 c5) (IHt36 k4 c5))) (fun (t : Tm) IHt35 (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal tabs (IHt35 (HS ty k4) c5))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c5 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt35 k4 c5) (let IHT5 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT5 k4 c5)))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c5 : (Cutoff ty)) =>
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
    (forall (k62 : Hvl) (c10 : (Cutoff ty)) (S43 : Ty) ,
      ((weakenTy (tshiftTy c10 S43) k62) =
      (tshiftTy (weakenCutoffty c10 k62) (weakenTy S43 k62)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenPat_tshiftPat  :
    (forall (k62 : Hvl) (c10 : (Cutoff ty)) (p30 : Pat) ,
      ((weakenPat (tshiftPat c10 p30) k62) =
      (tshiftPat (weakenCutoffty c10 k62) (weakenPat p30 k62)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k62 : Hvl) (c10 : (Cutoff tm)) (s18 : Tm) ,
      ((weakenTm (shiftTm c10 s18) k62) =
      (shiftTm (weakenCutofftm c10 k62) (weakenTm s18 k62)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k62 : Hvl) (c10 : (Cutoff ty)) (s18 : Tm) ,
      ((weakenTm (tshiftTm c10 s18) k62) =
      (tshiftTm (weakenCutoffty c10 k62) (weakenTm s18 k62)))).
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
        (tshiftTy_tsubstIndex0_comm_ind c10 S6 k12 X21))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tarr (IHT5 k12 c10 S6) (IHT6 k12 c10 S6))) (fun (T : Ty) IHT5 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal tall (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT5 (HS ty k12) c10 S6) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tprod (IHT5 k12 c10 S6) (IHT6 k12 c10 S6)))).
    Definition tshift_tsubst0_Pat_comm_ind := (ind_Pat (fun (p17 : Pat) =>
      (forall (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) ,
        ((tshiftPat (weakenCutoffty c10 k12) (tsubstPat (weakenTrace X0 k12) S6 p17)) =
        (tsubstPat (weakenTrace X0 k12) (tshiftTy c10 S6) (tshiftPat (weakenCutoffty (CS c10) k12) p17))))) (fun (T : Ty) (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal pvar (let IHT5 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT5 k12 c10 S6)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 pprod (IHp0 k12 c10 S6) (IHp3 k12 c10 S6)))).
    Definition shift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c10 : (Cutoff tm)) (s3 : Tm) ,
        ((shiftTm (weakenCutofftm c10 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (shiftTm c10 s3) (shiftTm (weakenCutofftm (CS c10) k12) s2))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
        (shiftTm_substIndex0_comm_ind c10 s2 k12 x29))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c10 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 app (IHt89 k12 c10 s2) (IHt90 k12 c10 s2))) (fun (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c10 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c10 : (Cutoff tm)) (s2 : Tm) =>
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
      (f_equal2 app (IHt89 k12 c10 S6) (IHt90 k12 c10 S6))) (fun (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) =>
      (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c10 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c10 : (Cutoff tm)) (S6 : Ty) =>
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
      (f_equal2 app (IHt89 k12 c10 s2) (IHt90 k12 c10 s2))) (fun (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c10 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tapp (IHt89 k12 c10 s2) eq_refl)) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 prod (IHt89 k12 c10 s2) (IHt90 k12 c10 s2))) (fun (p : Pat) (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal3 lett eq_refl (IHt89 k12 c10 s2) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c10 k12 (bindPat p)) (f_equal3 substTm (weakenTrace_append tm X0 k12 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt90 (appendHvl k12 (bindPat p)) c10 s2) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k12 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c10 k12 (bindPat p))) eq_refl))))))).
    Definition tshift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) ,
        ((tshiftTm (weakenCutoffty c10 k12) (tsubstTm (weakenTrace X0 k12) S6 s2)) =
        (tsubstTm (weakenTrace X0 k12) (tshiftTy c10 S6) (tshiftTm (weakenCutoffty (CS c10) k12) s2))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 abs (let IHT5 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT5 k12 c10 S6)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c10 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 app (IHt89 k12 c10 S6) (IHt90 k12 c10 S6))) (fun (t : Tm) IHt89 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c10 S6) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
      (f_equal2 tapp (IHt89 k12 c10 S6) (let IHT5 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT5 k12 c10 S6)))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c10 : (Cutoff ty)) (S6 : Ty) =>
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
    Definition tsubst_tshift0_Ty_comm_ind := (ind_Ty (fun (S26 : Ty) =>
      (forall (k46 : Hvl) (d34 : (Trace ty)) (S27 : Ty) ,
        ((tsubstTy (weakenTrace (XS ty d34) k46) S27 (tshiftTy (weakenCutoffty C0 k46) S26)) =
        (tshiftTy (weakenCutoffty C0 k46) (tsubstTy (weakenTrace d34 k46) S27 S26))))) (fun (X28 : (Index ty)) =>
      (fun (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
        (tsubstIndex_tshiftTy0_comm_ind d34 S26 k46 X28))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 tarr (IHT5 k46 d34 S26) (IHT6 k46 d34 S26))) (fun (T : Ty) IHT5 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d34) k46 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT5 (HS ty k46) d34 S26) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d34 k46 (HS ty H0))) eq_refl eq_refl)))))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 tprod (IHT5 k46 d34 S26) (IHT6 k46 d34 S26)))).
    Definition tsubst_tshift0_Pat_comm_ind := (ind_Pat (fun (p23 : Pat) =>
      (forall (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) ,
        ((tsubstPat (weakenTrace (XS ty d34) k46) S26 (tshiftPat (weakenCutoffty C0 k46) p23)) =
        (tshiftPat (weakenCutoffty C0 k46) (tsubstPat (weakenTrace d34 k46) S26 p23))))) (fun (T : Ty) (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal pvar (let IHT5 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT5 k46 d34 S26)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 pprod (IHp0 k46 d34 S26) (IHp3 k46 d34 S26)))).
    Definition subst_shift0_Tm_comm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k46 : Hvl) (d34 : (Trace tm)) (s17 : Tm) ,
        ((substTm (weakenTrace (XS tm d34) k46) s17 (shiftTm (weakenCutofftm C0 k46) s16)) =
        (shiftTm (weakenCutofftm C0 k46) (substTm (weakenTrace d34 k46) s17 s16))))) (fun (x42 : (Index tm)) =>
      (fun (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
        (substIndex_shiftTm0_comm_ind d34 s16 k46 x42))) (fun (T : Ty) (t : Tm) IHt125 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d34) k46 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k46) d34 s16) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d34 k46 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 app (IHt125 k46 d34 s16) (IHt126 k46 d34 s16))) (fun (t : Tm) IHt125 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d34) k46 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k46) d34 s16) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d34 k46 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 tapp (IHt125 k46 d34 s16) eq_refl)) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 prod (IHt125 k46 d34 s16) (IHt126 k46 d34 s16))) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal3 lett eq_refl (IHt125 k46 d34 s16) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d34) k46 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k46 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k46 (bindPat p)) d34 s16) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k46 (bindPat p))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d34 k46 (bindPat p))) eq_refl eq_refl))))))).
    Definition subst_tshift0_Tm_comm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k46 : Hvl) (d34 : (Trace tm)) (s17 : Tm) ,
        ((substTm (weakenTrace (XS ty d34) k46) s17 (tshiftTm (weakenCutoffty C0 k46) s16)) =
        (tshiftTm (weakenCutoffty C0 k46) (substTm (weakenTrace d34 k46) s17 s16))))) (fun (x42 : (Index tm)) =>
      (fun (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
        (substIndex_tshiftTm0_comm_ind d34 s16 k46 x42))) (fun (T : Ty) (t : Tm) IHt125 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d34) k46 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k46) d34 s16) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d34 k46 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 app (IHt125 k46 d34 s16) (IHt126 k46 d34 s16))) (fun (t : Tm) IHt125 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d34) k46 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k46) d34 s16) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d34 k46 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 tapp (IHt125 k46 d34 s16) eq_refl)) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal2 prod (IHt125 k46 d34 s16) (IHt126 k46 d34 s16))) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace tm)) (s16 : Tm) =>
      (f_equal3 lett eq_refl (IHt125 k46 d34 s16) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenTrace_append tm (XS ty d34) k46 (bindPat p))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k46 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k46 (bindPat p)) d34 s16) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k46 (bindPat p))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d34 k46 (bindPat p))) eq_refl eq_refl))))))).
    Definition tsubst_shift0_Tm_comm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) ,
        ((tsubstTm (weakenTrace d34 k46) S26 (shiftTm (weakenCutofftm C0 k46) s16)) =
        (shiftTm (weakenCutofftm C0 k46) (tsubstTm (weakenTrace d34 k46) S26 s16))))) (fun (x42 : (Index tm)) =>
      (fun (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt125 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d34 k46 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k46) d34 S26) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d34 k46 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 app (IHt125 k46 d34 S26) (IHt126 k46 d34 S26))) (fun (t : Tm) IHt125 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d34 k46 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k46) d34 S26) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d34 k46 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 tapp (IHt125 k46 d34 S26) eq_refl)) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 prod (IHt125 k46 d34 S26) (IHt126 k46 d34 S26))) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal3 lett eq_refl (IHt125 k46 d34 S26) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d34 k46 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k46 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k46 (bindPat p)) d34 S26) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k46 (bindPat p))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d34 k46 (bindPat p))) eq_refl eq_refl))))))).
    Definition tsubst_tshift0_Tm_comm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) ,
        ((tsubstTm (weakenTrace (XS ty d34) k46) S26 (tshiftTm (weakenCutoffty C0 k46) s16)) =
        (tshiftTm (weakenCutoffty C0 k46) (tsubstTm (weakenTrace d34 k46) S26 s16))))) (fun (x42 : (Index tm)) =>
      (fun (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt125 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 abs (let IHT5 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT5 k46 d34 S26)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d34) k46 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k46) d34 S26) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d34 k46 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 app (IHt125 k46 d34 S26) (IHt126 k46 d34 S26))) (fun (t : Tm) IHt125 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d34) k46 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k46) d34 S26) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d34 k46 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 tapp (IHt125 k46 d34 S26) (let IHT5 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT5 k46 d34 S26)))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 prod (IHt125 k46 d34 S26) (IHt126 k46 d34 S26))) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k46 : Hvl) (d34 : (Trace ty)) (S26 : Ty) =>
      (f_equal3 lett (let IHp := (tsubst_tshift0_Pat_comm_ind p) in
      (IHp k46 d34 S26)) (IHt125 k46 d34 S26) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenTrace_append ty (XS ty d34) k46 (bindPat p))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k46 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k46 (bindPat p)) d34 S26) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k46 (bindPat p))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d34 k46 (bindPat p))) eq_refl eq_refl))))))).
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S40 : Ty) : (forall (d47 : (Trace ty)) (S39 : Ty) ,
      ((tsubstTy (XS ty d47) S39 (tshiftTy C0 S40)) =
      (tshiftTy C0 (tsubstTy d47 S39 S40)))) := (tsubst_tshift0_Ty_comm_ind S40 H0).
    Definition tsubstPat_tshiftPat0_comm (p26 : Pat) : (forall (d47 : (Trace ty)) (S39 : Ty) ,
      ((tsubstPat (XS ty d47) S39 (tshiftPat C0 p26)) =
      (tshiftPat C0 (tsubstPat d47 S39 p26)))) := (tsubst_tshift0_Pat_comm_ind p26 H0).
    Definition substTm_shiftTm0_comm (s17 : Tm) : (forall (d47 : (Trace tm)) (s16 : Tm) ,
      ((substTm (XS tm d47) s16 (shiftTm C0 s17)) =
      (shiftTm C0 (substTm d47 s16 s17)))) := (subst_shift0_Tm_comm_ind s17 H0).
    Definition substTm_tshiftTm0_comm (s17 : Tm) : (forall (d47 : (Trace tm)) (s16 : Tm) ,
      ((substTm (XS ty d47) s16 (tshiftTm C0 s17)) =
      (tshiftTm C0 (substTm d47 s16 s17)))) := (subst_tshift0_Tm_comm_ind s17 H0).
    Definition tsubstTm_shiftTm0_comm (s16 : Tm) : (forall (d47 : (Trace ty)) (S39 : Ty) ,
      ((tsubstTm d47 S39 (shiftTm C0 s16)) =
      (shiftTm C0 (tsubstTm d47 S39 s16)))) := (tsubst_shift0_Tm_comm_ind s16 H0).
    Definition tsubstTm_tshiftTm0_comm (s16 : Tm) : (forall (d47 : (Trace ty)) (S39 : Ty) ,
      ((tsubstTm (XS ty d47) S39 (tshiftTm C0 s16)) =
      (tshiftTm C0 (tsubstTm d47 S39 s16)))) := (tsubst_tshift0_Tm_comm_ind s16 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Definition tsubst_tm_Ty_ind := (ind_Ty (fun (S39 : Ty) =>
      (forall (k59 : Hvl) (d47 : (Trace ty)) (S40 : Ty) ,
        ((tsubstTy (weakenTrace (XS tm d47) k59) S40 S39) =
        (tsubstTy (weakenTrace d47 k59) S40 S39)))) (fun (X32 : (Index ty)) =>
      (fun (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
        (tsubstIndex_shiftTy0_comm_ind d47 S39 k59 X32))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal2 tarr (IHT5 k59 d47 S39) (IHT6 k59 d47 S39))) (fun (T : Ty) IHT5 (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d47) k59 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT5 (HS ty k59) d47 S39) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d47 k59 (HS ty H0))) eq_refl eq_refl))))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal2 tprod (IHT5 k59 d47 S39) (IHT6 k59 d47 S39)))).
    Definition tsubst_tm_Pat_ind := (ind_Pat (fun (p26 : Pat) =>
      (forall (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) ,
        ((tsubstPat (weakenTrace (XS tm d47) k59) S39 p26) =
        (tsubstPat (weakenTrace d47 k59) S39 p26)))) (fun (T : Ty) (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal pvar (let IHT5 := (tsubst_tm_Ty_ind T) in
      (IHT5 k59 d47 S39)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal2 pprod (IHp0 k59 d47 S39) (IHp3 k59 d47 S39)))).
    Definition tsubst_tm_Tm_ind := (ind_Tm (fun (s16 : Tm) =>
      (forall (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) ,
        ((tsubstTm (weakenTrace (XS tm d47) k59) S39 s16) =
        (tsubstTm (weakenTrace d47 k59) S39 s16)))) (fun (x46 : (Index tm)) =>
      (fun (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt134 (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal2 abs (let IHT5 := (tsubst_tm_Ty_ind T) in
      (IHT5 k59 d47 S39)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d47) k59 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt134 (HS tm k59) d47 S39) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d47 k59 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt134 (t2 : Tm) IHt135 (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal2 app (IHt134 k59 d47 S39) (IHt135 k59 d47 S39))) (fun (t : Tm) IHt134 (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d47) k59 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt134 (HS ty k59) d47 S39) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d47 k59 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt134 (T : Ty) (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal2 tapp (IHt134 k59 d47 S39) (let IHT5 := (tsubst_tm_Ty_ind T) in
      (IHT5 k59 d47 S39)))) (fun (t1 : Tm) IHt134 (t2 : Tm) IHt135 (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal2 prod (IHt134 k59 d47 S39) (IHt135 k59 d47 S39))) (fun (p : Pat) (t1 : Tm) IHt134 (t2 : Tm) IHt135 (k59 : Hvl) (d47 : (Trace ty)) (S39 : Ty) =>
      (f_equal3 lett (let IHp := (tsubst_tm_Pat_ind p) in
      (IHp k59 d47 S39)) (IHt134 k59 d47 S39) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d47) k59 (bindPat p)) eq_refl eq_refl) (eq_trans (IHt135 (appendHvl k59 (bindPat p)) d47 S39) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d47 k59 (bindPat p))) eq_refl eq_refl)))))).
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S40 : Ty) : (forall (d47 : (Trace ty)) (S39 : Ty) ,
      ((tsubstTy (XS tm d47) S39 S40) =
      (tsubstTy d47 S39 S40))) := (tsubst_tm_Ty_ind S40 H0).
    Definition tsubstPat_tm (p26 : Pat) : (forall (d47 : (Trace ty)) (S39 : Ty) ,
      ((tsubstPat (XS tm d47) S39 p26) =
      (tsubstPat d47 S39 p26))) := (tsubst_tm_Pat_ind p26 H0).
    Definition tsubstTm_tm (s16 : Tm) : (forall (d47 : (Trace ty)) (S39 : Ty) ,
      ((tsubstTm (XS tm d47) S39 s16) =
      (tsubstTm d47 S39 s16))) := (tsubst_tm_Tm_ind s16 H0).
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
    Lemma substTm_substIndex0_commright_ind (d47 : (Trace tm)) (s16 : Tm) (s17 : Tm) :
      (forall (k59 : Hvl) (x46 : (Index tm)) ,
        ((substTm (weakenTrace d47 k59) s16 (substIndex (weakenTrace X0 k59) s17 x46)) =
        (substTm (weakenTrace X0 k59) (substTm d47 s16 s17) (substIndex (weakenTrace (XS tm d47) k59) s16 x46)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d47 : (Trace ty)) (S39 : Ty) (s16 : Tm) :
      (forall (k59 : Hvl) (x46 : (Index tm)) ,
        ((tsubstTm (weakenTrace d47 k59) S39 (substIndex (weakenTrace X0 k59) s16 x46)) =
        (substIndex (weakenTrace X0 k59) (tsubstTm d47 S39 s16) x46))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d47 : (Trace ty)) (S39 : Ty) (S40 : Ty) :
      (forall (k59 : Hvl) (X32 : (Index ty)) ,
        ((tsubstTy (weakenTrace d47 k59) S39 (tsubstIndex (weakenTrace X0 k59) S40 X32)) =
        (tsubstTy (weakenTrace X0 k59) (tsubstTy d47 S39 S40) (tsubstIndex (weakenTrace (XS ty d47) k59) S39 X32)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d47 : (Trace tm)) (s16 : Tm) (S39 : Ty) :
      (forall (k59 : Hvl) (x46 : (Index tm)) ,
        ((substIndex (weakenTrace d47 k59) s16 x46) =
        (tsubstTm (weakenTrace X0 k59) S39 (substIndex (weakenTrace (XS ty d47) k59) s16 x46)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition tsubst_tsubst0_Ty_comm_ind := (ind_Ty (fun (S43 : Ty) =>
      (forall (k62 : Hvl) (d50 : (Trace ty)) (S44 : Ty) (S45 : Ty) ,
        ((tsubstTy (weakenTrace d50 k62) S44 (tsubstTy (weakenTrace X0 k62) S45 S43)) =
        (tsubstTy (weakenTrace X0 k62) (tsubstTy d50 S44 S45) (tsubstTy (weakenTrace (XS ty d50) k62) S44 S43))))) (fun (X37 : (Index ty)) =>
      (fun (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
        (tsubstTy_tsubstIndex0_commright_ind d50 S43 S44 k62 X37))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal2 tarr (IHT5 k62 d50 S43 S44) (IHT6 k62 d50 S43 S44))) (fun (T : Ty) IHT5 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d50 k62 (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k62 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT5 (HS ty k62) d50 S43 S44) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k62 (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d50) k62 (HS ty H0))) eq_refl eq_refl)))))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal2 tprod (IHT5 k62 d50 S43 S44) (IHT6 k62 d50 S43 S44)))).
    Definition tsubst_tsubst0_Pat_comm_ind := (ind_Pat (fun (p30 : Pat) =>
      (forall (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) ,
        ((tsubstPat (weakenTrace d50 k62) S43 (tsubstPat (weakenTrace X0 k62) S44 p30)) =
        (tsubstPat (weakenTrace X0 k62) (tsubstTy d50 S43 S44) (tsubstPat (weakenTrace (XS ty d50) k62) S43 p30))))) (fun (T : Ty) (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal pvar (let IHT5 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT5 k62 d50 S43 S44)))) (fun (p1 : Pat) IHp0 (p2 : Pat) IHp3 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal2 pprod (IHp0 k62 d50 S43 S44) (IHp3 k62 d50 S43 S44)))).
    Definition subst_subst0_Tm_comm_ind := (ind_Tm (fun (s18 : Tm) =>
      (forall (k62 : Hvl) (d50 : (Trace tm)) (s19 : Tm) (s20 : Tm) ,
        ((substTm (weakenTrace d50 k62) s19 (substTm (weakenTrace X0 k62) s20 s18)) =
        (substTm (weakenTrace X0 k62) (substTm d50 s19 s20) (substTm (weakenTrace (XS tm d50) k62) s19 s18))))) (fun (x53 : (Index tm)) =>
      (fun (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
        (substTm_substIndex0_commright_ind d50 s18 s19 k62 x53))) (fun (T : Ty) (t : Tm) IHt152 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d50 k62 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k62 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k62) d50 s18 s19) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k62 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d50) k62 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal2 app (IHt152 k62 d50 s18 s19) (IHt153 k62 d50 s18 s19))) (fun (t : Tm) IHt152 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d50 k62 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k62 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k62) d50 s18 s19) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k62 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d50) k62 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal2 tapp (IHt152 k62 d50 s18 s19) eq_refl)) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal2 prod (IHt152 k62 d50 s18 s19) (IHt153 k62 d50 s18 s19))) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (s19 : Tm) =>
      (f_equal3 lett eq_refl (IHt152 k62 d50 s18 s19) (eq_trans (f_equal3 substTm (weakenTrace_append tm d50 k62 (bindPat p)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k62 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k62 (bindPat p)) d50 s18 s19) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k62 (bindPat p))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d50) k62 (bindPat p))) eq_refl eq_refl))))))).
    Definition subst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s18 : Tm) =>
      (forall (k62 : Hvl) (d50 : (Trace tm)) (s19 : Tm) (S43 : Ty) ,
        ((substTm (weakenTrace d50 k62) s19 (tsubstTm (weakenTrace X0 k62) S43 s18)) =
        (tsubstTm (weakenTrace X0 k62) S43 (substTm (weakenTrace (XS ty d50) k62) s19 s18))))) (fun (x53 : (Index tm)) =>
      (fun (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (S43 : Ty) =>
        (substTy_tsubstIndex0_commleft_ind d50 s18 S43 k62 x53))) (fun (T : Ty) (t : Tm) IHt152 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (S43 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d50 k62 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k62 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k62) d50 s18 S43) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k62 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d50) k62 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (S43 : Ty) =>
      (f_equal2 app (IHt152 k62 d50 s18 S43) (IHt153 k62 d50 s18 S43))) (fun (t : Tm) IHt152 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (S43 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d50 k62 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k62 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k62) d50 s18 S43) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k62 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d50) k62 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (S43 : Ty) =>
      (f_equal2 tapp (IHt152 k62 d50 s18 S43) eq_refl)) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (S43 : Ty) =>
      (f_equal2 prod (IHt152 k62 d50 s18 S43) (IHt153 k62 d50 s18 S43))) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (S43 : Ty) =>
      (f_equal3 lett eq_refl (IHt152 k62 d50 s18 S43) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenTrace_append tm d50 k62 (bindPat p))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k62 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k62 (bindPat p)) d50 s18 S43) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k62 (bindPat p))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d50) k62 (bindPat p))) eq_refl eq_refl))))))).
    Definition tsubst_subst0_Tm_comm_ind := (ind_Tm (fun (s18 : Tm) =>
      (forall (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (s19 : Tm) ,
        ((tsubstTm (weakenTrace d50 k62) S43 (substTm (weakenTrace X0 k62) s19 s18)) =
        (substTm (weakenTrace X0 k62) (tsubstTm d50 S43 s19) (tsubstTm (weakenTrace d50 k62) S43 s18))))) (fun (x53 : (Index tm)) =>
      (fun (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (s18 : Tm) =>
        (tsubstTm_substIndex0_commright_ind d50 S43 s18 k62 x53))) (fun (T : Ty) (t : Tm) IHt152 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (s18 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d50 k62 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k62 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k62) d50 S43 s18) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k62 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d50 k62 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (s18 : Tm) =>
      (f_equal2 app (IHt152 k62 d50 S43 s18) (IHt153 k62 d50 S43 s18))) (fun (t : Tm) IHt152 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (s18 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d50 k62 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k62 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k62) d50 S43 s18) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k62 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d50 k62 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (s18 : Tm) =>
      (f_equal2 tapp (IHt152 k62 d50 S43 s18) eq_refl)) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (s18 : Tm) =>
      (f_equal2 prod (IHt152 k62 d50 S43 s18) (IHt153 k62 d50 S43 s18))) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (s18 : Tm) =>
      (f_equal3 lett eq_refl (IHt152 k62 d50 S43 s18) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d50 k62 (bindPat p)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k62 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k62 (bindPat p)) d50 S43 s18) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k62 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d50 k62 (bindPat p))) eq_refl eq_refl))))))).
    Definition tsubst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s18 : Tm) =>
      (forall (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) ,
        ((tsubstTm (weakenTrace d50 k62) S43 (tsubstTm (weakenTrace X0 k62) S44 s18)) =
        (tsubstTm (weakenTrace X0 k62) (tsubstTy d50 S43 S44) (tsubstTm (weakenTrace (XS ty d50) k62) S43 s18))))) (fun (x53 : (Index tm)) =>
      (fun (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt152 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal2 abs (let IHT5 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT5 k62 d50 S43 S44)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d50 k62 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k62 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k62) d50 S43 S44) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k62 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d50) k62 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal2 app (IHt152 k62 d50 S43 S44) (IHt153 k62 d50 S43 S44))) (fun (t : Tm) IHt152 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d50 k62 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k62 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k62) d50 S43 S44) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k62 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d50) k62 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal2 tapp (IHt152 k62 d50 S43 S44) (let IHT5 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT5 k62 d50 S43 S44)))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal2 prod (IHt152 k62 d50 S43 S44) (IHt153 k62 d50 S43 S44))) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) =>
      (f_equal3 lett (let IHp := (tsubst_tsubst0_Pat_comm_ind p) in
      (IHp k62 d50 S43 S44)) (IHt152 k62 d50 S43 S44) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenTrace_append ty d50 k62 (bindPat p))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k62 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k62 (bindPat p)) d50 S43 S44) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k62 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d50) k62 (bindPat p))) eq_refl eq_refl))))))).
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S45 : Ty) : (forall (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) ,
      ((tsubstTy d50 S43 (tsubstTy X0 S44 S45)) =
      (tsubstTy X0 (tsubstTy d50 S43 S44) (tsubstTy (XS ty d50) S43 S45)))) := (tsubst_tsubst0_Ty_comm_ind S45 H0).
    Definition tsubstPat_tsubstPat0_comm (p30 : Pat) : (forall (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) ,
      ((tsubstPat d50 S43 (tsubstPat X0 S44 p30)) =
      (tsubstPat X0 (tsubstTy d50 S43 S44) (tsubstPat (XS ty d50) S43 p30)))) := (tsubst_tsubst0_Pat_comm_ind p30 H0).
    Definition substTm_substTm0_comm (s20 : Tm) : (forall (d50 : (Trace tm)) (s18 : Tm) (s19 : Tm) ,
      ((substTm d50 s18 (substTm X0 s19 s20)) =
      (substTm X0 (substTm d50 s18 s19) (substTm (XS tm d50) s18 s20)))) := (subst_subst0_Tm_comm_ind s20 H0).
    Definition substTm_tsubstTm0_comm (s19 : Tm) : (forall (d50 : (Trace tm)) (s18 : Tm) (S43 : Ty) ,
      ((substTm d50 s18 (tsubstTm X0 S43 s19)) =
      (tsubstTm X0 S43 (substTm (XS ty d50) s18 s19)))) := (subst_tsubst0_Tm_comm_ind s19 H0).
    Definition tsubstTm_substTm0_comm (s19 : Tm) : (forall (d50 : (Trace ty)) (S43 : Ty) (s18 : Tm) ,
      ((tsubstTm d50 S43 (substTm X0 s18 s19)) =
      (substTm X0 (tsubstTm d50 S43 s18) (tsubstTm d50 S43 s19)))) := (tsubst_subst0_Tm_comm_ind s19 H0).
    Definition tsubstTm_tsubstTm0_comm (s18 : Tm) : (forall (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) ,
      ((tsubstTm d50 S43 (tsubstTm X0 S44 s18)) =
      (tsubstTm X0 (tsubstTy d50 S43 S44) (tsubstTm (XS ty d50) S43 s18)))) := (tsubst_tsubst0_Tm_comm_ind s18 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (S44 : Ty) ,
        ((weakenTy (tsubstTy d50 S43 S44) k62) =
        (tsubstTy (weakenTrace d50 k62) S43 (weakenTy S44 k62)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPat_tsubstPat  :
      (forall (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (p30 : Pat) ,
        ((weakenPat (tsubstPat d50 S43 p30) k62) =
        (tsubstPat (weakenTrace d50 k62) S43 (weakenPat p30 k62)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k62 : Hvl) (d50 : (Trace tm)) (s18 : Tm) (s19 : Tm) ,
        ((weakenTm (substTm d50 s18 s19) k62) =
        (substTm (weakenTrace d50 k62) s18 (weakenTm s19 k62)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k62 : Hvl) (d50 : (Trace ty)) (S43 : Ty) (s18 : Tm) ,
        ((weakenTm (tsubstTm d50 S43 s18) k62) =
        (tsubstTm (weakenTrace d50 k62) S43 (weakenTm s18 k62)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenTy_append  :
      (forall (S43 : Ty) (k62 : Hvl) (k63 : Hvl) ,
        ((weakenTy (weakenTy S43 k62) k63) =
        (weakenTy S43 (appendHvl k62 k63)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenPat_append  :
      (forall (p30 : Pat) (k62 : Hvl) (k63 : Hvl) ,
        ((weakenPat (weakenPat p30 k62) k63) =
        (weakenPat p30 (appendHvl k62 k63)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s18 : Tm) (k62 : Hvl) (k63 : Hvl) ,
        ((weakenTm (weakenTm s18 k62) k63) =
        (weakenTm s18 (appendHvl k62 k63)))).
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
  Fixpoint wfindex {a : Namespace} (k62 : Hvl) (i : (Index a)) {struct k62} : Prop :=
    match k62 with
      | (H0) => False
      | (HS b k62) => match (eq_namespace_dec a b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k62 i)
        end
        | (right n) => (wfindex k62 i)
      end
    end.
  Inductive wfTy (k62 : Hvl) : Ty -> Prop :=
    | wfTy_tvar {X43 : (Index ty)}
        (wfi : (wfindex k62 X43)) :
        (wfTy k62 (tvar X43))
    | wfTy_tarr {T79 : Ty}
        (wf : (wfTy k62 T79)) {T80 : Ty}
        (wf0 : (wfTy k62 T80)) :
        (wfTy k62 (tarr T79 T80))
    | wfTy_tall {T81 : Ty}
        (wf : (wfTy (HS ty k62) T81)) :
        (wfTy k62 (tall T81))
    | wfTy_tprod {T82 : Ty}
        (wf : (wfTy k62 T82)) {T83 : Ty}
        (wf0 : (wfTy k62 T83)) :
        (wfTy k62 (tprod T82 T83)).
  Inductive wfPat (k62 : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T79 : Ty}
        (wf : (wfTy k62 T79)) :
        (wfPat k62 (pvar T79))
    | wfPat_pprod {p34 : Pat}
        (wf : (wfPat k62 p34))
        {p35 : Pat}
        (wf0 : (wfPat k62 p35)) :
        (wfPat k62 (pprod p34 p35)).
  Inductive wfTm (k62 : Hvl) : Tm -> Prop :=
    | wfTm_var {x59 : (Index tm)}
        (wfi : (wfindex k62 x59)) :
        (wfTm k62 (var x59))
    | wfTm_abs {T79 : Ty}
        (wf : (wfTy k62 T79))
        {t170 : Tm}
        (wf0 : (wfTm (HS tm k62) t170))
        : (wfTm k62 (abs T79 t170))
    | wfTm_app {t171 : Tm}
        (wf : (wfTm k62 t171))
        {t172 : Tm}
        (wf0 : (wfTm k62 t172)) :
        (wfTm k62 (app t171 t172))
    | wfTm_tabs {t173 : Tm}
        (wf : (wfTm (HS ty k62) t173)) :
        (wfTm k62 (tabs t173))
    | wfTm_tapp {t174 : Tm}
        (wf : (wfTm k62 t174))
        {T80 : Ty}
        (wf0 : (wfTy k62 T80)) :
        (wfTm k62 (tapp t174 T80))
    | wfTm_prod {t175 : Tm}
        (wf : (wfTm k62 t175))
        {t176 : Tm}
        (wf0 : (wfTm k62 t176)) :
        (wfTm k62 (prod t175 t176))
    | wfTm_lett {p34 : Pat}
        (wf : (wfPat k62 p34))
        {t177 : Tm}
        (wf0 : (wfTm k62 t177))
        {t178 : Tm}
        (wf1 : (wfTm (appendHvl k62 (bindPat p34)) t178))
        :
        (wfTm k62 (lett p34 t177 t178)).
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c13 : (Cutoff tm)) (k62 : Hvl) (k63 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k62 : Hvl)
        :
        (shifthvl_tm C0 k62 (HS tm k62))
    | shifthvl_tm_there_tm
        (c13 : (Cutoff tm)) (k62 : Hvl)
        (k63 : Hvl) :
        (shifthvl_tm c13 k62 k63) -> (shifthvl_tm (CS c13) (HS tm k62) (HS tm k63))
    | shifthvl_tm_there_ty
        (c13 : (Cutoff tm)) (k62 : Hvl)
        (k63 : Hvl) :
        (shifthvl_tm c13 k62 k63) -> (shifthvl_tm c13 (HS ty k62) (HS ty k63)).
  Inductive shifthvl_ty : (forall (c13 : (Cutoff ty)) (k62 : Hvl) (k63 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k62 : Hvl)
        :
        (shifthvl_ty C0 k62 (HS ty k62))
    | shifthvl_ty_there_tm
        (c13 : (Cutoff ty)) (k62 : Hvl)
        (k63 : Hvl) :
        (shifthvl_ty c13 k62 k63) -> (shifthvl_ty c13 (HS tm k62) (HS tm k63))
    | shifthvl_ty_there_ty
        (c13 : (Cutoff ty)) (k62 : Hvl)
        (k63 : Hvl) :
        (shifthvl_ty c13 k62 k63) -> (shifthvl_ty (CS c13) (HS ty k62) (HS ty k63)).
  Lemma weaken_shifthvl_tm  :
    (forall (k62 : Hvl) {c13 : (Cutoff tm)} {k63 : Hvl} {k64 : Hvl} ,
      (shifthvl_tm c13 k63 k64) -> (shifthvl_tm (weakenCutofftm c13 k62) (appendHvl k63 k62) (appendHvl k64 k62))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k62 : Hvl) {c13 : (Cutoff ty)} {k63 : Hvl} {k64 : Hvl} ,
      (shifthvl_ty c13 k63 k64) -> (shifthvl_ty (weakenCutoffty c13 k62) (appendHvl k63 k62) (appendHvl k64 k62))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c13 : (Cutoff tm)) (k62 : Hvl) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) (x59 : (Index tm)) ,
      (wfindex k62 x59) -> (wfindex k63 (shiftIndex c13 x59))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c13 : (Cutoff tm)) (k62 : Hvl) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) (X43 : (Index ty)) ,
      (wfindex k62 X43) -> (wfindex k63 X43)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c13 : (Cutoff ty)) (k62 : Hvl) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) (x59 : (Index tm)) ,
      (wfindex k62 x59) -> (wfindex k63 x59)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c13 : (Cutoff ty)) (k62 : Hvl) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) (X43 : (Index ty)) ,
      (wfindex k62 X43) -> (wfindex k63 (tshiftIndex c13 X43))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k62 : Hvl) ,
    (forall (S43 : Ty) (wf : (wfTy k62 S43)) ,
      (forall (c13 : (Cutoff tm)) (k63 : Hvl) ,
        (shifthvl_tm c13 k62 k63) -> (wfTy k63 S43)))) := (ind_wfTy (fun (k62 : Hvl) (S43 : Ty) (wf : (wfTy k62 S43)) =>
    (forall (c13 : (Cutoff tm)) (k63 : Hvl) ,
      (shifthvl_tm c13 k62 k63) -> (wfTy k63 S43))) (fun (k62 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k62 X43)) (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTy_tvar k63 (shift_wfindex_ty c13 k62 k63 ins X43 wfi))) (fun (k62 : Hvl) (T1 : Ty) (wf : (wfTy k62 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k62 T2)) IHT6 (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTy_tarr k63 (IHT5 c13 k63 (weaken_shifthvl_tm H0 ins)) (IHT6 c13 k63 (weaken_shifthvl_tm H0 ins)))) (fun (k62 : Hvl) (T : Ty) (wf : (wfTy (HS ty k62) T)) IHT5 (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTy_tall k63 (IHT5 c13 (HS ty k63) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k62 : Hvl) (T1 : Ty) (wf : (wfTy k62 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k62 T2)) IHT6 (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTy_tprod k63 (IHT5 c13 k63 (weaken_shifthvl_tm H0 ins)) (IHT6 c13 k63 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTy : (forall (k62 : Hvl) ,
    (forall (S43 : Ty) (wf : (wfTy k62 S43)) ,
      (forall (c13 : (Cutoff ty)) (k63 : Hvl) ,
        (shifthvl_ty c13 k62 k63) -> (wfTy k63 (tshiftTy c13 S43))))) := (ind_wfTy (fun (k62 : Hvl) (S43 : Ty) (wf : (wfTy k62 S43)) =>
    (forall (c13 : (Cutoff ty)) (k63 : Hvl) ,
      (shifthvl_ty c13 k62 k63) -> (wfTy k63 (tshiftTy c13 S43)))) (fun (k62 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k62 X43)) (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTy_tvar k63 (tshift_wfindex_ty c13 k62 k63 ins X43 wfi))) (fun (k62 : Hvl) (T1 : Ty) (wf : (wfTy k62 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k62 T2)) IHT6 (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTy_tarr k63 (IHT5 c13 k63 (weaken_shifthvl_ty H0 ins)) (IHT6 c13 k63 (weaken_shifthvl_ty H0 ins)))) (fun (k62 : Hvl) (T : Ty) (wf : (wfTy (HS ty k62) T)) IHT5 (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTy_tall k63 (IHT5 (CS c13) (HS ty k63) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k62 : Hvl) (T1 : Ty) (wf : (wfTy k62 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k62 T2)) IHT6 (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTy_tprod k63 (IHT5 c13 k63 (weaken_shifthvl_ty H0 ins)) (IHT6 c13 k63 (weaken_shifthvl_ty H0 ins))))).
  Definition shift_wfPat : (forall (k62 : Hvl) ,
    (forall (p34 : Pat) (wf : (wfPat k62 p34)) ,
      (forall (c13 : (Cutoff tm)) (k63 : Hvl) ,
        (shifthvl_tm c13 k62 k63) -> (wfPat k63 p34)))) := (fun (k62 : Hvl) =>
    (ind_wfPat k62 (fun (p34 : Pat) (wf : (wfPat k62 p34)) =>
      (forall (c13 : (Cutoff tm)) (k63 : Hvl) ,
        (shifthvl_tm c13 k62 k63) -> (wfPat k63 p34))) (fun (T : Ty) (wf : (wfTy k62 T)) (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
      (wfPat_pvar k63 (shift_wfTy k62 T wf c13 k63 (weaken_shifthvl_tm H0 ins)))) (fun (p1 : Pat) (wf : (wfPat k62 p1)) IHp0 (p2 : Pat) (wf0 : (wfPat k62 p2)) IHp3 (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
      (wfPat_pprod k63 (IHp0 c13 k63 (weaken_shifthvl_tm H0 ins)) (IHp3 c13 k63 (weaken_shifthvl_tm H0 ins)))))).
  Definition tshift_wfPat : (forall (k62 : Hvl) ,
    (forall (p34 : Pat) (wf : (wfPat k62 p34)) ,
      (forall (c13 : (Cutoff ty)) (k63 : Hvl) ,
        (shifthvl_ty c13 k62 k63) -> (wfPat k63 (tshiftPat c13 p34))))) := (fun (k62 : Hvl) =>
    (ind_wfPat k62 (fun (p34 : Pat) (wf : (wfPat k62 p34)) =>
      (forall (c13 : (Cutoff ty)) (k63 : Hvl) ,
        (shifthvl_ty c13 k62 k63) -> (wfPat k63 (tshiftPat c13 p34)))) (fun (T : Ty) (wf : (wfTy k62 T)) (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
      (wfPat_pvar k63 (tshift_wfTy k62 T wf c13 k63 (weaken_shifthvl_ty H0 ins)))) (fun (p1 : Pat) (wf : (wfPat k62 p1)) IHp0 (p2 : Pat) (wf0 : (wfPat k62 p2)) IHp3 (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
      (wfPat_pprod k63 (IHp0 c13 k63 (weaken_shifthvl_ty H0 ins)) (IHp3 c13 k63 (weaken_shifthvl_ty H0 ins)))))).
  Definition shift_wfTm : (forall (k62 : Hvl) ,
    (forall (s18 : Tm) (wf : (wfTm k62 s18)) ,
      (forall (c13 : (Cutoff tm)) (k63 : Hvl) ,
        (shifthvl_tm c13 k62 k63) -> (wfTm k63 (shiftTm c13 s18))))) := (ind_wfTm (fun (k62 : Hvl) (s18 : Tm) (wf : (wfTm k62 s18)) =>
    (forall (c13 : (Cutoff tm)) (k63 : Hvl) ,
      (shifthvl_tm c13 k62 k63) -> (wfTm k63 (shiftTm c13 s18)))) (fun (k62 : Hvl) (x59 : (Index tm)) (wfi : (wfindex k62 x59)) (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTm_var k63 (shift_wfindex_tm c13 k62 k63 ins x59 wfi))) (fun (k62 : Hvl) (T : Ty) (wf : (wfTy k62 T)) (t : Tm) (wf0 : (wfTm (HS tm k62) t)) IHt170 (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTm_abs k63 (shift_wfTy k62 T wf c13 k63 (weaken_shifthvl_tm H0 ins)) (IHt170 (CS c13) (HS tm k63) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k62 : Hvl) (t1 : Tm) (wf : (wfTm k62 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k62 t2)) IHt171 (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTm_app k63 (IHt170 c13 k63 (weaken_shifthvl_tm H0 ins)) (IHt171 c13 k63 (weaken_shifthvl_tm H0 ins)))) (fun (k62 : Hvl) (t : Tm) (wf : (wfTm (HS ty k62) t)) IHt170 (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTm_tabs k63 (IHt170 c13 (HS ty k63) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k62 : Hvl) (t : Tm) (wf : (wfTm k62 t)) IHt170 (T : Ty) (wf0 : (wfTy k62 T)) (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTm_tapp k63 (IHt170 c13 k63 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k62 T wf0 c13 k63 (weaken_shifthvl_tm H0 ins)))) (fun (k62 : Hvl) (t1 : Tm) (wf : (wfTm k62 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k62 t2)) IHt171 (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTm_prod k63 (IHt170 c13 k63 (weaken_shifthvl_tm H0 ins)) (IHt171 c13 k63 (weaken_shifthvl_tm H0 ins)))) (fun (k62 : Hvl) (p : Pat) (wf : (wfPat k62 p)) (t1 : Tm) (wf0 : (wfTm k62 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm (appendHvl k62 (bindPat p)) t2)) IHt171 (c13 : (Cutoff tm)) (k63 : Hvl) (ins : (shifthvl_tm c13 k62 k63)) =>
    (wfTm_lett k63 (shift_wfPat k62 p wf c13 k63 (weaken_shifthvl_tm H0 ins)) (IHt170 c13 k63 (weaken_shifthvl_tm H0 ins)) (IHt171 (weakenCutofftm c13 (bindPat p)) (appendHvl k63 (bindPat p)) (weaken_shifthvl_tm (bindPat p) ins))))).
  Definition tshift_wfTm : (forall (k62 : Hvl) ,
    (forall (s18 : Tm) (wf : (wfTm k62 s18)) ,
      (forall (c13 : (Cutoff ty)) (k63 : Hvl) ,
        (shifthvl_ty c13 k62 k63) -> (wfTm k63 (tshiftTm c13 s18))))) := (ind_wfTm (fun (k62 : Hvl) (s18 : Tm) (wf : (wfTm k62 s18)) =>
    (forall (c13 : (Cutoff ty)) (k63 : Hvl) ,
      (shifthvl_ty c13 k62 k63) -> (wfTm k63 (tshiftTm c13 s18)))) (fun (k62 : Hvl) (x59 : (Index tm)) (wfi : (wfindex k62 x59)) (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTm_var k63 (tshift_wfindex_tm c13 k62 k63 ins x59 wfi))) (fun (k62 : Hvl) (T : Ty) (wf : (wfTy k62 T)) (t : Tm) (wf0 : (wfTm (HS tm k62) t)) IHt170 (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTm_abs k63 (tshift_wfTy k62 T wf c13 k63 (weaken_shifthvl_ty H0 ins)) (IHt170 c13 (HS tm k63) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k62 : Hvl) (t1 : Tm) (wf : (wfTm k62 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k62 t2)) IHt171 (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTm_app k63 (IHt170 c13 k63 (weaken_shifthvl_ty H0 ins)) (IHt171 c13 k63 (weaken_shifthvl_ty H0 ins)))) (fun (k62 : Hvl) (t : Tm) (wf : (wfTm (HS ty k62) t)) IHt170 (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTm_tabs k63 (IHt170 (CS c13) (HS ty k63) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k62 : Hvl) (t : Tm) (wf : (wfTm k62 t)) IHt170 (T : Ty) (wf0 : (wfTy k62 T)) (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTm_tapp k63 (IHt170 c13 k63 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k62 T wf0 c13 k63 (weaken_shifthvl_ty H0 ins)))) (fun (k62 : Hvl) (t1 : Tm) (wf : (wfTm k62 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k62 t2)) IHt171 (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTm_prod k63 (IHt170 c13 k63 (weaken_shifthvl_ty H0 ins)) (IHt171 c13 k63 (weaken_shifthvl_ty H0 ins)))) (fun (k62 : Hvl) (p : Pat) (wf : (wfPat k62 p)) (t1 : Tm) (wf0 : (wfTm k62 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm (appendHvl k62 (bindPat p)) t2)) IHt171 (c13 : (Cutoff ty)) (k63 : Hvl) (ins : (shifthvl_ty c13 k62 k63)) =>
    (wfTm_lett k63 (tshift_wfPat k62 p wf c13 k63 (weaken_shifthvl_ty H0 ins)) (IHt170 c13 k63 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k63) (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0))) eq_refl (IHt171 (weakenCutoffty c13 (bindPat p)) (appendHvl k63 (bindPat p)) (weaken_shifthvl_ty (bindPat p) ins)))))).
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
  Inductive substhvl_tm (k62 : Hvl) : (forall (d50 : (Trace tm)) (k63 : Hvl) (k64 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k62 X0 (HS tm k62) k62)
    | substhvl_tm_there_tm
        {d50 : (Trace tm)} {k63 : Hvl}
        {k64 : Hvl} :
        (substhvl_tm k62 d50 k63 k64) -> (substhvl_tm k62 (XS tm d50) (HS tm k63) (HS tm k64))
    | substhvl_tm_there_ty
        {d50 : (Trace tm)} {k63 : Hvl}
        {k64 : Hvl} :
        (substhvl_tm k62 d50 k63 k64) -> (substhvl_tm k62 (XS ty d50) (HS ty k63) (HS ty k64)).
  Inductive substhvl_ty (k62 : Hvl) : (forall (d50 : (Trace ty)) (k63 : Hvl) (k64 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k62 X0 (HS ty k62) k62)
    | substhvl_ty_there_tm
        {d50 : (Trace ty)} {k63 : Hvl}
        {k64 : Hvl} :
        (substhvl_ty k62 d50 k63 k64) -> (substhvl_ty k62 (XS tm d50) (HS tm k63) (HS tm k64))
    | substhvl_ty_there_ty
        {d50 : (Trace ty)} {k63 : Hvl}
        {k64 : Hvl} :
        (substhvl_ty k62 d50 k63 k64) -> (substhvl_ty k62 (XS ty d50) (HS ty k63) (HS ty k64)).
  Lemma weaken_substhvl_tm  :
    (forall {k63 : Hvl} (k62 : Hvl) {d50 : (Trace tm)} {k64 : Hvl} {k65 : Hvl} ,
      (substhvl_tm k63 d50 k64 k65) -> (substhvl_tm k63 (weakenTrace d50 k62) (appendHvl k64 k62) (appendHvl k65 k62))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k63 : Hvl} (k62 : Hvl) {d50 : (Trace ty)} {k64 : Hvl} {k65 : Hvl} ,
      (substhvl_ty k63 d50 k64 k65) -> (substhvl_ty k63 (weakenTrace d50 k62) (appendHvl k64 k62) (appendHvl k65 k62))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k66 : Hvl} {s18 : Tm} (wft : (wfTm k66 s18)) :
    (forall {d50 : (Trace tm)} {k67 : Hvl} {k68 : Hvl} ,
      (substhvl_tm k66 d50 k67 k68) -> (forall {x59 : (Index tm)} ,
        (wfindex k67 x59) -> (wfTm k68 (substIndex d50 s18 x59)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k66 : Hvl} {S44 : Ty} (wft : (wfTy k66 S44)) :
    (forall {d50 : (Trace ty)} {k67 : Hvl} {k68 : Hvl} ,
      (substhvl_ty k66 d50 k67 k68) -> (forall {X43 : (Index ty)} ,
        (wfindex k67 X43) -> (wfTy k68 (tsubstIndex d50 S44 X43)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k66 : Hvl} :
    (forall {d50 : (Trace tm)} {k67 : Hvl} {k68 : Hvl} ,
      (substhvl_tm k66 d50 k67 k68) -> (forall {X43 : (Index ty)} ,
        (wfindex k67 X43) -> (wfindex k68 X43))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k66 : Hvl} :
    (forall {d50 : (Trace ty)} {k67 : Hvl} {k68 : Hvl} ,
      (substhvl_ty k66 d50 k67 k68) -> (forall {x59 : (Index tm)} ,
        (wfindex k67 x59) -> (wfindex k68 x59))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k66 : Hvl} : (forall (k67 : Hvl) ,
    (forall (S44 : Ty) (wf0 : (wfTy k67 S44)) ,
      (forall {d50 : (Trace tm)} {k68 : Hvl} ,
        (substhvl_tm k66 d50 k67 k68) -> (wfTy k68 S44)))) := (ind_wfTy (fun (k67 : Hvl) (S44 : Ty) (wf0 : (wfTy k67 S44)) =>
    (forall {d50 : (Trace tm)} {k68 : Hvl} ,
      (substhvl_tm k66 d50 k67 k68) -> (wfTy k68 S44))) (fun (k67 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k67 X43)) {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTy_tvar k68 (substhvl_tm_wfindex_ty del wfi))) (fun (k67 : Hvl) (T1 : Ty) (wf0 : (wfTy k67 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k67 T2)) IHT6 {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTy_tarr k68 (IHT5 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)) (IHT6 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)))) (fun (k67 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k67) T)) IHT5 {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTy_tall k68 (IHT5 (weakenTrace d50 (HS ty H0)) (HS ty k68) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k67 : Hvl) (T1 : Ty) (wf0 : (wfTy k67 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k67 T2)) IHT6 {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTy_tprod k68 (IHT5 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)) (IHT6 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTy {k66 : Hvl} {S44 : Ty} (wf : (wfTy k66 S44)) : (forall (k67 : Hvl) ,
    (forall (S45 : Ty) (wf0 : (wfTy k67 S45)) ,
      (forall {d50 : (Trace ty)} {k68 : Hvl} ,
        (substhvl_ty k66 d50 k67 k68) -> (wfTy k68 (tsubstTy d50 S44 S45))))) := (ind_wfTy (fun (k67 : Hvl) (S45 : Ty) (wf0 : (wfTy k67 S45)) =>
    (forall {d50 : (Trace ty)} {k68 : Hvl} ,
      (substhvl_ty k66 d50 k67 k68) -> (wfTy k68 (tsubstTy d50 S44 S45)))) (fun (k67 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k67 X43)) {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k67 : Hvl) (T1 : Ty) (wf0 : (wfTy k67 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k67 T2)) IHT6 {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTy_tarr k68 (IHT5 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)) (IHT6 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)))) (fun (k67 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k67) T)) IHT5 {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTy_tall k68 (IHT5 (weakenTrace d50 (HS ty H0)) (HS ty k68) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k67 : Hvl) (T1 : Ty) (wf0 : (wfTy k67 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k67 T2)) IHT6 {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTy_tprod k68 (IHT5 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)) (IHT6 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del))))).
  Definition substhvl_tm_wfPat {k66 : Hvl} : (forall (k67 : Hvl) ,
    (forall (p35 : Pat) (wf0 : (wfPat k67 p35)) ,
      (forall {d50 : (Trace tm)} {k68 : Hvl} ,
        (substhvl_tm k66 d50 k67 k68) -> (wfPat k68 p35)))) := (fun (k67 : Hvl) =>
    (ind_wfPat k67 (fun (p35 : Pat) (wf0 : (wfPat k67 p35)) =>
      (forall {d50 : (Trace tm)} {k68 : Hvl} ,
        (substhvl_tm k66 d50 k67 k68) -> (wfPat k68 p35))) (fun (T : Ty) (wf0 : (wfTy k67 T)) {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
      (wfPat_pvar k68 (substhvl_tm_wfTy k67 T wf0 (weaken_substhvl_tm H0 del)))) (fun (p1 : Pat) (wf0 : (wfPat k67 p1)) IHp0 (p2 : Pat) (wf1 : (wfPat k67 p2)) IHp3 {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
      (wfPat_pprod k68 (IHp0 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)) (IHp3 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_ty_wfPat {k66 : Hvl} {S44 : Ty} (wf : (wfTy k66 S44)) : (forall (k67 : Hvl) ,
    (forall (p35 : Pat) (wf0 : (wfPat k67 p35)) ,
      (forall {d50 : (Trace ty)} {k68 : Hvl} ,
        (substhvl_ty k66 d50 k67 k68) -> (wfPat k68 (tsubstPat d50 S44 p35))))) := (fun (k67 : Hvl) =>
    (ind_wfPat k67 (fun (p35 : Pat) (wf0 : (wfPat k67 p35)) =>
      (forall {d50 : (Trace ty)} {k68 : Hvl} ,
        (substhvl_ty k66 d50 k67 k68) -> (wfPat k68 (tsubstPat d50 S44 p35)))) (fun (T : Ty) (wf0 : (wfTy k67 T)) {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
      (wfPat_pvar k68 (substhvl_ty_wfTy wf k67 T wf0 (weaken_substhvl_ty H0 del)))) (fun (p1 : Pat) (wf0 : (wfPat k67 p1)) IHp0 (p2 : Pat) (wf1 : (wfPat k67 p2)) IHp3 {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
      (wfPat_pprod k68 (IHp0 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)) (IHp3 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)))))).
  Definition substhvl_tm_wfTm {k66 : Hvl} {s18 : Tm} (wf : (wfTm k66 s18)) : (forall (k67 : Hvl) ,
    (forall (s19 : Tm) (wf0 : (wfTm k67 s19)) ,
      (forall {d50 : (Trace tm)} {k68 : Hvl} ,
        (substhvl_tm k66 d50 k67 k68) -> (wfTm k68 (substTm d50 s18 s19))))) := (ind_wfTm (fun (k67 : Hvl) (s19 : Tm) (wf0 : (wfTm k67 s19)) =>
    (forall {d50 : (Trace tm)} {k68 : Hvl} ,
      (substhvl_tm k66 d50 k67 k68) -> (wfTm k68 (substTm d50 s18 s19)))) (fun (k67 : Hvl) {x59 : (Index tm)} (wfi : (wfindex k67 x59)) {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k67 : Hvl) (T : Ty) (wf0 : (wfTy k67 T)) (t : Tm) (wf1 : (wfTm (HS tm k67) t)) IHt170 {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTm_abs k68 (substhvl_tm_wfTy k67 T wf0 (weaken_substhvl_tm H0 del)) (IHt170 (weakenTrace d50 (HS tm H0)) (HS tm k68) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k67 : Hvl) (t1 : Tm) (wf0 : (wfTm k67 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k67 t2)) IHt171 {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTm_app k68 (IHt170 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)) (IHt171 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)))) (fun (k67 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k67) t)) IHt170 {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTm_tabs k68 (IHt170 (weakenTrace d50 (HS ty H0)) (HS ty k68) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k67 : Hvl) (t : Tm) (wf0 : (wfTm k67 t)) IHt170 (T : Ty) (wf1 : (wfTy k67 T)) {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTm_tapp k68 (IHt170 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k67 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k67 : Hvl) (t1 : Tm) (wf0 : (wfTm k67 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k67 t2)) IHt171 {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTm_prod k68 (IHt170 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)) (IHt171 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)))) (fun (k67 : Hvl) (p : Pat) (wf0 : (wfPat k67 p)) (t1 : Tm) (wf1 : (wfTm k67 t1)) IHt170 (t2 : Tm) (wf2 : (wfTm (appendHvl k67 (bindPat p)) t2)) IHt171 {d50 : (Trace tm)} {k68 : Hvl} (del : (substhvl_tm k66 d50 k67 k68)) =>
    (wfTm_lett k68 (substhvl_tm_wfPat k67 p wf0 (weaken_substhvl_tm H0 del)) (IHt170 (weakenTrace d50 H0) k68 (weaken_substhvl_tm H0 del)) (IHt171 (weakenTrace d50 (bindPat p)) (appendHvl k68 (bindPat p)) (weaken_substhvl_tm (bindPat p) del))))).
  Definition substhvl_ty_wfTm {k66 : Hvl} {S44 : Ty} (wf : (wfTy k66 S44)) : (forall (k67 : Hvl) ,
    (forall (s18 : Tm) (wf0 : (wfTm k67 s18)) ,
      (forall {d50 : (Trace ty)} {k68 : Hvl} ,
        (substhvl_ty k66 d50 k67 k68) -> (wfTm k68 (tsubstTm d50 S44 s18))))) := (ind_wfTm (fun (k67 : Hvl) (s18 : Tm) (wf0 : (wfTm k67 s18)) =>
    (forall {d50 : (Trace ty)} {k68 : Hvl} ,
      (substhvl_ty k66 d50 k67 k68) -> (wfTm k68 (tsubstTm d50 S44 s18)))) (fun (k67 : Hvl) {x59 : (Index tm)} (wfi : (wfindex k67 x59)) {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTm_var k68 (substhvl_ty_wfindex_tm del wfi))) (fun (k67 : Hvl) (T : Ty) (wf0 : (wfTy k67 T)) (t : Tm) (wf1 : (wfTm (HS tm k67) t)) IHt170 {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTm_abs k68 (substhvl_ty_wfTy wf k67 T wf0 (weaken_substhvl_ty H0 del)) (IHt170 (weakenTrace d50 (HS tm H0)) (HS tm k68) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k67 : Hvl) (t1 : Tm) (wf0 : (wfTm k67 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k67 t2)) IHt171 {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTm_app k68 (IHt170 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)) (IHt171 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)))) (fun (k67 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k67) t)) IHt170 {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTm_tabs k68 (IHt170 (weakenTrace d50 (HS ty H0)) (HS ty k68) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k67 : Hvl) (t : Tm) (wf0 : (wfTm k67 t)) IHt170 (T : Ty) (wf1 : (wfTy k67 T)) {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTm_tapp k68 (IHt170 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k67 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k67 : Hvl) (t1 : Tm) (wf0 : (wfTm k67 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k67 t2)) IHt171 {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTm_prod k68 (IHt170 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)) (IHt171 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)))) (fun (k67 : Hvl) (p : Pat) (wf0 : (wfPat k67 p)) (t1 : Tm) (wf1 : (wfTm k67 t1)) IHt170 (t2 : Tm) (wf2 : (wfTm (appendHvl k67 (bindPat p)) t2)) IHt171 {d50 : (Trace ty)} {k68 : Hvl} (del : (substhvl_ty k66 d50 k67 k68)) =>
    (wfTm_lett k68 (substhvl_ty_wfPat wf k67 p wf0 (weaken_substhvl_ty H0 del)) (IHt170 (weakenTrace d50 H0) k68 (weaken_substhvl_ty H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k68) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))) eq_refl (IHt171 (weakenTrace d50 (bindPat p)) (appendHvl k68 (bindPat p)) (weaken_substhvl_ty (bindPat p) del)))))).
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
Fixpoint subhvl_tm (k66 : Hvl) {struct k66} : Prop :=
  match k66 with
    | (H0) => True
    | (HS a k66) => match a with
      | (tm) => (subhvl_tm k66)
      | _ => False
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k66 : Hvl) (k67 : Hvl) ,
    (subhvl_tm k66) -> (subhvl_tm k67) -> (subhvl_tm (appendHvl k66 k67))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfPat_strengthen_subhvl_tm  :
  (forall (k63 : Hvl) (k62 : Hvl) (p34 : Pat) ,
    (subhvl_tm k63) -> (wfPat (appendHvl k62 k63) (weakenPat p34 k63)) -> (wfPat k62 p34)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k65 : Hvl) (k64 : Hvl) (S43 : Ty) ,
    (subhvl_tm k65) -> (wfTy (appendHvl k64 k65) (weakenTy S43 k65)) -> (wfTy k64 S43)).
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
    | etvar (G : Env).
  Fixpoint appendEnv (G : Env) (G0 : Env) : Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
      | (etvar G1) => (etvar (appendEnv G G1))
    end.
  Fixpoint domainEnv (G : Env) : Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS tm (domainEnv G0))
      | (etvar G0) => (HS ty (domainEnv G0))
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
      | (etvar G0) => (etvar (shiftEnv c13 G0))
    end.
  Fixpoint tshiftEnv (c13 : (Cutoff ty)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c13 G0) (tshiftTy (weakenCutoffty c13 (domainEnv G0)) T))
      | (etvar G0) => (etvar (tshiftEnv c13 G0))
    end.
  Fixpoint substEnv (d50 : (Trace tm)) (s18 : Tm) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d50 s18 G0) T)
      | (etvar G0) => (etvar (substEnv d50 s18 G0))
    end.
  Fixpoint tsubstEnv (d50 : (Trace ty)) (S44 : Ty) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d50 S44 G0) (tsubstTy (weakenTrace d50 (domainEnv G0)) S44 T))
      | (etvar G0) => (etvar (tsubstEnv d50 S44 G0))
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
    (forall (d50 : (Trace tm)) (s18 : Tm) (G : Env) ,
      ((domainEnv (substEnv d50 s18 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d50 : (Trace ty)) (S44 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d50 S44 G)) =
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
      (forall (d50 : (Trace tm)) (s18 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d50 s18 (appendEnv G G0)) =
        (appendEnv (substEnv d50 s18 G) (substEnv (weakenTrace d50 (domainEnv G)) s18 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d50 : (Trace ty)) (S44 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d50 S44 (appendEnv G G0)) =
        (appendEnv (tsubstEnv d50 S44 G) (tsubstEnv (weakenTrace d50 (domainEnv G)) S44 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          {T79 : Ty} :
          (wfTy (domainEnv G) T79) -> (lookup_evar (evar G T79) I0 T79)
      | lookup_evar_there_evar
          {G : Env} {x59 : (Index tm)}
          {T79 : Ty} {T80 : Ty} :
          (lookup_evar G x59 T79) -> (lookup_evar (evar G T80) (IS x59) T79)
      | lookup_evar_there_etvar
          {G : Env} {x59 : (Index tm)}
          {T79 : Ty} :
          (lookup_evar G x59 T79) -> (lookup_evar (etvar G) x59 (tshiftTy C0 T79)).
    Inductive lookup_etvar : Env -> (Index ty) -> Prop :=
      | lookup_etvar_here {G : Env}
          : (lookup_etvar (etvar G) I0)
      | lookup_etvar_there_evar
          {G : Env} {X43 : (Index ty)}
          {T79 : Ty} :
          (lookup_etvar G X43) -> (lookup_etvar (evar G T79) X43)
      | lookup_etvar_there_etvar
          {G : Env} {X43 : (Index ty)} :
          (lookup_etvar G X43) -> (lookup_etvar (etvar G) (IS X43)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (S44 : Ty) (S45 : Ty) ,
        (lookup_evar (evar G S44) I0 S45) -> (S44 =
        S45)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x59 : (Index tm)} ,
        (forall {S44 : Ty} ,
          (lookup_evar G x59 S44) -> (forall {S45 : Ty} ,
            (lookup_evar G x59 S45) -> (S44 =
            S45)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x59 : (Index tm)} {S44 : Ty} ,
        (lookup_evar G x59 S44) -> (wfTy (domainEnv G) S44)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x59 : (Index tm)} {T79 : Ty} ,
        (lookup_evar G x59 T79) -> (lookup_evar (appendEnv G G0) (weakenIndextm x59 (domainEnv G0)) (weakenTy T79 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X43 : (Index ty)} ,
        (lookup_etvar G X43) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X43 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x59 : (Index tm)} {S44 : Ty} ,
        (lookup_evar G x59 S44) -> (wfindex (domainEnv G) x59)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X43 : (Index ty)} ,
        (lookup_etvar G X43) -> (wfindex (domainEnv G) X43)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T79 : Ty} :
        (shift_evar C0 G (evar G T79))
    | shiftevar_there_evar
        {c13 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c13 G G0) -> (shift_evar (CS c13) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c13 : (Cutoff tm)} {G : Env}
        {G0 : Env} :
        (shift_evar c13 G G0) -> (shift_evar c13 (etvar G) (etvar G0)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c13 : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c13 G0 G1) -> (shift_evar (weakenCutofftm c13 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env} :
        (shift_etvar C0 G (etvar G))
    | shiftetvar_there_evar
        {c13 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c13 G G0) -> (shift_etvar c13 (evar G T) (evar G0 (tshiftTy c13 T)))
    | shiftetvar_there_etvar
        {c13 : (Cutoff ty)} {G : Env}
        {G0 : Env} :
        (shift_etvar c13 G G0) -> (shift_etvar (CS c13) (etvar G) (etvar G0)).
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
  Inductive subst_evar (G : Env) (T79 : Ty) (s18 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T79 s18 X0 (evar G T79) G)
    | subst_evar_there_evar
        {d50 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T79 s18 d50 G0 G1) -> (subst_evar G T79 s18 (XS tm d50) (evar G0 T) (evar G1 T))
    | subst_evar_there_etvar
        {d50 : (Trace tm)} {G0 : Env}
        {G1 : Env} :
        (subst_evar G T79 s18 d50 G0 G1) -> (subst_evar G T79 s18 (XS ty d50) (etvar G0) (etvar G1)).
  Lemma weaken_subst_evar {G : Env} {T79 : Ty} {s18 : Tm} :
    (forall (G0 : Env) {d50 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T79 s18 d50 G1 G2) -> (subst_evar G T79 s18 (weakenTrace d50 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (S44 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G S44 X0 (etvar G) G)
    | subst_etvar_there_evar
        {d50 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G S44 d50 G0 G1) -> (subst_etvar G S44 (XS tm d50) (evar G0 T) (evar G1 (tsubstTy d50 S44 T)))
    | subst_etvar_there_etvar
        {d50 : (Trace ty)} {G0 : Env}
        {G1 : Env} :
        (subst_etvar G S44 d50 G0 G1) -> (subst_etvar G S44 (XS ty d50) (etvar G0) (etvar G1)).
  Lemma weaken_subst_etvar {G : Env} {S44 : Ty} :
    (forall (G0 : Env) {d50 : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G S44 d50 G1 G2) -> (subst_etvar G S44 (weakenTrace d50 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d50 S44 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s18 : Tm} {T79 : Ty} :
    (forall {d50 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T79 s18 d50 G0 G1) -> (substhvl_tm (domainEnv G) d50 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S44 : Ty} :
    (forall {d50 : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G S44 d50 G0 G1) -> (substhvl_ty (domainEnv G) d50 (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T79 : Ty} (wf : (wfTy (domainEnv G) T79)) ,
    (lookup_evar (appendEnv (evar G T79) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T79 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) ,
    (lookup_etvar (appendEnv (etvar G) G0) (weakenIndexty I0 (domainEnv G0)))).
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
  | H : (wfTy _ (tarr _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tall _)) |- _ => inversion H; subst; clear H
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
  | H : (wfTm _ (tabs _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tapp _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (prod _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (lett _ _ _)) |- _ => inversion H; subst; clear H
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
Lemma shift_evar_lookup_evar  :
  (forall {c13 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c13 G G0)) {x59 : (Index tm)} {T79 : Ty} ,
    (lookup_evar G x59 T79) -> (lookup_evar G0 (shiftIndex c13 x59) T79)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c13 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c13 G G0)) {X43 : (Index ty)} ,
    (lookup_etvar G X43) -> (lookup_etvar G0 X43)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c13 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c13 G G0)) {x59 : (Index tm)} {T79 : Ty} ,
    (lookup_evar G x59 T79) -> (lookup_evar G0 x59 (tshiftTy c13 T79))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c13 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c13 G G0)) {X43 : (Index ty)} ,
    (lookup_etvar G X43) -> (lookup_etvar G0 (tshiftIndex c13 X43))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} {T80 : Ty} {s18 : Tm} :
  (forall {d50 : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T80 s18 d50 G0 G1)) {X43 : (Index ty)} ,
    (lookup_etvar G0 X43) -> (lookup_etvar G1 X43)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} {S44 : Ty} (wf : (wfTy (domainEnv G) S44)) :
  (forall {d50 : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G S44 d50 G0 G1)) {x59 : (Index tm)} {T80 : Ty} ,
    (lookup_evar G0 x59 T80) -> (lookup_evar G1 x59 (tsubstTy d50 S44 T80))).
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
    | (tprod T0 T3) => (plus 1 (plus (size_Ty T0) (size_Ty T3)))
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
    | (tabs t0) => (plus 1 (size_Tm t0))
    | (tapp t3 T0) => (plus 1 (plus (size_Tm t3) (size_Ty T0)))
    | (prod t4 t5) => (plus 1 (plus (size_Tm t4) (size_Tm t5)))
    | (lett p t6 t7) => (plus 1 (plus (size_Pat p) (plus (size_Tm t6) (size_Tm t7))))
  end.
Lemma tshift_size_Ty  :
  (forall (S43 : Ty) (c10 : (Cutoff ty)) ,
    ((size_Ty (tshiftTy c10 S43)) =
    (size_Ty S43))).
Proof.
  apply_mutual_ind ind_Ty.
  - intros X38 c10.
  reflexivity.
  - intros T69 IHT69 T70 IHT70.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT69 c11)).
  + exact ((IHT70 c11)).
  - intros T71 IHT71.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT71 (CS c11))).
  - intros T72 IHT72 T73 IHT73.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT72 c11)).
  + exact ((IHT73 c11)).
Qed.

Lemma tshift_size_Pat  :
  (forall (p30 : Pat) (c11 : (Cutoff ty)) ,
    ((size_Pat (tshiftPat c11 p30)) =
    (size_Pat p30))).
Proof.
  apply_mutual_ind ind_Pat.
  - intros T74.
  pose proof ((tshift_size_Ty T74)) as IHT74.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT74 c11)).
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
  - intros T75 t152 IHt152.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt152 (CS c12))).
  - intros t153 IHt153 t154 IHt154.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt153 c12)).
  + exact ((IHt154 c12)).
  - intros t155 IHt155.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt155 c12)).
  - intros t156 IHt156 T76.
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
  - intros T77 t161 IHt161.
  pose proof ((tshift_size_Ty T77)) as IHT77.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT77 c13)).
  + exact ((IHt161 c13)).
  - intros t162 IHt162 t163 IHt163.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt162 c13)).
  + exact ((IHt163 c13)).
  - intros t164 IHt164.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt164 (CS c13))).
  - intros t165 IHt165 T78.
  pose proof ((tshift_size_Ty T78)) as IHT78.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt165 c13)).
  + exact ((IHT78 c13)).
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
  (forall (k62 : Hvl) (p34 : Pat) ,
    ((size_Pat (weakenPat p34 k62)) =
    (size_Pat p34))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k62 : Hvl) (s18 : Tm) ,
    ((size_Tm (weakenTm s18 k62)) =
    (size_Tm s18))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k62 : Hvl) (S43 : Ty) ,
    ((size_Ty (weakenTy S43 k62)) =
    (size_Ty S43))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : weaken_size.