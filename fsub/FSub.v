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
    | tall (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (T : Ty) (t : Tm)
    | tapp (t : Tm) (T : Ty).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  
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
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var (shiftIndex c x))
      | (abs T t) => (abs T (shiftTm (weakenCutofftm c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (shiftTm (weakenCutofftm c H0) t1) (shiftTm (weakenCutofftm c H0) t2))
      | (tabs T0 t0) => (tabs T0 (shiftTm (weakenCutofftm c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T1) => (tapp (shiftTm (weakenCutofftm c H0) t3) T1)
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tshiftTy (weakenCutoffty c H0) T) (tshiftTm (weakenCutoffty c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (tshiftTm (weakenCutoffty c H0) t1) (tshiftTm (weakenCutoffty c H0) t2))
      | (tabs T0 t0) => (tabs (tshiftTy (weakenCutoffty c H0) T0) (tshiftTm (weakenCutoffty c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T1) => (tapp (tshiftTm (weakenCutoffty c H0) t3) (tshiftTy (weakenCutoffty c H0) T1))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} : Ty :=
    match k with
      | (H0) => S0
      | (HS tm k) => (weakenTy S0 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S0 k))
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
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} : Tm :=
    match s0 with
      | (var x) => (substIndex d s x)
      | (abs T t) => (abs T (substTm (XS tm d) s t))
      | (app t1 t2) => (app (substTm d s t1) (substTm d s t2))
      | (tabs T0 t0) => (tabs T0 (substTm (XS ty d) s t0))
      | (tapp t3 T1) => (tapp (substTm d s t3) T1)
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tsubstTy d S0 T) (tsubstTm (XS tm d) S0 t))
      | (app t1 t2) => (app (tsubstTm d S0 t1) (tsubstTm d S0 t2))
      | (tabs T0 t0) => (tabs (tsubstTy d S0 T0) (tsubstTm (XS ty d) S0 t0))
      | (tapp t3 T1) => (tapp (tsubstTm d S0 t3) (tsubstTy d S0 T1))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : interaction.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : interaction.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k4 : Hvl) (x9 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k4) s (shiftIndex (weakenCutofftm C0 k4) x9)) =
      (var x9))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S0 : Ty) :
    (forall (k4 : Hvl) (X8 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k4) S0 (tshiftIndex (weakenCutoffty C0 k4) X8)) =
      (tvar X8))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Definition tsubst0_tshift0_Ty_reflection_ind := (ind_Ty (fun (S2 : Ty) =>
    (forall (k7 : Hvl) (S3 : Ty) ,
      ((tsubstTy (weakenTrace X0 k7) S3 (tshiftTy (weakenCutoffty C0 k7) S2)) =
      S2))) (fun (X14 : (Index ty)) =>
    (fun (k7 : Hvl) (S2 : Ty) =>
      (tsubstIndex0_tshiftIndex0_reflection_ind S2 k7 X14))) (fun (k7 : Hvl) (S2 : Ty) =>
    eq_refl) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tarr (IHT4 k7 S2) (IHT5 k7 S2))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tall (IHT4 k7 S2) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHT5 (HS ty k7) S2))))).
  Definition subst0_shift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (s1 : Tm) ,
      ((substTm (weakenTrace X0 k7) s1 (shiftTm (weakenCutofftm C0 k7) s0)) =
      s0))) (fun (x14 : (Index tm)) =>
    (fun (k7 : Hvl) (s0 : Tm) =>
      (substIndex0_shiftIndex0_reflection_ind s0 k7 x14))) (fun (T : Ty) (t : Tm) IHt29 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt29 (HS tm k7) s0)))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 app (IHt29 k7 s0) (IHt30 k7 s0))) (fun (T : Ty) (t : Tm) IHt29 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt29 (HS ty k7) s0)))) (fun (t : Tm) IHt29 (T : Ty) (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tapp (IHt29 k7 s0) eq_refl))).
  Definition tsubst0_tshift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (S2 : Ty) ,
      ((tsubstTm (weakenTrace X0 k7) S2 (tshiftTm (weakenCutoffty C0 k7) s0)) =
      s0))) (fun (x14 : (Index tm)) =>
    (fun (k7 : Hvl) (S2 : Ty) =>
      eq_refl)) (fun (T : Ty) (t : Tm) IHt29 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 abs (let IHT := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT k7 S2)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt29 (HS tm k7) S2)))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 app (IHt29 k7 S2) (IHt30 k7 S2))) (fun (T : Ty) (t : Tm) IHt29 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tabs (let IHT := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT k7 S2)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt29 (HS ty k7) S2)))) (fun (t : Tm) IHt29 (T : Ty) (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tapp (IHt29 k7 S2) (let IHT := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT k7 S2))))).
  Definition tsubstTy0_tshiftTy0_reflection (S3 : Ty) : (forall (S2 : Ty) ,
    ((tsubstTy X0 S2 (tshiftTy C0 S3)) =
    S3)) := (tsubst0_tshift0_Ty_reflection_ind S3 H0).
  Definition substTm0_shiftTm0_reflection (s1 : Tm) : (forall (s0 : Tm) ,
    ((substTm X0 s0 (shiftTm C0 s1)) =
    s1)) := (subst0_shift0_Tm_reflection_ind s1 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s0 : Tm) : (forall (S2 : Ty) ,
    ((tsubstTm X0 S2 (tshiftTm C0 s0)) =
    s0)) := (tsubst0_tshift0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff tm)) (x : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c) k) (shiftIndex (weakenCutofftm C0 k) x)) =
        (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c k) x)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff ty)) (X : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c) k) (tshiftIndex (weakenCutoffty C0 k) X)) =
        (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c k) X)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Definition tshift_tshift0_Ty_comm_ind := (ind_Ty (fun (S0 : Ty) =>
      (forall (k4 : Hvl) (c4 : (Cutoff ty)) ,
        ((tshiftTy (weakenCutoffty (CS c4) k4) (tshiftTy (weakenCutoffty C0 k4) S0)) =
        (tshiftTy (weakenCutoffty C0 k4) (tshiftTy (weakenCutoffty c4 k4) S0))))) (fun (X8 : (Index ty)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k4 c4 X8)))) (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
      eq_refl) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tarr (IHT4 k4 c4) (IHT5 k4 c4))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tall (IHT4 k4 c4) (IHT5 (HS ty k4) c4)))).
    Definition shift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm (CS c4) k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff tm)) =>
        (f_equal var (shiftIndex_shiftIndex0_comm_ind k4 c4 x9)))) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tabs eq_refl (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt19 k4 c4) eq_refl))).
    Definition shift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm c4 k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (shiftTm (weakenCutofftm c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff tm)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tabs eq_refl (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt19 k4 c4) eq_refl))).
    Definition tshift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty c4 k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (tshiftTm (weakenCutoffty c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 abs eq_refl (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tabs eq_refl (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt19 k4 c4) eq_refl))).
    Definition tshift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty (CS c4) k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 abs (let IHT := (tshift_tshift0_Ty_comm_ind T) in
      (IHT k4 c4)) (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tabs (let IHT := (tshift_tshift0_Ty_comm_ind T) in
      (IHT k4 c4)) (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt19 k4 c4) (let IHT := (tshift_tshift0_Ty_comm_ind T) in
      (IHT k4 c4))))).
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S0 : Ty) : (forall (c4 : (Cutoff ty)) ,
      ((tshiftTy (CS c4) (tshiftTy C0 S0)) =
      (tshiftTy C0 (tshiftTy c4 S0)))) := (tshift_tshift0_Ty_comm_ind S0 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c4 : (Cutoff tm)) ,
      ((shiftTm (CS c4) (shiftTm C0 s)) =
      (shiftTm C0 (shiftTm c4 s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c4 : (Cutoff tm)) ,
      ((shiftTm c4 (tshiftTm C0 s)) =
      (tshiftTm C0 (shiftTm c4 s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c4 : (Cutoff ty)) ,
      ((tshiftTm c4 (shiftTm C0 s)) =
      (shiftTm C0 (tshiftTm c4 s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c4 : (Cutoff ty)) ,
      ((tshiftTm (CS c4) (tshiftTm C0 s)) =
      (tshiftTm C0 (tshiftTm c4 s)))) := (tshift_tshift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k48 : Hvl) (c9 : (Cutoff ty)) (S32 : Ty) ,
      ((weakenTy (tshiftTy c9 S32) k48) =
      (tshiftTy (weakenCutoffty c9 k48) (weakenTy S32 k48)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k48 : Hvl) (c9 : (Cutoff tm)) (s14 : Tm) ,
      ((weakenTm (shiftTm c9 s14) k48) =
      (shiftTm (weakenCutofftm c9 k48) (weakenTm s14 k48)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k48 : Hvl) (c9 : (Cutoff ty)) (s14 : Tm) ,
      ((weakenTm (tshiftTm c9 s14) k48) =
      (tshiftTm (weakenCutoffty c9 k48) (weakenTm s14 k48)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c4 : (Cutoff tm)) (s0 : Tm) :
      (forall (k7 : Hvl) (x14 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c4 k7) (substIndex (weakenTrace X0 k7) s0 x14)) =
        (substIndex (weakenTrace X0 k7) (shiftTm c4 s0) (shiftIndex (weakenCutofftm (CS c4) k7) x14)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c4 : (Cutoff ty)) (s0 : Tm) :
      (forall (k7 : Hvl) (x14 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c4 k7) (substIndex (weakenTrace X0 k7) s0 x14)) =
        (substIndex (weakenTrace X0 k7) (tshiftTm c4 s0) x14))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c4 : (Cutoff ty)) (S2 : Ty) :
      (forall (k7 : Hvl) (X14 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c4 k7) (tsubstIndex (weakenTrace X0 k7) S2 X14)) =
        (tsubstIndex (weakenTrace X0 k7) (tshiftTy c4 S2) (tshiftIndex (weakenCutoffty (CS c4) k7) X14)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Definition tshift_tsubst0_Ty_comm_ind := (ind_Ty (fun (S5 : Ty) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (S6 : Ty) ,
        ((tshiftTy (weakenCutoffty c9 k12) (tsubstTy (weakenTrace X0 k12) S6 S5)) =
        (tsubstTy (weakenTrace X0 k12) (tshiftTy c9 S6) (tshiftTy (weakenCutoffty (CS c9) k12) S5))))) (fun (X21 : (Index ty)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
        (tshiftTy_tsubstIndex0_comm_ind c9 S5 k12 X21))) (fun (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tarr (IHT4 k12 c9 S5) (IHT5 k12 c9 S5))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tall (IHT4 k12 c9 S5) (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT5 (HS ty k12) c9 S5) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl)))))).
    Definition shift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff tm)) (s3 : Tm) ,
        ((shiftTm (weakenCutofftm c9 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (shiftTm c9 s3) (shiftTm (weakenCutofftm (CS c9) k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
        (shiftTm_substIndex0_comm_ind c9 s2 k12 x26))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 app (IHt49 k12 c9 s2) (IHt50 k12 c9 s2))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 tapp (IHt49 k12 c9 s2) eq_refl))).
    Definition shift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) ,
        ((shiftTm (weakenCutofftm c9 k12) (tsubstTm (weakenTrace X0 k12) S5 s2)) =
        (tsubstTm (weakenTrace X0 k12) S5 (shiftTm (weakenCutofftm c9 k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 app (IHt49 k12 c9 S5) (IHt50 k12 c9 S5))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 tapp (IHt49 k12 c9 S5) eq_refl))).
    Definition tshift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (s3 : Tm) ,
        ((tshiftTm (weakenCutoffty c9 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (tshiftTm c9 s3) (tshiftTm (weakenCutoffty c9 k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
        (tshiftTm_substIndex0_comm_ind c9 s2 k12 x26))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 app (IHt49 k12 c9 s2) (IHt50 k12 c9 s2))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tapp (IHt49 k12 c9 s2) eq_refl))).
    Definition tshift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) ,
        ((tshiftTm (weakenCutoffty c9 k12) (tsubstTm (weakenTrace X0 k12) S5 s2)) =
        (tsubstTm (weakenTrace X0 k12) (tshiftTy c9 S5) (tshiftTm (weakenCutoffty (CS c9) k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 abs (let IHT := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT k12 c9 S5)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 app (IHt49 k12 c9 S5) (IHt50 k12 c9 S5))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tabs (let IHT := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT k12 c9 S5)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tapp (IHt49 k12 c9 S5) (let IHT := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT k12 c9 S5))))).
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S6 : Ty) : (forall (c9 : (Cutoff ty)) (S5 : Ty) ,
      ((tshiftTy c9 (tsubstTy X0 S5 S6)) =
      (tsubstTy X0 (tshiftTy c9 S5) (tshiftTy (CS c9) S6)))) := (tshift_tsubst0_Ty_comm_ind S6 H0).
    Definition shiftTm_substTm0_comm (s3 : Tm) : (forall (c9 : (Cutoff tm)) (s2 : Tm) ,
      ((shiftTm c9 (substTm X0 s2 s3)) =
      (substTm X0 (shiftTm c9 s2) (shiftTm (CS c9) s3)))) := (shift_subst0_Tm_comm_ind s3 H0).
    Definition shiftTm_tsubstTm0_comm (s2 : Tm) : (forall (c9 : (Cutoff tm)) (S5 : Ty) ,
      ((shiftTm c9 (tsubstTm X0 S5 s2)) =
      (tsubstTm X0 S5 (shiftTm c9 s2)))) := (shift_tsubst0_Tm_comm_ind s2 H0).
    Definition tshiftTm_substTm0_comm (s3 : Tm) : (forall (c9 : (Cutoff ty)) (s2 : Tm) ,
      ((tshiftTm c9 (substTm X0 s2 s3)) =
      (substTm X0 (tshiftTm c9 s2) (tshiftTm c9 s3)))) := (tshift_subst0_Tm_comm_ind s3 H0).
    Definition tshiftTm_tsubstTm0_comm (s2 : Tm) : (forall (c9 : (Cutoff ty)) (S5 : Ty) ,
      ((tshiftTm c9 (tsubstTm X0 S5 s2)) =
      (tsubstTm X0 (tshiftTy c9 S5) (tshiftTm (CS c9) s2)))) := (tshift_tsubst0_Tm_comm_ind s2 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace tm)) (s2 : Tm) :
      (forall (k12 : Hvl) (x26 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d) k12) s2 (shiftIndex (weakenCutofftm C0 k12) x26)) =
        (shiftTm (weakenCutofftm C0 k12) (substIndex (weakenTrace d k12) s2 x26)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d : (Trace tm)) (s2 : Tm) :
      (forall (k12 : Hvl) (x26 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d) k12) s2 x26) =
        (tshiftTm (weakenCutoffty C0 k12) (substIndex (weakenTrace d k12) s2 x26)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d : (Trace ty)) (S5 : Ty) :
      (forall (k12 : Hvl) (X21 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d) k12) S5 X21) =
        (tsubstIndex (weakenTrace d k12) S5 X21))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace ty)) (S5 : Ty) :
      (forall (k12 : Hvl) (X21 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d) k12) S5 (tshiftIndex (weakenCutoffty C0 k12) X21)) =
        (tshiftTy (weakenCutoffty C0 k12) (tsubstIndex (weakenTrace d k12) S5 X21)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Definition tsubst_tshift0_Ty_comm_ind := (ind_Ty (fun (S19 : Ty) =>
      (forall (k36 : Hvl) (d23 : (Trace ty)) (S20 : Ty) ,
        ((tsubstTy (weakenTrace (XS ty d23) k36) S20 (tshiftTy (weakenCutoffty C0 k36) S19)) =
        (tshiftTy (weakenCutoffty C0 k36) (tsubstTy (weakenTrace d23 k36) S20 S19))))) (fun (X28 : (Index ty)) =>
      (fun (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
        (tsubstIndex_tshiftTy0_comm_ind d23 S19 k36 X28))) (fun (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 tarr (IHT4 k36 d23 S19) (IHT5 k36 d23 S19))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 tall (IHT4 k36 d23 S19) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d23) k36 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT5 (HS ty k36) d23 S19) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d23 k36 (HS ty H0))) eq_refl eq_refl))))))).
    Definition subst_shift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k36 : Hvl) (d23 : (Trace tm)) (s13 : Tm) ,
        ((substTm (weakenTrace (XS tm d23) k36) s13 (shiftTm (weakenCutofftm C0 k36) s12)) =
        (shiftTm (weakenCutofftm C0 k36) (substTm (weakenTrace d23 k36) s13 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
        (substIndex_shiftTm0_comm_ind d23 s12 k36 x38))) (fun (T : Ty) (t : Tm) IHt69 (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d23) k36 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k36) d23 s12) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d23 k36 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 app (IHt69 k36 d23 s12) (IHt70 k36 d23 s12))) (fun (T : Ty) (t : Tm) IHt69 (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d23) k36 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k36) d23 s12) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d23 k36 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tapp (IHt69 k36 d23 s12) eq_refl))).
    Definition subst_tshift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k36 : Hvl) (d23 : (Trace tm)) (s13 : Tm) ,
        ((substTm (weakenTrace (XS ty d23) k36) s13 (tshiftTm (weakenCutoffty C0 k36) s12)) =
        (tshiftTm (weakenCutoffty C0 k36) (substTm (weakenTrace d23 k36) s13 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
        (substIndex_tshiftTm0_comm_ind d23 s12 k36 x38))) (fun (T : Ty) (t : Tm) IHt69 (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d23) k36 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k36) d23 s12) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d23 k36 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 app (IHt69 k36 d23 s12) (IHt70 k36 d23 s12))) (fun (T : Ty) (t : Tm) IHt69 (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d23) k36 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k36) d23 s12) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d23 k36 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k36 : Hvl) (d23 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tapp (IHt69 k36 d23 s12) eq_refl))).
    Definition tsubst_shift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) ,
        ((tsubstTm (weakenTrace d23 k36) S19 (shiftTm (weakenCutofftm C0 k36) s12)) =
        (shiftTm (weakenCutofftm C0 k36) (tsubstTm (weakenTrace d23 k36) S19 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt69 (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d23 k36 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k36) d23 S19) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d23 k36 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 app (IHt69 k36 d23 S19) (IHt70 k36 d23 S19))) (fun (T : Ty) (t : Tm) IHt69 (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d23 k36 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k36) d23 S19) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d23 k36 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 tapp (IHt69 k36 d23 S19) eq_refl))).
    Definition tsubst_tshift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) ,
        ((tsubstTm (weakenTrace (XS ty d23) k36) S19 (tshiftTm (weakenCutoffty C0 k36) s12)) =
        (tshiftTm (weakenCutoffty C0 k36) (tsubstTm (weakenTrace d23 k36) S19 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt69 (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 abs (let IHT := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT k36 d23 S19)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d23) k36 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k36) d23 S19) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d23 k36 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 app (IHt69 k36 d23 S19) (IHt70 k36 d23 S19))) (fun (T : Ty) (t : Tm) IHt69 (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 tabs (let IHT := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT k36 d23 S19)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d23) k36 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k36) d23 S19) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d23 k36 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k36 : Hvl) (d23 : (Trace ty)) (S19 : Ty) =>
      (f_equal2 tapp (IHt69 k36 d23 S19) (let IHT := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT k36 d23 S19))))).
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S29 : Ty) : (forall (d32 : (Trace ty)) (S28 : Ty) ,
      ((tsubstTy (XS ty d32) S28 (tshiftTy C0 S29)) =
      (tshiftTy C0 (tsubstTy d32 S28 S29)))) := (tsubst_tshift0_Ty_comm_ind S29 H0).
    Definition substTm_shiftTm0_comm (s13 : Tm) : (forall (d32 : (Trace tm)) (s12 : Tm) ,
      ((substTm (XS tm d32) s12 (shiftTm C0 s13)) =
      (shiftTm C0 (substTm d32 s12 s13)))) := (subst_shift0_Tm_comm_ind s13 H0).
    Definition substTm_tshiftTm0_comm (s13 : Tm) : (forall (d32 : (Trace tm)) (s12 : Tm) ,
      ((substTm (XS ty d32) s12 (tshiftTm C0 s13)) =
      (tshiftTm C0 (substTm d32 s12 s13)))) := (subst_tshift0_Tm_comm_ind s13 H0).
    Definition tsubstTm_shiftTm0_comm (s12 : Tm) : (forall (d32 : (Trace ty)) (S28 : Ty) ,
      ((tsubstTm d32 S28 (shiftTm C0 s12)) =
      (shiftTm C0 (tsubstTm d32 S28 s12)))) := (tsubst_shift0_Tm_comm_ind s12 H0).
    Definition tsubstTm_tshiftTm0_comm (s12 : Tm) : (forall (d32 : (Trace ty)) (S28 : Ty) ,
      ((tsubstTm (XS ty d32) S28 (tshiftTm C0 s12)) =
      (tshiftTm C0 (tsubstTm d32 S28 s12)))) := (tsubst_tshift0_Tm_comm_ind s12 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Definition tsubst_tm_Ty_ind := (ind_Ty (fun (S28 : Ty) =>
      (forall (k45 : Hvl) (d32 : (Trace ty)) (S29 : Ty) ,
        ((tsubstTy (weakenTrace (XS tm d32) k45) S29 S28) =
        (tsubstTy (weakenTrace d32 k45) S29 S28)))) (fun (X32 : (Index ty)) =>
      (fun (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) =>
        (tsubstIndex_shiftTy0_comm_ind d32 S28 k45 X32))) (fun (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) =>
      (f_equal2 tarr (IHT4 k45 d32 S28) (IHT5 k45 d32 S28))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) =>
      (f_equal2 tall (IHT4 k45 d32 S28) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d32) k45 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT5 (HS ty k45) d32 S28) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d32 k45 (HS ty H0))) eq_refl eq_refl)))))).
    Definition tsubst_tm_Tm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) ,
        ((tsubstTm (weakenTrace (XS tm d32) k45) S28 s12) =
        (tsubstTm (weakenTrace d32 k45) S28 s12)))) (fun (x41 : (Index tm)) =>
      (fun (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt74 (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) =>
      (f_equal2 abs (let IHT := (tsubst_tm_Ty_ind T) in
      (IHT k45 d32 S28)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d32) k45 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt74 (HS tm k45) d32 S28) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d32 k45 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt74 (t2 : Tm) IHt75 (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) =>
      (f_equal2 app (IHt74 k45 d32 S28) (IHt75 k45 d32 S28))) (fun (T : Ty) (t : Tm) IHt74 (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) =>
      (f_equal2 tabs (let IHT := (tsubst_tm_Ty_ind T) in
      (IHT k45 d32 S28)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d32) k45 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt74 (HS ty k45) d32 S28) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d32 k45 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt74 (T : Ty) (k45 : Hvl) (d32 : (Trace ty)) (S28 : Ty) =>
      (f_equal2 tapp (IHt74 k45 d32 S28) (let IHT := (tsubst_tm_Ty_ind T) in
      (IHT k45 d32 S28))))).
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S29 : Ty) : (forall (d32 : (Trace ty)) (S28 : Ty) ,
      ((tsubstTy (XS tm d32) S28 S29) =
      (tsubstTy d32 S28 S29))) := (tsubst_tm_Ty_ind S29 H0).
    Definition tsubstTm_tm (s12 : Tm) : (forall (d32 : (Trace ty)) (S28 : Ty) ,
      ((tsubstTm (XS tm d32) S28 s12) =
      (tsubstTm d32 S28 s12))) := (tsubst_tm_Tm_ind s12 H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d32 : (Trace tm)) (s12 : Tm) (s13 : Tm) :
      (forall (k45 : Hvl) (x41 : (Index tm)) ,
        ((substTm (weakenTrace d32 k45) s12 (substIndex (weakenTrace X0 k45) s13 x41)) =
        (substTm (weakenTrace X0 k45) (substTm d32 s12 s13) (substIndex (weakenTrace (XS tm d32) k45) s12 x41)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d32 : (Trace ty)) (S28 : Ty) (s12 : Tm) :
      (forall (k45 : Hvl) (x41 : (Index tm)) ,
        ((tsubstTm (weakenTrace d32 k45) S28 (substIndex (weakenTrace X0 k45) s12 x41)) =
        (substIndex (weakenTrace X0 k45) (tsubstTm d32 S28 s12) x41))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d32 : (Trace ty)) (S28 : Ty) (S29 : Ty) :
      (forall (k45 : Hvl) (X32 : (Index ty)) ,
        ((tsubstTy (weakenTrace d32 k45) S28 (tsubstIndex (weakenTrace X0 k45) S29 X32)) =
        (tsubstTy (weakenTrace X0 k45) (tsubstTy d32 S28 S29) (tsubstIndex (weakenTrace (XS ty d32) k45) S28 X32)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d32 : (Trace tm)) (s12 : Tm) (S28 : Ty) :
      (forall (k45 : Hvl) (x41 : (Index tm)) ,
        ((substIndex (weakenTrace d32 k45) s12 x41) =
        (tsubstTm (weakenTrace X0 k45) S28 (substIndex (weakenTrace (XS ty d32) k45) s12 x41)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition tsubst_tsubst0_Ty_comm_ind := (ind_Ty (fun (S32 : Ty) =>
      (forall (k48 : Hvl) (d35 : (Trace ty)) (S33 : Ty) (S34 : Ty) ,
        ((tsubstTy (weakenTrace d35 k48) S33 (tsubstTy (weakenTrace X0 k48) S34 S32)) =
        (tsubstTy (weakenTrace X0 k48) (tsubstTy d35 S33 S34) (tsubstTy (weakenTrace (XS ty d35) k48) S33 S32))))) (fun (X37 : (Index ty)) =>
      (fun (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) =>
        (tsubstTy_tsubstIndex0_commright_ind d35 S32 S33 k48 X37))) (fun (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) =>
      (f_equal2 tarr (IHT4 k48 d35 S32 S33) (IHT5 k48 d35 S32 S33))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) =>
      (f_equal2 tall (IHT4 k48 d35 S32 S33) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d35 k48 (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k48 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT5 (HS ty k48) d35 S32 S33) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k48 (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d35) k48 (HS ty H0))) eq_refl eq_refl))))))).
    Definition subst_subst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k48 : Hvl) (d35 : (Trace tm)) (s15 : Tm) (s16 : Tm) ,
        ((substTm (weakenTrace d35 k48) s15 (substTm (weakenTrace X0 k48) s16 s14)) =
        (substTm (weakenTrace X0 k48) (substTm d35 s15 s16) (substTm (weakenTrace (XS tm d35) k48) s15 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
        (substTm_substIndex0_commright_ind d35 s14 s15 k48 x47))) (fun (T : Ty) (t : Tm) IHt84 (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d35 k48 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k48 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k48) d35 s14 s15) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k48 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d35) k48 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 app (IHt84 k48 d35 s14 s15) (IHt85 k48 d35 s14 s15))) (fun (T : Ty) (t : Tm) IHt84 (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d35 k48 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k48 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k48) d35 s14 s15) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k48 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d35) k48 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 tapp (IHt84 k48 d35 s14 s15) eq_refl))).
    Definition subst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k48 : Hvl) (d35 : (Trace tm)) (s15 : Tm) (S32 : Ty) ,
        ((substTm (weakenTrace d35 k48) s15 (tsubstTm (weakenTrace X0 k48) S32 s14)) =
        (tsubstTm (weakenTrace X0 k48) S32 (substTm (weakenTrace (XS ty d35) k48) s15 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (S32 : Ty) =>
        (substTy_tsubstIndex0_commleft_ind d35 s14 S32 k48 x47))) (fun (T : Ty) (t : Tm) IHt84 (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (S32 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d35 k48 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k48 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k48) d35 s14 S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k48 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d35) k48 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (S32 : Ty) =>
      (f_equal2 app (IHt84 k48 d35 s14 S32) (IHt85 k48 d35 s14 S32))) (fun (T : Ty) (t : Tm) IHt84 (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (S32 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d35 k48 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k48 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k48) d35 s14 S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k48 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d35) k48 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (S32 : Ty) =>
      (f_equal2 tapp (IHt84 k48 d35 s14 S32) eq_refl))).
    Definition tsubst_subst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (s15 : Tm) ,
        ((tsubstTm (weakenTrace d35 k48) S32 (substTm (weakenTrace X0 k48) s15 s14)) =
        (substTm (weakenTrace X0 k48) (tsubstTm d35 S32 s15) (tsubstTm (weakenTrace d35 k48) S32 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (s14 : Tm) =>
        (tsubstTm_substIndex0_commright_ind d35 S32 s14 k48 x47))) (fun (T : Ty) (t : Tm) IHt84 (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (s14 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d35 k48 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k48 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k48) d35 S32 s14) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k48 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d35 k48 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (s14 : Tm) =>
      (f_equal2 app (IHt84 k48 d35 S32 s14) (IHt85 k48 d35 S32 s14))) (fun (T : Ty) (t : Tm) IHt84 (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (s14 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d35 k48 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k48 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k48) d35 S32 s14) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k48 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d35 k48 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (s14 : Tm) =>
      (f_equal2 tapp (IHt84 k48 d35 S32 s14) eq_refl))).
    Definition tsubst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
        ((tsubstTm (weakenTrace d35 k48) S32 (tsubstTm (weakenTrace X0 k48) S33 s14)) =
        (tsubstTm (weakenTrace X0 k48) (tsubstTy d35 S32 S33) (tsubstTm (weakenTrace (XS ty d35) k48) S32 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt84 (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) =>
      (f_equal2 abs (let IHT := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT k48 d35 S32 S33)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d35 k48 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k48 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k48) d35 S32 S33) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k48 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d35) k48 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) =>
      (f_equal2 app (IHt84 k48 d35 S32 S33) (IHt85 k48 d35 S32 S33))) (fun (T : Ty) (t : Tm) IHt84 (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) =>
      (f_equal2 tabs (let IHT := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT k48 d35 S32 S33)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d35 k48 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k48 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k48) d35 S32 S33) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k48 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d35) k48 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) =>
      (f_equal2 tapp (IHt84 k48 d35 S32 S33) (let IHT := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT k48 d35 S32 S33))))).
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S34 : Ty) : (forall (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
      ((tsubstTy d35 S32 (tsubstTy X0 S33 S34)) =
      (tsubstTy X0 (tsubstTy d35 S32 S33) (tsubstTy (XS ty d35) S32 S34)))) := (tsubst_tsubst0_Ty_comm_ind S34 H0).
    Definition substTm_substTm0_comm (s16 : Tm) : (forall (d35 : (Trace tm)) (s14 : Tm) (s15 : Tm) ,
      ((substTm d35 s14 (substTm X0 s15 s16)) =
      (substTm X0 (substTm d35 s14 s15) (substTm (XS tm d35) s14 s16)))) := (subst_subst0_Tm_comm_ind s16 H0).
    Definition substTm_tsubstTm0_comm (s15 : Tm) : (forall (d35 : (Trace tm)) (s14 : Tm) (S32 : Ty) ,
      ((substTm d35 s14 (tsubstTm X0 S32 s15)) =
      (tsubstTm X0 S32 (substTm (XS ty d35) s14 s15)))) := (subst_tsubst0_Tm_comm_ind s15 H0).
    Definition tsubstTm_substTm0_comm (s15 : Tm) : (forall (d35 : (Trace ty)) (S32 : Ty) (s14 : Tm) ,
      ((tsubstTm d35 S32 (substTm X0 s14 s15)) =
      (substTm X0 (tsubstTm d35 S32 s14) (tsubstTm d35 S32 s15)))) := (tsubst_subst0_Tm_comm_ind s15 H0).
    Definition tsubstTm_tsubstTm0_comm (s14 : Tm) : (forall (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
      ((tsubstTm d35 S32 (tsubstTm X0 S33 s14)) =
      (tsubstTm X0 (tsubstTy d35 S32 S33) (tsubstTm (XS ty d35) S32 s14)))) := (tsubst_tsubst0_Tm_comm_ind s14 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
        ((weakenTy (tsubstTy d35 S32 S33) k48) =
        (tsubstTy (weakenTrace d35 k48) S32 (weakenTy S33 k48)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k48 : Hvl) (d35 : (Trace tm)) (s14 : Tm) (s15 : Tm) ,
        ((weakenTm (substTm d35 s14 s15) k48) =
        (substTm (weakenTrace d35 k48) s14 (weakenTm s15 k48)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k48 : Hvl) (d35 : (Trace ty)) (S32 : Ty) (s14 : Tm) ,
        ((weakenTm (tsubstTm d35 S32 s14) k48) =
        (tsubstTm (weakenTrace d35 k48) S32 (weakenTm s14 k48)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenTy_append  :
      (forall (S32 : Ty) (k48 : Hvl) (k49 : Hvl) ,
        ((weakenTy (weakenTy S32 k48) k49) =
        (weakenTy S32 (appendHvl k48 k49)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s14 : Tm) (k48 : Hvl) (k49 : Hvl) ,
        ((weakenTm (weakenTm s14 k48) k49) =
        (weakenTm s14 (appendHvl k48 k49)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
  End WeakenAppend.
End SubstSubstInteraction.
 Hint Rewrite substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
Section WellFormed.
  Fixpoint wfindex {a : Namespace} (k48 : Hvl) (i : (Index a)) {struct k48} : Prop :=
    match k48 with
      | (H0) => False
      | (HS b k48) => match (eq_namespace_dec a b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k48 i)
        end
        | (right n) => (wfindex k48 i)
      end
    end.
  Inductive wfTy (k48 : Hvl) : Ty -> Prop :=
    | wfTy_tvar {X43 : (Index ty)}
        (wfi : (wfindex k48 X43)) :
        (wfTy k48 (tvar X43))
    | wfTy_top : (wfTy k48 (top))
    | wfTy_tarr {T84 : Ty}
        (wf : (wfTy k48 T84)) {T85 : Ty}
        (wf0 : (wfTy k48 T85)) :
        (wfTy k48 (tarr T84 T85))
    | wfTy_tall {T86 : Ty}
        (wf : (wfTy k48 T86)) {T87 : Ty}
        (wf0 : (wfTy (HS ty k48) T87)) :
        (wfTy k48 (tall T86 T87)).
  Inductive wfTm (k48 : Hvl) : Tm -> Prop :=
    | wfTm_var {x52 : (Index tm)}
        (wfi : (wfindex k48 x52)) :
        (wfTm k48 (var x52))
    | wfTm_abs {T84 : Ty}
        (wf : (wfTy k48 T84)) {t94 : Tm}
        (wf0 : (wfTm (HS tm k48) t94)) :
        (wfTm k48 (abs T84 t94))
    | wfTm_app {t95 : Tm}
        (wf : (wfTm k48 t95)) {t96 : Tm}
        (wf0 : (wfTm k48 t96)) :
        (wfTm k48 (app t95 t96))
    | wfTm_tabs {T85 : Ty}
        (wf : (wfTy k48 T85)) {t97 : Tm}
        (wf0 : (wfTm (HS ty k48) t97)) :
        (wfTm k48 (tabs T85 t97))
    | wfTm_tapp {t98 : Tm}
        (wf : (wfTm k48 t98)) {T86 : Ty}
        (wf0 : (wfTy k48 T86)) :
        (wfTm k48 (tapp t98 T86)).
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c12 : (Cutoff tm)) (k48 : Hvl) (k49 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k48 : Hvl)
        :
        (shifthvl_tm C0 k48 (HS tm k48))
    | shifthvl_tm_there_tm
        (c12 : (Cutoff tm)) (k48 : Hvl)
        (k49 : Hvl) :
        (shifthvl_tm c12 k48 k49) -> (shifthvl_tm (CS c12) (HS tm k48) (HS tm k49))
    | shifthvl_tm_there_ty
        (c12 : (Cutoff tm)) (k48 : Hvl)
        (k49 : Hvl) :
        (shifthvl_tm c12 k48 k49) -> (shifthvl_tm c12 (HS ty k48) (HS ty k49)).
  Inductive shifthvl_ty : (forall (c12 : (Cutoff ty)) (k48 : Hvl) (k49 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k48 : Hvl)
        :
        (shifthvl_ty C0 k48 (HS ty k48))
    | shifthvl_ty_there_tm
        (c12 : (Cutoff ty)) (k48 : Hvl)
        (k49 : Hvl) :
        (shifthvl_ty c12 k48 k49) -> (shifthvl_ty c12 (HS tm k48) (HS tm k49))
    | shifthvl_ty_there_ty
        (c12 : (Cutoff ty)) (k48 : Hvl)
        (k49 : Hvl) :
        (shifthvl_ty c12 k48 k49) -> (shifthvl_ty (CS c12) (HS ty k48) (HS ty k49)).
  Lemma weaken_shifthvl_tm  :
    (forall (k48 : Hvl) {c12 : (Cutoff tm)} {k49 : Hvl} {k50 : Hvl} ,
      (shifthvl_tm c12 k49 k50) -> (shifthvl_tm (weakenCutofftm c12 k48) (appendHvl k49 k48) (appendHvl k50 k48))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k48 : Hvl) {c12 : (Cutoff ty)} {k49 : Hvl} {k50 : Hvl} ,
      (shifthvl_ty c12 k49 k50) -> (shifthvl_ty (weakenCutoffty c12 k48) (appendHvl k49 k48) (appendHvl k50 k48))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c12 : (Cutoff tm)) (k48 : Hvl) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) (x52 : (Index tm)) ,
      (wfindex k48 x52) -> (wfindex k49 (shiftIndex c12 x52))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c12 : (Cutoff tm)) (k48 : Hvl) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) (X43 : (Index ty)) ,
      (wfindex k48 X43) -> (wfindex k49 X43)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c12 : (Cutoff ty)) (k48 : Hvl) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) (x52 : (Index tm)) ,
      (wfindex k48 x52) -> (wfindex k49 x52)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c12 : (Cutoff ty)) (k48 : Hvl) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) (X43 : (Index ty)) ,
      (wfindex k48 X43) -> (wfindex k49 (tshiftIndex c12 X43))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k48 : Hvl) ,
    (forall (S32 : Ty) (wf : (wfTy k48 S32)) ,
      (forall (c12 : (Cutoff tm)) (k49 : Hvl) ,
        (shifthvl_tm c12 k48 k49) -> (wfTy k49 S32)))) := (ind_wfTy (fun (k48 : Hvl) (S32 : Ty) (wf : (wfTy k48 S32)) =>
    (forall (c12 : (Cutoff tm)) (k49 : Hvl) ,
      (shifthvl_tm c12 k48 k49) -> (wfTy k49 S32))) (fun (k48 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k48 X43)) (c12 : (Cutoff tm)) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) =>
    (wfTy_tvar k49 (shift_wfindex_ty c12 k48 k49 ins X43 wfi))) (fun (k48 : Hvl) (c12 : (Cutoff tm)) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) =>
    (wfTy_top k49)) (fun (k48 : Hvl) (T1 : Ty) (wf : (wfTy k48 T1)) IHT4 (T2 : Ty) (wf0 : (wfTy k48 T2)) IHT5 (c12 : (Cutoff tm)) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) =>
    (wfTy_tarr k49 (IHT4 c12 k49 (weaken_shifthvl_tm H0 ins)) (IHT5 c12 k49 (weaken_shifthvl_tm H0 ins)))) (fun (k48 : Hvl) (T1 : Ty) (wf : (wfTy k48 T1)) IHT4 (T2 : Ty) (wf0 : (wfTy (HS ty k48) T2)) IHT5 (c12 : (Cutoff tm)) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) =>
    (wfTy_tall k49 (IHT4 c12 k49 (weaken_shifthvl_tm H0 ins)) (IHT5 c12 (HS ty k49) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k48 : Hvl) ,
    (forall (S32 : Ty) (wf : (wfTy k48 S32)) ,
      (forall (c12 : (Cutoff ty)) (k49 : Hvl) ,
        (shifthvl_ty c12 k48 k49) -> (wfTy k49 (tshiftTy c12 S32))))) := (ind_wfTy (fun (k48 : Hvl) (S32 : Ty) (wf : (wfTy k48 S32)) =>
    (forall (c12 : (Cutoff ty)) (k49 : Hvl) ,
      (shifthvl_ty c12 k48 k49) -> (wfTy k49 (tshiftTy c12 S32)))) (fun (k48 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k48 X43)) (c12 : (Cutoff ty)) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) =>
    (wfTy_tvar k49 (tshift_wfindex_ty c12 k48 k49 ins X43 wfi))) (fun (k48 : Hvl) (c12 : (Cutoff ty)) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) =>
    (wfTy_top k49)) (fun (k48 : Hvl) (T1 : Ty) (wf : (wfTy k48 T1)) IHT4 (T2 : Ty) (wf0 : (wfTy k48 T2)) IHT5 (c12 : (Cutoff ty)) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) =>
    (wfTy_tarr k49 (IHT4 c12 k49 (weaken_shifthvl_ty H0 ins)) (IHT5 c12 k49 (weaken_shifthvl_ty H0 ins)))) (fun (k48 : Hvl) (T1 : Ty) (wf : (wfTy k48 T1)) IHT4 (T2 : Ty) (wf0 : (wfTy (HS ty k48) T2)) IHT5 (c12 : (Cutoff ty)) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) =>
    (wfTy_tall k49 (IHT4 c12 k49 (weaken_shifthvl_ty H0 ins)) (IHT5 (CS c12) (HS ty k49) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfTm : (forall (k48 : Hvl) ,
    (forall (s14 : Tm) (wf : (wfTm k48 s14)) ,
      (forall (c12 : (Cutoff tm)) (k49 : Hvl) ,
        (shifthvl_tm c12 k48 k49) -> (wfTm k49 (shiftTm c12 s14))))) := (ind_wfTm (fun (k48 : Hvl) (s14 : Tm) (wf : (wfTm k48 s14)) =>
    (forall (c12 : (Cutoff tm)) (k49 : Hvl) ,
      (shifthvl_tm c12 k48 k49) -> (wfTm k49 (shiftTm c12 s14)))) (fun (k48 : Hvl) (x52 : (Index tm)) (wfi : (wfindex k48 x52)) (c12 : (Cutoff tm)) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) =>
    (wfTm_var k49 (shift_wfindex_tm c12 k48 k49 ins x52 wfi))) (fun (k48 : Hvl) (T : Ty) (wf : (wfTy k48 T)) (t : Tm) (wf0 : (wfTm (HS tm k48) t)) IHt94 (c12 : (Cutoff tm)) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) =>
    (wfTm_abs k49 (shift_wfTy k48 T wf c12 k49 (weaken_shifthvl_tm H0 ins)) (IHt94 (CS c12) (HS tm k49) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k48 : Hvl) (t1 : Tm) (wf : (wfTm k48 t1)) IHt94 (t2 : Tm) (wf0 : (wfTm k48 t2)) IHt95 (c12 : (Cutoff tm)) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) =>
    (wfTm_app k49 (IHt94 c12 k49 (weaken_shifthvl_tm H0 ins)) (IHt95 c12 k49 (weaken_shifthvl_tm H0 ins)))) (fun (k48 : Hvl) (T : Ty) (wf : (wfTy k48 T)) (t : Tm) (wf0 : (wfTm (HS ty k48) t)) IHt94 (c12 : (Cutoff tm)) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) =>
    (wfTm_tabs k49 (shift_wfTy k48 T wf c12 k49 (weaken_shifthvl_tm H0 ins)) (IHt94 c12 (HS ty k49) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k48 : Hvl) (t : Tm) (wf : (wfTm k48 t)) IHt94 (T : Ty) (wf0 : (wfTy k48 T)) (c12 : (Cutoff tm)) (k49 : Hvl) (ins : (shifthvl_tm c12 k48 k49)) =>
    (wfTm_tapp k49 (IHt94 c12 k49 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k48 T wf0 c12 k49 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTm : (forall (k48 : Hvl) ,
    (forall (s14 : Tm) (wf : (wfTm k48 s14)) ,
      (forall (c12 : (Cutoff ty)) (k49 : Hvl) ,
        (shifthvl_ty c12 k48 k49) -> (wfTm k49 (tshiftTm c12 s14))))) := (ind_wfTm (fun (k48 : Hvl) (s14 : Tm) (wf : (wfTm k48 s14)) =>
    (forall (c12 : (Cutoff ty)) (k49 : Hvl) ,
      (shifthvl_ty c12 k48 k49) -> (wfTm k49 (tshiftTm c12 s14)))) (fun (k48 : Hvl) (x52 : (Index tm)) (wfi : (wfindex k48 x52)) (c12 : (Cutoff ty)) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) =>
    (wfTm_var k49 (tshift_wfindex_tm c12 k48 k49 ins x52 wfi))) (fun (k48 : Hvl) (T : Ty) (wf : (wfTy k48 T)) (t : Tm) (wf0 : (wfTm (HS tm k48) t)) IHt94 (c12 : (Cutoff ty)) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) =>
    (wfTm_abs k49 (tshift_wfTy k48 T wf c12 k49 (weaken_shifthvl_ty H0 ins)) (IHt94 c12 (HS tm k49) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k48 : Hvl) (t1 : Tm) (wf : (wfTm k48 t1)) IHt94 (t2 : Tm) (wf0 : (wfTm k48 t2)) IHt95 (c12 : (Cutoff ty)) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) =>
    (wfTm_app k49 (IHt94 c12 k49 (weaken_shifthvl_ty H0 ins)) (IHt95 c12 k49 (weaken_shifthvl_ty H0 ins)))) (fun (k48 : Hvl) (T : Ty) (wf : (wfTy k48 T)) (t : Tm) (wf0 : (wfTm (HS ty k48) t)) IHt94 (c12 : (Cutoff ty)) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) =>
    (wfTm_tabs k49 (tshift_wfTy k48 T wf c12 k49 (weaken_shifthvl_ty H0 ins)) (IHt94 (CS c12) (HS ty k49) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k48 : Hvl) (t : Tm) (wf : (wfTm k48 t)) IHt94 (T : Ty) (wf0 : (wfTy k48 T)) (c12 : (Cutoff ty)) (k49 : Hvl) (ins : (shifthvl_ty c12 k48 k49)) =>
    (wfTm_tapp k49 (IHt94 c12 k49 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k48 T wf0 c12 k49 (weaken_shifthvl_ty H0 ins))))).
End ShiftWellFormed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfTm shift_wfTy tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfTm shift_wfTy tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfTm shift_wfTy tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfTm shift_wfTy tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_tm (k48 : Hvl) : (forall (d35 : (Trace tm)) (k49 : Hvl) (k50 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k48 X0 (HS tm k48) k48)
    | substhvl_tm_there_tm
        {d35 : (Trace tm)} {k49 : Hvl}
        {k50 : Hvl} :
        (substhvl_tm k48 d35 k49 k50) -> (substhvl_tm k48 (XS tm d35) (HS tm k49) (HS tm k50))
    | substhvl_tm_there_ty
        {d35 : (Trace tm)} {k49 : Hvl}
        {k50 : Hvl} :
        (substhvl_tm k48 d35 k49 k50) -> (substhvl_tm k48 (XS ty d35) (HS ty k49) (HS ty k50)).
  Inductive substhvl_ty (k48 : Hvl) : (forall (d35 : (Trace ty)) (k49 : Hvl) (k50 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k48 X0 (HS ty k48) k48)
    | substhvl_ty_there_tm
        {d35 : (Trace ty)} {k49 : Hvl}
        {k50 : Hvl} :
        (substhvl_ty k48 d35 k49 k50) -> (substhvl_ty k48 (XS tm d35) (HS tm k49) (HS tm k50))
    | substhvl_ty_there_ty
        {d35 : (Trace ty)} {k49 : Hvl}
        {k50 : Hvl} :
        (substhvl_ty k48 d35 k49 k50) -> (substhvl_ty k48 (XS ty d35) (HS ty k49) (HS ty k50)).
  Lemma weaken_substhvl_tm  :
    (forall {k49 : Hvl} (k48 : Hvl) {d35 : (Trace tm)} {k50 : Hvl} {k51 : Hvl} ,
      (substhvl_tm k49 d35 k50 k51) -> (substhvl_tm k49 (weakenTrace d35 k48) (appendHvl k50 k48) (appendHvl k51 k48))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k49 : Hvl} (k48 : Hvl) {d35 : (Trace ty)} {k50 : Hvl} {k51 : Hvl} ,
      (substhvl_ty k49 d35 k50 k51) -> (substhvl_ty k49 (weakenTrace d35 k48) (appendHvl k50 k48) (appendHvl k51 k48))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k48 : Hvl} {s14 : Tm} (wft : (wfTm k48 s14)) :
    (forall {d35 : (Trace tm)} {k49 : Hvl} {k50 : Hvl} ,
      (substhvl_tm k48 d35 k49 k50) -> (forall {x52 : (Index tm)} ,
        (wfindex k49 x52) -> (wfTm k50 (substIndex d35 s14 x52)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k48 : Hvl} {S32 : Ty} (wft : (wfTy k48 S32)) :
    (forall {d35 : (Trace ty)} {k49 : Hvl} {k50 : Hvl} ,
      (substhvl_ty k48 d35 k49 k50) -> (forall {X43 : (Index ty)} ,
        (wfindex k49 X43) -> (wfTy k50 (tsubstIndex d35 S32 X43)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k48 : Hvl} :
    (forall {d35 : (Trace tm)} {k49 : Hvl} {k50 : Hvl} ,
      (substhvl_tm k48 d35 k49 k50) -> (forall {X43 : (Index ty)} ,
        (wfindex k49 X43) -> (wfindex k50 X43))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k48 : Hvl} :
    (forall {d35 : (Trace ty)} {k49 : Hvl} {k50 : Hvl} ,
      (substhvl_ty k48 d35 k49 k50) -> (forall {x52 : (Index tm)} ,
        (wfindex k49 x52) -> (wfindex k50 x52))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k48 : Hvl} : (forall (k49 : Hvl) ,
    (forall (S32 : Ty) (wf0 : (wfTy k49 S32)) ,
      (forall {d35 : (Trace tm)} {k50 : Hvl} ,
        (substhvl_tm k48 d35 k49 k50) -> (wfTy k50 S32)))) := (ind_wfTy (fun (k49 : Hvl) (S32 : Ty) (wf0 : (wfTy k49 S32)) =>
    (forall {d35 : (Trace tm)} {k50 : Hvl} ,
      (substhvl_tm k48 d35 k49 k50) -> (wfTy k50 S32))) (fun (k49 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k49 X43)) {d35 : (Trace tm)} {k50 : Hvl} (del : (substhvl_tm k48 d35 k49 k50)) =>
    (wfTy_tvar k50 (substhvl_tm_wfindex_ty del wfi))) (fun (k49 : Hvl) {d35 : (Trace tm)} {k50 : Hvl} (del : (substhvl_tm k48 d35 k49 k50)) =>
    (wfTy_top k50)) (fun (k49 : Hvl) (T1 : Ty) (wf0 : (wfTy k49 T1)) IHT4 (T2 : Ty) (wf1 : (wfTy k49 T2)) IHT5 {d35 : (Trace tm)} {k50 : Hvl} (del : (substhvl_tm k48 d35 k49 k50)) =>
    (wfTy_tarr k50 (IHT4 (weakenTrace d35 H0) k50 (weaken_substhvl_tm H0 del)) (IHT5 (weakenTrace d35 H0) k50 (weaken_substhvl_tm H0 del)))) (fun (k49 : Hvl) (T1 : Ty) (wf0 : (wfTy k49 T1)) IHT4 (T2 : Ty) (wf1 : (wfTy (HS ty k49) T2)) IHT5 {d35 : (Trace tm)} {k50 : Hvl} (del : (substhvl_tm k48 d35 k49 k50)) =>
    (wfTy_tall k50 (IHT4 (weakenTrace d35 H0) k50 (weaken_substhvl_tm H0 del)) (IHT5 (weakenTrace d35 (HS ty H0)) (HS ty k50) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k48 : Hvl} {S32 : Ty} (wf : (wfTy k48 S32)) : (forall (k49 : Hvl) ,
    (forall (S33 : Ty) (wf0 : (wfTy k49 S33)) ,
      (forall {d35 : (Trace ty)} {k50 : Hvl} ,
        (substhvl_ty k48 d35 k49 k50) -> (wfTy k50 (tsubstTy d35 S32 S33))))) := (ind_wfTy (fun (k49 : Hvl) (S33 : Ty) (wf0 : (wfTy k49 S33)) =>
    (forall {d35 : (Trace ty)} {k50 : Hvl} ,
      (substhvl_ty k48 d35 k49 k50) -> (wfTy k50 (tsubstTy d35 S32 S33)))) (fun (k49 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k49 X43)) {d35 : (Trace ty)} {k50 : Hvl} (del : (substhvl_ty k48 d35 k49 k50)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k49 : Hvl) {d35 : (Trace ty)} {k50 : Hvl} (del : (substhvl_ty k48 d35 k49 k50)) =>
    (wfTy_top k50)) (fun (k49 : Hvl) (T1 : Ty) (wf0 : (wfTy k49 T1)) IHT4 (T2 : Ty) (wf1 : (wfTy k49 T2)) IHT5 {d35 : (Trace ty)} {k50 : Hvl} (del : (substhvl_ty k48 d35 k49 k50)) =>
    (wfTy_tarr k50 (IHT4 (weakenTrace d35 H0) k50 (weaken_substhvl_ty H0 del)) (IHT5 (weakenTrace d35 H0) k50 (weaken_substhvl_ty H0 del)))) (fun (k49 : Hvl) (T1 : Ty) (wf0 : (wfTy k49 T1)) IHT4 (T2 : Ty) (wf1 : (wfTy (HS ty k49) T2)) IHT5 {d35 : (Trace ty)} {k50 : Hvl} (del : (substhvl_ty k48 d35 k49 k50)) =>
    (wfTy_tall k50 (IHT4 (weakenTrace d35 H0) k50 (weaken_substhvl_ty H0 del)) (IHT5 (weakenTrace d35 (HS ty H0)) (HS ty k50) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfTm {k48 : Hvl} {s14 : Tm} (wf : (wfTm k48 s14)) : (forall (k49 : Hvl) ,
    (forall (s15 : Tm) (wf0 : (wfTm k49 s15)) ,
      (forall {d35 : (Trace tm)} {k50 : Hvl} ,
        (substhvl_tm k48 d35 k49 k50) -> (wfTm k50 (substTm d35 s14 s15))))) := (ind_wfTm (fun (k49 : Hvl) (s15 : Tm) (wf0 : (wfTm k49 s15)) =>
    (forall {d35 : (Trace tm)} {k50 : Hvl} ,
      (substhvl_tm k48 d35 k49 k50) -> (wfTm k50 (substTm d35 s14 s15)))) (fun (k49 : Hvl) {x52 : (Index tm)} (wfi : (wfindex k49 x52)) {d35 : (Trace tm)} {k50 : Hvl} (del : (substhvl_tm k48 d35 k49 k50)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k49 : Hvl) (T : Ty) (wf0 : (wfTy k49 T)) (t : Tm) (wf1 : (wfTm (HS tm k49) t)) IHt94 {d35 : (Trace tm)} {k50 : Hvl} (del : (substhvl_tm k48 d35 k49 k50)) =>
    (wfTm_abs k50 (substhvl_tm_wfTy k49 T wf0 (weaken_substhvl_tm H0 del)) (IHt94 (weakenTrace d35 (HS tm H0)) (HS tm k50) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k49 : Hvl) (t1 : Tm) (wf0 : (wfTm k49 t1)) IHt94 (t2 : Tm) (wf1 : (wfTm k49 t2)) IHt95 {d35 : (Trace tm)} {k50 : Hvl} (del : (substhvl_tm k48 d35 k49 k50)) =>
    (wfTm_app k50 (IHt94 (weakenTrace d35 H0) k50 (weaken_substhvl_tm H0 del)) (IHt95 (weakenTrace d35 H0) k50 (weaken_substhvl_tm H0 del)))) (fun (k49 : Hvl) (T : Ty) (wf0 : (wfTy k49 T)) (t : Tm) (wf1 : (wfTm (HS ty k49) t)) IHt94 {d35 : (Trace tm)} {k50 : Hvl} (del : (substhvl_tm k48 d35 k49 k50)) =>
    (wfTm_tabs k50 (substhvl_tm_wfTy k49 T wf0 (weaken_substhvl_tm H0 del)) (IHt94 (weakenTrace d35 (HS ty H0)) (HS ty k50) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k49 : Hvl) (t : Tm) (wf0 : (wfTm k49 t)) IHt94 (T : Ty) (wf1 : (wfTy k49 T)) {d35 : (Trace tm)} {k50 : Hvl} (del : (substhvl_tm k48 d35 k49 k50)) =>
    (wfTm_tapp k50 (IHt94 (weakenTrace d35 H0) k50 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k49 T wf1 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTm {k48 : Hvl} {S32 : Ty} (wf : (wfTy k48 S32)) : (forall (k49 : Hvl) ,
    (forall (s14 : Tm) (wf0 : (wfTm k49 s14)) ,
      (forall {d35 : (Trace ty)} {k50 : Hvl} ,
        (substhvl_ty k48 d35 k49 k50) -> (wfTm k50 (tsubstTm d35 S32 s14))))) := (ind_wfTm (fun (k49 : Hvl) (s14 : Tm) (wf0 : (wfTm k49 s14)) =>
    (forall {d35 : (Trace ty)} {k50 : Hvl} ,
      (substhvl_ty k48 d35 k49 k50) -> (wfTm k50 (tsubstTm d35 S32 s14)))) (fun (k49 : Hvl) {x52 : (Index tm)} (wfi : (wfindex k49 x52)) {d35 : (Trace ty)} {k50 : Hvl} (del : (substhvl_ty k48 d35 k49 k50)) =>
    (wfTm_var k50 (substhvl_ty_wfindex_tm del wfi))) (fun (k49 : Hvl) (T : Ty) (wf0 : (wfTy k49 T)) (t : Tm) (wf1 : (wfTm (HS tm k49) t)) IHt94 {d35 : (Trace ty)} {k50 : Hvl} (del : (substhvl_ty k48 d35 k49 k50)) =>
    (wfTm_abs k50 (substhvl_ty_wfTy wf k49 T wf0 (weaken_substhvl_ty H0 del)) (IHt94 (weakenTrace d35 (HS tm H0)) (HS tm k50) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k49 : Hvl) (t1 : Tm) (wf0 : (wfTm k49 t1)) IHt94 (t2 : Tm) (wf1 : (wfTm k49 t2)) IHt95 {d35 : (Trace ty)} {k50 : Hvl} (del : (substhvl_ty k48 d35 k49 k50)) =>
    (wfTm_app k50 (IHt94 (weakenTrace d35 H0) k50 (weaken_substhvl_ty H0 del)) (IHt95 (weakenTrace d35 H0) k50 (weaken_substhvl_ty H0 del)))) (fun (k49 : Hvl) (T : Ty) (wf0 : (wfTy k49 T)) (t : Tm) (wf1 : (wfTm (HS ty k49) t)) IHt94 {d35 : (Trace ty)} {k50 : Hvl} (del : (substhvl_ty k48 d35 k49 k50)) =>
    (wfTm_tabs k50 (substhvl_ty_wfTy wf k49 T wf0 (weaken_substhvl_ty H0 del)) (IHt94 (weakenTrace d35 (HS ty H0)) (HS ty k50) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k49 : Hvl) (t : Tm) (wf0 : (wfTm k49 t)) IHt94 (T : Ty) (wf1 : (wfTy k49 T)) {d35 : (Trace ty)} {k50 : Hvl} (del : (substhvl_ty k48 d35 k49 k50)) =>
    (wfTm_tapp k50 (IHt94 (weakenTrace d35 H0) k50 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k49 T wf1 (weaken_substhvl_ty H0 del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
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
  Fixpoint shiftEnv (c12 : (Cutoff tm)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftEnv c12 G0) T)
      | (etvar G0 T) => (etvar (shiftEnv c12 G0) T)
    end.
  Fixpoint tshiftEnv (c12 : (Cutoff ty)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c12 G0) (tshiftTy (weakenCutoffty c12 (domainEnv G0)) T))
      | (etvar G0 T) => (etvar (tshiftEnv c12 G0) (tshiftTy (weakenCutoffty c12 (domainEnv G0)) T))
    end.
  Fixpoint substEnv (d35 : (Trace tm)) (s14 : Tm) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d35 s14 G0) T)
      | (etvar G0 T) => (etvar (substEnv d35 s14 G0) T)
    end.
  Fixpoint tsubstEnv (d35 : (Trace ty)) (S32 : Ty) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d35 S32 G0) (tsubstTy (weakenTrace d35 (domainEnv G0)) S32 T))
      | (etvar G0 T) => (etvar (tsubstEnv d35 S32 G0) (tsubstTy (weakenTrace d35 (domainEnv G0)) S32 T))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c12 : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c12 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c12 : (Cutoff ty)) (G : Env) ,
      ((domainEnv (tshiftEnv c12 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d35 : (Trace tm)) (s14 : Tm) (G : Env) ,
      ((domainEnv (substEnv d35 s14 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d35 : (Trace ty)) (S32 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d35 S32 G)) =
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
      (forall (c12 : (Cutoff tm)) (G : Env) (G0 : Env) ,
        ((shiftEnv c12 (appendEnv G G0)) =
        (appendEnv (shiftEnv c12 G) (shiftEnv (weakenCutofftm c12 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftEnv_appendEnv  :
      (forall (c12 : (Cutoff ty)) (G : Env) (G0 : Env) ,
        ((tshiftEnv c12 (appendEnv G G0)) =
        (appendEnv (tshiftEnv c12 G) (tshiftEnv (weakenCutoffty c12 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d35 : (Trace tm)) (s14 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d35 s14 (appendEnv G G0)) =
        (appendEnv (substEnv d35 s14 G) (substEnv (weakenTrace d35 (domainEnv G)) s14 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d35 : (Trace ty)) (S32 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d35 S32 (appendEnv G G0)) =
        (appendEnv (tsubstEnv d35 S32 G) (tsubstEnv (weakenTrace d35 (domainEnv G)) S32 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          {T84 : Ty} :
          (wfTy (domainEnv G) T84) -> (lookup_evar (evar G T84) I0 T84)
      | lookup_evar_there_evar
          {G : Env} {x52 : (Index tm)}
          {T84 : Ty} {T85 : Ty} :
          (lookup_evar G x52 T84) -> (lookup_evar (evar G T85) (IS x52) T84)
      | lookup_evar_there_etvar
          {G : Env} {x52 : (Index tm)}
          {T84 : Ty} {T85 : Ty} :
          (lookup_evar G x52 T84) -> (lookup_evar (etvar G T85) x52 (tshiftTy C0 T84)).
    Inductive lookup_etvar : Env -> (Index ty) -> Ty -> Prop :=
      | lookup_etvar_here {G : Env}
          {T84 : Ty} :
          (wfTy (domainEnv G) T84) -> (lookup_etvar (etvar G T84) I0 (tshiftTy C0 T84))
      | lookup_etvar_there_evar
          {G : Env} {X43 : (Index ty)}
          {T84 : Ty} {T85 : Ty} :
          (lookup_etvar G X43 T84) -> (lookup_etvar (evar G T85) X43 T84)
      | lookup_etvar_there_etvar
          {G : Env} {X43 : (Index ty)}
          {T84 : Ty} {T85 : Ty} :
          (lookup_etvar G X43 T84) -> (lookup_etvar (etvar G T85) (IS X43) (tshiftTy C0 T84)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (S32 : Ty) (S33 : Ty) ,
        (lookup_evar (evar G S32) I0 S33) -> (S32 =
        S33)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (S32 : Ty) (S33 : Ty) ,
        (lookup_etvar (etvar G S32) I0 S33) -> ((tshiftTy C0 S32) =
        S33)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x52 : (Index tm)} ,
        (forall {S32 : Ty} ,
          (lookup_evar G x52 S32) -> (forall {S33 : Ty} ,
            (lookup_evar G x52 S33) -> (S32 =
            S33)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X43 : (Index ty)} ,
        (forall {S32 : Ty} ,
          (lookup_etvar G X43 S32) -> (forall {S33 : Ty} ,
            (lookup_etvar G X43 S33) -> (S32 =
            S33)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x52 : (Index tm)} {S32 : Ty} ,
        (lookup_evar G x52 S32) -> (wfTy (domainEnv G) S32)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X43 : (Index ty)} {S32 : Ty} ,
        (lookup_etvar G X43 S32) -> (wfTy (domainEnv G) S32)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x52 : (Index tm)} {T84 : Ty} ,
        (lookup_evar G x52 T84) -> (lookup_evar (appendEnv G G0) (weakenIndextm x52 (domainEnv G0)) (weakenTy T84 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X43 : (Index ty)} {T84 : Ty} ,
        (lookup_etvar G X43 T84) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X43 (domainEnv G0)) (weakenTy T84 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x52 : (Index tm)} {S32 : Ty} ,
        (lookup_evar G x52 S32) -> (wfindex (domainEnv G) x52)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X43 : (Index ty)} {S32 : Ty} ,
        (lookup_etvar G X43 S32) -> (wfindex (domainEnv G) X43)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T84 : Ty} :
        (shift_evar C0 G (evar G T84))
    | shiftevar_there_evar
        {c12 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c12 G G0) -> (shift_evar (CS c12) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c12 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c12 G G0) -> (shift_evar c12 (etvar G T) (etvar G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c12 : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c12 G0 G1) -> (shift_evar (weakenCutofftm c12 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {T84 : Ty} :
        (shift_etvar C0 G (etvar G T84))
    | shiftetvar_there_evar
        {c12 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c12 G G0) -> (shift_etvar c12 (evar G T) (evar G0 (tshiftTy c12 T)))
    | shiftetvar_there_etvar
        {c12 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c12 G G0) -> (shift_etvar (CS c12) (etvar G T) (etvar G0 (tshiftTy c12 T))).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c12 : (Cutoff ty)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c12 G0 G1) -> (shift_etvar (weakenCutoffty c12 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (tshiftEnv c12 G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c12 : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c12 G G0) -> (shifthvl_tm c12 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c12 : (Cutoff ty)} {G : Env} {G0 : Env} ,
      (shift_etvar c12 G G0) -> (shifthvl_ty c12 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T84 : Ty) (s14 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T84 s14 X0 (evar G T84) G)
    | subst_evar_there_evar
        {d35 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T84 s14 d35 G0 G1) -> (subst_evar G T84 s14 (XS tm d35) (evar G0 T) (evar G1 T))
    | subst_evar_there_etvar
        {d35 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T84 s14 d35 G0 G1) -> (subst_evar G T84 s14 (XS ty d35) (etvar G0 T) (etvar G1 T)).
  Lemma weaken_subst_evar {G : Env} {T84 : Ty} {s14 : Tm} :
    (forall (G0 : Env) {d35 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T84 s14 d35 G1 G2) -> (subst_evar G T84 s14 (weakenTrace d35 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (T84 : Ty) (S32 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G T84 S32 X0 (etvar G T84) G)
    | subst_etvar_there_evar
        {d35 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G T84 S32 d35 G0 G1) -> (subst_etvar G T84 S32 (XS tm d35) (evar G0 T) (evar G1 (tsubstTy d35 S32 T)))
    | subst_etvar_there_etvar
        {d35 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G T84 S32 d35 G0 G1) -> (subst_etvar G T84 S32 (XS ty d35) (etvar G0 T) (etvar G1 (tsubstTy d35 S32 T))).
  Lemma weaken_subst_etvar {G : Env} {T84 : Ty} {S32 : Ty} :
    (forall (G0 : Env) {d35 : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G T84 S32 d35 G1 G2) -> (subst_etvar G T84 S32 (weakenTrace d35 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d35 S32 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s14 : Tm} {T84 : Ty} :
    (forall {d35 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T84 s14 d35 G0 G1) -> (substhvl_tm (domainEnv G) d35 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S32 : Ty} {T85 : Ty} :
    (forall {d35 : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G T85 S32 d35 G0 G1) -> (substhvl_ty (domainEnv G) d35 (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T84 : Ty} (wf : (wfTy (domainEnv G) T84)) ,
    (lookup_evar (appendEnv (evar G T84) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T84 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {T84 : Ty} (wf : (wfTy (domainEnv G) T84)) ,
    (lookup_etvar (appendEnv (etvar G T84) G0) (weakenIndexty I0 (domainEnv G0)) (weakenTy (tshiftTy C0 T84) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfTm wfTy : infra.
 Hint Constructors wfTm wfTy : wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H : (wfTy _ (tvar _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (top)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tarr _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tall _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H : (wfTm _ (var _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (abs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (app _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tabs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tapp _ _)) |- _ => inversion H; subst; clear H
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
  (forall {c12 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c12 G G0)) {x52 : (Index tm)} {T84 : Ty} ,
    (lookup_evar G x52 T84) -> (lookup_evar G0 (shiftIndex c12 x52) T84)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c12 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c12 G G0)) {X43 : (Index ty)} {T84 : Ty} ,
    (lookup_etvar G X43 T84) -> (lookup_etvar G0 X43 T84)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c12 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c12 G G0)) {x52 : (Index tm)} {T84 : Ty} ,
    (lookup_evar G x52 T84) -> (lookup_evar G0 x52 (tshiftTy c12 T84))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c12 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c12 G G0)) {X43 : (Index ty)} {T84 : Ty} ,
    (lookup_etvar G X43 T84) -> (lookup_etvar G0 (tshiftIndex c12 X43) (tshiftTy c12 T84))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} {T86 : Ty} {s14 : Tm} :
  (forall {d35 : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T86 s14 d35 G0 G1)) {X43 : (Index ty)} {T87 : Ty} ,
    (lookup_etvar G0 X43 T87) -> (lookup_etvar G1 X43 T87)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} {T86 : Ty} {S32 : Ty} (wf : (wfTy (domainEnv G) S32)) :
  (forall {d35 : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G T86 S32 d35 G0 G1)) {x52 : (Index tm)} {T87 : Ty} ,
    (lookup_evar G0 x52 T87) -> (lookup_evar G1 x52 (tsubstTy d35 S32 T87))).
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
  end.
Fixpoint size_Tm (s : Tm) {struct s} : nat :=
  match s with
    | (var x) => 1
    | (abs T t) => (plus 1 (plus (size_Ty T) (size_Tm t)))
    | (app t1 t2) => (plus 1 (plus (size_Tm t1) (size_Tm t2)))
    | (tabs T0 t0) => (plus 1 (plus (size_Ty T0) (size_Tm t0)))
    | (tapp t3 T1) => (plus 1 (plus (size_Tm t3) (size_Ty T1)))
  end.
Lemma tshift_size_Ty  :
  (forall (S32 : Ty) (c9 : (Cutoff ty)) ,
    ((size_Ty (tshiftTy c9 S32)) =
    (size_Ty S32))).
Proof.
  apply_mutual_ind ind_Ty.
  - intros X38 c9.
  reflexivity.
  - intros c10; simpl; apply ((f_equal S)); reflexivity.
  - intros T74 IHT74 T75 IHT75.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT74 c10)).
  + exact ((IHT75 c10)).
  - intros T76 IHT76 T77 IHT77.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT76 c10)).
  + exact ((IHT77 (CS c10))).
Qed.

Lemma shift_size_Tm  :
  (forall (s14 : Tm) (c10 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c10 s14)) =
    (size_Tm s14))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros x48 c10.
  reflexivity.
  - intros T78 t84 IHt84.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt84 (CS c11))).
  - intros t85 IHt85 t86 IHt86.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt85 c11)).
  + exact ((IHt86 c11)).
  - intros T79 t87 IHt87.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt87 c11)).
  - intros t88 IHt88 T80.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt88 c11)).
  + reflexivity.
Qed.

Lemma tshift_size_Tm  :
  (forall (s14 : Tm) (c11 : (Cutoff ty)) ,
    ((size_Tm (tshiftTm c11 s14)) =
    (size_Tm s14))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros X41 c11.
  reflexivity.
  - intros T81 t89 IHt89.
  pose proof ((tshift_size_Ty T81)) as IHT81.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT81 c12)).
  + exact ((IHt89 c12)).
  - intros t90 IHt90 t91 IHt91.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt90 c12)).
  + exact ((IHt91 c12)).
  - intros T82 t92 IHt92.
  pose proof ((tshift_size_Ty T82)) as IHT82.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT82 c12)).
  + exact ((IHt92 (CS c12))).
  - intros t93 IHt93 T83.
  pose proof ((tshift_size_Ty T83)) as IHT83.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt93 c12)).
  + exact ((IHT83 c12)).
Qed.

 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Tm  :
  (forall (k48 : Hvl) (s14 : Tm) ,
    ((size_Tm (weakenTm s14 k48)) =
    (size_Tm s14))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k48 : Hvl) (S32 : Ty) ,
    ((size_Ty (weakenTy S32 k48)) =
    (size_Ty S32))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : weaken_size.