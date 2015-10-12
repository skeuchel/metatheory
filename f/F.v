Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.
Require Export Coq.Unicode.Utf8.
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
      | H0 => k
      | HS a k0 => (HS a (appendHvl k k0))
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
      | H0 => x
      | HS a k => match a with
        | tm => (IS (weakenIndextm x k))
        | _ => (weakenIndextm x k)
      end
    end.
  Fixpoint weakenIndexty (X : (Index ty)) (k : Hvl) {struct k} : (Index ty) :=
    match k with
      | H0 => X
      | HS a k => match a with
        | ty => (IS (weakenIndexty X k))
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
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (t : Tm)
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
      | H0 => c
      | HS a k => match a with
        | tm => (CS (weakenCutofftm c k))
        | _ => (weakenCutofftm c k)
      end
    end.
  Fixpoint weakenCutoffty (c : (Cutoff ty)) (k : Hvl) {struct k} : (Cutoff ty) :=
    match k with
      | H0 => c
      | HS a k => match a with
        | ty => (CS (weakenCutoffty c k))
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
      | C0 => (IS x)
      | CS c => match x with
        | I0 => I0
        | IS x => (IS (shiftIndex c x))
      end
    end.
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X : (Index ty)) {struct c} : (Index ty) :=
    match c with
      | C0 => (IS X)
      | CS c => match X with
        | I0 => I0
        | IS X => (IS (tshiftIndex c X))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff ty)) (S0 : Ty) {struct S0} : Ty :=
    match S0 with
      | tvar X => (tvar (tshiftIndex c X))
      | tarr T1 T2 => (tarr (tshiftTy (weakenCutoffty c H0) T1) (tshiftTy (weakenCutoffty c H0) T2))
      | tall T => (tall (tshiftTy (weakenCutoffty c (appendHvl (HS ty H0) H0)) T))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} : Tm :=
    match s with
      | var x => (var (shiftIndex c x))
      | abs T t => (abs T (shiftTm (weakenCutofftm c (appendHvl (HS tm H0) H0)) t))
      | app t1 t2 => (app (shiftTm (weakenCutofftm c H0) t1) (shiftTm (weakenCutofftm c H0) t2))
      | tabs t0 => (tabs (shiftTm (weakenCutofftm c (appendHvl (HS ty H0) H0)) t0))
      | tapp t3 T0 => (tapp (shiftTm (weakenCutofftm c H0) t3) T0)
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} : Tm :=
    match s with
      | var x => (var x)
      | abs T t => (abs (tshiftTy (weakenCutoffty c H0) T) (tshiftTm (weakenCutoffty c (appendHvl (HS tm H0) H0)) t))
      | app t1 t2 => (app (tshiftTm (weakenCutoffty c H0) t1) (tshiftTm (weakenCutoffty c H0) t2))
      | tabs t0 => (tabs (tshiftTm (weakenCutoffty c (appendHvl (HS ty H0) H0)) t0))
      | tapp t3 T0 => (tapp (tshiftTm (weakenCutoffty c H0) t3) (tshiftTy (weakenCutoffty c H0) T0))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} : Ty :=
    match k with
      | H0 => S0
      | HS tm k => (weakenTy S0 k)
      | HS ty k => (tshiftTy C0 (weakenTy S0 k))
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} : Tm :=
    match k with
      | H0 => s
      | HS tm k => (shiftTm C0 (weakenTm s k))
      | HS ty k => (tshiftTm C0 (weakenTm s k))
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
      | H0 => x
      | HS b k => (XS b (weakenTrace x k))
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
      | X0 => match x with
        | I0 => s
        | IS x => (var x)
      end
      | XS tm d => match x with
        | I0 => (var I0)
        | IS x => (shiftTm C0 (substIndex d s x))
      end
      | XS ty d => (tshiftTm C0 (substIndex d s x))
    end.
  Fixpoint tsubstIndex (d : (Trace ty)) (S0 : Ty) (X : (Index ty)) {struct d} : Ty :=
    match d with
      | X0 => match X with
        | I0 => S0
        | IS X => (tvar X)
      end
      | XS tm d => (tsubstIndex d S0 X)
      | XS ty d => match X with
        | I0 => (tvar I0)
        | IS X => (tshiftTy C0 (tsubstIndex d S0 X))
      end
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S1} : Ty :=
    match S1 with
      | tvar X => (tsubstIndex d S0 X)
      | tarr T1 T2 => (tarr (tsubstTy d S0 T1) (tsubstTy d S0 T2))
      | tall T => (tall (tsubstTy (XS ty d) S0 T))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} : Tm :=
    match s0 with
      | var x => (substIndex d s x)
      | abs T t => (abs T (substTm (XS tm d) s t))
      | app t1 t2 => (app (substTm d s t1) (substTm d s t2))
      | tabs t0 => (tabs (substTm (XS ty d) s t0))
      | tapp t3 T0 => (tapp (substTm d s t3) T0)
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} : Tm :=
    match s with
      | var x => (var x)
      | abs T t => (abs (tsubstTy d S0 T) (tsubstTm (XS tm d) S0 t))
      | app t1 t2 => (app (tsubstTm d S0 t1) (tsubstTm d S0 t2))
      | tabs t0 => (tabs (tsubstTm (XS ty d) S0 t0))
      | tapp t3 T0 => (tapp (tsubstTm d S0 t3) (tsubstTy d S0 T0))
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
      (tsubstIndex0_tshiftIndex0_reflection_ind S2 k7 X14))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tarr (IHT0 k7 S2) (IHT3 k7 S2))) (fun (T : Ty) IHT0 (k7 : Hvl) (S2 : Ty) =>
    (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHT0 (HS ty k7) S2))))).
  Definition subst0_shift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (s1 : Tm) ,
      ((substTm (weakenTrace X0 k7) s1 (shiftTm (weakenCutofftm C0 k7) s0)) =
      s0))) (fun (x14 : (Index tm)) =>
    (fun (k7 : Hvl) (s0 : Tm) =>
      (substIndex0_shiftIndex0_reflection_ind s0 k7 x14))) (fun (T : Ty) (t : Tm) IHt29 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt29 (HS tm k7) s0)))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 app (IHt29 k7 s0) (IHt30 k7 s0))) (fun (t : Tm) IHt29 (k7 : Hvl) (s0 : Tm) =>
    (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt29 (HS ty k7) s0)))) (fun (t : Tm) IHt29 (T : Ty) (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tapp (IHt29 k7 s0) eq_refl))).
  Definition tsubst0_tshift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (S2 : Ty) ,
      ((tsubstTm (weakenTrace X0 k7) S2 (tshiftTm (weakenCutoffty C0 k7) s0)) =
      s0))) (fun (x14 : (Index tm)) =>
    (fun (k7 : Hvl) (S2 : Ty) =>
      eq_refl)) (fun (T : Ty) (t : Tm) IHt29 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 abs (let IHT0 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT0 k7 S2)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt29 (HS tm k7) S2)))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 app (IHt29 k7 S2) (IHt30 k7 S2))) (fun (t : Tm) IHt29 (k7 : Hvl) (S2 : Ty) =>
    (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt29 (HS ty k7) S2)))) (fun (t : Tm) IHt29 (T : Ty) (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tapp (IHt29 k7 S2) (let IHT0 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT0 k7 S2))))).
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
        (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k4 c4 X8)))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tarr (IHT0 k4 c4) (IHT3 k4 c4))) (fun (T : Ty) IHT0 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal tall (IHT0 (HS ty k4) c4)))).
    Definition shift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm (CS c4) k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff tm)) =>
        (f_equal var (shiftIndex_shiftIndex0_comm_ind k4 c4 x9)))) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal tabs (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt19 k4 c4) eq_refl))).
    Definition shift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm c4 k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (shiftTm (weakenCutofftm c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff tm)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal tabs (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt19 k4 c4) eq_refl))).
    Definition tshift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty c4 k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (tshiftTm (weakenCutoffty c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 abs eq_refl (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal tabs (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt19 k4 c4) eq_refl))).
    Definition tshift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty (CS c4) k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 abs (let IHT0 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT0 k4 c4)) (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal tabs (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt19 k4 c4) (let IHT0 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT0 k4 c4))))).
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
    (forall (k46 : Hvl) (c9 : (Cutoff ty)) (S30 : Ty) ,
      ((weakenTy (tshiftTy c9 S30) k46) =
      (tshiftTy (weakenCutoffty c9 k46) (weakenTy S30 k46)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k46 : Hvl) (c9 : (Cutoff tm)) (s14 : Tm) ,
      ((weakenTm (shiftTm c9 s14) k46) =
      (shiftTm (weakenCutofftm c9 k46) (weakenTm s14 k46)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k46 : Hvl) (c9 : (Cutoff ty)) (s14 : Tm) ,
      ((weakenTm (tshiftTm c9 s14) k46) =
      (tshiftTm (weakenCutoffty c9 k46) (weakenTm s14 k46)))).
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
        (tshiftTy_tsubstIndex0_comm_ind c9 S5 k12 X21))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tarr (IHT0 k12 c9 S5) (IHT3 k12 c9 S5))) (fun (T : Ty) IHT0 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal tall (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT0 (HS ty k12) c9 S5) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl)))))).
    Definition shift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff tm)) (s3 : Tm) ,
        ((shiftTm (weakenCutofftm c9 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (shiftTm c9 s3) (shiftTm (weakenCutofftm (CS c9) k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
        (shiftTm_substIndex0_comm_ind c9 s2 k12 x26))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 app (IHt49 k12 c9 s2) (IHt50 k12 c9 s2))) (fun (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 tapp (IHt49 k12 c9 s2) eq_refl))).
    Definition shift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) ,
        ((shiftTm (weakenCutofftm c9 k12) (tsubstTm (weakenTrace X0 k12) S5 s2)) =
        (tsubstTm (weakenTrace X0 k12) S5 (shiftTm (weakenCutofftm c9 k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 app (IHt49 k12 c9 S5) (IHt50 k12 c9 S5))) (fun (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 tapp (IHt49 k12 c9 S5) eq_refl))).
    Definition tshift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (s3 : Tm) ,
        ((tshiftTm (weakenCutoffty c9 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (tshiftTm c9 s3) (tshiftTm (weakenCutoffty c9 k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
        (tshiftTm_substIndex0_comm_ind c9 s2 k12 x26))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 app (IHt49 k12 c9 s2) (IHt50 k12 c9 s2))) (fun (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tapp (IHt49 k12 c9 s2) eq_refl))).
    Definition tshift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) ,
        ((tshiftTm (weakenCutoffty c9 k12) (tsubstTm (weakenTrace X0 k12) S5 s2)) =
        (tsubstTm (weakenTrace X0 k12) (tshiftTy c9 S5) (tshiftTm (weakenCutoffty (CS c9) k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 abs (let IHT0 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT0 k12 c9 S5)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 app (IHt49 k12 c9 S5) (IHt50 k12 c9 S5))) (fun (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tapp (IHt49 k12 c9 S5) (let IHT0 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT0 k12 c9 S5))))).
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
    Definition tsubst_tshift0_Ty_comm_ind := (ind_Ty (fun (S18 : Ty) =>
      (forall (k35 : Hvl) (d22 : (Trace ty)) (S19 : Ty) ,
        ((tsubstTy (weakenTrace (XS ty d22) k35) S19 (tshiftTy (weakenCutoffty C0 k35) S18)) =
        (tshiftTy (weakenCutoffty C0 k35) (tsubstTy (weakenTrace d22 k35) S19 S18))))) (fun (X28 : (Index ty)) =>
      (fun (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
        (tsubstIndex_tshiftTy0_comm_ind d22 S18 k35 X28))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal2 tarr (IHT0 k35 d22 S18) (IHT3 k35 d22 S18))) (fun (T : Ty) IHT0 (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d22) k35 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT0 (HS ty k35) d22 S18) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d22 k35 (HS ty H0))) eq_refl eq_refl))))))).
    Definition subst_shift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k35 : Hvl) (d22 : (Trace tm)) (s13 : Tm) ,
        ((substTm (weakenTrace (XS tm d22) k35) s13 (shiftTm (weakenCutofftm C0 k35) s12)) =
        (shiftTm (weakenCutofftm C0 k35) (substTm (weakenTrace d22 k35) s13 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
        (substIndex_shiftTm0_comm_ind d22 s12 k35 x38))) (fun (T : Ty) (t : Tm) IHt69 (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d22) k35 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k35) d22 s12) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d22 k35 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 app (IHt69 k35 d22 s12) (IHt70 k35 d22 s12))) (fun (t : Tm) IHt69 (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d22) k35 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k35) d22 s12) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d22 k35 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tapp (IHt69 k35 d22 s12) eq_refl))).
    Definition subst_tshift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k35 : Hvl) (d22 : (Trace tm)) (s13 : Tm) ,
        ((substTm (weakenTrace (XS ty d22) k35) s13 (tshiftTm (weakenCutoffty C0 k35) s12)) =
        (tshiftTm (weakenCutoffty C0 k35) (substTm (weakenTrace d22 k35) s13 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
        (substIndex_tshiftTm0_comm_ind d22 s12 k35 x38))) (fun (T : Ty) (t : Tm) IHt69 (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d22) k35 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k35) d22 s12) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d22 k35 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 app (IHt69 k35 d22 s12) (IHt70 k35 d22 s12))) (fun (t : Tm) IHt69 (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d22) k35 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k35) d22 s12) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d22 k35 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k35 : Hvl) (d22 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tapp (IHt69 k35 d22 s12) eq_refl))).
    Definition tsubst_shift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) ,
        ((tsubstTm (weakenTrace d22 k35) S18 (shiftTm (weakenCutofftm C0 k35) s12)) =
        (shiftTm (weakenCutofftm C0 k35) (tsubstTm (weakenTrace d22 k35) S18 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt69 (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d22 k35 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k35) d22 S18) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d22 k35 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal2 app (IHt69 k35 d22 S18) (IHt70 k35 d22 S18))) (fun (t : Tm) IHt69 (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d22 k35 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k35) d22 S18) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d22 k35 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal2 tapp (IHt69 k35 d22 S18) eq_refl))).
    Definition tsubst_tshift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) ,
        ((tsubstTm (weakenTrace (XS ty d22) k35) S18 (tshiftTm (weakenCutoffty C0 k35) s12)) =
        (tshiftTm (weakenCutoffty C0 k35) (tsubstTm (weakenTrace d22 k35) S18 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt69 (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal2 abs (let IHT0 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT0 k35 d22 S18)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d22) k35 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k35) d22 S18) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d22 k35 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal2 app (IHt69 k35 d22 S18) (IHt70 k35 d22 S18))) (fun (t : Tm) IHt69 (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d22) k35 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k35) d22 S18) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d22 k35 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k35 : Hvl) (d22 : (Trace ty)) (S18 : Ty) =>
      (f_equal2 tapp (IHt69 k35 d22 S18) (let IHT0 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT0 k35 d22 S18))))).
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S27 : Ty) : (forall (d30 : (Trace ty)) (S26 : Ty) ,
      ((tsubstTy (XS ty d30) S26 (tshiftTy C0 S27)) =
      (tshiftTy C0 (tsubstTy d30 S26 S27)))) := (tsubst_tshift0_Ty_comm_ind S27 H0).
    Definition substTm_shiftTm0_comm (s13 : Tm) : (forall (d30 : (Trace tm)) (s12 : Tm) ,
      ((substTm (XS tm d30) s12 (shiftTm C0 s13)) =
      (shiftTm C0 (substTm d30 s12 s13)))) := (subst_shift0_Tm_comm_ind s13 H0).
    Definition substTm_tshiftTm0_comm (s13 : Tm) : (forall (d30 : (Trace tm)) (s12 : Tm) ,
      ((substTm (XS ty d30) s12 (tshiftTm C0 s13)) =
      (tshiftTm C0 (substTm d30 s12 s13)))) := (subst_tshift0_Tm_comm_ind s13 H0).
    Definition tsubstTm_shiftTm0_comm (s12 : Tm) : (forall (d30 : (Trace ty)) (S26 : Ty) ,
      ((tsubstTm d30 S26 (shiftTm C0 s12)) =
      (shiftTm C0 (tsubstTm d30 S26 s12)))) := (tsubst_shift0_Tm_comm_ind s12 H0).
    Definition tsubstTm_tshiftTm0_comm (s12 : Tm) : (forall (d30 : (Trace ty)) (S26 : Ty) ,
      ((tsubstTm (XS ty d30) S26 (tshiftTm C0 s12)) =
      (tshiftTm C0 (tsubstTm d30 S26 s12)))) := (tsubst_tshift0_Tm_comm_ind s12 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Definition tsubst_tm_Ty_ind := (ind_Ty (fun (S26 : Ty) =>
      (forall (k43 : Hvl) (d30 : (Trace ty)) (S27 : Ty) ,
        ((tsubstTy (weakenTrace (XS tm d30) k43) S27 S26) =
        (tsubstTy (weakenTrace d30 k43) S27 S26)))) (fun (X32 : (Index ty)) =>
      (fun (k43 : Hvl) (d30 : (Trace ty)) (S26 : Ty) =>
        (tsubstIndex_shiftTy0_comm_ind d30 S26 k43 X32))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k43 : Hvl) (d30 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 tarr (IHT0 k43 d30 S26) (IHT3 k43 d30 S26))) (fun (T : Ty) IHT0 (k43 : Hvl) (d30 : (Trace ty)) (S26 : Ty) =>
      (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d30) k43 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT0 (HS ty k43) d30 S26) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d30 k43 (HS ty H0))) eq_refl eq_refl)))))).
    Definition tsubst_tm_Tm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k43 : Hvl) (d30 : (Trace ty)) (S26 : Ty) ,
        ((tsubstTm (weakenTrace (XS tm d30) k43) S26 s12) =
        (tsubstTm (weakenTrace d30 k43) S26 s12)))) (fun (x41 : (Index tm)) =>
      (fun (k43 : Hvl) (d30 : (Trace ty)) (S26 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt74 (k43 : Hvl) (d30 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 abs (let IHT0 := (tsubst_tm_Ty_ind T) in
      (IHT0 k43 d30 S26)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d30) k43 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt74 (HS tm k43) d30 S26) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d30 k43 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt74 (t2 : Tm) IHt75 (k43 : Hvl) (d30 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 app (IHt74 k43 d30 S26) (IHt75 k43 d30 S26))) (fun (t : Tm) IHt74 (k43 : Hvl) (d30 : (Trace ty)) (S26 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d30) k43 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt74 (HS ty k43) d30 S26) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d30 k43 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt74 (T : Ty) (k43 : Hvl) (d30 : (Trace ty)) (S26 : Ty) =>
      (f_equal2 tapp (IHt74 k43 d30 S26) (let IHT0 := (tsubst_tm_Ty_ind T) in
      (IHT0 k43 d30 S26))))).
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S27 : Ty) : (forall (d30 : (Trace ty)) (S26 : Ty) ,
      ((tsubstTy (XS tm d30) S26 S27) =
      (tsubstTy d30 S26 S27))) := (tsubst_tm_Ty_ind S27 H0).
    Definition tsubstTm_tm (s12 : Tm) : (forall (d30 : (Trace ty)) (S26 : Ty) ,
      ((tsubstTm (XS tm d30) S26 s12) =
      (tsubstTm d30 S26 s12))) := (tsubst_tm_Tm_ind s12 H0).
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
    Lemma substTm_substIndex0_commright_ind (d30 : (Trace tm)) (s12 : Tm) (s13 : Tm) :
      (forall (k43 : Hvl) (x41 : (Index tm)) ,
        ((substTm (weakenTrace d30 k43) s12 (substIndex (weakenTrace X0 k43) s13 x41)) =
        (substTm (weakenTrace X0 k43) (substTm d30 s12 s13) (substIndex (weakenTrace (XS tm d30) k43) s12 x41)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d30 : (Trace ty)) (S26 : Ty) (s12 : Tm) :
      (forall (k43 : Hvl) (x41 : (Index tm)) ,
        ((tsubstTm (weakenTrace d30 k43) S26 (substIndex (weakenTrace X0 k43) s12 x41)) =
        (substIndex (weakenTrace X0 k43) (tsubstTm d30 S26 s12) x41))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d30 : (Trace ty)) (S26 : Ty) (S27 : Ty) :
      (forall (k43 : Hvl) (X32 : (Index ty)) ,
        ((tsubstTy (weakenTrace d30 k43) S26 (tsubstIndex (weakenTrace X0 k43) S27 X32)) =
        (tsubstTy (weakenTrace X0 k43) (tsubstTy d30 S26 S27) (tsubstIndex (weakenTrace (XS ty d30) k43) S26 X32)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d30 : (Trace tm)) (s12 : Tm) (S26 : Ty) :
      (forall (k43 : Hvl) (x41 : (Index tm)) ,
        ((substIndex (weakenTrace d30 k43) s12 x41) =
        (tsubstTm (weakenTrace X0 k43) S26 (substIndex (weakenTrace (XS ty d30) k43) s12 x41)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition tsubst_tsubst0_Ty_comm_ind := (ind_Ty (fun (S30 : Ty) =>
      (forall (k46 : Hvl) (d33 : (Trace ty)) (S31 : Ty) (S32 : Ty) ,
        ((tsubstTy (weakenTrace d33 k46) S31 (tsubstTy (weakenTrace X0 k46) S32 S30)) =
        (tsubstTy (weakenTrace X0 k46) (tsubstTy d33 S31 S32) (tsubstTy (weakenTrace (XS ty d33) k46) S31 S30))))) (fun (X37 : (Index ty)) =>
      (fun (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) =>
        (tsubstTy_tsubstIndex0_commright_ind d33 S30 S31 k46 X37))) (fun (T1 : Ty) IHT0 (T2 : Ty) IHT3 (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) =>
      (f_equal2 tarr (IHT0 k46 d33 S30 S31) (IHT3 k46 d33 S30 S31))) (fun (T : Ty) IHT0 (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) =>
      (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d33 k46 (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k46 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT0 (HS ty k46) d33 S30 S31) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k46 (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d33) k46 (HS ty H0))) eq_refl eq_refl))))))).
    Definition subst_subst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k46 : Hvl) (d33 : (Trace tm)) (s15 : Tm) (s16 : Tm) ,
        ((substTm (weakenTrace d33 k46) s15 (substTm (weakenTrace X0 k46) s16 s14)) =
        (substTm (weakenTrace X0 k46) (substTm d33 s15 s16) (substTm (weakenTrace (XS tm d33) k46) s15 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
        (substTm_substIndex0_commright_ind d33 s14 s15 k46 x47))) (fun (T : Ty) (t : Tm) IHt84 (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d33 k46 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k46 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k46) d33 s14 s15) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k46 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d33) k46 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 app (IHt84 k46 d33 s14 s15) (IHt85 k46 d33 s14 s15))) (fun (t : Tm) IHt84 (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d33 k46 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k46 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k46) d33 s14 s15) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k46 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d33) k46 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 tapp (IHt84 k46 d33 s14 s15) eq_refl))).
    Definition subst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k46 : Hvl) (d33 : (Trace tm)) (s15 : Tm) (S30 : Ty) ,
        ((substTm (weakenTrace d33 k46) s15 (tsubstTm (weakenTrace X0 k46) S30 s14)) =
        (tsubstTm (weakenTrace X0 k46) S30 (substTm (weakenTrace (XS ty d33) k46) s15 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (S30 : Ty) =>
        (substTy_tsubstIndex0_commleft_ind d33 s14 S30 k46 x47))) (fun (T : Ty) (t : Tm) IHt84 (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (S30 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d33 k46 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k46 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k46) d33 s14 S30) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k46 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d33) k46 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (S30 : Ty) =>
      (f_equal2 app (IHt84 k46 d33 s14 S30) (IHt85 k46 d33 s14 S30))) (fun (t : Tm) IHt84 (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (S30 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d33 k46 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k46 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k46) d33 s14 S30) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k46 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d33) k46 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (S30 : Ty) =>
      (f_equal2 tapp (IHt84 k46 d33 s14 S30) eq_refl))).
    Definition tsubst_subst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (s15 : Tm) ,
        ((tsubstTm (weakenTrace d33 k46) S30 (substTm (weakenTrace X0 k46) s15 s14)) =
        (substTm (weakenTrace X0 k46) (tsubstTm d33 S30 s15) (tsubstTm (weakenTrace d33 k46) S30 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (s14 : Tm) =>
        (tsubstTm_substIndex0_commright_ind d33 S30 s14 k46 x47))) (fun (T : Ty) (t : Tm) IHt84 (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (s14 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d33 k46 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k46 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k46) d33 S30 s14) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k46 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d33 k46 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (s14 : Tm) =>
      (f_equal2 app (IHt84 k46 d33 S30 s14) (IHt85 k46 d33 S30 s14))) (fun (t : Tm) IHt84 (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (s14 : Tm) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d33 k46 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k46 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k46) d33 S30 s14) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k46 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d33 k46 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (s14 : Tm) =>
      (f_equal2 tapp (IHt84 k46 d33 S30 s14) eq_refl))).
    Definition tsubst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) ,
        ((tsubstTm (weakenTrace d33 k46) S30 (tsubstTm (weakenTrace X0 k46) S31 s14)) =
        (tsubstTm (weakenTrace X0 k46) (tsubstTy d33 S30 S31) (tsubstTm (weakenTrace (XS ty d33) k46) S30 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt84 (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) =>
      (f_equal2 abs (let IHT0 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT0 k46 d33 S30 S31)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d33 k46 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k46 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k46) d33 S30 S31) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k46 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d33) k46 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) =>
      (f_equal2 app (IHt84 k46 d33 S30 S31) (IHt85 k46 d33 S30 S31))) (fun (t : Tm) IHt84 (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) =>
      (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d33 k46 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k46 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k46) d33 S30 S31) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k46 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d33) k46 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) =>
      (f_equal2 tapp (IHt84 k46 d33 S30 S31) (let IHT0 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT0 k46 d33 S30 S31))))).
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S32 : Ty) : (forall (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) ,
      ((tsubstTy d33 S30 (tsubstTy X0 S31 S32)) =
      (tsubstTy X0 (tsubstTy d33 S30 S31) (tsubstTy (XS ty d33) S30 S32)))) := (tsubst_tsubst0_Ty_comm_ind S32 H0).
    Definition substTm_substTm0_comm (s16 : Tm) : (forall (d33 : (Trace tm)) (s14 : Tm) (s15 : Tm) ,
      ((substTm d33 s14 (substTm X0 s15 s16)) =
      (substTm X0 (substTm d33 s14 s15) (substTm (XS tm d33) s14 s16)))) := (subst_subst0_Tm_comm_ind s16 H0).
    Definition substTm_tsubstTm0_comm (s15 : Tm) : (forall (d33 : (Trace tm)) (s14 : Tm) (S30 : Ty) ,
      ((substTm d33 s14 (tsubstTm X0 S30 s15)) =
      (tsubstTm X0 S30 (substTm (XS ty d33) s14 s15)))) := (subst_tsubst0_Tm_comm_ind s15 H0).
    Definition tsubstTm_substTm0_comm (s15 : Tm) : (forall (d33 : (Trace ty)) (S30 : Ty) (s14 : Tm) ,
      ((tsubstTm d33 S30 (substTm X0 s14 s15)) =
      (substTm X0 (tsubstTm d33 S30 s14) (tsubstTm d33 S30 s15)))) := (tsubst_subst0_Tm_comm_ind s15 H0).
    Definition tsubstTm_tsubstTm0_comm (s14 : Tm) : (forall (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) ,
      ((tsubstTm d33 S30 (tsubstTm X0 S31 s14)) =
      (tsubstTm X0 (tsubstTy d33 S30 S31) (tsubstTm (XS ty d33) S30 s14)))) := (tsubst_tsubst0_Tm_comm_ind s14 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (S31 : Ty) ,
        ((weakenTy (tsubstTy d33 S30 S31) k46) =
        (tsubstTy (weakenTrace d33 k46) S30 (weakenTy S31 k46)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k46 : Hvl) (d33 : (Trace tm)) (s14 : Tm) (s15 : Tm) ,
        ((weakenTm (substTm d33 s14 s15) k46) =
        (substTm (weakenTrace d33 k46) s14 (weakenTm s15 k46)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k46 : Hvl) (d33 : (Trace ty)) (S30 : Ty) (s14 : Tm) ,
        ((weakenTm (tsubstTm d33 S30 s14) k46) =
        (tsubstTm (weakenTrace d33 k46) S30 (weakenTm s14 k46)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenTy_append  :
      (forall (S30 : Ty) (k46 : Hvl) (k47 : Hvl) ,
        ((weakenTy (weakenTy S30 k46) k47) =
        (weakenTy S30 (appendHvl k46 k47)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s14 : Tm) (k46 : Hvl) (k47 : Hvl) ,
        ((weakenTm (weakenTm s14 k46) k47) =
        (weakenTm s14 (appendHvl k46 k47)))).
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
  Fixpoint wfindex {a : Namespace} (k46 : Hvl) (i : (Index a)) {struct k46} : Prop :=
    match k46 with
      | H0 => False
      | HS b k46 => match (eq_namespace_dec a b) with
        | left e => match i with
          | I0 => True
          | IS i => (wfindex k46 i)
        end
        | right n => (wfindex k46 i)
      end
    end.
  Inductive wfTy (k46 : Hvl) : Ty -> Prop :=
    | wfTy_tvar {X43 : (Index ty)}
        (wfi : (wfindex k46 X43)) :
        (wfTy k46 (tvar X43))
    | wfTy_tarr {T58 : Ty}
        (wf : (wfTy k46 T58)) {T59 : Ty}
        (wf0 : (wfTy k46 T59)) :
        (wfTy k46 (tarr T58 T59))
    | wfTy_tall {T60 : Ty}
        (wf : (wfTy (HS ty k46) T60)) :
        (wfTy k46 (tall T60)).
  Inductive wfTm (k46 : Hvl) : Tm -> Prop :=
    | wfTm_var {x52 : (Index tm)}
        (wfi : (wfindex k46 x52)) :
        (wfTm k46 (var x52))
    | wfTm_abs {T58 : Ty}
        (wf : (wfTy k46 T58)) {t94 : Tm}
        (wf0 : (wfTm (HS tm k46) t94)) :
        (wfTm k46 (abs T58 t94))
    | wfTm_app {t95 : Tm}
        (wf : (wfTm k46 t95)) {t96 : Tm}
        (wf0 : (wfTm k46 t96)) :
        (wfTm k46 (app t95 t96))
    | wfTm_tabs {t97 : Tm}
        (wf : (wfTm (HS ty k46) t97)) :
        (wfTm k46 (tabs t97))
    | wfTm_tapp {t98 : Tm}
        (wf : (wfTm k46 t98)) {T59 : Ty}
        (wf0 : (wfTy k46 T59)) :
        (wfTm k46 (tapp t98 T59)).
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c12 : (Cutoff tm)) (k46 : Hvl) (k47 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k46 : Hvl)
        :
        (shifthvl_tm C0 k46 (HS tm k46))
    | shifthvl_tm_there_tm
        (c12 : (Cutoff tm)) (k46 : Hvl)
        (k47 : Hvl) :
        (shifthvl_tm c12 k46 k47) -> (shifthvl_tm (CS c12) (HS tm k46) (HS tm k47))
    | shifthvl_tm_there_ty
        (c12 : (Cutoff tm)) (k46 : Hvl)
        (k47 : Hvl) :
        (shifthvl_tm c12 k46 k47) -> (shifthvl_tm c12 (HS ty k46) (HS ty k47)).
  Inductive shifthvl_ty : (forall (c12 : (Cutoff ty)) (k46 : Hvl) (k47 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k46 : Hvl)
        :
        (shifthvl_ty C0 k46 (HS ty k46))
    | shifthvl_ty_there_tm
        (c12 : (Cutoff ty)) (k46 : Hvl)
        (k47 : Hvl) :
        (shifthvl_ty c12 k46 k47) -> (shifthvl_ty c12 (HS tm k46) (HS tm k47))
    | shifthvl_ty_there_ty
        (c12 : (Cutoff ty)) (k46 : Hvl)
        (k47 : Hvl) :
        (shifthvl_ty c12 k46 k47) -> (shifthvl_ty (CS c12) (HS ty k46) (HS ty k47)).
  Lemma weaken_shifthvl_tm  :
    (forall (k46 : Hvl) {c12 : (Cutoff tm)} {k47 : Hvl} {k48 : Hvl} ,
      (shifthvl_tm c12 k47 k48) -> (shifthvl_tm (weakenCutofftm c12 k46) (appendHvl k47 k46) (appendHvl k48 k46))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k46 : Hvl) {c12 : (Cutoff ty)} {k47 : Hvl} {k48 : Hvl} ,
      (shifthvl_ty c12 k47 k48) -> (shifthvl_ty (weakenCutoffty c12 k46) (appendHvl k47 k46) (appendHvl k48 k46))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c12 : (Cutoff tm)) (k46 : Hvl) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) (x52 : (Index tm)) ,
      (wfindex k46 x52) -> (wfindex k47 (shiftIndex c12 x52))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c12 : (Cutoff tm)) (k46 : Hvl) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) (X43 : (Index ty)) ,
      (wfindex k46 X43) -> (wfindex k47 X43)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c12 : (Cutoff ty)) (k46 : Hvl) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) (x52 : (Index tm)) ,
      (wfindex k46 x52) -> (wfindex k47 x52)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c12 : (Cutoff ty)) (k46 : Hvl) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) (X43 : (Index ty)) ,
      (wfindex k46 X43) -> (wfindex k47 (tshiftIndex c12 X43))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k46 : Hvl) ,
    (forall (S30 : Ty) (wf : (wfTy k46 S30)) ,
      (forall (c12 : (Cutoff tm)) (k47 : Hvl) ,
        (shifthvl_tm c12 k46 k47) -> (wfTy k47 S30)))) := (ind_wfTy (fun (k46 : Hvl) (S30 : Ty) (wf : (wfTy k46 S30)) =>
    (forall (c12 : (Cutoff tm)) (k47 : Hvl) ,
      (shifthvl_tm c12 k46 k47) -> (wfTy k47 S30))) (fun (k46 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k46 X43)) (c12 : (Cutoff tm)) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) =>
    (wfTy_tvar k47 (shift_wfindex_ty c12 k46 k47 ins X43 wfi))) (fun (k46 : Hvl) (T1 : Ty) (wf : (wfTy k46 T1)) IHT0 (T2 : Ty) (wf0 : (wfTy k46 T2)) IHT3 (c12 : (Cutoff tm)) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) =>
    (wfTy_tarr k47 (IHT0 c12 k47 (weaken_shifthvl_tm H0 ins)) (IHT3 c12 k47 (weaken_shifthvl_tm H0 ins)))) (fun (k46 : Hvl) (T : Ty) (wf : (wfTy (HS ty k46) T)) IHT0 (c12 : (Cutoff tm)) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) =>
    (wfTy_tall k47 (IHT0 c12 (HS ty k47) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k46 : Hvl) ,
    (forall (S30 : Ty) (wf : (wfTy k46 S30)) ,
      (forall (c12 : (Cutoff ty)) (k47 : Hvl) ,
        (shifthvl_ty c12 k46 k47) -> (wfTy k47 (tshiftTy c12 S30))))) := (ind_wfTy (fun (k46 : Hvl) (S30 : Ty) (wf : (wfTy k46 S30)) =>
    (forall (c12 : (Cutoff ty)) (k47 : Hvl) ,
      (shifthvl_ty c12 k46 k47) -> (wfTy k47 (tshiftTy c12 S30)))) (fun (k46 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k46 X43)) (c12 : (Cutoff ty)) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) =>
    (wfTy_tvar k47 (tshift_wfindex_ty c12 k46 k47 ins X43 wfi))) (fun (k46 : Hvl) (T1 : Ty) (wf : (wfTy k46 T1)) IHT0 (T2 : Ty) (wf0 : (wfTy k46 T2)) IHT3 (c12 : (Cutoff ty)) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) =>
    (wfTy_tarr k47 (IHT0 c12 k47 (weaken_shifthvl_ty H0 ins)) (IHT3 c12 k47 (weaken_shifthvl_ty H0 ins)))) (fun (k46 : Hvl) (T : Ty) (wf : (wfTy (HS ty k46) T)) IHT0 (c12 : (Cutoff ty)) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) =>
    (wfTy_tall k47 (IHT0 (CS c12) (HS ty k47) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfTm : (forall (k46 : Hvl) ,
    (forall (s14 : Tm) (wf : (wfTm k46 s14)) ,
      (forall (c12 : (Cutoff tm)) (k47 : Hvl) ,
        (shifthvl_tm c12 k46 k47) -> (wfTm k47 (shiftTm c12 s14))))) := (ind_wfTm (fun (k46 : Hvl) (s14 : Tm) (wf : (wfTm k46 s14)) =>
    (forall (c12 : (Cutoff tm)) (k47 : Hvl) ,
      (shifthvl_tm c12 k46 k47) -> (wfTm k47 (shiftTm c12 s14)))) (fun (k46 : Hvl) (x52 : (Index tm)) (wfi : (wfindex k46 x52)) (c12 : (Cutoff tm)) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) =>
    (wfTm_var k47 (shift_wfindex_tm c12 k46 k47 ins x52 wfi))) (fun (k46 : Hvl) (T : Ty) (wf : (wfTy k46 T)) (t : Tm) (wf0 : (wfTm (HS tm k46) t)) IHt94 (c12 : (Cutoff tm)) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) =>
    (wfTm_abs k47 (shift_wfTy k46 T wf c12 k47 (weaken_shifthvl_tm H0 ins)) (IHt94 (CS c12) (HS tm k47) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k46 : Hvl) (t1 : Tm) (wf : (wfTm k46 t1)) IHt94 (t2 : Tm) (wf0 : (wfTm k46 t2)) IHt95 (c12 : (Cutoff tm)) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) =>
    (wfTm_app k47 (IHt94 c12 k47 (weaken_shifthvl_tm H0 ins)) (IHt95 c12 k47 (weaken_shifthvl_tm H0 ins)))) (fun (k46 : Hvl) (t : Tm) (wf : (wfTm (HS ty k46) t)) IHt94 (c12 : (Cutoff tm)) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) =>
    (wfTm_tabs k47 (IHt94 c12 (HS ty k47) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k46 : Hvl) (t : Tm) (wf : (wfTm k46 t)) IHt94 (T : Ty) (wf0 : (wfTy k46 T)) (c12 : (Cutoff tm)) (k47 : Hvl) (ins : (shifthvl_tm c12 k46 k47)) =>
    (wfTm_tapp k47 (IHt94 c12 k47 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k46 T wf0 c12 k47 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTm : (forall (k46 : Hvl) ,
    (forall (s14 : Tm) (wf : (wfTm k46 s14)) ,
      (forall (c12 : (Cutoff ty)) (k47 : Hvl) ,
        (shifthvl_ty c12 k46 k47) -> (wfTm k47 (tshiftTm c12 s14))))) := (ind_wfTm (fun (k46 : Hvl) (s14 : Tm) (wf : (wfTm k46 s14)) =>
    (forall (c12 : (Cutoff ty)) (k47 : Hvl) ,
      (shifthvl_ty c12 k46 k47) -> (wfTm k47 (tshiftTm c12 s14)))) (fun (k46 : Hvl) (x52 : (Index tm)) (wfi : (wfindex k46 x52)) (c12 : (Cutoff ty)) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) =>
    (wfTm_var k47 (tshift_wfindex_tm c12 k46 k47 ins x52 wfi))) (fun (k46 : Hvl) (T : Ty) (wf : (wfTy k46 T)) (t : Tm) (wf0 : (wfTm (HS tm k46) t)) IHt94 (c12 : (Cutoff ty)) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) =>
    (wfTm_abs k47 (tshift_wfTy k46 T wf c12 k47 (weaken_shifthvl_ty H0 ins)) (IHt94 c12 (HS tm k47) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k46 : Hvl) (t1 : Tm) (wf : (wfTm k46 t1)) IHt94 (t2 : Tm) (wf0 : (wfTm k46 t2)) IHt95 (c12 : (Cutoff ty)) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) =>
    (wfTm_app k47 (IHt94 c12 k47 (weaken_shifthvl_ty H0 ins)) (IHt95 c12 k47 (weaken_shifthvl_ty H0 ins)))) (fun (k46 : Hvl) (t : Tm) (wf : (wfTm (HS ty k46) t)) IHt94 (c12 : (Cutoff ty)) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) =>
    (wfTm_tabs k47 (IHt94 (CS c12) (HS ty k47) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k46 : Hvl) (t : Tm) (wf : (wfTm k46 t)) IHt94 (T : Ty) (wf0 : (wfTy k46 T)) (c12 : (Cutoff ty)) (k47 : Hvl) (ins : (shifthvl_ty c12 k46 k47)) =>
    (wfTm_tapp k47 (IHt94 c12 k47 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k46 T wf0 c12 k47 (weaken_shifthvl_ty H0 ins))))).
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
  Inductive substhvl_tm (k46 : Hvl) : (forall (d33 : (Trace tm)) (k47 : Hvl) (k48 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k46 X0 (HS tm k46) k46)
    | substhvl_tm_there_tm
        {d33 : (Trace tm)} {k47 : Hvl}
        {k48 : Hvl} :
        (substhvl_tm k46 d33 k47 k48) -> (substhvl_tm k46 (XS tm d33) (HS tm k47) (HS tm k48))
    | substhvl_tm_there_ty
        {d33 : (Trace tm)} {k47 : Hvl}
        {k48 : Hvl} :
        (substhvl_tm k46 d33 k47 k48) -> (substhvl_tm k46 (XS ty d33) (HS ty k47) (HS ty k48)).
  Inductive substhvl_ty (k46 : Hvl) : (forall (d33 : (Trace ty)) (k47 : Hvl) (k48 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k46 X0 (HS ty k46) k46)
    | substhvl_ty_there_tm
        {d33 : (Trace ty)} {k47 : Hvl}
        {k48 : Hvl} :
        (substhvl_ty k46 d33 k47 k48) -> (substhvl_ty k46 (XS tm d33) (HS tm k47) (HS tm k48))
    | substhvl_ty_there_ty
        {d33 : (Trace ty)} {k47 : Hvl}
        {k48 : Hvl} :
        (substhvl_ty k46 d33 k47 k48) -> (substhvl_ty k46 (XS ty d33) (HS ty k47) (HS ty k48)).
  Lemma weaken_substhvl_tm  :
    (forall {k47 : Hvl} (k46 : Hvl) {d33 : (Trace tm)} {k48 : Hvl} {k49 : Hvl} ,
      (substhvl_tm k47 d33 k48 k49) -> (substhvl_tm k47 (weakenTrace d33 k46) (appendHvl k48 k46) (appendHvl k49 k46))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k47 : Hvl} (k46 : Hvl) {d33 : (Trace ty)} {k48 : Hvl} {k49 : Hvl} ,
      (substhvl_ty k47 d33 k48 k49) -> (substhvl_ty k47 (weakenTrace d33 k46) (appendHvl k48 k46) (appendHvl k49 k46))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k46 : Hvl} {s14 : Tm} (wft : (wfTm k46 s14)) :
    (forall {d33 : (Trace tm)} {k47 : Hvl} {k48 : Hvl} ,
      (substhvl_tm k46 d33 k47 k48) -> (forall {x52 : (Index tm)} ,
        (wfindex k47 x52) -> (wfTm k48 (substIndex d33 s14 x52)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k46 : Hvl} {S30 : Ty} (wft : (wfTy k46 S30)) :
    (forall {d33 : (Trace ty)} {k47 : Hvl} {k48 : Hvl} ,
      (substhvl_ty k46 d33 k47 k48) -> (forall {X43 : (Index ty)} ,
        (wfindex k47 X43) -> (wfTy k48 (tsubstIndex d33 S30 X43)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k46 : Hvl} :
    (forall {d33 : (Trace tm)} {k47 : Hvl} {k48 : Hvl} ,
      (substhvl_tm k46 d33 k47 k48) -> (forall {X43 : (Index ty)} ,
        (wfindex k47 X43) -> (wfindex k48 X43))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k46 : Hvl} :
    (forall {d33 : (Trace ty)} {k47 : Hvl} {k48 : Hvl} ,
      (substhvl_ty k46 d33 k47 k48) -> (forall {x52 : (Index tm)} ,
        (wfindex k47 x52) -> (wfindex k48 x52))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k46 : Hvl} : (forall (k47 : Hvl) ,
    (forall (S30 : Ty) (wf0 : (wfTy k47 S30)) ,
      (forall {d33 : (Trace tm)} {k48 : Hvl} ,
        (substhvl_tm k46 d33 k47 k48) -> (wfTy k48 S30)))) := (ind_wfTy (fun (k47 : Hvl) (S30 : Ty) (wf0 : (wfTy k47 S30)) =>
    (forall {d33 : (Trace tm)} {k48 : Hvl} ,
      (substhvl_tm k46 d33 k47 k48) -> (wfTy k48 S30))) (fun (k47 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k47 X43)) {d33 : (Trace tm)} {k48 : Hvl} (del : (substhvl_tm k46 d33 k47 k48)) =>
    (wfTy_tvar k48 (substhvl_tm_wfindex_ty del wfi))) (fun (k47 : Hvl) (T1 : Ty) (wf0 : (wfTy k47 T1)) IHT0 (T2 : Ty) (wf1 : (wfTy k47 T2)) IHT3 {d33 : (Trace tm)} {k48 : Hvl} (del : (substhvl_tm k46 d33 k47 k48)) =>
    (wfTy_tarr k48 (IHT0 (weakenTrace d33 H0) k48 (weaken_substhvl_tm H0 del)) (IHT3 (weakenTrace d33 H0) k48 (weaken_substhvl_tm H0 del)))) (fun (k47 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k47) T)) IHT0 {d33 : (Trace tm)} {k48 : Hvl} (del : (substhvl_tm k46 d33 k47 k48)) =>
    (wfTy_tall k48 (IHT0 (weakenTrace d33 (HS ty H0)) (HS ty k48) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k46 : Hvl} {S30 : Ty} (wf : (wfTy k46 S30)) : (forall (k47 : Hvl) ,
    (forall (S31 : Ty) (wf0 : (wfTy k47 S31)) ,
      (forall {d33 : (Trace ty)} {k48 : Hvl} ,
        (substhvl_ty k46 d33 k47 k48) -> (wfTy k48 (tsubstTy d33 S30 S31))))) := (ind_wfTy (fun (k47 : Hvl) (S31 : Ty) (wf0 : (wfTy k47 S31)) =>
    (forall {d33 : (Trace ty)} {k48 : Hvl} ,
      (substhvl_ty k46 d33 k47 k48) -> (wfTy k48 (tsubstTy d33 S30 S31)))) (fun (k47 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k47 X43)) {d33 : (Trace ty)} {k48 : Hvl} (del : (substhvl_ty k46 d33 k47 k48)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k47 : Hvl) (T1 : Ty) (wf0 : (wfTy k47 T1)) IHT0 (T2 : Ty) (wf1 : (wfTy k47 T2)) IHT3 {d33 : (Trace ty)} {k48 : Hvl} (del : (substhvl_ty k46 d33 k47 k48)) =>
    (wfTy_tarr k48 (IHT0 (weakenTrace d33 H0) k48 (weaken_substhvl_ty H0 del)) (IHT3 (weakenTrace d33 H0) k48 (weaken_substhvl_ty H0 del)))) (fun (k47 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k47) T)) IHT0 {d33 : (Trace ty)} {k48 : Hvl} (del : (substhvl_ty k46 d33 k47 k48)) =>
    (wfTy_tall k48 (IHT0 (weakenTrace d33 (HS ty H0)) (HS ty k48) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfTm {k46 : Hvl} {s14 : Tm} (wf : (wfTm k46 s14)) : (forall (k47 : Hvl) ,
    (forall (s15 : Tm) (wf0 : (wfTm k47 s15)) ,
      (forall {d33 : (Trace tm)} {k48 : Hvl} ,
        (substhvl_tm k46 d33 k47 k48) -> (wfTm k48 (substTm d33 s14 s15))))) := (ind_wfTm (fun (k47 : Hvl) (s15 : Tm) (wf0 : (wfTm k47 s15)) =>
    (forall {d33 : (Trace tm)} {k48 : Hvl} ,
      (substhvl_tm k46 d33 k47 k48) -> (wfTm k48 (substTm d33 s14 s15)))) (fun (k47 : Hvl) {x52 : (Index tm)} (wfi : (wfindex k47 x52)) {d33 : (Trace tm)} {k48 : Hvl} (del : (substhvl_tm k46 d33 k47 k48)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k47 : Hvl) (T : Ty) (wf0 : (wfTy k47 T)) (t : Tm) (wf1 : (wfTm (HS tm k47) t)) IHt94 {d33 : (Trace tm)} {k48 : Hvl} (del : (substhvl_tm k46 d33 k47 k48)) =>
    (wfTm_abs k48 (substhvl_tm_wfTy k47 T wf0 (weaken_substhvl_tm H0 del)) (IHt94 (weakenTrace d33 (HS tm H0)) (HS tm k48) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k47 : Hvl) (t1 : Tm) (wf0 : (wfTm k47 t1)) IHt94 (t2 : Tm) (wf1 : (wfTm k47 t2)) IHt95 {d33 : (Trace tm)} {k48 : Hvl} (del : (substhvl_tm k46 d33 k47 k48)) =>
    (wfTm_app k48 (IHt94 (weakenTrace d33 H0) k48 (weaken_substhvl_tm H0 del)) (IHt95 (weakenTrace d33 H0) k48 (weaken_substhvl_tm H0 del)))) (fun (k47 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k47) t)) IHt94 {d33 : (Trace tm)} {k48 : Hvl} (del : (substhvl_tm k46 d33 k47 k48)) =>
    (wfTm_tabs k48 (IHt94 (weakenTrace d33 (HS ty H0)) (HS ty k48) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k47 : Hvl) (t : Tm) (wf0 : (wfTm k47 t)) IHt94 (T : Ty) (wf1 : (wfTy k47 T)) {d33 : (Trace tm)} {k48 : Hvl} (del : (substhvl_tm k46 d33 k47 k48)) =>
    (wfTm_tapp k48 (IHt94 (weakenTrace d33 H0) k48 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k47 T wf1 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTm {k46 : Hvl} {S30 : Ty} (wf : (wfTy k46 S30)) : (forall (k47 : Hvl) ,
    (forall (s14 : Tm) (wf0 : (wfTm k47 s14)) ,
      (forall {d33 : (Trace ty)} {k48 : Hvl} ,
        (substhvl_ty k46 d33 k47 k48) -> (wfTm k48 (tsubstTm d33 S30 s14))))) := (ind_wfTm (fun (k47 : Hvl) (s14 : Tm) (wf0 : (wfTm k47 s14)) =>
    (forall {d33 : (Trace ty)} {k48 : Hvl} ,
      (substhvl_ty k46 d33 k47 k48) -> (wfTm k48 (tsubstTm d33 S30 s14)))) (fun (k47 : Hvl) {x52 : (Index tm)} (wfi : (wfindex k47 x52)) {d33 : (Trace ty)} {k48 : Hvl} (del : (substhvl_ty k46 d33 k47 k48)) =>
    (wfTm_var k48 (substhvl_ty_wfindex_tm del wfi))) (fun (k47 : Hvl) (T : Ty) (wf0 : (wfTy k47 T)) (t : Tm) (wf1 : (wfTm (HS tm k47) t)) IHt94 {d33 : (Trace ty)} {k48 : Hvl} (del : (substhvl_ty k46 d33 k47 k48)) =>
    (wfTm_abs k48 (substhvl_ty_wfTy wf k47 T wf0 (weaken_substhvl_ty H0 del)) (IHt94 (weakenTrace d33 (HS tm H0)) (HS tm k48) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k47 : Hvl) (t1 : Tm) (wf0 : (wfTm k47 t1)) IHt94 (t2 : Tm) (wf1 : (wfTm k47 t2)) IHt95 {d33 : (Trace ty)} {k48 : Hvl} (del : (substhvl_ty k46 d33 k47 k48)) =>
    (wfTm_app k48 (IHt94 (weakenTrace d33 H0) k48 (weaken_substhvl_ty H0 del)) (IHt95 (weakenTrace d33 H0) k48 (weaken_substhvl_ty H0 del)))) (fun (k47 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k47) t)) IHt94 {d33 : (Trace ty)} {k48 : Hvl} (del : (substhvl_ty k46 d33 k47 k48)) =>
    (wfTm_tabs k48 (IHt94 (weakenTrace d33 (HS ty H0)) (HS ty k48) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k47 : Hvl) (t : Tm) (wf0 : (wfTm k47 t)) IHt94 (T : Ty) (wf1 : (wfTy k47 T)) {d33 : (Trace ty)} {k48 : Hvl} (del : (substhvl_ty k46 d33 k47 k48)) =>
    (wfTm_tapp k48 (IHt94 (weakenTrace d33 H0) k48 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k47 T wf1 (weaken_substhvl_ty H0 del))))).
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
    | etvar (G : Env).
  Fixpoint appendEnv (G : Env) (G0 : Env) : Env :=
    match G0 with
      | empty => G
      | evar G1 T => (evar (appendEnv G G1) T)
      | etvar G1 => (etvar (appendEnv G G1))
    end.
  Fixpoint domainEnv (G : Env) : Hvl :=
    match G with
      | empty => H0
      | evar G0 T => (HS tm (domainEnv G0))
      | etvar G0 => (HS ty (domainEnv G0))
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
      | empty => empty
      | evar G0 T => (evar (shiftEnv c12 G0) T)
      | etvar G0 => (etvar (shiftEnv c12 G0))
    end.
  Fixpoint tshiftEnv (c12 : (Cutoff ty)) (G : Env) : Env :=
    match G with
      | empty => empty
      | evar G0 T => (evar (tshiftEnv c12 G0) (tshiftTy (weakenCutoffty c12 (domainEnv G0)) T))
      | etvar G0 => (etvar (tshiftEnv c12 G0))
    end.
  Fixpoint substEnv (d33 : (Trace tm)) (s14 : Tm) (G : Env) : Env :=
    match G with
      | empty => empty
      | evar G0 T => (evar (substEnv d33 s14 G0) T)
      | etvar G0 => (etvar (substEnv d33 s14 G0))
    end.
  Fixpoint tsubstEnv (d33 : (Trace ty)) (S30 : Ty) (G : Env) : Env :=
    match G with
      | empty => empty
      | evar G0 T => (evar (tsubstEnv d33 S30 G0) (tsubstTy (weakenTrace d33 (domainEnv G0)) S30 T))
      | etvar G0 => (etvar (tsubstEnv d33 S30 G0))
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
    (forall (d33 : (Trace tm)) (s14 : Tm) (G : Env) ,
      ((domainEnv (substEnv d33 s14 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d33 : (Trace ty)) (S30 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d33 S30 G)) =
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
      (forall (d33 : (Trace tm)) (s14 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d33 s14 (appendEnv G G0)) =
        (appendEnv (substEnv d33 s14 G) (substEnv (weakenTrace d33 (domainEnv G)) s14 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d33 : (Trace ty)) (S30 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d33 S30 (appendEnv G G0)) =
        (appendEnv (tsubstEnv d33 S30 G) (tsubstEnv (weakenTrace d33 (domainEnv G)) S30 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          {T58 : Ty} :
          (wfTy (domainEnv G) T58) -> (lookup_evar (evar G T58) I0 T58)
      | lookup_evar_there_evar
          {G : Env} {x52 : (Index tm)}
          {T58 : Ty} {T59 : Ty} :
          (lookup_evar G x52 T58) -> (lookup_evar (evar G T59) (IS x52) T58)
      | lookup_evar_there_etvar
          {G : Env} {x52 : (Index tm)}
          {T58 : Ty} :
          (lookup_evar G x52 T58) -> (lookup_evar (etvar G) x52 (tshiftTy C0 T58)).
    Inductive lookup_etvar : Env -> (Index ty) -> Prop :=
      | lookup_etvar_here {G : Env}
          : (lookup_etvar (etvar G) I0)
      | lookup_etvar_there_evar
          {G : Env} {X43 : (Index ty)}
          {T58 : Ty} :
          (lookup_etvar G X43) -> (lookup_etvar (evar G T58) X43)
      | lookup_etvar_there_etvar
          {G : Env} {X43 : (Index ty)} :
          (lookup_etvar G X43) -> (lookup_etvar (etvar G) (IS X43)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (S30 : Ty) (S31 : Ty) ,
        (lookup_evar (evar G S30) I0 S31) -> (S30 =
        S31)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x52 : (Index tm)} ,
        (forall {S30 : Ty} ,
          (lookup_evar G x52 S30) -> (forall {S31 : Ty} ,
            (lookup_evar G x52 S31) -> (S30 =
            S31)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x52 : (Index tm)} {S30 : Ty} ,
        (lookup_evar G x52 S30) -> (wfTy (domainEnv G) S30)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x52 : (Index tm)} {T58 : Ty} ,
        (lookup_evar G x52 T58) -> (lookup_evar (appendEnv G G0) (weakenIndextm x52 (domainEnv G0)) (weakenTy T58 (domainEnv G0)))).
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
      (forall {G : Env} {x52 : (Index tm)} {S30 : Ty} ,
        (lookup_evar G x52 S30) -> (wfindex (domainEnv G) x52)).
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
        {T58 : Ty} :
        (shift_evar C0 G (evar G T58))
    | shiftevar_there_evar
        {c12 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c12 G G0) -> (shift_evar (CS c12) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c12 : (Cutoff tm)} {G : Env}
        {G0 : Env} :
        (shift_evar c12 G G0) -> (shift_evar c12 (etvar G) (etvar G0)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c12 : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c12 G0 G1) -> (shift_evar (weakenCutofftm c12 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env} :
        (shift_etvar C0 G (etvar G))
    | shiftetvar_there_evar
        {c12 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c12 G G0) -> (shift_etvar c12 (evar G T) (evar G0 (tshiftTy c12 T)))
    | shiftetvar_there_etvar
        {c12 : (Cutoff ty)} {G : Env}
        {G0 : Env} :
        (shift_etvar c12 G G0) -> (shift_etvar (CS c12) (etvar G) (etvar G0)).
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
  Inductive subst_evar (G : Env) (T58 : Ty) (s14 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T58 s14 X0 (evar G T58) G)
    | subst_evar_there_evar
        {d33 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T58 s14 d33 G0 G1) -> (subst_evar G T58 s14 (XS tm d33) (evar G0 T) (evar G1 T))
    | subst_evar_there_etvar
        {d33 : (Trace tm)} {G0 : Env}
        {G1 : Env} :
        (subst_evar G T58 s14 d33 G0 G1) -> (subst_evar G T58 s14 (XS ty d33) (etvar G0) (etvar G1)).
  Lemma weaken_subst_evar {G : Env} {T58 : Ty} {s14 : Tm} :
    (forall (G0 : Env) {d33 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T58 s14 d33 G1 G2) -> (subst_evar G T58 s14 (weakenTrace d33 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (S30 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G S30 X0 (etvar G) G)
    | subst_etvar_there_evar
        {d33 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G S30 d33 G0 G1) -> (subst_etvar G S30 (XS tm d33) (evar G0 T) (evar G1 (tsubstTy d33 S30 T)))
    | subst_etvar_there_etvar
        {d33 : (Trace ty)} {G0 : Env}
        {G1 : Env} :
        (subst_etvar G S30 d33 G0 G1) -> (subst_etvar G S30 (XS ty d33) (etvar G0) (etvar G1)).
  Lemma weaken_subst_etvar {G : Env} {S30 : Ty} :
    (forall (G0 : Env) {d33 : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G S30 d33 G1 G2) -> (subst_etvar G S30 (weakenTrace d33 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d33 S30 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s14 : Tm} {T58 : Ty} :
    (forall {d33 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T58 s14 d33 G0 G1) -> (substhvl_tm (domainEnv G) d33 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S30 : Ty} :
    (forall {d33 : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G S30 d33 G0 G1) -> (substhvl_ty (domainEnv G) d33 (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T58 : Ty} (wf : (wfTy (domainEnv G) T58)) ,
    (lookup_evar (appendEnv (evar G T58) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T58 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) ,
    (lookup_etvar (appendEnv (etvar G) G0) (weakenIndexty I0 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfTm wfTy : infra.
 Hint Constructors wfTm wfTy : wf.
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
  (forall {c12 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c12 G G0)) {x52 : (Index tm)} {T58 : Ty} ,
    (lookup_evar G x52 T58) -> (lookup_evar G0 (shiftIndex c12 x52) T58)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c12 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c12 G G0)) {X43 : (Index ty)} ,
    (lookup_etvar G X43) -> (lookup_etvar G0 X43)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c12 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c12 G G0)) {x52 : (Index tm)} {T58 : Ty} ,
    (lookup_evar G x52 T58) -> (lookup_evar G0 x52 (tshiftTy c12 T58))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c12 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c12 G G0)) {X43 : (Index ty)} ,
    (lookup_etvar G X43) -> (lookup_etvar G0 (tshiftIndex c12 X43))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} {T59 : Ty} {s14 : Tm} :
  (forall {d33 : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T59 s14 d33 G0 G1)) {X43 : (Index ty)} ,
    (lookup_etvar G0 X43) -> (lookup_etvar G1 X43)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} {S30 : Ty} (wf : (wfTy (domainEnv G) S30)) :
  (forall {d33 : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G S30 d33 G0 G1)) {x52 : (Index tm)} {T59 : Ty} ,
    (lookup_evar G0 x52 T59) -> (lookup_evar G1 x52 (tsubstTy d33 S30 T59))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} : nat :=
  match S0 with
    | tvar X => 1
    | tarr T1 T2 => (plus 1 (plus (size_Ty T1) (size_Ty T2)))
    | tall T => (plus 1 (size_Ty T))
  end.
Fixpoint size_Tm (s : Tm) {struct s} : nat :=
  match s with
    | var x => 1
    | abs T t => (plus 1 (plus (size_Ty T) (size_Tm t)))
    | app t1 t2 => (plus 1 (plus (size_Tm t1) (size_Tm t2)))
    | tabs t0 => (plus 1 (size_Tm t0))
    | tapp t3 T0 => (plus 1 (plus (size_Tm t3) (size_Ty T0)))
  end.
Lemma tshift_size_Ty  :
  (forall (S30 : Ty) (c9 : (Cutoff ty)) ,
    ((size_Ty (tshiftTy c9 S30)) =
    (size_Ty S30))).
Proof.
  apply_mutual_ind ind_Ty.
  - intros X38 c9.
  reflexivity.
  - intros T51 IHT51 T52 IHT52.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT51 c10)).
  + exact ((IHT52 c10)).
  - intros T53 IHT53.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT53 (CS c10))).
Qed.

Lemma shift_size_Tm  :
  (forall (s14 : Tm) (c10 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c10 s14)) =
    (size_Tm s14))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros x48 c10.
  reflexivity.
  - intros T54 t84 IHt84.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt84 (CS c11))).
  - intros t85 IHt85 t86 IHt86.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt85 c11)).
  + exact ((IHt86 c11)).
  - intros t87 IHt87.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt87 c11)).
  - intros t88 IHt88 T55.
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
  - intros T56 t89 IHt89.
  pose proof ((tshift_size_Ty T56)) as IHT56.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT56 c12)).
  + exact ((IHt89 c12)).
  - intros t90 IHt90 t91 IHt91.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt90 c12)).
  + exact ((IHt91 c12)).
  - intros t92 IHt92.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt92 (CS c12))).
  - intros t93 IHt93 T57.
  pose proof ((tshift_size_Ty T57)) as IHT57.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt93 c12)).
  + exact ((IHT57 c12)).
Qed.

 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Tm  :
  (forall (k46 : Hvl) (s14 : Tm) ,
    ((size_Tm (weakenTm s14 k46)) =
    (size_Tm s14))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k46 : Hvl) (S30 : Ty) ,
    ((size_Ty (weakenTy S30 k46)) =
    (size_Ty S30))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : weaken_size.