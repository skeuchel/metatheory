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
  Inductive Kind : Set :=
    | star 
    | karr (K1 : Kind) (K2 : Kind).
  Scheme ind_Kind := Induction for Kind Sort Prop.
  
  Inductive Ty : Set :=
    | tvar (X : (Index ty))
    | tabs (K : Kind) (T : Ty)
    | tapp (T1 : Ty) (T2 : Ty)
    | tarr (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm).
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
      | (tabs K T) => (tabs K (tshiftTy (weakenCutoffty c (appendHvl (HS ty H0) H0)) T))
      | (tapp T1 T2) => (tapp (tshiftTy (weakenCutoffty c H0) T1) (tshiftTy (weakenCutoffty c H0) T2))
      | (tarr T0 T3) => (tarr (tshiftTy (weakenCutoffty c H0) T0) (tshiftTy (weakenCutoffty c H0) T3))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var (shiftIndex c x))
      | (abs T t) => (abs T (shiftTm (weakenCutofftm c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (shiftTm (weakenCutofftm c H0) t1) (shiftTm (weakenCutofftm c H0) t2))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tshiftTy (weakenCutoffty c H0) T) (tshiftTm (weakenCutoffty c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (tshiftTm (weakenCutoffty c H0) t1) (tshiftTm (weakenCutoffty c H0) t2))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenKind (K : Kind) (k : Hvl) {struct k} : Kind :=
    match k with
      | (H0) => K
      | (HS tm k) => (weakenKind K k)
      | (HS ty k) => (weakenKind K k)
    end.
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
      | (tabs K T) => (tabs K (tsubstTy (XS ty d) S0 T))
      | (tapp T1 T2) => (tapp (tsubstTy d S0 T1) (tsubstTy d S0 T2))
      | (tarr T0 T3) => (tarr (tsubstTy d S0 T0) (tsubstTy d S0 T3))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} : Tm :=
    match s0 with
      | (var x) => (substIndex d s x)
      | (abs T t) => (abs T (substTm (XS tm d) s t))
      | (app t1 t2) => (app (substTm d s t1) (substTm d s t2))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tsubstTy d S0 T) (tsubstTm (XS tm d) S0 t))
      | (app t1 t2) => (app (tsubstTm d S0 t1) (tsubstTm d S0 t2))
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
    (forall (k4 : Hvl) (X4 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k4) S0 (tshiftIndex (weakenCutoffty C0 k4) X4)) =
      (tvar X4))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Definition tsubst0_tshift0_Ty_reflection_ind := (ind_Ty (fun (S2 : Ty) =>
    (forall (k7 : Hvl) (S3 : Ty) ,
      ((tsubstTy (weakenTrace X0 k7) S3 (tshiftTy (weakenCutoffty C0 k7) S2)) =
      S2))) (fun (X8 : (Index ty)) =>
    (fun (k7 : Hvl) (S2 : Ty) =>
      (tsubstIndex0_tshiftIndex0_reflection_ind S2 k7 X8))) (fun (K : Kind) (T : Ty) IHT4 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHT4 (HS ty k7) S2)))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tapp (IHT4 k7 S2) (IHT5 k7 S2))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tarr (IHT4 k7 S2) (IHT5 k7 S2)))).
  Definition subst0_shift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (s1 : Tm) ,
      ((substTm (weakenTrace X0 k7) s1 (shiftTm (weakenCutofftm C0 k7) s0)) =
      s0))) (fun (x14 : (Index tm)) =>
    (fun (k7 : Hvl) (s0 : Tm) =>
      (substIndex0_shiftIndex0_reflection_ind s0 k7 x14))) (fun (T : Ty) (t : Tm) IHt17 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt17 (HS tm k7) s0)))) (fun (t1 : Tm) IHt17 (t2 : Tm) IHt18 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 app (IHt17 k7 s0) (IHt18 k7 s0)))).
  Definition tsubst0_tshift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (S2 : Ty) ,
      ((tsubstTm (weakenTrace X0 k7) S2 (tshiftTm (weakenCutoffty C0 k7) s0)) =
      s0))) (fun (x14 : (Index tm)) =>
    (fun (k7 : Hvl) (S2 : Ty) =>
      eq_refl)) (fun (T : Ty) (t : Tm) IHt17 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 abs (let IHT4 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT4 k7 S2)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt17 (HS tm k7) S2)))) (fun (t1 : Tm) IHt17 (t2 : Tm) IHt18 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 app (IHt17 k7 S2) (IHt18 k7 S2)))).
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
        (tshiftTy (weakenCutoffty C0 k4) (tshiftTy (weakenCutoffty c4 k4) S0))))) (fun (X4 : (Index ty)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k4 c4 X4)))) (fun (K : Kind) (T : Ty) IHT4 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tabs eq_refl (IHT4 (HS ty k4) c4))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tapp (IHT4 k4 c4) (IHT5 k4 c4))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tarr (IHT4 k4 c4) (IHT5 k4 c4)))).
    Definition shift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm (CS c4) k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff tm)) =>
        (f_equal var (shiftIndex_shiftIndex0_comm_ind k4 c4 x9)))) (fun (T : Ty) (t : Tm) IHt11 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt11 (HS tm k4) c4))) (fun (t1 : Tm) IHt11 (t2 : Tm) IHt12 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 app (IHt11 k4 c4) (IHt12 k4 c4)))).
    Definition shift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm c4 k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (shiftTm (weakenCutofftm c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff tm)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt11 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt11 (HS tm k4) c4))) (fun (t1 : Tm) IHt11 (t2 : Tm) IHt12 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 app (IHt11 k4 c4) (IHt12 k4 c4)))).
    Definition tshift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty c4 k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (tshiftTm (weakenCutoffty c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt11 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 abs eq_refl (IHt11 (HS tm k4) c4))) (fun (t1 : Tm) IHt11 (t2 : Tm) IHt12 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 app (IHt11 k4 c4) (IHt12 k4 c4)))).
    Definition tshift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty (CS c4) k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt11 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 abs (let IHT4 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT4 k4 c4)) (IHt11 (HS tm k4) c4))) (fun (t1 : Tm) IHt11 (t2 : Tm) IHt12 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 app (IHt11 k4 c4) (IHt12 k4 c4)))).
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
    (forall (k38 : Hvl) (c9 : (Cutoff ty)) (S26 : Ty) ,
      ((weakenTy (tshiftTy c9 S26) k38) =
      (tshiftTy (weakenCutoffty c9 k38) (weakenTy S26 k38)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k38 : Hvl) (c9 : (Cutoff tm)) (s10 : Tm) ,
      ((weakenTm (shiftTm c9 s10) k38) =
      (shiftTm (weakenCutofftm c9 k38) (weakenTm s10 k38)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k38 : Hvl) (c9 : (Cutoff ty)) (s10 : Tm) ,
      ((weakenTm (tshiftTm c9 s10) k38) =
      (tshiftTm (weakenCutoffty c9 k38) (weakenTm s10 k38)))).
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
      (forall (k7 : Hvl) (X8 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c4 k7) (tsubstIndex (weakenTrace X0 k7) S2 X8)) =
        (tsubstIndex (weakenTrace X0 k7) (tshiftTy c4 S2) (tshiftIndex (weakenCutoffty (CS c4) k7) X8)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Definition tshift_tsubst0_Ty_comm_ind := (ind_Ty (fun (S5 : Ty) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (S6 : Ty) ,
        ((tshiftTy (weakenCutoffty c9 k12) (tsubstTy (weakenTrace X0 k12) S6 S5)) =
        (tsubstTy (weakenTrace X0 k12) (tshiftTy c9 S6) (tshiftTy (weakenCutoffty (CS c9) k12) S5))))) (fun (X11 : (Index ty)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
        (tshiftTy_tsubstIndex0_comm_ind c9 S5 k12 X11))) (fun (K : Kind) (T : Ty) IHT4 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT4 (HS ty k12) c9 S5) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tapp (IHT4 k12 c9 S5) (IHT5 k12 c9 S5))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tarr (IHT4 k12 c9 S5) (IHT5 k12 c9 S5)))).
    Definition shift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff tm)) (s3 : Tm) ,
        ((shiftTm (weakenCutofftm c9 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (shiftTm c9 s3) (shiftTm (weakenCutofftm (CS c9) k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
        (shiftTm_substIndex0_comm_ind c9 s2 k12 x26))) (fun (T : Ty) (t : Tm) IHt29 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt29 (HS tm k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 app (IHt29 k12 c9 s2) (IHt30 k12 c9 s2)))).
    Definition shift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) ,
        ((shiftTm (weakenCutofftm c9 k12) (tsubstTm (weakenTrace X0 k12) S5 s2)) =
        (tsubstTm (weakenTrace X0 k12) S5 (shiftTm (weakenCutofftm c9 k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt29 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt29 (HS tm k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 app (IHt29 k12 c9 S5) (IHt30 k12 c9 S5)))).
    Definition tshift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (s3 : Tm) ,
        ((tshiftTm (weakenCutoffty c9 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (tshiftTm c9 s3) (tshiftTm (weakenCutoffty c9 k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
        (tshiftTm_substIndex0_comm_ind c9 s2 k12 x26))) (fun (T : Ty) (t : Tm) IHt29 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt29 (HS tm k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 app (IHt29 k12 c9 s2) (IHt30 k12 c9 s2)))).
    Definition tshift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) ,
        ((tshiftTm (weakenCutoffty c9 k12) (tsubstTm (weakenTrace X0 k12) S5 s2)) =
        (tsubstTm (weakenTrace X0 k12) (tshiftTy c9 S5) (tshiftTm (weakenCutoffty (CS c9) k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt29 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 abs (let IHT4 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT4 k12 c9 S5)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt29 (HS tm k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 app (IHt29 k12 c9 S5) (IHt30 k12 c9 S5)))).
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
      (forall (k12 : Hvl) (X11 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d) k12) S5 X11) =
        (tsubstIndex (weakenTrace d k12) S5 X11))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace ty)) (S5 : Ty) :
      (forall (k12 : Hvl) (X11 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d) k12) S5 (tshiftIndex (weakenCutoffty C0 k12) X11)) =
        (tshiftTy (weakenCutoffty C0 k12) (tsubstIndex (weakenTrace d k12) S5 X11)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Definition tsubst_tshift0_Ty_comm_ind := (ind_Ty (fun (S15 : Ty) =>
      (forall (k28 : Hvl) (d15 : (Trace ty)) (S16 : Ty) ,
        ((tsubstTy (weakenTrace (XS ty d15) k28) S16 (tshiftTy (weakenCutoffty C0 k28) S15)) =
        (tshiftTy (weakenCutoffty C0 k28) (tsubstTy (weakenTrace d15 k28) S16 S15))))) (fun (X14 : (Index ty)) =>
      (fun (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
        (tsubstIndex_tshiftTy0_comm_ind d15 S15 k28 X14))) (fun (K : Kind) (T : Ty) IHT4 (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d15) k28 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT4 (HS ty k28) d15 S15) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d15 k28 (HS ty H0))) eq_refl eq_refl)))))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
      (f_equal2 tapp (IHT4 k28 d15 S15) (IHT5 k28 d15 S15))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
      (f_equal2 tarr (IHT4 k28 d15 S15) (IHT5 k28 d15 S15)))).
    Definition subst_shift0_Tm_comm_ind := (ind_Tm (fun (s8 : Tm) =>
      (forall (k28 : Hvl) (d15 : (Trace tm)) (s9 : Tm) ,
        ((substTm (weakenTrace (XS tm d15) k28) s9 (shiftTm (weakenCutofftm C0 k28) s8)) =
        (shiftTm (weakenCutofftm C0 k28) (substTm (weakenTrace d15 k28) s9 s8))))) (fun (x38 : (Index tm)) =>
      (fun (k28 : Hvl) (d15 : (Trace tm)) (s8 : Tm) =>
        (substIndex_shiftTm0_comm_ind d15 s8 k28 x38))) (fun (T : Ty) (t : Tm) IHt41 (k28 : Hvl) (d15 : (Trace tm)) (s8 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d15) k28 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt41 (HS tm k28) d15 s8) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d15 k28 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt41 (t2 : Tm) IHt42 (k28 : Hvl) (d15 : (Trace tm)) (s8 : Tm) =>
      (f_equal2 app (IHt41 k28 d15 s8) (IHt42 k28 d15 s8)))).
    Definition subst_tshift0_Tm_comm_ind := (ind_Tm (fun (s8 : Tm) =>
      (forall (k28 : Hvl) (d15 : (Trace tm)) (s9 : Tm) ,
        ((substTm (weakenTrace (XS ty d15) k28) s9 (tshiftTm (weakenCutoffty C0 k28) s8)) =
        (tshiftTm (weakenCutoffty C0 k28) (substTm (weakenTrace d15 k28) s9 s8))))) (fun (x38 : (Index tm)) =>
      (fun (k28 : Hvl) (d15 : (Trace tm)) (s8 : Tm) =>
        (substIndex_tshiftTm0_comm_ind d15 s8 k28 x38))) (fun (T : Ty) (t : Tm) IHt41 (k28 : Hvl) (d15 : (Trace tm)) (s8 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d15) k28 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt41 (HS tm k28) d15 s8) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d15 k28 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt41 (t2 : Tm) IHt42 (k28 : Hvl) (d15 : (Trace tm)) (s8 : Tm) =>
      (f_equal2 app (IHt41 k28 d15 s8) (IHt42 k28 d15 s8)))).
    Definition tsubst_shift0_Tm_comm_ind := (ind_Tm (fun (s8 : Tm) =>
      (forall (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) ,
        ((tsubstTm (weakenTrace d15 k28) S15 (shiftTm (weakenCutofftm C0 k28) s8)) =
        (shiftTm (weakenCutofftm C0 k28) (tsubstTm (weakenTrace d15 k28) S15 s8))))) (fun (x38 : (Index tm)) =>
      (fun (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt41 (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d15 k28 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt41 (HS tm k28) d15 S15) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d15 k28 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt41 (t2 : Tm) IHt42 (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
      (f_equal2 app (IHt41 k28 d15 S15) (IHt42 k28 d15 S15)))).
    Definition tsubst_tshift0_Tm_comm_ind := (ind_Tm (fun (s8 : Tm) =>
      (forall (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) ,
        ((tsubstTm (weakenTrace (XS ty d15) k28) S15 (tshiftTm (weakenCutoffty C0 k28) s8)) =
        (tshiftTm (weakenCutoffty C0 k28) (tsubstTm (weakenTrace d15 k28) S15 s8))))) (fun (x38 : (Index tm)) =>
      (fun (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt41 (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
      (f_equal2 abs (let IHT4 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT4 k28 d15 S15)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d15) k28 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt41 (HS tm k28) d15 S15) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d15 k28 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt41 (t2 : Tm) IHt42 (k28 : Hvl) (d15 : (Trace ty)) (S15 : Ty) =>
      (f_equal2 app (IHt41 k28 d15 S15) (IHt42 k28 d15 S15)))).
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S23 : Ty) : (forall (d22 : (Trace ty)) (S22 : Ty) ,
      ((tsubstTy (XS ty d22) S22 (tshiftTy C0 S23)) =
      (tshiftTy C0 (tsubstTy d22 S22 S23)))) := (tsubst_tshift0_Ty_comm_ind S23 H0).
    Definition substTm_shiftTm0_comm (s9 : Tm) : (forall (d22 : (Trace tm)) (s8 : Tm) ,
      ((substTm (XS tm d22) s8 (shiftTm C0 s9)) =
      (shiftTm C0 (substTm d22 s8 s9)))) := (subst_shift0_Tm_comm_ind s9 H0).
    Definition substTm_tshiftTm0_comm (s9 : Tm) : (forall (d22 : (Trace tm)) (s8 : Tm) ,
      ((substTm (XS ty d22) s8 (tshiftTm C0 s9)) =
      (tshiftTm C0 (substTm d22 s8 s9)))) := (subst_tshift0_Tm_comm_ind s9 H0).
    Definition tsubstTm_shiftTm0_comm (s8 : Tm) : (forall (d22 : (Trace ty)) (S22 : Ty) ,
      ((tsubstTm d22 S22 (shiftTm C0 s8)) =
      (shiftTm C0 (tsubstTm d22 S22 s8)))) := (tsubst_shift0_Tm_comm_ind s8 H0).
    Definition tsubstTm_tshiftTm0_comm (s8 : Tm) : (forall (d22 : (Trace ty)) (S22 : Ty) ,
      ((tsubstTm (XS ty d22) S22 (tshiftTm C0 s8)) =
      (tshiftTm C0 (tsubstTm d22 S22 s8)))) := (tsubst_tshift0_Tm_comm_ind s8 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Definition tsubst_tm_Ty_ind := (ind_Ty (fun (S22 : Ty) =>
      (forall (k35 : Hvl) (d22 : (Trace ty)) (S23 : Ty) ,
        ((tsubstTy (weakenTrace (XS tm d22) k35) S23 S22) =
        (tsubstTy (weakenTrace d22 k35) S23 S22)))) (fun (X17 : (Index ty)) =>
      (fun (k35 : Hvl) (d22 : (Trace ty)) (S22 : Ty) =>
        (tsubstIndex_shiftTy0_comm_ind d22 S22 k35 X17))) (fun (K : Kind) (T : Ty) IHT4 (k35 : Hvl) (d22 : (Trace ty)) (S22 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d22) k35 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT4 (HS ty k35) d22 S22) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d22 k35 (HS ty H0))) eq_refl eq_refl))))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k35 : Hvl) (d22 : (Trace ty)) (S22 : Ty) =>
      (f_equal2 tapp (IHT4 k35 d22 S22) (IHT5 k35 d22 S22))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k35 : Hvl) (d22 : (Trace ty)) (S22 : Ty) =>
      (f_equal2 tarr (IHT4 k35 d22 S22) (IHT5 k35 d22 S22)))).
    Definition tsubst_tm_Tm_ind := (ind_Tm (fun (s8 : Tm) =>
      (forall (k35 : Hvl) (d22 : (Trace ty)) (S22 : Ty) ,
        ((tsubstTm (weakenTrace (XS tm d22) k35) S22 s8) =
        (tsubstTm (weakenTrace d22 k35) S22 s8)))) (fun (x41 : (Index tm)) =>
      (fun (k35 : Hvl) (d22 : (Trace ty)) (S22 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt44 (k35 : Hvl) (d22 : (Trace ty)) (S22 : Ty) =>
      (f_equal2 abs (let IHT4 := (tsubst_tm_Ty_ind T) in
      (IHT4 k35 d22 S22)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d22) k35 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt44 (HS tm k35) d22 S22) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d22 k35 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt44 (t2 : Tm) IHt45 (k35 : Hvl) (d22 : (Trace ty)) (S22 : Ty) =>
      (f_equal2 app (IHt44 k35 d22 S22) (IHt45 k35 d22 S22)))).
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S23 : Ty) : (forall (d22 : (Trace ty)) (S22 : Ty) ,
      ((tsubstTy (XS tm d22) S22 S23) =
      (tsubstTy d22 S22 S23))) := (tsubst_tm_Ty_ind S23 H0).
    Definition tsubstTm_tm (s8 : Tm) : (forall (d22 : (Trace ty)) (S22 : Ty) ,
      ((tsubstTm (XS tm d22) S22 s8) =
      (tsubstTm d22 S22 s8))) := (tsubst_tm_Tm_ind s8 H0).
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
    Lemma substTm_substIndex0_commright_ind (d22 : (Trace tm)) (s8 : Tm) (s9 : Tm) :
      (forall (k35 : Hvl) (x41 : (Index tm)) ,
        ((substTm (weakenTrace d22 k35) s8 (substIndex (weakenTrace X0 k35) s9 x41)) =
        (substTm (weakenTrace X0 k35) (substTm d22 s8 s9) (substIndex (weakenTrace (XS tm d22) k35) s8 x41)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d22 : (Trace ty)) (S22 : Ty) (s8 : Tm) :
      (forall (k35 : Hvl) (x41 : (Index tm)) ,
        ((tsubstTm (weakenTrace d22 k35) S22 (substIndex (weakenTrace X0 k35) s8 x41)) =
        (substIndex (weakenTrace X0 k35) (tsubstTm d22 S22 s8) x41))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d22 : (Trace ty)) (S22 : Ty) (S23 : Ty) :
      (forall (k35 : Hvl) (X17 : (Index ty)) ,
        ((tsubstTy (weakenTrace d22 k35) S22 (tsubstIndex (weakenTrace X0 k35) S23 X17)) =
        (tsubstTy (weakenTrace X0 k35) (tsubstTy d22 S22 S23) (tsubstIndex (weakenTrace (XS ty d22) k35) S22 X17)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d22 : (Trace tm)) (s8 : Tm) (S22 : Ty) :
      (forall (k35 : Hvl) (x41 : (Index tm)) ,
        ((substIndex (weakenTrace d22 k35) s8 x41) =
        (tsubstTm (weakenTrace X0 k35) S22 (substIndex (weakenTrace (XS ty d22) k35) s8 x41)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition tsubst_tsubst0_Ty_comm_ind := (ind_Ty (fun (S26 : Ty) =>
      (forall (k38 : Hvl) (d25 : (Trace ty)) (S27 : Ty) (S28 : Ty) ,
        ((tsubstTy (weakenTrace d25 k38) S27 (tsubstTy (weakenTrace X0 k38) S28 S26)) =
        (tsubstTy (weakenTrace X0 k38) (tsubstTy d25 S27 S28) (tsubstTy (weakenTrace (XS ty d25) k38) S27 S26))))) (fun (X20 : (Index ty)) =>
      (fun (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) =>
        (tsubstTy_tsubstIndex0_commright_ind d25 S26 S27 k38 X20))) (fun (K : Kind) (T : Ty) IHT4 (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d25 k38 (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k38 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT4 (HS ty k38) d25 S26 S27) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k38 (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d25) k38 (HS ty H0))) eq_refl eq_refl)))))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) =>
      (f_equal2 tapp (IHT4 k38 d25 S26 S27) (IHT5 k38 d25 S26 S27))) (fun (T1 : Ty) IHT4 (T2 : Ty) IHT5 (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) =>
      (f_equal2 tarr (IHT4 k38 d25 S26 S27) (IHT5 k38 d25 S26 S27)))).
    Definition subst_subst0_Tm_comm_ind := (ind_Tm (fun (s10 : Tm) =>
      (forall (k38 : Hvl) (d25 : (Trace tm)) (s11 : Tm) (s12 : Tm) ,
        ((substTm (weakenTrace d25 k38) s11 (substTm (weakenTrace X0 k38) s12 s10)) =
        (substTm (weakenTrace X0 k38) (substTm d25 s11 s12) (substTm (weakenTrace (XS tm d25) k38) s11 s10))))) (fun (x47 : (Index tm)) =>
      (fun (k38 : Hvl) (d25 : (Trace tm)) (s10 : Tm) (s11 : Tm) =>
        (substTm_substIndex0_commright_ind d25 s10 s11 k38 x47))) (fun (T : Ty) (t : Tm) IHt50 (k38 : Hvl) (d25 : (Trace tm)) (s10 : Tm) (s11 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d25 k38 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k38 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt50 (HS tm k38) d25 s10 s11) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k38 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d25) k38 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt50 (t2 : Tm) IHt51 (k38 : Hvl) (d25 : (Trace tm)) (s10 : Tm) (s11 : Tm) =>
      (f_equal2 app (IHt50 k38 d25 s10 s11) (IHt51 k38 d25 s10 s11)))).
    Definition subst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s10 : Tm) =>
      (forall (k38 : Hvl) (d25 : (Trace tm)) (s11 : Tm) (S26 : Ty) ,
        ((substTm (weakenTrace d25 k38) s11 (tsubstTm (weakenTrace X0 k38) S26 s10)) =
        (tsubstTm (weakenTrace X0 k38) S26 (substTm (weakenTrace (XS ty d25) k38) s11 s10))))) (fun (x47 : (Index tm)) =>
      (fun (k38 : Hvl) (d25 : (Trace tm)) (s10 : Tm) (S26 : Ty) =>
        (substTy_tsubstIndex0_commleft_ind d25 s10 S26 k38 x47))) (fun (T : Ty) (t : Tm) IHt50 (k38 : Hvl) (d25 : (Trace tm)) (s10 : Tm) (S26 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d25 k38 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k38 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt50 (HS tm k38) d25 s10 S26) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k38 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d25) k38 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt50 (t2 : Tm) IHt51 (k38 : Hvl) (d25 : (Trace tm)) (s10 : Tm) (S26 : Ty) =>
      (f_equal2 app (IHt50 k38 d25 s10 S26) (IHt51 k38 d25 s10 S26)))).
    Definition tsubst_subst0_Tm_comm_ind := (ind_Tm (fun (s10 : Tm) =>
      (forall (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (s11 : Tm) ,
        ((tsubstTm (weakenTrace d25 k38) S26 (substTm (weakenTrace X0 k38) s11 s10)) =
        (substTm (weakenTrace X0 k38) (tsubstTm d25 S26 s11) (tsubstTm (weakenTrace d25 k38) S26 s10))))) (fun (x47 : (Index tm)) =>
      (fun (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (s10 : Tm) =>
        (tsubstTm_substIndex0_commright_ind d25 S26 s10 k38 x47))) (fun (T : Ty) (t : Tm) IHt50 (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (s10 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d25 k38 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k38 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt50 (HS tm k38) d25 S26 s10) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k38 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d25 k38 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt50 (t2 : Tm) IHt51 (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (s10 : Tm) =>
      (f_equal2 app (IHt50 k38 d25 S26 s10) (IHt51 k38 d25 S26 s10)))).
    Definition tsubst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s10 : Tm) =>
      (forall (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) ,
        ((tsubstTm (weakenTrace d25 k38) S26 (tsubstTm (weakenTrace X0 k38) S27 s10)) =
        (tsubstTm (weakenTrace X0 k38) (tsubstTy d25 S26 S27) (tsubstTm (weakenTrace (XS ty d25) k38) S26 s10))))) (fun (x47 : (Index tm)) =>
      (fun (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt50 (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) =>
      (f_equal2 abs (let IHT4 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT4 k38 d25 S26 S27)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d25 k38 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k38 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt50 (HS tm k38) d25 S26 S27) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k38 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d25) k38 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt50 (t2 : Tm) IHt51 (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) =>
      (f_equal2 app (IHt50 k38 d25 S26 S27) (IHt51 k38 d25 S26 S27)))).
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S28 : Ty) : (forall (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) ,
      ((tsubstTy d25 S26 (tsubstTy X0 S27 S28)) =
      (tsubstTy X0 (tsubstTy d25 S26 S27) (tsubstTy (XS ty d25) S26 S28)))) := (tsubst_tsubst0_Ty_comm_ind S28 H0).
    Definition substTm_substTm0_comm (s12 : Tm) : (forall (d25 : (Trace tm)) (s10 : Tm) (s11 : Tm) ,
      ((substTm d25 s10 (substTm X0 s11 s12)) =
      (substTm X0 (substTm d25 s10 s11) (substTm (XS tm d25) s10 s12)))) := (subst_subst0_Tm_comm_ind s12 H0).
    Definition substTm_tsubstTm0_comm (s11 : Tm) : (forall (d25 : (Trace tm)) (s10 : Tm) (S26 : Ty) ,
      ((substTm d25 s10 (tsubstTm X0 S26 s11)) =
      (tsubstTm X0 S26 (substTm (XS ty d25) s10 s11)))) := (subst_tsubst0_Tm_comm_ind s11 H0).
    Definition tsubstTm_substTm0_comm (s11 : Tm) : (forall (d25 : (Trace ty)) (S26 : Ty) (s10 : Tm) ,
      ((tsubstTm d25 S26 (substTm X0 s10 s11)) =
      (substTm X0 (tsubstTm d25 S26 s10) (tsubstTm d25 S26 s11)))) := (tsubst_subst0_Tm_comm_ind s11 H0).
    Definition tsubstTm_tsubstTm0_comm (s10 : Tm) : (forall (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) ,
      ((tsubstTm d25 S26 (tsubstTm X0 S27 s10)) =
      (tsubstTm X0 (tsubstTy d25 S26 S27) (tsubstTm (XS ty d25) S26 s10)))) := (tsubst_tsubst0_Tm_comm_ind s10 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (S27 : Ty) ,
        ((weakenTy (tsubstTy d25 S26 S27) k38) =
        (tsubstTy (weakenTrace d25 k38) S26 (weakenTy S27 k38)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k38 : Hvl) (d25 : (Trace tm)) (s10 : Tm) (s11 : Tm) ,
        ((weakenTm (substTm d25 s10 s11) k38) =
        (substTm (weakenTrace d25 k38) s10 (weakenTm s11 k38)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k38 : Hvl) (d25 : (Trace ty)) (S26 : Ty) (s10 : Tm) ,
        ((weakenTm (tsubstTm d25 S26 s10) k38) =
        (tsubstTm (weakenTrace d25 k38) S26 (weakenTm s10 k38)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenKind_append  :
      (forall (K5 : Kind) (k38 : Hvl) (k39 : Hvl) ,
        ((weakenKind (weakenKind K5 k38) k39) =
        (weakenKind K5 (appendHvl k38 k39)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTy_append  :
      (forall (S26 : Ty) (k38 : Hvl) (k39 : Hvl) ,
        ((weakenTy (weakenTy S26 k38) k39) =
        (weakenTy S26 (appendHvl k38 k39)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s10 : Tm) (k38 : Hvl) (k39 : Hvl) ,
        ((weakenTm (weakenTm s10 k38) k39) =
        (weakenTm s10 (appendHvl k38 k39)))).
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
  Fixpoint wfindex {a : Namespace} (k38 : Hvl) (i : (Index a)) {struct k38} : Prop :=
    match k38 with
      | (H0) => False
      | (HS b k38) => match (eq_namespace_dec a b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k38 i)
        end
        | (right n) => (wfindex k38 i)
      end
    end.
  Inductive wfKind (k38 : Hvl) : Kind -> Prop :=
    | wfKind_star :
        (wfKind k38 (star))
    | wfKind_karr {K6 : Kind}
        (wf : (wfKind k38 K6))
        {K7 : Kind}
        (wf0 : (wfKind k38 K7)) :
        (wfKind k38 (karr K6 K7)).
  Inductive wfTy (k38 : Hvl) : Ty -> Prop :=
    | wfTy_tvar {X24 : (Index ty)}
        (wfi : (wfindex k38 X24)) :
        (wfTy k38 (tvar X24))
    | wfTy_tabs {K6 : Kind}
        (wf : (wfKind k38 K6))
        {T53 : Ty}
        (wf0 : (wfTy (HS ty k38) T53)) :
        (wfTy k38 (tabs K6 T53))
    | wfTy_tapp {T54 : Ty}
        (wf : (wfTy k38 T54)) {T55 : Ty}
        (wf0 : (wfTy k38 T55)) :
        (wfTy k38 (tapp T54 T55))
    | wfTy_tarr {T56 : Ty}
        (wf : (wfTy k38 T56)) {T57 : Ty}
        (wf0 : (wfTy k38 T57)) :
        (wfTy k38 (tarr T56 T57)).
  Inductive wfTm (k38 : Hvl) : Tm -> Prop :=
    | wfTm_var {x52 : (Index tm)}
        (wfi : (wfindex k38 x52)) :
        (wfTm k38 (var x52))
    | wfTm_abs {T53 : Ty}
        (wf : (wfTy k38 T53)) {t56 : Tm}
        (wf0 : (wfTm (HS tm k38) t56)) :
        (wfTm k38 (abs T53 t56))
    | wfTm_app {t57 : Tm}
        (wf : (wfTm k38 t57)) {t58 : Tm}
        (wf0 : (wfTm k38 t58)) :
        (wfTm k38 (app t57 t58)).
  Scheme ind_wfKind := Induction for wfKind Sort Prop.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c12 : (Cutoff tm)) (k38 : Hvl) (k39 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k38 : Hvl)
        :
        (shifthvl_tm C0 k38 (HS tm k38))
    | shifthvl_tm_there_tm
        (c12 : (Cutoff tm)) (k38 : Hvl)
        (k39 : Hvl) :
        (shifthvl_tm c12 k38 k39) -> (shifthvl_tm (CS c12) (HS tm k38) (HS tm k39))
    | shifthvl_tm_there_ty
        (c12 : (Cutoff tm)) (k38 : Hvl)
        (k39 : Hvl) :
        (shifthvl_tm c12 k38 k39) -> (shifthvl_tm c12 (HS ty k38) (HS ty k39)).
  Inductive shifthvl_ty : (forall (c12 : (Cutoff ty)) (k38 : Hvl) (k39 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k38 : Hvl)
        :
        (shifthvl_ty C0 k38 (HS ty k38))
    | shifthvl_ty_there_tm
        (c12 : (Cutoff ty)) (k38 : Hvl)
        (k39 : Hvl) :
        (shifthvl_ty c12 k38 k39) -> (shifthvl_ty c12 (HS tm k38) (HS tm k39))
    | shifthvl_ty_there_ty
        (c12 : (Cutoff ty)) (k38 : Hvl)
        (k39 : Hvl) :
        (shifthvl_ty c12 k38 k39) -> (shifthvl_ty (CS c12) (HS ty k38) (HS ty k39)).
  Lemma weaken_shifthvl_tm  :
    (forall (k38 : Hvl) {c12 : (Cutoff tm)} {k39 : Hvl} {k40 : Hvl} ,
      (shifthvl_tm c12 k39 k40) -> (shifthvl_tm (weakenCutofftm c12 k38) (appendHvl k39 k38) (appendHvl k40 k38))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k38 : Hvl) {c12 : (Cutoff ty)} {k39 : Hvl} {k40 : Hvl} ,
      (shifthvl_ty c12 k39 k40) -> (shifthvl_ty (weakenCutoffty c12 k38) (appendHvl k39 k38) (appendHvl k40 k38))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c12 : (Cutoff tm)) (k38 : Hvl) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) (x52 : (Index tm)) ,
      (wfindex k38 x52) -> (wfindex k39 (shiftIndex c12 x52))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c12 : (Cutoff tm)) (k38 : Hvl) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) (X24 : (Index ty)) ,
      (wfindex k38 X24) -> (wfindex k39 X24)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c12 : (Cutoff ty)) (k38 : Hvl) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) (x52 : (Index tm)) ,
      (wfindex k38 x52) -> (wfindex k39 x52)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c12 : (Cutoff ty)) (k38 : Hvl) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) (X24 : (Index ty)) ,
      (wfindex k38 X24) -> (wfindex k39 (tshiftIndex c12 X24))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfKind : (forall (k38 : Hvl) ,
    (forall (K6 : Kind) (wf : (wfKind k38 K6)) ,
      (forall (c12 : (Cutoff tm)) (k39 : Hvl) ,
        (shifthvl_tm c12 k38 k39) -> (wfKind k39 K6)))) := (fun (k38 : Hvl) =>
    (ind_wfKind k38 (fun (K6 : Kind) (wf : (wfKind k38 K6)) =>
      (forall (c12 : (Cutoff tm)) (k39 : Hvl) ,
        (shifthvl_tm c12 k38 k39) -> (wfKind k39 K6))) (fun (c12 : (Cutoff tm)) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) =>
      (wfKind_star k39)) (fun (K1 : Kind) (wf : (wfKind k38 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k38 K2)) IHK2 (c12 : (Cutoff tm)) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) =>
      (wfKind_karr k39 (IHK1 c12 k39 (weaken_shifthvl_tm H0 ins)) (IHK2 c12 k39 (weaken_shifthvl_tm H0 ins)))))).
  Definition tshift_wfKind : (forall (k38 : Hvl) ,
    (forall (K6 : Kind) (wf : (wfKind k38 K6)) ,
      (forall (c12 : (Cutoff ty)) (k39 : Hvl) ,
        (shifthvl_ty c12 k38 k39) -> (wfKind k39 K6)))) := (fun (k38 : Hvl) =>
    (ind_wfKind k38 (fun (K6 : Kind) (wf : (wfKind k38 K6)) =>
      (forall (c12 : (Cutoff ty)) (k39 : Hvl) ,
        (shifthvl_ty c12 k38 k39) -> (wfKind k39 K6))) (fun (c12 : (Cutoff ty)) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) =>
      (wfKind_star k39)) (fun (K1 : Kind) (wf : (wfKind k38 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k38 K2)) IHK2 (c12 : (Cutoff ty)) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) =>
      (wfKind_karr k39 (IHK1 c12 k39 (weaken_shifthvl_ty H0 ins)) (IHK2 c12 k39 (weaken_shifthvl_ty H0 ins)))))).
  Definition shift_wfTy : (forall (k38 : Hvl) ,
    (forall (S26 : Ty) (wf : (wfTy k38 S26)) ,
      (forall (c12 : (Cutoff tm)) (k39 : Hvl) ,
        (shifthvl_tm c12 k38 k39) -> (wfTy k39 S26)))) := (ind_wfTy (fun (k38 : Hvl) (S26 : Ty) (wf : (wfTy k38 S26)) =>
    (forall (c12 : (Cutoff tm)) (k39 : Hvl) ,
      (shifthvl_tm c12 k38 k39) -> (wfTy k39 S26))) (fun (k38 : Hvl) (X24 : (Index ty)) (wfi : (wfindex k38 X24)) (c12 : (Cutoff tm)) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) =>
    (wfTy_tvar k39 (shift_wfindex_ty c12 k38 k39 ins X24 wfi))) (fun (k38 : Hvl) (K : Kind) (wf : (wfKind k38 K)) (T : Ty) (wf0 : (wfTy (HS ty k38) T)) IHT4 (c12 : (Cutoff tm)) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) =>
    (wfTy_tabs k39 (shift_wfKind k38 K wf c12 k39 (weaken_shifthvl_tm H0 ins)) (IHT4 c12 (HS ty k39) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k38 : Hvl) (T1 : Ty) (wf : (wfTy k38 T1)) IHT4 (T2 : Ty) (wf0 : (wfTy k38 T2)) IHT5 (c12 : (Cutoff tm)) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) =>
    (wfTy_tapp k39 (IHT4 c12 k39 (weaken_shifthvl_tm H0 ins)) (IHT5 c12 k39 (weaken_shifthvl_tm H0 ins)))) (fun (k38 : Hvl) (T1 : Ty) (wf : (wfTy k38 T1)) IHT4 (T2 : Ty) (wf0 : (wfTy k38 T2)) IHT5 (c12 : (Cutoff tm)) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) =>
    (wfTy_tarr k39 (IHT4 c12 k39 (weaken_shifthvl_tm H0 ins)) (IHT5 c12 k39 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTy : (forall (k38 : Hvl) ,
    (forall (S26 : Ty) (wf : (wfTy k38 S26)) ,
      (forall (c12 : (Cutoff ty)) (k39 : Hvl) ,
        (shifthvl_ty c12 k38 k39) -> (wfTy k39 (tshiftTy c12 S26))))) := (ind_wfTy (fun (k38 : Hvl) (S26 : Ty) (wf : (wfTy k38 S26)) =>
    (forall (c12 : (Cutoff ty)) (k39 : Hvl) ,
      (shifthvl_ty c12 k38 k39) -> (wfTy k39 (tshiftTy c12 S26)))) (fun (k38 : Hvl) (X24 : (Index ty)) (wfi : (wfindex k38 X24)) (c12 : (Cutoff ty)) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) =>
    (wfTy_tvar k39 (tshift_wfindex_ty c12 k38 k39 ins X24 wfi))) (fun (k38 : Hvl) (K : Kind) (wf : (wfKind k38 K)) (T : Ty) (wf0 : (wfTy (HS ty k38) T)) IHT4 (c12 : (Cutoff ty)) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) =>
    (wfTy_tabs k39 (tshift_wfKind k38 K wf c12 k39 (weaken_shifthvl_ty H0 ins)) (IHT4 (CS c12) (HS ty k39) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k38 : Hvl) (T1 : Ty) (wf : (wfTy k38 T1)) IHT4 (T2 : Ty) (wf0 : (wfTy k38 T2)) IHT5 (c12 : (Cutoff ty)) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) =>
    (wfTy_tapp k39 (IHT4 c12 k39 (weaken_shifthvl_ty H0 ins)) (IHT5 c12 k39 (weaken_shifthvl_ty H0 ins)))) (fun (k38 : Hvl) (T1 : Ty) (wf : (wfTy k38 T1)) IHT4 (T2 : Ty) (wf0 : (wfTy k38 T2)) IHT5 (c12 : (Cutoff ty)) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) =>
    (wfTy_tarr k39 (IHT4 c12 k39 (weaken_shifthvl_ty H0 ins)) (IHT5 c12 k39 (weaken_shifthvl_ty H0 ins))))).
  Definition shift_wfTm : (forall (k38 : Hvl) ,
    (forall (s10 : Tm) (wf : (wfTm k38 s10)) ,
      (forall (c12 : (Cutoff tm)) (k39 : Hvl) ,
        (shifthvl_tm c12 k38 k39) -> (wfTm k39 (shiftTm c12 s10))))) := (ind_wfTm (fun (k38 : Hvl) (s10 : Tm) (wf : (wfTm k38 s10)) =>
    (forall (c12 : (Cutoff tm)) (k39 : Hvl) ,
      (shifthvl_tm c12 k38 k39) -> (wfTm k39 (shiftTm c12 s10)))) (fun (k38 : Hvl) (x52 : (Index tm)) (wfi : (wfindex k38 x52)) (c12 : (Cutoff tm)) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) =>
    (wfTm_var k39 (shift_wfindex_tm c12 k38 k39 ins x52 wfi))) (fun (k38 : Hvl) (T : Ty) (wf : (wfTy k38 T)) (t : Tm) (wf0 : (wfTm (HS tm k38) t)) IHt56 (c12 : (Cutoff tm)) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) =>
    (wfTm_abs k39 (shift_wfTy k38 T wf c12 k39 (weaken_shifthvl_tm H0 ins)) (IHt56 (CS c12) (HS tm k39) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k38 : Hvl) (t1 : Tm) (wf : (wfTm k38 t1)) IHt56 (t2 : Tm) (wf0 : (wfTm k38 t2)) IHt57 (c12 : (Cutoff tm)) (k39 : Hvl) (ins : (shifthvl_tm c12 k38 k39)) =>
    (wfTm_app k39 (IHt56 c12 k39 (weaken_shifthvl_tm H0 ins)) (IHt57 c12 k39 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTm : (forall (k38 : Hvl) ,
    (forall (s10 : Tm) (wf : (wfTm k38 s10)) ,
      (forall (c12 : (Cutoff ty)) (k39 : Hvl) ,
        (shifthvl_ty c12 k38 k39) -> (wfTm k39 (tshiftTm c12 s10))))) := (ind_wfTm (fun (k38 : Hvl) (s10 : Tm) (wf : (wfTm k38 s10)) =>
    (forall (c12 : (Cutoff ty)) (k39 : Hvl) ,
      (shifthvl_ty c12 k38 k39) -> (wfTm k39 (tshiftTm c12 s10)))) (fun (k38 : Hvl) (x52 : (Index tm)) (wfi : (wfindex k38 x52)) (c12 : (Cutoff ty)) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) =>
    (wfTm_var k39 (tshift_wfindex_tm c12 k38 k39 ins x52 wfi))) (fun (k38 : Hvl) (T : Ty) (wf : (wfTy k38 T)) (t : Tm) (wf0 : (wfTm (HS tm k38) t)) IHt56 (c12 : (Cutoff ty)) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) =>
    (wfTm_abs k39 (tshift_wfTy k38 T wf c12 k39 (weaken_shifthvl_ty H0 ins)) (IHt56 c12 (HS tm k39) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k38 : Hvl) (t1 : Tm) (wf : (wfTm k38 t1)) IHt56 (t2 : Tm) (wf0 : (wfTm k38 t2)) IHt57 (c12 : (Cutoff ty)) (k39 : Hvl) (ins : (shifthvl_ty c12 k38 k39)) =>
    (wfTm_app k39 (IHt56 c12 k39 (weaken_shifthvl_ty H0 ins)) (IHt57 c12 k39 (weaken_shifthvl_ty H0 ins))))).
End ShiftWellFormed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_tm (k38 : Hvl) : (forall (d25 : (Trace tm)) (k39 : Hvl) (k40 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k38 X0 (HS tm k38) k38)
    | substhvl_tm_there_tm
        {d25 : (Trace tm)} {k39 : Hvl}
        {k40 : Hvl} :
        (substhvl_tm k38 d25 k39 k40) -> (substhvl_tm k38 (XS tm d25) (HS tm k39) (HS tm k40))
    | substhvl_tm_there_ty
        {d25 : (Trace tm)} {k39 : Hvl}
        {k40 : Hvl} :
        (substhvl_tm k38 d25 k39 k40) -> (substhvl_tm k38 (XS ty d25) (HS ty k39) (HS ty k40)).
  Inductive substhvl_ty (k38 : Hvl) : (forall (d25 : (Trace ty)) (k39 : Hvl) (k40 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k38 X0 (HS ty k38) k38)
    | substhvl_ty_there_tm
        {d25 : (Trace ty)} {k39 : Hvl}
        {k40 : Hvl} :
        (substhvl_ty k38 d25 k39 k40) -> (substhvl_ty k38 (XS tm d25) (HS tm k39) (HS tm k40))
    | substhvl_ty_there_ty
        {d25 : (Trace ty)} {k39 : Hvl}
        {k40 : Hvl} :
        (substhvl_ty k38 d25 k39 k40) -> (substhvl_ty k38 (XS ty d25) (HS ty k39) (HS ty k40)).
  Lemma weaken_substhvl_tm  :
    (forall {k39 : Hvl} (k38 : Hvl) {d25 : (Trace tm)} {k40 : Hvl} {k41 : Hvl} ,
      (substhvl_tm k39 d25 k40 k41) -> (substhvl_tm k39 (weakenTrace d25 k38) (appendHvl k40 k38) (appendHvl k41 k38))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k39 : Hvl} (k38 : Hvl) {d25 : (Trace ty)} {k40 : Hvl} {k41 : Hvl} ,
      (substhvl_ty k39 d25 k40 k41) -> (substhvl_ty k39 (weakenTrace d25 k38) (appendHvl k40 k38) (appendHvl k41 k38))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k38 : Hvl} {s10 : Tm} (wft : (wfTm k38 s10)) :
    (forall {d25 : (Trace tm)} {k39 : Hvl} {k40 : Hvl} ,
      (substhvl_tm k38 d25 k39 k40) -> (forall {x52 : (Index tm)} ,
        (wfindex k39 x52) -> (wfTm k40 (substIndex d25 s10 x52)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k38 : Hvl} {S26 : Ty} (wft : (wfTy k38 S26)) :
    (forall {d25 : (Trace ty)} {k39 : Hvl} {k40 : Hvl} ,
      (substhvl_ty k38 d25 k39 k40) -> (forall {X24 : (Index ty)} ,
        (wfindex k39 X24) -> (wfTy k40 (tsubstIndex d25 S26 X24)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k38 : Hvl} :
    (forall {d25 : (Trace tm)} {k39 : Hvl} {k40 : Hvl} ,
      (substhvl_tm k38 d25 k39 k40) -> (forall {X24 : (Index ty)} ,
        (wfindex k39 X24) -> (wfindex k40 X24))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k38 : Hvl} :
    (forall {d25 : (Trace ty)} {k39 : Hvl} {k40 : Hvl} ,
      (substhvl_ty k38 d25 k39 k40) -> (forall {x52 : (Index tm)} ,
        (wfindex k39 x52) -> (wfindex k40 x52))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfKind {k38 : Hvl} : (forall (k39 : Hvl) ,
    (forall (K6 : Kind) (wf0 : (wfKind k39 K6)) ,
      (forall {d25 : (Trace tm)} {k40 : Hvl} ,
        (substhvl_tm k38 d25 k39 k40) -> (wfKind k40 K6)))) := (fun (k39 : Hvl) =>
    (ind_wfKind k39 (fun (K6 : Kind) (wf0 : (wfKind k39 K6)) =>
      (forall {d25 : (Trace tm)} {k40 : Hvl} ,
        (substhvl_tm k38 d25 k39 k40) -> (wfKind k40 K6))) (fun {d25 : (Trace tm)} {k40 : Hvl} (del : (substhvl_tm k38 d25 k39 k40)) =>
      (wfKind_star k40)) (fun (K1 : Kind) (wf0 : (wfKind k39 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k39 K2)) IHK2 {d25 : (Trace tm)} {k40 : Hvl} (del : (substhvl_tm k38 d25 k39 k40)) =>
      (wfKind_karr k40 (IHK1 (weakenTrace d25 H0) k40 (weaken_substhvl_tm H0 del)) (IHK2 (weakenTrace d25 H0) k40 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_ty_wfKind {k38 : Hvl} : (forall (k39 : Hvl) ,
    (forall (K6 : Kind) (wf0 : (wfKind k39 K6)) ,
      (forall {d25 : (Trace ty)} {k40 : Hvl} ,
        (substhvl_ty k38 d25 k39 k40) -> (wfKind k40 K6)))) := (fun (k39 : Hvl) =>
    (ind_wfKind k39 (fun (K6 : Kind) (wf0 : (wfKind k39 K6)) =>
      (forall {d25 : (Trace ty)} {k40 : Hvl} ,
        (substhvl_ty k38 d25 k39 k40) -> (wfKind k40 K6))) (fun {d25 : (Trace ty)} {k40 : Hvl} (del : (substhvl_ty k38 d25 k39 k40)) =>
      (wfKind_star k40)) (fun (K1 : Kind) (wf0 : (wfKind k39 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k39 K2)) IHK2 {d25 : (Trace ty)} {k40 : Hvl} (del : (substhvl_ty k38 d25 k39 k40)) =>
      (wfKind_karr k40 (IHK1 (weakenTrace d25 H0) k40 (weaken_substhvl_ty H0 del)) (IHK2 (weakenTrace d25 H0) k40 (weaken_substhvl_ty H0 del)))))).
  Definition substhvl_tm_wfTy {k38 : Hvl} : (forall (k39 : Hvl) ,
    (forall (S26 : Ty) (wf0 : (wfTy k39 S26)) ,
      (forall {d25 : (Trace tm)} {k40 : Hvl} ,
        (substhvl_tm k38 d25 k39 k40) -> (wfTy k40 S26)))) := (ind_wfTy (fun (k39 : Hvl) (S26 : Ty) (wf0 : (wfTy k39 S26)) =>
    (forall {d25 : (Trace tm)} {k40 : Hvl} ,
      (substhvl_tm k38 d25 k39 k40) -> (wfTy k40 S26))) (fun (k39 : Hvl) {X24 : (Index ty)} (wfi : (wfindex k39 X24)) {d25 : (Trace tm)} {k40 : Hvl} (del : (substhvl_tm k38 d25 k39 k40)) =>
    (wfTy_tvar k40 (substhvl_tm_wfindex_ty del wfi))) (fun (k39 : Hvl) (K : Kind) (wf0 : (wfKind k39 K)) (T : Ty) (wf1 : (wfTy (HS ty k39) T)) IHT4 {d25 : (Trace tm)} {k40 : Hvl} (del : (substhvl_tm k38 d25 k39 k40)) =>
    (wfTy_tabs k40 (substhvl_tm_wfKind k39 K wf0 (weaken_substhvl_tm H0 del)) (IHT4 (weakenTrace d25 (HS ty H0)) (HS ty k40) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k39 : Hvl) (T1 : Ty) (wf0 : (wfTy k39 T1)) IHT4 (T2 : Ty) (wf1 : (wfTy k39 T2)) IHT5 {d25 : (Trace tm)} {k40 : Hvl} (del : (substhvl_tm k38 d25 k39 k40)) =>
    (wfTy_tapp k40 (IHT4 (weakenTrace d25 H0) k40 (weaken_substhvl_tm H0 del)) (IHT5 (weakenTrace d25 H0) k40 (weaken_substhvl_tm H0 del)))) (fun (k39 : Hvl) (T1 : Ty) (wf0 : (wfTy k39 T1)) IHT4 (T2 : Ty) (wf1 : (wfTy k39 T2)) IHT5 {d25 : (Trace tm)} {k40 : Hvl} (del : (substhvl_tm k38 d25 k39 k40)) =>
    (wfTy_tarr k40 (IHT4 (weakenTrace d25 H0) k40 (weaken_substhvl_tm H0 del)) (IHT5 (weakenTrace d25 H0) k40 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTy {k38 : Hvl} {S26 : Ty} (wf : (wfTy k38 S26)) : (forall (k39 : Hvl) ,
    (forall (S27 : Ty) (wf0 : (wfTy k39 S27)) ,
      (forall {d25 : (Trace ty)} {k40 : Hvl} ,
        (substhvl_ty k38 d25 k39 k40) -> (wfTy k40 (tsubstTy d25 S26 S27))))) := (ind_wfTy (fun (k39 : Hvl) (S27 : Ty) (wf0 : (wfTy k39 S27)) =>
    (forall {d25 : (Trace ty)} {k40 : Hvl} ,
      (substhvl_ty k38 d25 k39 k40) -> (wfTy k40 (tsubstTy d25 S26 S27)))) (fun (k39 : Hvl) {X24 : (Index ty)} (wfi : (wfindex k39 X24)) {d25 : (Trace ty)} {k40 : Hvl} (del : (substhvl_ty k38 d25 k39 k40)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k39 : Hvl) (K : Kind) (wf0 : (wfKind k39 K)) (T : Ty) (wf1 : (wfTy (HS ty k39) T)) IHT4 {d25 : (Trace ty)} {k40 : Hvl} (del : (substhvl_ty k38 d25 k39 k40)) =>
    (wfTy_tabs k40 (substhvl_ty_wfKind k39 K wf0 (weaken_substhvl_ty H0 del)) (IHT4 (weakenTrace d25 (HS ty H0)) (HS ty k40) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k39 : Hvl) (T1 : Ty) (wf0 : (wfTy k39 T1)) IHT4 (T2 : Ty) (wf1 : (wfTy k39 T2)) IHT5 {d25 : (Trace ty)} {k40 : Hvl} (del : (substhvl_ty k38 d25 k39 k40)) =>
    (wfTy_tapp k40 (IHT4 (weakenTrace d25 H0) k40 (weaken_substhvl_ty H0 del)) (IHT5 (weakenTrace d25 H0) k40 (weaken_substhvl_ty H0 del)))) (fun (k39 : Hvl) (T1 : Ty) (wf0 : (wfTy k39 T1)) IHT4 (T2 : Ty) (wf1 : (wfTy k39 T2)) IHT5 {d25 : (Trace ty)} {k40 : Hvl} (del : (substhvl_ty k38 d25 k39 k40)) =>
    (wfTy_tarr k40 (IHT4 (weakenTrace d25 H0) k40 (weaken_substhvl_ty H0 del)) (IHT5 (weakenTrace d25 H0) k40 (weaken_substhvl_ty H0 del))))).
  Definition substhvl_tm_wfTm {k38 : Hvl} {s10 : Tm} (wf : (wfTm k38 s10)) : (forall (k39 : Hvl) ,
    (forall (s11 : Tm) (wf0 : (wfTm k39 s11)) ,
      (forall {d25 : (Trace tm)} {k40 : Hvl} ,
        (substhvl_tm k38 d25 k39 k40) -> (wfTm k40 (substTm d25 s10 s11))))) := (ind_wfTm (fun (k39 : Hvl) (s11 : Tm) (wf0 : (wfTm k39 s11)) =>
    (forall {d25 : (Trace tm)} {k40 : Hvl} ,
      (substhvl_tm k38 d25 k39 k40) -> (wfTm k40 (substTm d25 s10 s11)))) (fun (k39 : Hvl) {x52 : (Index tm)} (wfi : (wfindex k39 x52)) {d25 : (Trace tm)} {k40 : Hvl} (del : (substhvl_tm k38 d25 k39 k40)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k39 : Hvl) (T : Ty) (wf0 : (wfTy k39 T)) (t : Tm) (wf1 : (wfTm (HS tm k39) t)) IHt56 {d25 : (Trace tm)} {k40 : Hvl} (del : (substhvl_tm k38 d25 k39 k40)) =>
    (wfTm_abs k40 (substhvl_tm_wfTy k39 T wf0 (weaken_substhvl_tm H0 del)) (IHt56 (weakenTrace d25 (HS tm H0)) (HS tm k40) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k39 : Hvl) (t1 : Tm) (wf0 : (wfTm k39 t1)) IHt56 (t2 : Tm) (wf1 : (wfTm k39 t2)) IHt57 {d25 : (Trace tm)} {k40 : Hvl} (del : (substhvl_tm k38 d25 k39 k40)) =>
    (wfTm_app k40 (IHt56 (weakenTrace d25 H0) k40 (weaken_substhvl_tm H0 del)) (IHt57 (weakenTrace d25 H0) k40 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTm {k38 : Hvl} {S26 : Ty} (wf : (wfTy k38 S26)) : (forall (k39 : Hvl) ,
    (forall (s10 : Tm) (wf0 : (wfTm k39 s10)) ,
      (forall {d25 : (Trace ty)} {k40 : Hvl} ,
        (substhvl_ty k38 d25 k39 k40) -> (wfTm k40 (tsubstTm d25 S26 s10))))) := (ind_wfTm (fun (k39 : Hvl) (s10 : Tm) (wf0 : (wfTm k39 s10)) =>
    (forall {d25 : (Trace ty)} {k40 : Hvl} ,
      (substhvl_ty k38 d25 k39 k40) -> (wfTm k40 (tsubstTm d25 S26 s10)))) (fun (k39 : Hvl) {x52 : (Index tm)} (wfi : (wfindex k39 x52)) {d25 : (Trace ty)} {k40 : Hvl} (del : (substhvl_ty k38 d25 k39 k40)) =>
    (wfTm_var k40 (substhvl_ty_wfindex_tm del wfi))) (fun (k39 : Hvl) (T : Ty) (wf0 : (wfTy k39 T)) (t : Tm) (wf1 : (wfTm (HS tm k39) t)) IHt56 {d25 : (Trace ty)} {k40 : Hvl} (del : (substhvl_ty k38 d25 k39 k40)) =>
    (wfTm_abs k40 (substhvl_ty_wfTy wf k39 T wf0 (weaken_substhvl_ty H0 del)) (IHt56 (weakenTrace d25 (HS tm H0)) (HS tm k40) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k39 : Hvl) (t1 : Tm) (wf0 : (wfTm k39 t1)) IHt56 (t2 : Tm) (wf1 : (wfTm k39 t2)) IHt57 {d25 : (Trace ty)} {k40 : Hvl} (del : (substhvl_ty k38 d25 k39 k40)) =>
    (wfTm_app k40 (IHt56 (weakenTrace d25 H0) k40 (weaken_substhvl_ty H0 del)) (IHt57 (weakenTrace d25 H0) k40 (weaken_substhvl_ty H0 del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G : Env) (T : Ty)
    | etvar (G : Env) (K : Kind).
  Fixpoint appendEnv (G : Env) (G0 : Env) : Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
      | (etvar G1 K) => (etvar (appendEnv G G1) K)
    end.
  Fixpoint domainEnv (G : Env) : Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS tm (domainEnv G0))
      | (etvar G0 K) => (HS ty (domainEnv G0))
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
      | (etvar G0 K) => (etvar (shiftEnv c12 G0) K)
    end.
  Fixpoint tshiftEnv (c12 : (Cutoff ty)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c12 G0) (tshiftTy (weakenCutoffty c12 (domainEnv G0)) T))
      | (etvar G0 K) => (etvar (tshiftEnv c12 G0) K)
    end.
  Fixpoint substEnv (d25 : (Trace tm)) (s10 : Tm) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d25 s10 G0) T)
      | (etvar G0 K) => (etvar (substEnv d25 s10 G0) K)
    end.
  Fixpoint tsubstEnv (d25 : (Trace ty)) (S26 : Ty) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d25 S26 G0) (tsubstTy (weakenTrace d25 (domainEnv G0)) S26 T))
      | (etvar G0 K) => (etvar (tsubstEnv d25 S26 G0) K)
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
    (forall (d25 : (Trace tm)) (s10 : Tm) (G : Env) ,
      ((domainEnv (substEnv d25 s10 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d25 : (Trace ty)) (S26 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d25 S26 G)) =
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
      (forall (d25 : (Trace tm)) (s10 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d25 s10 (appendEnv G G0)) =
        (appendEnv (substEnv d25 s10 G) (substEnv (weakenTrace d25 (domainEnv G)) s10 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d25 : (Trace ty)) (S26 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d25 S26 (appendEnv G G0)) =
        (appendEnv (tsubstEnv d25 S26 G) (tsubstEnv (weakenTrace d25 (domainEnv G)) S26 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          {T53 : Ty} :
          (wfTy (domainEnv G) T53) -> (lookup_evar (evar G T53) I0 T53)
      | lookup_evar_there_evar
          {G : Env} {x52 : (Index tm)}
          {T53 : Ty} {T54 : Ty} :
          (lookup_evar G x52 T53) -> (lookup_evar (evar G T54) (IS x52) T53)
      | lookup_evar_there_etvar
          {G : Env} {x52 : (Index tm)}
          {T53 : Ty} {K6 : Kind} :
          (lookup_evar G x52 T53) -> (lookup_evar (etvar G K6) x52 (tshiftTy C0 T53)).
    Inductive lookup_etvar : Env -> (Index ty) -> Kind -> Prop :=
      | lookup_etvar_here {G : Env}
          {K6 : Kind} :
          (wfKind (domainEnv G) K6) -> (lookup_etvar (etvar G K6) I0 K6)
      | lookup_etvar_there_evar
          {G : Env} {X24 : (Index ty)}
          {K6 : Kind} {T53 : Ty} :
          (lookup_etvar G X24 K6) -> (lookup_etvar (evar G T53) X24 K6)
      | lookup_etvar_there_etvar
          {G : Env} {X24 : (Index ty)}
          {K6 : Kind} {K7 : Kind} :
          (lookup_etvar G X24 K6) -> (lookup_etvar (etvar G K7) (IS X24) K6).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (S26 : Ty) (S27 : Ty) ,
        (lookup_evar (evar G S26) I0 S27) -> (S26 =
        S27)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (K6 : Kind) (K7 : Kind) ,
        (lookup_etvar (etvar G K6) I0 K7) -> (K6 =
        K7)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x52 : (Index tm)} ,
        (forall {S26 : Ty} ,
          (lookup_evar G x52 S26) -> (forall {S27 : Ty} ,
            (lookup_evar G x52 S27) -> (S26 =
            S27)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X24 : (Index ty)} ,
        (forall {K6 : Kind} ,
          (lookup_etvar G X24 K6) -> (forall {K7 : Kind} ,
            (lookup_etvar G X24 K7) -> (K6 =
            K7)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x52 : (Index tm)} {S26 : Ty} ,
        (lookup_evar G x52 S26) -> (wfTy (domainEnv G) S26)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X24 : (Index ty)} {K6 : Kind} ,
        (lookup_etvar G X24 K6) -> (wfKind (domainEnv G) K6)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x52 : (Index tm)} {T53 : Ty} ,
        (lookup_evar G x52 T53) -> (lookup_evar (appendEnv G G0) (weakenIndextm x52 (domainEnv G0)) (weakenTy T53 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X24 : (Index ty)} {K6 : Kind} ,
        (lookup_etvar G X24 K6) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X24 (domainEnv G0)) (weakenKind K6 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x52 : (Index tm)} {S26 : Ty} ,
        (lookup_evar G x52 S26) -> (wfindex (domainEnv G) x52)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X24 : (Index ty)} {K7 : Kind} ,
        (lookup_etvar G X24 K7) -> (wfindex (domainEnv G) X24)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T53 : Ty} :
        (shift_evar C0 G (evar G T53))
    | shiftevar_there_evar
        {c12 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c12 G G0) -> (shift_evar (CS c12) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c12 : (Cutoff tm)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_evar c12 G G0) -> (shift_evar c12 (etvar G K) (etvar G0 K)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c12 : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c12 G0 G1) -> (shift_evar (weakenCutofftm c12 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {K6 : Kind} :
        (shift_etvar C0 G (etvar G K6))
    | shiftetvar_there_evar
        {c12 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c12 G G0) -> (shift_etvar c12 (evar G T) (evar G0 (tshiftTy c12 T)))
    | shiftetvar_there_etvar
        {c12 : (Cutoff ty)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_etvar c12 G G0) -> (shift_etvar (CS c12) (etvar G K) (etvar G0 K)).
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
  Inductive subst_evar (G : Env) (T53 : Ty) (s10 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T53 s10 X0 (evar G T53) G)
    | subst_evar_there_evar
        {d25 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T53 s10 d25 G0 G1) -> (subst_evar G T53 s10 (XS tm d25) (evar G0 T) (evar G1 T))
    | subst_evar_there_etvar
        {d25 : (Trace tm)} {G0 : Env}
        {G1 : Env} {K : Kind} :
        (subst_evar G T53 s10 d25 G0 G1) -> (subst_evar G T53 s10 (XS ty d25) (etvar G0 K) (etvar G1 K)).
  Lemma weaken_subst_evar {G : Env} {T53 : Ty} {s10 : Tm} :
    (forall (G0 : Env) {d25 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T53 s10 d25 G1 G2) -> (subst_evar G T53 s10 (weakenTrace d25 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (K6 : Kind) (S26 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G K6 S26 X0 (etvar G K6) G)
    | subst_etvar_there_evar
        {d25 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G K6 S26 d25 G0 G1) -> (subst_etvar G K6 S26 (XS tm d25) (evar G0 T) (evar G1 (tsubstTy d25 S26 T)))
    | subst_etvar_there_etvar
        {d25 : (Trace ty)} {G0 : Env}
        {G1 : Env} {K : Kind} :
        (subst_etvar G K6 S26 d25 G0 G1) -> (subst_etvar G K6 S26 (XS ty d25) (etvar G0 K) (etvar G1 K)).
  Lemma weaken_subst_etvar {G : Env} {K6 : Kind} {S26 : Ty} :
    (forall (G0 : Env) {d25 : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G K6 S26 d25 G1 G2) -> (subst_etvar G K6 S26 (weakenTrace d25 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d25 S26 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s10 : Tm} {T53 : Ty} :
    (forall {d25 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T53 s10 d25 G0 G1) -> (substhvl_tm (domainEnv G) d25 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S26 : Ty} {K6 : Kind} :
    (forall {d25 : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G K6 S26 d25 G0 G1) -> (substhvl_ty (domainEnv G) d25 (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T53 : Ty} (wf : (wfTy (domainEnv G) T53)) ,
    (lookup_evar (appendEnv (evar G T53) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T53 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {K6 : Kind} (wf : (wfKind (domainEnv G) K6)) ,
    (lookup_etvar (appendEnv (etvar G K6) G0) (weakenIndexty I0 (domainEnv G0)) (weakenKind K6 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfKind wfTm wfTy : infra.
 Hint Constructors wfKind wfTm wfTy : wf.
 Hint Extern 10 ((wfKind _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfKind _ _)) => match goal with
  | H : (wfKind _ (star)) |- _ => inversion H; subst; clear H
  | H : (wfKind _ (karr _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H : (wfTy _ (tvar _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tabs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tapp _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tarr _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H : (wfTm _ (var _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (abs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (app _ _)) |- _ => inversion H; subst; clear H
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
  (forall {c12 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c12 G G0)) {x52 : (Index tm)} {T53 : Ty} ,
    (lookup_evar G x52 T53) -> (lookup_evar G0 (shiftIndex c12 x52) T53)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c12 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c12 G G0)) {X24 : (Index ty)} {K6 : Kind} ,
    (lookup_etvar G X24 K6) -> (lookup_etvar G0 X24 K6)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c12 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c12 G G0)) {x52 : (Index tm)} {T53 : Ty} ,
    (lookup_evar G x52 T53) -> (lookup_evar G0 x52 (tshiftTy c12 T53))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c12 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c12 G G0)) {X24 : (Index ty)} {K6 : Kind} ,
    (lookup_etvar G X24 K6) -> (lookup_etvar G0 (tshiftIndex c12 X24) K6)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} {T54 : Ty} {s10 : Tm} :
  (forall {d25 : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T54 s10 d25 G0 G1)) {X24 : (Index ty)} {K7 : Kind} ,
    (lookup_etvar G0 X24 K7) -> (lookup_etvar G1 X24 K7)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} {K7 : Kind} {S26 : Ty} (wf : (wfTy (domainEnv G) S26)) :
  (forall {d25 : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G K7 S26 d25 G0 G1)) {x52 : (Index tm)} {T54 : Ty} ,
    (lookup_evar G0 x52 T54) -> (lookup_evar G1 x52 (tsubstTy d25 S26 T54))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Kind (K : Kind) {struct K} : nat :=
  match K with
    | (star) => 1
    | (karr K1 K2) => (plus 1 (plus (size_Kind K1) (size_Kind K2)))
  end.
Fixpoint size_Ty (S0 : Ty) {struct S0} : nat :=
  match S0 with
    | (tvar X) => 1
    | (tabs K T) => (plus 1 (plus (size_Kind K) (size_Ty T)))
    | (tapp T1 T2) => (plus 1 (plus (size_Ty T1) (size_Ty T2)))
    | (tarr T0 T3) => (plus 1 (plus (size_Ty T0) (size_Ty T3)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} : nat :=
  match s with
    | (var x) => 1
    | (abs T t) => (plus 1 (plus (size_Ty T) (size_Tm t)))
    | (app t1 t2) => (plus 1 (plus (size_Tm t1) (size_Tm t2)))
  end.
Lemma tshift_size_Ty  :
  (forall (S26 : Ty) (c9 : (Cutoff ty)) ,
    ((size_Ty (tshiftTy c9 S26)) =
    (size_Ty S26))).
Proof.
  apply_mutual_ind ind_Ty.
  - intros X21 c9.
  reflexivity.
  - intros K5 T46 IHT46.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHT46 (CS c10))).
  - intros T47 IHT47 T48 IHT48.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT47 c10)).
  + exact ((IHT48 c10)).
  - intros T49 IHT49 T50 IHT50.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT49 c10)).
  + exact ((IHT50 c10)).
Qed.

Lemma shift_size_Tm  :
  (forall (s10 : Tm) (c10 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c10 s10)) =
    (size_Tm s10))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros x48 c10.
  reflexivity.
  - intros T51 t50 IHt50.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt50 (CS c11))).
  - intros t51 IHt51 t52 IHt52.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt51 c11)).
  + exact ((IHt52 c11)).
Qed.

Lemma tshift_size_Tm  :
  (forall (s10 : Tm) (c11 : (Cutoff ty)) ,
    ((size_Tm (tshiftTm c11 s10)) =
    (size_Tm s10))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros X23 c11.
  reflexivity.
  - intros T52 t53 IHt53.
  pose proof ((tshift_size_Ty T52)) as IHT52.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT52 c12)).
  + exact ((IHt53 c12)).
  - intros t54 IHt54 t55 IHt55.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt54 c12)).
  + exact ((IHt55 c12)).
Qed.

 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Kind  :
  (forall (k38 : Hvl) (K6 : Kind) ,
    ((size_Kind (weakenKind K6 k38)) =
    (size_Kind K6))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k38 : Hvl) (s10 : Tm) ,
    ((size_Tm (weakenTm s10 k38)) =
    (size_Tm s10))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k38 : Hvl) (S26 : Ty) ,
    ((size_Ty (weakenTy S26 k38)) =
    (size_Ty S26))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : weaken_size.