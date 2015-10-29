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
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (K : Kind) (T : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tyabs (K : Kind) (t : Tm)
    | tyapp (t : Tm) (T : Ty).
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
      | (tall K0 T4) => (tall K0 (tshiftTy (weakenCutoffty c (appendHvl (HS ty H0) H0)) T4))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var (shiftIndex c x))
      | (abs T t) => (abs T (shiftTm (weakenCutofftm c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (shiftTm (weakenCutofftm c H0) t1) (shiftTm (weakenCutofftm c H0) t2))
      | (tyabs K t0) => (tyabs K (shiftTm (weakenCutofftm c (appendHvl (HS ty H0) H0)) t0))
      | (tyapp t3 T0) => (tyapp (shiftTm (weakenCutofftm c H0) t3) T0)
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tshiftTy (weakenCutoffty c H0) T) (tshiftTm (weakenCutoffty c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (tshiftTm (weakenCutoffty c H0) t1) (tshiftTm (weakenCutoffty c H0) t2))
      | (tyabs K t0) => (tyabs K (tshiftTm (weakenCutoffty c (appendHvl (HS ty H0) H0)) t0))
      | (tyapp t3 T0) => (tyapp (tshiftTm (weakenCutoffty c H0) t3) (tshiftTy (weakenCutoffty c H0) T0))
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
      | (tall K0 T4) => (tall K0 (tsubstTy (XS ty d) S0 T4))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} : Tm :=
    match s0 with
      | (var x) => (substIndex d s x)
      | (abs T t) => (abs T (substTm (XS tm d) s t))
      | (app t1 t2) => (app (substTm d s t1) (substTm d s t2))
      | (tyabs K t0) => (tyabs K (substTm (XS ty d) s t0))
      | (tyapp t3 T0) => (tyapp (substTm d s t3) T0)
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tsubstTy d S0 T) (tsubstTm (XS tm d) S0 t))
      | (app t1 t2) => (app (tsubstTm d S0 t1) (tsubstTm d S0 t2))
      | (tyabs K t0) => (tyabs K (tsubstTm (XS ty d) S0 t0))
      | (tyapp t3 T0) => (tyapp (tsubstTm d S0 t3) (tsubstTy d S0 T0))
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
    (forall (k4 : Hvl) (X9 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k4) S0 (tshiftIndex (weakenCutoffty C0 k4) X9)) =
      (tvar X9))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Definition tsubst0_tshift0_Ty_reflection_ind := (ind_Ty (fun (S2 : Ty) =>
    (forall (k7 : Hvl) (S3 : Ty) ,
      ((tsubstTy (weakenTrace X0 k7) S3 (tshiftTy (weakenCutoffty C0 k7) S2)) =
      S2))) (fun (X16 : (Index ty)) =>
    (fun (k7 : Hvl) (S2 : Ty) =>
      (tsubstIndex0_tshiftIndex0_reflection_ind S2 k7 X16))) (fun (K : Kind) (T : Ty) IHT5 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHT5 (HS ty k7) S2)))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tapp (IHT5 k7 S2) (IHT6 k7 S2))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tarr (IHT5 k7 S2) (IHT6 k7 S2))) (fun (K : Kind) (T : Ty) IHT5 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHT5 (HS ty k7) S2))))).
  Definition subst0_shift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (s1 : Tm) ,
      ((substTm (weakenTrace X0 k7) s1 (shiftTm (weakenCutofftm C0 k7) s0)) =
      s0))) (fun (x14 : (Index tm)) =>
    (fun (k7 : Hvl) (s0 : Tm) =>
      (substIndex0_shiftIndex0_reflection_ind s0 k7 x14))) (fun (T : Ty) (t : Tm) IHt29 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt29 (HS tm k7) s0)))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 app (IHt29 k7 s0) (IHt30 k7 s0))) (fun (K : Kind) (t : Tm) IHt29 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt29 (HS ty k7) s0)))) (fun (t : Tm) IHt29 (T : Ty) (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tyapp (IHt29 k7 s0) eq_refl))).
  Definition tsubst0_tshift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (S2 : Ty) ,
      ((tsubstTm (weakenTrace X0 k7) S2 (tshiftTm (weakenCutoffty C0 k7) s0)) =
      s0))) (fun (x14 : (Index tm)) =>
    (fun (k7 : Hvl) (S2 : Ty) =>
      eq_refl)) (fun (T : Ty) (t : Tm) IHt29 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 abs (let IHT5 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT5 k7 S2)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt29 (HS tm k7) S2)))) (fun (t1 : Tm) IHt29 (t2 : Tm) IHt30 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 app (IHt29 k7 S2) (IHt30 k7 S2))) (fun (K : Kind) (t : Tm) IHt29 (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt29 (HS ty k7) S2)))) (fun (t : Tm) IHt29 (T : Ty) (k7 : Hvl) (S2 : Ty) =>
    (f_equal2 tyapp (IHt29 k7 S2) (let IHT5 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT5 k7 S2))))).
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
        (tshiftTy (weakenCutoffty C0 k4) (tshiftTy (weakenCutoffty c4 k4) S0))))) (fun (X9 : (Index ty)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k4 c4 X9)))) (fun (K : Kind) (T : Ty) IHT5 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tabs eq_refl (IHT5 (HS ty k4) c4))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tapp (IHT5 k4 c4) (IHT6 k4 c4))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tarr (IHT5 k4 c4) (IHT6 k4 c4))) (fun (K : Kind) (T : Ty) IHT5 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tall eq_refl (IHT5 (HS ty k4) c4)))).
    Definition shift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm (CS c4) k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff tm)) =>
        (f_equal var (shiftIndex_shiftIndex0_comm_ind k4 c4 x9)))) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (K : Kind) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tyabs eq_refl (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tyapp (IHt19 k4 c4) eq_refl))).
    Definition shift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm c4 k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (shiftTm (weakenCutofftm c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff tm)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (K : Kind) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tyabs eq_refl (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff tm)) =>
      (f_equal2 tyapp (IHt19 k4 c4) eq_refl))).
    Definition tshift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty c4 k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (tshiftTm (weakenCutoffty c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 abs eq_refl (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (K : Kind) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tyabs eq_refl (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tyapp (IHt19 k4 c4) eq_refl))).
    Definition tshift_tshift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k4 : Hvl) (c4 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty (CS c4) k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c4 k4) s))))) (fun (x9 : (Index tm)) =>
      (fun (k4 : Hvl) (c4 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 abs (let IHT5 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT5 k4 c4)) (IHt19 (HS tm k4) c4))) (fun (t1 : Tm) IHt19 (t2 : Tm) IHt20 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 app (IHt19 k4 c4) (IHt20 k4 c4))) (fun (K : Kind) (t : Tm) IHt19 (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tyabs eq_refl (IHt19 (HS ty k4) c4))) (fun (t : Tm) IHt19 (T : Ty) (k4 : Hvl) (c4 : (Cutoff ty)) =>
      (f_equal2 tyapp (IHt19 k4 c4) (let IHT5 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT5 k4 c4))))).
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
    (forall (k50 : Hvl) (c9 : (Cutoff ty)) (S34 : Ty) ,
      ((weakenTy (tshiftTy c9 S34) k50) =
      (tshiftTy (weakenCutoffty c9 k50) (weakenTy S34 k50)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k50 : Hvl) (c9 : (Cutoff tm)) (s14 : Tm) ,
      ((weakenTm (shiftTm c9 s14) k50) =
      (shiftTm (weakenCutofftm c9 k50) (weakenTm s14 k50)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k50 : Hvl) (c9 : (Cutoff ty)) (s14 : Tm) ,
      ((weakenTm (tshiftTm c9 s14) k50) =
      (tshiftTm (weakenCutoffty c9 k50) (weakenTm s14 k50)))).
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
      (forall (k7 : Hvl) (X16 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c4 k7) (tsubstIndex (weakenTrace X0 k7) S2 X16)) =
        (tsubstIndex (weakenTrace X0 k7) (tshiftTy c4 S2) (tshiftIndex (weakenCutoffty (CS c4) k7) X16)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Definition tshift_tsubst0_Ty_comm_ind := (ind_Ty (fun (S5 : Ty) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (S6 : Ty) ,
        ((tshiftTy (weakenCutoffty c9 k12) (tsubstTy (weakenTrace X0 k12) S6 S5)) =
        (tsubstTy (weakenTrace X0 k12) (tshiftTy c9 S6) (tshiftTy (weakenCutoffty (CS c9) k12) S5))))) (fun (X24 : (Index ty)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
        (tshiftTy_tsubstIndex0_comm_ind c9 S5 k12 X24))) (fun (K : Kind) (T : Ty) IHT5 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT5 (HS ty k12) c9 S5) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tapp (IHT5 k12 c9 S5) (IHT6 k12 c9 S5))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tarr (IHT5 k12 c9 S5) (IHT6 k12 c9 S5))) (fun (K : Kind) (T : Ty) IHT5 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tall eq_refl (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT5 (HS ty k12) c9 S5) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl)))))).
    Definition shift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff tm)) (s3 : Tm) ,
        ((shiftTm (weakenCutofftm c9 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (shiftTm c9 s3) (shiftTm (weakenCutofftm (CS c9) k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
        (shiftTm_substIndex0_comm_ind c9 s2 k12 x26))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 app (IHt49 k12 c9 s2) (IHt50 k12 c9 s2))) (fun (K : Kind) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 tyapp (IHt49 k12 c9 s2) eq_refl))).
    Definition shift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) ,
        ((shiftTm (weakenCutofftm c9 k12) (tsubstTm (weakenTrace X0 k12) S5 s2)) =
        (tsubstTm (weakenTrace X0 k12) S5 (shiftTm (weakenCutofftm c9 k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 app (IHt49 k12 c9 S5) (IHt50 k12 c9 S5))) (fun (K : Kind) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff tm)) (S5 : Ty) =>
      (f_equal2 tyapp (IHt49 k12 c9 S5) eq_refl))).
    Definition tshift_subst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (s3 : Tm) ,
        ((tshiftTm (weakenCutoffty c9 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (tshiftTm c9 s3) (tshiftTm (weakenCutoffty c9 k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
        (tshiftTm_substIndex0_comm_ind c9 s2 k12 x26))) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 app (IHt49 k12 c9 s2) (IHt50 k12 c9 s2))) (fun (K : Kind) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tyapp (IHt49 k12 c9 s2) eq_refl))).
    Definition tshift_tsubst0_Tm_comm_ind := (ind_Tm (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) ,
        ((tshiftTm (weakenCutoffty c9 k12) (tsubstTm (weakenTrace X0 k12) S5 s2)) =
        (tsubstTm (weakenTrace X0 k12) (tshiftTy c9 S5) (tshiftTm (weakenCutoffty (CS c9) k12) s2))))) (fun (x26 : (Index tm)) =>
      (fun (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 abs (let IHT5 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT5 k12 c9 S5)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS tm k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt49 (t2 : Tm) IHt50 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 app (IHt49 k12 c9 S5) (IHt50 k12 c9 S5))) (fun (K : Kind) (t : Tm) IHt49 (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt49 (HS ty k12) c9 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt49 (T : Ty) (k12 : Hvl) (c9 : (Cutoff ty)) (S5 : Ty) =>
      (f_equal2 tyapp (IHt49 k12 c9 S5) (let IHT5 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT5 k12 c9 S5))))).
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
      (forall (k12 : Hvl) (X24 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d) k12) S5 X24) =
        (tsubstIndex (weakenTrace d k12) S5 X24))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace ty)) (S5 : Ty) :
      (forall (k12 : Hvl) (X24 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d) k12) S5 (tshiftIndex (weakenCutoffty C0 k12) X24)) =
        (tshiftTy (weakenCutoffty C0 k12) (tsubstIndex (weakenTrace d k12) S5 X24)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Definition tsubst_tshift0_Ty_comm_ind := (ind_Ty (fun (S20 : Ty) =>
      (forall (k37 : Hvl) (d24 : (Trace ty)) (S21 : Ty) ,
        ((tsubstTy (weakenTrace (XS ty d24) k37) S21 (tshiftTy (weakenCutoffty C0 k37) S20)) =
        (tshiftTy (weakenCutoffty C0 k37) (tsubstTy (weakenTrace d24 k37) S21 S20))))) (fun (X32 : (Index ty)) =>
      (fun (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
        (tsubstIndex_tshiftTy0_comm_ind d24 S20 k37 X32))) (fun (K : Kind) (T : Ty) IHT5 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d24) k37 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT5 (HS ty k37) d24 S20) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d24 k37 (HS ty H0))) eq_refl eq_refl)))))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 tapp (IHT5 k37 d24 S20) (IHT6 k37 d24 S20))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 tarr (IHT5 k37 d24 S20) (IHT6 k37 d24 S20))) (fun (K : Kind) (T : Ty) IHT5 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d24) k37 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT5 (HS ty k37) d24 S20) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d24 k37 (HS ty H0))) eq_refl eq_refl))))))).
    Definition subst_shift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k37 : Hvl) (d24 : (Trace tm)) (s13 : Tm) ,
        ((substTm (weakenTrace (XS tm d24) k37) s13 (shiftTm (weakenCutofftm C0 k37) s12)) =
        (shiftTm (weakenCutofftm C0 k37) (substTm (weakenTrace d24 k37) s13 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
        (substIndex_shiftTm0_comm_ind d24 s12 k37 x38))) (fun (T : Ty) (t : Tm) IHt69 (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d24) k37 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k37) d24 s12) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d24 k37 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 app (IHt69 k37 d24 s12) (IHt70 k37 d24 s12))) (fun (K : Kind) (t : Tm) IHt69 (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d24) k37 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k37) d24 s12) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d24 k37 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tyapp (IHt69 k37 d24 s12) eq_refl))).
    Definition subst_tshift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k37 : Hvl) (d24 : (Trace tm)) (s13 : Tm) ,
        ((substTm (weakenTrace (XS ty d24) k37) s13 (tshiftTm (weakenCutoffty C0 k37) s12)) =
        (tshiftTm (weakenCutoffty C0 k37) (substTm (weakenTrace d24 k37) s13 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
        (substIndex_tshiftTm0_comm_ind d24 s12 k37 x38))) (fun (T : Ty) (t : Tm) IHt69 (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d24) k37 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k37) d24 s12) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d24 k37 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 app (IHt69 k37 d24 s12) (IHt70 k37 d24 s12))) (fun (K : Kind) (t : Tm) IHt69 (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d24) k37 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k37) d24 s12) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d24 k37 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k37 : Hvl) (d24 : (Trace tm)) (s12 : Tm) =>
      (f_equal2 tyapp (IHt69 k37 d24 s12) eq_refl))).
    Definition tsubst_shift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) ,
        ((tsubstTm (weakenTrace d24 k37) S20 (shiftTm (weakenCutofftm C0 k37) s12)) =
        (shiftTm (weakenCutofftm C0 k37) (tsubstTm (weakenTrace d24 k37) S20 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt69 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d24 k37 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k37) d24 S20) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d24 k37 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 app (IHt69 k37 d24 S20) (IHt70 k37 d24 S20))) (fun (K : Kind) (t : Tm) IHt69 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d24 k37 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k37) d24 S20) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d24 k37 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 tyapp (IHt69 k37 d24 S20) eq_refl))).
    Definition tsubst_tshift0_Tm_comm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) ,
        ((tsubstTm (weakenTrace (XS ty d24) k37) S20 (tshiftTm (weakenCutoffty C0 k37) s12)) =
        (tshiftTm (weakenCutoffty C0 k37) (tsubstTm (weakenTrace d24 k37) S20 s12))))) (fun (x38 : (Index tm)) =>
      (fun (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt69 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 abs (let IHT5 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT5 k37 d24 S20)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d24) k37 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS tm k37) d24 S20) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d24 k37 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt69 (t2 : Tm) IHt70 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 app (IHt69 k37 d24 S20) (IHt70 k37 d24 S20))) (fun (K : Kind) (t : Tm) IHt69 (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d24) k37 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt69 (HS ty k37) d24 S20) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d24 k37 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt69 (T : Ty) (k37 : Hvl) (d24 : (Trace ty)) (S20 : Ty) =>
      (f_equal2 tyapp (IHt69 k37 d24 S20) (let IHT5 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT5 k37 d24 S20))))).
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S31 : Ty) : (forall (d34 : (Trace ty)) (S30 : Ty) ,
      ((tsubstTy (XS ty d34) S30 (tshiftTy C0 S31)) =
      (tshiftTy C0 (tsubstTy d34 S30 S31)))) := (tsubst_tshift0_Ty_comm_ind S31 H0).
    Definition substTm_shiftTm0_comm (s13 : Tm) : (forall (d34 : (Trace tm)) (s12 : Tm) ,
      ((substTm (XS tm d34) s12 (shiftTm C0 s13)) =
      (shiftTm C0 (substTm d34 s12 s13)))) := (subst_shift0_Tm_comm_ind s13 H0).
    Definition substTm_tshiftTm0_comm (s13 : Tm) : (forall (d34 : (Trace tm)) (s12 : Tm) ,
      ((substTm (XS ty d34) s12 (tshiftTm C0 s13)) =
      (tshiftTm C0 (substTm d34 s12 s13)))) := (subst_tshift0_Tm_comm_ind s13 H0).
    Definition tsubstTm_shiftTm0_comm (s12 : Tm) : (forall (d34 : (Trace ty)) (S30 : Ty) ,
      ((tsubstTm d34 S30 (shiftTm C0 s12)) =
      (shiftTm C0 (tsubstTm d34 S30 s12)))) := (tsubst_shift0_Tm_comm_ind s12 H0).
    Definition tsubstTm_tshiftTm0_comm (s12 : Tm) : (forall (d34 : (Trace ty)) (S30 : Ty) ,
      ((tsubstTm (XS ty d34) S30 (tshiftTm C0 s12)) =
      (tshiftTm C0 (tsubstTm d34 S30 s12)))) := (tsubst_tshift0_Tm_comm_ind s12 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Definition tsubst_tm_Ty_ind := (ind_Ty (fun (S30 : Ty) =>
      (forall (k47 : Hvl) (d34 : (Trace ty)) (S31 : Ty) ,
        ((tsubstTy (weakenTrace (XS tm d34) k47) S31 S30) =
        (tsubstTy (weakenTrace d34 k47) S31 S30)))) (fun (X37 : (Index ty)) =>
      (fun (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
        (tsubstIndex_shiftTy0_comm_ind d34 S30 k47 X37))) (fun (K : Kind) (T : Ty) IHT5 (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d34) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT5 (HS ty k47) d34 S30) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d34 k47 (HS ty H0))) eq_refl eq_refl))))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
      (f_equal2 tapp (IHT5 k47 d34 S30) (IHT6 k47 d34 S30))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
      (f_equal2 tarr (IHT5 k47 d34 S30) (IHT6 k47 d34 S30))) (fun (K : Kind) (T : Ty) IHT5 (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
      (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d34) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT5 (HS ty k47) d34 S30) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d34 k47 (HS ty H0))) eq_refl eq_refl)))))).
    Definition tsubst_tm_Tm_ind := (ind_Tm (fun (s12 : Tm) =>
      (forall (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) ,
        ((tsubstTm (weakenTrace (XS tm d34) k47) S30 s12) =
        (tsubstTm (weakenTrace d34 k47) S30 s12)))) (fun (x41 : (Index tm)) =>
      (fun (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt74 (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
      (f_equal2 abs (let IHT5 := (tsubst_tm_Ty_ind T) in
      (IHT5 k47 d34 S30)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d34) k47 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt74 (HS tm k47) d34 S30) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d34 k47 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt74 (t2 : Tm) IHt75 (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
      (f_equal2 app (IHt74 k47 d34 S30) (IHt75 k47 d34 S30))) (fun (K : Kind) (t : Tm) IHt74 (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d34) k47 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt74 (HS ty k47) d34 S30) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d34 k47 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt74 (T : Ty) (k47 : Hvl) (d34 : (Trace ty)) (S30 : Ty) =>
      (f_equal2 tyapp (IHt74 k47 d34 S30) (let IHT5 := (tsubst_tm_Ty_ind T) in
      (IHT5 k47 d34 S30))))).
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S31 : Ty) : (forall (d34 : (Trace ty)) (S30 : Ty) ,
      ((tsubstTy (XS tm d34) S30 S31) =
      (tsubstTy d34 S30 S31))) := (tsubst_tm_Ty_ind S31 H0).
    Definition tsubstTm_tm (s12 : Tm) : (forall (d34 : (Trace ty)) (S30 : Ty) ,
      ((tsubstTm (XS tm d34) S30 s12) =
      (tsubstTm d34 S30 s12))) := (tsubst_tm_Tm_ind s12 H0).
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
    Lemma substTm_substIndex0_commright_ind (d34 : (Trace tm)) (s12 : Tm) (s13 : Tm) :
      (forall (k47 : Hvl) (x41 : (Index tm)) ,
        ((substTm (weakenTrace d34 k47) s12 (substIndex (weakenTrace X0 k47) s13 x41)) =
        (substTm (weakenTrace X0 k47) (substTm d34 s12 s13) (substIndex (weakenTrace (XS tm d34) k47) s12 x41)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d34 : (Trace ty)) (S30 : Ty) (s12 : Tm) :
      (forall (k47 : Hvl) (x41 : (Index tm)) ,
        ((tsubstTm (weakenTrace d34 k47) S30 (substIndex (weakenTrace X0 k47) s12 x41)) =
        (substIndex (weakenTrace X0 k47) (tsubstTm d34 S30 s12) x41))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d34 : (Trace ty)) (S30 : Ty) (S31 : Ty) :
      (forall (k47 : Hvl) (X37 : (Index ty)) ,
        ((tsubstTy (weakenTrace d34 k47) S30 (tsubstIndex (weakenTrace X0 k47) S31 X37)) =
        (tsubstTy (weakenTrace X0 k47) (tsubstTy d34 S30 S31) (tsubstIndex (weakenTrace (XS ty d34) k47) S30 X37)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d34 : (Trace tm)) (s12 : Tm) (S30 : Ty) :
      (forall (k47 : Hvl) (x41 : (Index tm)) ,
        ((substIndex (weakenTrace d34 k47) s12 x41) =
        (tsubstTm (weakenTrace X0 k47) S30 (substIndex (weakenTrace (XS ty d34) k47) s12 x41)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition tsubst_tsubst0_Ty_comm_ind := (ind_Ty (fun (S34 : Ty) =>
      (forall (k50 : Hvl) (d37 : (Trace ty)) (S35 : Ty) (S36 : Ty) ,
        ((tsubstTy (weakenTrace d37 k50) S35 (tsubstTy (weakenTrace X0 k50) S36 S34)) =
        (tsubstTy (weakenTrace X0 k50) (tsubstTy d37 S35 S36) (tsubstTy (weakenTrace (XS ty d37) k50) S35 S34))))) (fun (X43 : (Index ty)) =>
      (fun (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
        (tsubstTy_tsubstIndex0_commright_ind d37 S34 S35 k50 X43))) (fun (K : Kind) (T : Ty) IHT5 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d37 k50 (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k50 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT5 (HS ty k50) d37 S34 S35) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k50 (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d37) k50 (HS ty H0))) eq_refl eq_refl)))))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
      (f_equal2 tapp (IHT5 k50 d37 S34 S35) (IHT6 k50 d37 S34 S35))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
      (f_equal2 tarr (IHT5 k50 d37 S34 S35) (IHT6 k50 d37 S34 S35))) (fun (K : Kind) (T : Ty) IHT5 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
      (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d37 k50 (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k50 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT5 (HS ty k50) d37 S34 S35) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k50 (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d37) k50 (HS ty H0))) eq_refl eq_refl))))))).
    Definition subst_subst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k50 : Hvl) (d37 : (Trace tm)) (s15 : Tm) (s16 : Tm) ,
        ((substTm (weakenTrace d37 k50) s15 (substTm (weakenTrace X0 k50) s16 s14)) =
        (substTm (weakenTrace X0 k50) (substTm d37 s15 s16) (substTm (weakenTrace (XS tm d37) k50) s15 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
        (substTm_substIndex0_commright_ind d37 s14 s15 k50 x47))) (fun (T : Ty) (t : Tm) IHt84 (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d37 k50 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k50 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k50) d37 s14 s15) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k50 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d37) k50 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 app (IHt84 k50 d37 s14 s15) (IHt85 k50 d37 s14 s15))) (fun (K : Kind) (t : Tm) IHt84 (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d37 k50 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k50 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k50) d37 s14 s15) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k50 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d37) k50 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (s15 : Tm) =>
      (f_equal2 tyapp (IHt84 k50 d37 s14 s15) eq_refl))).
    Definition subst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k50 : Hvl) (d37 : (Trace tm)) (s15 : Tm) (S34 : Ty) ,
        ((substTm (weakenTrace d37 k50) s15 (tsubstTm (weakenTrace X0 k50) S34 s14)) =
        (tsubstTm (weakenTrace X0 k50) S34 (substTm (weakenTrace (XS ty d37) k50) s15 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (S34 : Ty) =>
        (substTy_tsubstIndex0_commleft_ind d37 s14 S34 k50 x47))) (fun (T : Ty) (t : Tm) IHt84 (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (S34 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d37 k50 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k50 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k50) d37 s14 S34) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k50 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d37) k50 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (S34 : Ty) =>
      (f_equal2 app (IHt84 k50 d37 s14 S34) (IHt85 k50 d37 s14 S34))) (fun (K : Kind) (t : Tm) IHt84 (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (S34 : Ty) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d37 k50 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k50 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k50) d37 s14 S34) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k50 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d37) k50 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (S34 : Ty) =>
      (f_equal2 tyapp (IHt84 k50 d37 s14 S34) eq_refl))).
    Definition tsubst_subst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (s15 : Tm) ,
        ((tsubstTm (weakenTrace d37 k50) S34 (substTm (weakenTrace X0 k50) s15 s14)) =
        (substTm (weakenTrace X0 k50) (tsubstTm d37 S34 s15) (tsubstTm (weakenTrace d37 k50) S34 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (s14 : Tm) =>
        (tsubstTm_substIndex0_commright_ind d37 S34 s14 k50 x47))) (fun (T : Ty) (t : Tm) IHt84 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (s14 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d37 k50 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k50 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k50) d37 S34 s14) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k50 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d37 k50 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (s14 : Tm) =>
      (f_equal2 app (IHt84 k50 d37 S34 s14) (IHt85 k50 d37 S34 s14))) (fun (K : Kind) (t : Tm) IHt84 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (s14 : Tm) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d37 k50 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k50 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k50) d37 S34 s14) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k50 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d37 k50 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (s14 : Tm) =>
      (f_equal2 tyapp (IHt84 k50 d37 S34 s14) eq_refl))).
    Definition tsubst_tsubst0_Tm_comm_ind := (ind_Tm (fun (s14 : Tm) =>
      (forall (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) ,
        ((tsubstTm (weakenTrace d37 k50) S34 (tsubstTm (weakenTrace X0 k50) S35 s14)) =
        (tsubstTm (weakenTrace X0 k50) (tsubstTy d37 S34 S35) (tsubstTm (weakenTrace (XS ty d37) k50) S34 s14))))) (fun (x47 : (Index tm)) =>
      (fun (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt84 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
      (f_equal2 abs (let IHT5 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT5 k50 d37 S34 S35)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d37 k50 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k50 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS tm k50) d37 S34 S35) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k50 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d37) k50 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt84 (t2 : Tm) IHt85 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
      (f_equal2 app (IHt84 k50 d37 S34 S35) (IHt85 k50 d37 S34 S35))) (fun (K : Kind) (t : Tm) IHt84 (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
      (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d37 k50 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k50 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt84 (HS ty k50) d37 S34 S35) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k50 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d37) k50 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt84 (T : Ty) (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) =>
      (f_equal2 tyapp (IHt84 k50 d37 S34 S35) (let IHT5 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT5 k50 d37 S34 S35))))).
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S36 : Ty) : (forall (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) ,
      ((tsubstTy d37 S34 (tsubstTy X0 S35 S36)) =
      (tsubstTy X0 (tsubstTy d37 S34 S35) (tsubstTy (XS ty d37) S34 S36)))) := (tsubst_tsubst0_Ty_comm_ind S36 H0).
    Definition substTm_substTm0_comm (s16 : Tm) : (forall (d37 : (Trace tm)) (s14 : Tm) (s15 : Tm) ,
      ((substTm d37 s14 (substTm X0 s15 s16)) =
      (substTm X0 (substTm d37 s14 s15) (substTm (XS tm d37) s14 s16)))) := (subst_subst0_Tm_comm_ind s16 H0).
    Definition substTm_tsubstTm0_comm (s15 : Tm) : (forall (d37 : (Trace tm)) (s14 : Tm) (S34 : Ty) ,
      ((substTm d37 s14 (tsubstTm X0 S34 s15)) =
      (tsubstTm X0 S34 (substTm (XS ty d37) s14 s15)))) := (subst_tsubst0_Tm_comm_ind s15 H0).
    Definition tsubstTm_substTm0_comm (s15 : Tm) : (forall (d37 : (Trace ty)) (S34 : Ty) (s14 : Tm) ,
      ((tsubstTm d37 S34 (substTm X0 s14 s15)) =
      (substTm X0 (tsubstTm d37 S34 s14) (tsubstTm d37 S34 s15)))) := (tsubst_subst0_Tm_comm_ind s15 H0).
    Definition tsubstTm_tsubstTm0_comm (s14 : Tm) : (forall (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) ,
      ((tsubstTm d37 S34 (tsubstTm X0 S35 s14)) =
      (tsubstTm X0 (tsubstTy d37 S34 S35) (tsubstTm (XS ty d37) S34 s14)))) := (tsubst_tsubst0_Tm_comm_ind s14 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (S35 : Ty) ,
        ((weakenTy (tsubstTy d37 S34 S35) k50) =
        (tsubstTy (weakenTrace d37 k50) S34 (weakenTy S35 k50)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k50 : Hvl) (d37 : (Trace tm)) (s14 : Tm) (s15 : Tm) ,
        ((weakenTm (substTm d37 s14 s15) k50) =
        (substTm (weakenTrace d37 k50) s14 (weakenTm s15 k50)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k50 : Hvl) (d37 : (Trace ty)) (S34 : Ty) (s14 : Tm) ,
        ((weakenTm (tsubstTm d37 S34 s14) k50) =
        (tsubstTm (weakenTrace d37 k50) S34 (weakenTm s14 k50)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenKind_append  :
      (forall (K28 : Kind) (k50 : Hvl) (k51 : Hvl) ,
        ((weakenKind (weakenKind K28 k50) k51) =
        (weakenKind K28 (appendHvl k50 k51)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTy_append  :
      (forall (S34 : Ty) (k50 : Hvl) (k51 : Hvl) ,
        ((weakenTy (weakenTy S34 k50) k51) =
        (weakenTy S34 (appendHvl k50 k51)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s14 : Tm) (k50 : Hvl) (k51 : Hvl) ,
        ((weakenTm (weakenTm s14 k50) k51) =
        (weakenTm s14 (appendHvl k50 k51)))).
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
  Fixpoint wfindex {a : Namespace} (k50 : Hvl) (i : (Index a)) {struct k50} : Prop :=
    match k50 with
      | (H0) => False
      | (HS b k50) => match (eq_namespace_dec a b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k50 i)
        end
        | (right n) => (wfindex k50 i)
      end
    end.
  Inductive wfKind (k50 : Hvl) : Kind -> Prop :=
    | wfKind_star :
        (wfKind k50 (star))
    | wfKind_karr {K32 : Kind}
        (wf : (wfKind k50 K32))
        {K33 : Kind}
        (wf0 : (wfKind k50 K33)) :
        (wfKind k50 (karr K32 K33)).
  Inductive wfTy (k50 : Hvl) : Ty -> Prop :=
    | wfTy_tvar {X50 : (Index ty)}
        (wfi : (wfindex k50 X50)) :
        (wfTy k50 (tvar X50))
    | wfTy_tabs {K32 : Kind}
        (wf : (wfKind k50 K32))
        {T79 : Ty}
        (wf0 : (wfTy (HS ty k50) T79)) :
        (wfTy k50 (tabs K32 T79))
    | wfTy_tapp {T80 : Ty}
        (wf : (wfTy k50 T80)) {T81 : Ty}
        (wf0 : (wfTy k50 T81)) :
        (wfTy k50 (tapp T80 T81))
    | wfTy_tarr {T82 : Ty}
        (wf : (wfTy k50 T82)) {T83 : Ty}
        (wf0 : (wfTy k50 T83)) :
        (wfTy k50 (tarr T82 T83))
    | wfTy_tall {K33 : Kind}
        (wf : (wfKind k50 K33))
        {T84 : Ty}
        (wf0 : (wfTy (HS ty k50) T84)) :
        (wfTy k50 (tall K33 T84)).
  Inductive wfTm (k50 : Hvl) : Tm -> Prop :=
    | wfTm_var {x52 : (Index tm)}
        (wfi : (wfindex k50 x52)) :
        (wfTm k50 (var x52))
    | wfTm_abs {T79 : Ty}
        (wf : (wfTy k50 T79)) {t94 : Tm}
        (wf0 : (wfTm (HS tm k50) t94)) :
        (wfTm k50 (abs T79 t94))
    | wfTm_app {t95 : Tm}
        (wf : (wfTm k50 t95)) {t96 : Tm}
        (wf0 : (wfTm k50 t96)) :
        (wfTm k50 (app t95 t96))
    | wfTm_tyabs {K32 : Kind}
        (wf : (wfKind k50 K32))
        {t97 : Tm}
        (wf0 : (wfTm (HS ty k50) t97)) :
        (wfTm k50 (tyabs K32 t97))
    | wfTm_tyapp {t98 : Tm}
        (wf : (wfTm k50 t98)) {T80 : Ty}
        (wf0 : (wfTy k50 T80)) :
        (wfTm k50 (tyapp t98 T80)).
  Scheme ind_wfKind := Induction for wfKind Sort Prop.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c12 : (Cutoff tm)) (k50 : Hvl) (k51 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k50 : Hvl)
        :
        (shifthvl_tm C0 k50 (HS tm k50))
    | shifthvl_tm_there_tm
        (c12 : (Cutoff tm)) (k50 : Hvl)
        (k51 : Hvl) :
        (shifthvl_tm c12 k50 k51) -> (shifthvl_tm (CS c12) (HS tm k50) (HS tm k51))
    | shifthvl_tm_there_ty
        (c12 : (Cutoff tm)) (k50 : Hvl)
        (k51 : Hvl) :
        (shifthvl_tm c12 k50 k51) -> (shifthvl_tm c12 (HS ty k50) (HS ty k51)).
  Inductive shifthvl_ty : (forall (c12 : (Cutoff ty)) (k50 : Hvl) (k51 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k50 : Hvl)
        :
        (shifthvl_ty C0 k50 (HS ty k50))
    | shifthvl_ty_there_tm
        (c12 : (Cutoff ty)) (k50 : Hvl)
        (k51 : Hvl) :
        (shifthvl_ty c12 k50 k51) -> (shifthvl_ty c12 (HS tm k50) (HS tm k51))
    | shifthvl_ty_there_ty
        (c12 : (Cutoff ty)) (k50 : Hvl)
        (k51 : Hvl) :
        (shifthvl_ty c12 k50 k51) -> (shifthvl_ty (CS c12) (HS ty k50) (HS ty k51)).
  Lemma weaken_shifthvl_tm  :
    (forall (k50 : Hvl) {c12 : (Cutoff tm)} {k51 : Hvl} {k52 : Hvl} ,
      (shifthvl_tm c12 k51 k52) -> (shifthvl_tm (weakenCutofftm c12 k50) (appendHvl k51 k50) (appendHvl k52 k50))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k50 : Hvl) {c12 : (Cutoff ty)} {k51 : Hvl} {k52 : Hvl} ,
      (shifthvl_ty c12 k51 k52) -> (shifthvl_ty (weakenCutoffty c12 k50) (appendHvl k51 k50) (appendHvl k52 k50))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c12 : (Cutoff tm)) (k50 : Hvl) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) (x52 : (Index tm)) ,
      (wfindex k50 x52) -> (wfindex k51 (shiftIndex c12 x52))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c12 : (Cutoff tm)) (k50 : Hvl) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) (X50 : (Index ty)) ,
      (wfindex k50 X50) -> (wfindex k51 X50)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c12 : (Cutoff ty)) (k50 : Hvl) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) (x52 : (Index tm)) ,
      (wfindex k50 x52) -> (wfindex k51 x52)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c12 : (Cutoff ty)) (k50 : Hvl) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) (X50 : (Index ty)) ,
      (wfindex k50 X50) -> (wfindex k51 (tshiftIndex c12 X50))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfKind : (forall (k50 : Hvl) ,
    (forall (K32 : Kind) (wf : (wfKind k50 K32)) ,
      (forall (c12 : (Cutoff tm)) (k51 : Hvl) ,
        (shifthvl_tm c12 k50 k51) -> (wfKind k51 K32)))) := (fun (k50 : Hvl) =>
    (ind_wfKind k50 (fun (K32 : Kind) (wf : (wfKind k50 K32)) =>
      (forall (c12 : (Cutoff tm)) (k51 : Hvl) ,
        (shifthvl_tm c12 k50 k51) -> (wfKind k51 K32))) (fun (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
      (wfKind_star k51)) (fun (K1 : Kind) (wf : (wfKind k50 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k50 K2)) IHK2 (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
      (wfKind_karr k51 (IHK1 c12 k51 (weaken_shifthvl_tm H0 ins)) (IHK2 c12 k51 (weaken_shifthvl_tm H0 ins)))))).
  Definition tshift_wfKind : (forall (k50 : Hvl) ,
    (forall (K32 : Kind) (wf : (wfKind k50 K32)) ,
      (forall (c12 : (Cutoff ty)) (k51 : Hvl) ,
        (shifthvl_ty c12 k50 k51) -> (wfKind k51 K32)))) := (fun (k50 : Hvl) =>
    (ind_wfKind k50 (fun (K32 : Kind) (wf : (wfKind k50 K32)) =>
      (forall (c12 : (Cutoff ty)) (k51 : Hvl) ,
        (shifthvl_ty c12 k50 k51) -> (wfKind k51 K32))) (fun (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
      (wfKind_star k51)) (fun (K1 : Kind) (wf : (wfKind k50 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k50 K2)) IHK2 (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
      (wfKind_karr k51 (IHK1 c12 k51 (weaken_shifthvl_ty H0 ins)) (IHK2 c12 k51 (weaken_shifthvl_ty H0 ins)))))).
  Definition shift_wfTy : (forall (k50 : Hvl) ,
    (forall (S34 : Ty) (wf : (wfTy k50 S34)) ,
      (forall (c12 : (Cutoff tm)) (k51 : Hvl) ,
        (shifthvl_tm c12 k50 k51) -> (wfTy k51 S34)))) := (ind_wfTy (fun (k50 : Hvl) (S34 : Ty) (wf : (wfTy k50 S34)) =>
    (forall (c12 : (Cutoff tm)) (k51 : Hvl) ,
      (shifthvl_tm c12 k50 k51) -> (wfTy k51 S34))) (fun (k50 : Hvl) (X50 : (Index ty)) (wfi : (wfindex k50 X50)) (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTy_tvar k51 (shift_wfindex_ty c12 k50 k51 ins X50 wfi))) (fun (k50 : Hvl) (K : Kind) (wf : (wfKind k50 K)) (T : Ty) (wf0 : (wfTy (HS ty k50) T)) IHT5 (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTy_tabs k51 (shift_wfKind k50 K wf c12 k51 (weaken_shifthvl_tm H0 ins)) (IHT5 c12 (HS ty k51) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k50 : Hvl) (T1 : Ty) (wf : (wfTy k50 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k50 T2)) IHT6 (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTy_tapp k51 (IHT5 c12 k51 (weaken_shifthvl_tm H0 ins)) (IHT6 c12 k51 (weaken_shifthvl_tm H0 ins)))) (fun (k50 : Hvl) (T1 : Ty) (wf : (wfTy k50 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k50 T2)) IHT6 (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTy_tarr k51 (IHT5 c12 k51 (weaken_shifthvl_tm H0 ins)) (IHT6 c12 k51 (weaken_shifthvl_tm H0 ins)))) (fun (k50 : Hvl) (K : Kind) (wf : (wfKind k50 K)) (T : Ty) (wf0 : (wfTy (HS ty k50) T)) IHT5 (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTy_tall k51 (shift_wfKind k50 K wf c12 k51 (weaken_shifthvl_tm H0 ins)) (IHT5 c12 (HS ty k51) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k50 : Hvl) ,
    (forall (S34 : Ty) (wf : (wfTy k50 S34)) ,
      (forall (c12 : (Cutoff ty)) (k51 : Hvl) ,
        (shifthvl_ty c12 k50 k51) -> (wfTy k51 (tshiftTy c12 S34))))) := (ind_wfTy (fun (k50 : Hvl) (S34 : Ty) (wf : (wfTy k50 S34)) =>
    (forall (c12 : (Cutoff ty)) (k51 : Hvl) ,
      (shifthvl_ty c12 k50 k51) -> (wfTy k51 (tshiftTy c12 S34)))) (fun (k50 : Hvl) (X50 : (Index ty)) (wfi : (wfindex k50 X50)) (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTy_tvar k51 (tshift_wfindex_ty c12 k50 k51 ins X50 wfi))) (fun (k50 : Hvl) (K : Kind) (wf : (wfKind k50 K)) (T : Ty) (wf0 : (wfTy (HS ty k50) T)) IHT5 (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTy_tabs k51 (tshift_wfKind k50 K wf c12 k51 (weaken_shifthvl_ty H0 ins)) (IHT5 (CS c12) (HS ty k51) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k50 : Hvl) (T1 : Ty) (wf : (wfTy k50 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k50 T2)) IHT6 (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTy_tapp k51 (IHT5 c12 k51 (weaken_shifthvl_ty H0 ins)) (IHT6 c12 k51 (weaken_shifthvl_ty H0 ins)))) (fun (k50 : Hvl) (T1 : Ty) (wf : (wfTy k50 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k50 T2)) IHT6 (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTy_tarr k51 (IHT5 c12 k51 (weaken_shifthvl_ty H0 ins)) (IHT6 c12 k51 (weaken_shifthvl_ty H0 ins)))) (fun (k50 : Hvl) (K : Kind) (wf : (wfKind k50 K)) (T : Ty) (wf0 : (wfTy (HS ty k50) T)) IHT5 (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTy_tall k51 (tshift_wfKind k50 K wf c12 k51 (weaken_shifthvl_ty H0 ins)) (IHT5 (CS c12) (HS ty k51) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfTm : (forall (k50 : Hvl) ,
    (forall (s14 : Tm) (wf : (wfTm k50 s14)) ,
      (forall (c12 : (Cutoff tm)) (k51 : Hvl) ,
        (shifthvl_tm c12 k50 k51) -> (wfTm k51 (shiftTm c12 s14))))) := (ind_wfTm (fun (k50 : Hvl) (s14 : Tm) (wf : (wfTm k50 s14)) =>
    (forall (c12 : (Cutoff tm)) (k51 : Hvl) ,
      (shifthvl_tm c12 k50 k51) -> (wfTm k51 (shiftTm c12 s14)))) (fun (k50 : Hvl) (x52 : (Index tm)) (wfi : (wfindex k50 x52)) (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTm_var k51 (shift_wfindex_tm c12 k50 k51 ins x52 wfi))) (fun (k50 : Hvl) (T : Ty) (wf : (wfTy k50 T)) (t : Tm) (wf0 : (wfTm (HS tm k50) t)) IHt94 (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTm_abs k51 (shift_wfTy k50 T wf c12 k51 (weaken_shifthvl_tm H0 ins)) (IHt94 (CS c12) (HS tm k51) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k50 : Hvl) (t1 : Tm) (wf : (wfTm k50 t1)) IHt94 (t2 : Tm) (wf0 : (wfTm k50 t2)) IHt95 (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTm_app k51 (IHt94 c12 k51 (weaken_shifthvl_tm H0 ins)) (IHt95 c12 k51 (weaken_shifthvl_tm H0 ins)))) (fun (k50 : Hvl) (K : Kind) (wf : (wfKind k50 K)) (t : Tm) (wf0 : (wfTm (HS ty k50) t)) IHt94 (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTm_tyabs k51 (shift_wfKind k50 K wf c12 k51 (weaken_shifthvl_tm H0 ins)) (IHt94 c12 (HS ty k51) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k50 : Hvl) (t : Tm) (wf : (wfTm k50 t)) IHt94 (T : Ty) (wf0 : (wfTy k50 T)) (c12 : (Cutoff tm)) (k51 : Hvl) (ins : (shifthvl_tm c12 k50 k51)) =>
    (wfTm_tyapp k51 (IHt94 c12 k51 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k50 T wf0 c12 k51 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTm : (forall (k50 : Hvl) ,
    (forall (s14 : Tm) (wf : (wfTm k50 s14)) ,
      (forall (c12 : (Cutoff ty)) (k51 : Hvl) ,
        (shifthvl_ty c12 k50 k51) -> (wfTm k51 (tshiftTm c12 s14))))) := (ind_wfTm (fun (k50 : Hvl) (s14 : Tm) (wf : (wfTm k50 s14)) =>
    (forall (c12 : (Cutoff ty)) (k51 : Hvl) ,
      (shifthvl_ty c12 k50 k51) -> (wfTm k51 (tshiftTm c12 s14)))) (fun (k50 : Hvl) (x52 : (Index tm)) (wfi : (wfindex k50 x52)) (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTm_var k51 (tshift_wfindex_tm c12 k50 k51 ins x52 wfi))) (fun (k50 : Hvl) (T : Ty) (wf : (wfTy k50 T)) (t : Tm) (wf0 : (wfTm (HS tm k50) t)) IHt94 (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTm_abs k51 (tshift_wfTy k50 T wf c12 k51 (weaken_shifthvl_ty H0 ins)) (IHt94 c12 (HS tm k51) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k50 : Hvl) (t1 : Tm) (wf : (wfTm k50 t1)) IHt94 (t2 : Tm) (wf0 : (wfTm k50 t2)) IHt95 (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTm_app k51 (IHt94 c12 k51 (weaken_shifthvl_ty H0 ins)) (IHt95 c12 k51 (weaken_shifthvl_ty H0 ins)))) (fun (k50 : Hvl) (K : Kind) (wf : (wfKind k50 K)) (t : Tm) (wf0 : (wfTm (HS ty k50) t)) IHt94 (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTm_tyabs k51 (tshift_wfKind k50 K wf c12 k51 (weaken_shifthvl_ty H0 ins)) (IHt94 (CS c12) (HS ty k51) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k50 : Hvl) (t : Tm) (wf : (wfTm k50 t)) IHt94 (T : Ty) (wf0 : (wfTy k50 T)) (c12 : (Cutoff ty)) (k51 : Hvl) (ins : (shifthvl_ty c12 k50 k51)) =>
    (wfTm_tyapp k51 (IHt94 c12 k51 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k50 T wf0 c12 k51 (weaken_shifthvl_ty H0 ins))))).
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
  Inductive substhvl_tm (k50 : Hvl) : (forall (d37 : (Trace tm)) (k51 : Hvl) (k52 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k50 X0 (HS tm k50) k50)
    | substhvl_tm_there_tm
        {d37 : (Trace tm)} {k51 : Hvl}
        {k52 : Hvl} :
        (substhvl_tm k50 d37 k51 k52) -> (substhvl_tm k50 (XS tm d37) (HS tm k51) (HS tm k52))
    | substhvl_tm_there_ty
        {d37 : (Trace tm)} {k51 : Hvl}
        {k52 : Hvl} :
        (substhvl_tm k50 d37 k51 k52) -> (substhvl_tm k50 (XS ty d37) (HS ty k51) (HS ty k52)).
  Inductive substhvl_ty (k50 : Hvl) : (forall (d37 : (Trace ty)) (k51 : Hvl) (k52 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k50 X0 (HS ty k50) k50)
    | substhvl_ty_there_tm
        {d37 : (Trace ty)} {k51 : Hvl}
        {k52 : Hvl} :
        (substhvl_ty k50 d37 k51 k52) -> (substhvl_ty k50 (XS tm d37) (HS tm k51) (HS tm k52))
    | substhvl_ty_there_ty
        {d37 : (Trace ty)} {k51 : Hvl}
        {k52 : Hvl} :
        (substhvl_ty k50 d37 k51 k52) -> (substhvl_ty k50 (XS ty d37) (HS ty k51) (HS ty k52)).
  Lemma weaken_substhvl_tm  :
    (forall {k51 : Hvl} (k50 : Hvl) {d37 : (Trace tm)} {k52 : Hvl} {k53 : Hvl} ,
      (substhvl_tm k51 d37 k52 k53) -> (substhvl_tm k51 (weakenTrace d37 k50) (appendHvl k52 k50) (appendHvl k53 k50))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k51 : Hvl} (k50 : Hvl) {d37 : (Trace ty)} {k52 : Hvl} {k53 : Hvl} ,
      (substhvl_ty k51 d37 k52 k53) -> (substhvl_ty k51 (weakenTrace d37 k50) (appendHvl k52 k50) (appendHvl k53 k50))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k50 : Hvl} {s14 : Tm} (wft : (wfTm k50 s14)) :
    (forall {d37 : (Trace tm)} {k51 : Hvl} {k52 : Hvl} ,
      (substhvl_tm k50 d37 k51 k52) -> (forall {x52 : (Index tm)} ,
        (wfindex k51 x52) -> (wfTm k52 (substIndex d37 s14 x52)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k50 : Hvl} {S34 : Ty} (wft : (wfTy k50 S34)) :
    (forall {d37 : (Trace ty)} {k51 : Hvl} {k52 : Hvl} ,
      (substhvl_ty k50 d37 k51 k52) -> (forall {X50 : (Index ty)} ,
        (wfindex k51 X50) -> (wfTy k52 (tsubstIndex d37 S34 X50)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k50 : Hvl} :
    (forall {d37 : (Trace tm)} {k51 : Hvl} {k52 : Hvl} ,
      (substhvl_tm k50 d37 k51 k52) -> (forall {X50 : (Index ty)} ,
        (wfindex k51 X50) -> (wfindex k52 X50))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k50 : Hvl} :
    (forall {d37 : (Trace ty)} {k51 : Hvl} {k52 : Hvl} ,
      (substhvl_ty k50 d37 k51 k52) -> (forall {x52 : (Index tm)} ,
        (wfindex k51 x52) -> (wfindex k52 x52))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfKind {k50 : Hvl} : (forall (k51 : Hvl) ,
    (forall (K32 : Kind) (wf0 : (wfKind k51 K32)) ,
      (forall {d37 : (Trace tm)} {k52 : Hvl} ,
        (substhvl_tm k50 d37 k51 k52) -> (wfKind k52 K32)))) := (fun (k51 : Hvl) =>
    (ind_wfKind k51 (fun (K32 : Kind) (wf0 : (wfKind k51 K32)) =>
      (forall {d37 : (Trace tm)} {k52 : Hvl} ,
        (substhvl_tm k50 d37 k51 k52) -> (wfKind k52 K32))) (fun {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
      (wfKind_star k52)) (fun (K1 : Kind) (wf0 : (wfKind k51 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k51 K2)) IHK2 {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
      (wfKind_karr k52 (IHK1 (weakenTrace d37 H0) k52 (weaken_substhvl_tm H0 del)) (IHK2 (weakenTrace d37 H0) k52 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_ty_wfKind {k50 : Hvl} : (forall (k51 : Hvl) ,
    (forall (K32 : Kind) (wf0 : (wfKind k51 K32)) ,
      (forall {d37 : (Trace ty)} {k52 : Hvl} ,
        (substhvl_ty k50 d37 k51 k52) -> (wfKind k52 K32)))) := (fun (k51 : Hvl) =>
    (ind_wfKind k51 (fun (K32 : Kind) (wf0 : (wfKind k51 K32)) =>
      (forall {d37 : (Trace ty)} {k52 : Hvl} ,
        (substhvl_ty k50 d37 k51 k52) -> (wfKind k52 K32))) (fun {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
      (wfKind_star k52)) (fun (K1 : Kind) (wf0 : (wfKind k51 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k51 K2)) IHK2 {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
      (wfKind_karr k52 (IHK1 (weakenTrace d37 H0) k52 (weaken_substhvl_ty H0 del)) (IHK2 (weakenTrace d37 H0) k52 (weaken_substhvl_ty H0 del)))))).
  Definition substhvl_tm_wfTy {k50 : Hvl} : (forall (k51 : Hvl) ,
    (forall (S34 : Ty) (wf0 : (wfTy k51 S34)) ,
      (forall {d37 : (Trace tm)} {k52 : Hvl} ,
        (substhvl_tm k50 d37 k51 k52) -> (wfTy k52 S34)))) := (ind_wfTy (fun (k51 : Hvl) (S34 : Ty) (wf0 : (wfTy k51 S34)) =>
    (forall {d37 : (Trace tm)} {k52 : Hvl} ,
      (substhvl_tm k50 d37 k51 k52) -> (wfTy k52 S34))) (fun (k51 : Hvl) {X50 : (Index ty)} (wfi : (wfindex k51 X50)) {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (wfTy_tvar k52 (substhvl_tm_wfindex_ty del wfi))) (fun (k51 : Hvl) (K : Kind) (wf0 : (wfKind k51 K)) (T : Ty) (wf1 : (wfTy (HS ty k51) T)) IHT5 {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (wfTy_tabs k52 (substhvl_tm_wfKind k51 K wf0 (weaken_substhvl_tm H0 del)) (IHT5 (weakenTrace d37 (HS ty H0)) (HS ty k52) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k51 : Hvl) (T1 : Ty) (wf0 : (wfTy k51 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k51 T2)) IHT6 {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (wfTy_tapp k52 (IHT5 (weakenTrace d37 H0) k52 (weaken_substhvl_tm H0 del)) (IHT6 (weakenTrace d37 H0) k52 (weaken_substhvl_tm H0 del)))) (fun (k51 : Hvl) (T1 : Ty) (wf0 : (wfTy k51 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k51 T2)) IHT6 {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (wfTy_tarr k52 (IHT5 (weakenTrace d37 H0) k52 (weaken_substhvl_tm H0 del)) (IHT6 (weakenTrace d37 H0) k52 (weaken_substhvl_tm H0 del)))) (fun (k51 : Hvl) (K : Kind) (wf0 : (wfKind k51 K)) (T : Ty) (wf1 : (wfTy (HS ty k51) T)) IHT5 {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (wfTy_tall k52 (substhvl_tm_wfKind k51 K wf0 (weaken_substhvl_tm H0 del)) (IHT5 (weakenTrace d37 (HS ty H0)) (HS ty k52) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k50 : Hvl} {S34 : Ty} (wf : (wfTy k50 S34)) : (forall (k51 : Hvl) ,
    (forall (S35 : Ty) (wf0 : (wfTy k51 S35)) ,
      (forall {d37 : (Trace ty)} {k52 : Hvl} ,
        (substhvl_ty k50 d37 k51 k52) -> (wfTy k52 (tsubstTy d37 S34 S35))))) := (ind_wfTy (fun (k51 : Hvl) (S35 : Ty) (wf0 : (wfTy k51 S35)) =>
    (forall {d37 : (Trace ty)} {k52 : Hvl} ,
      (substhvl_ty k50 d37 k51 k52) -> (wfTy k52 (tsubstTy d37 S34 S35)))) (fun (k51 : Hvl) {X50 : (Index ty)} (wfi : (wfindex k51 X50)) {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k51 : Hvl) (K : Kind) (wf0 : (wfKind k51 K)) (T : Ty) (wf1 : (wfTy (HS ty k51) T)) IHT5 {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (wfTy_tabs k52 (substhvl_ty_wfKind k51 K wf0 (weaken_substhvl_ty H0 del)) (IHT5 (weakenTrace d37 (HS ty H0)) (HS ty k52) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k51 : Hvl) (T1 : Ty) (wf0 : (wfTy k51 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k51 T2)) IHT6 {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (wfTy_tapp k52 (IHT5 (weakenTrace d37 H0) k52 (weaken_substhvl_ty H0 del)) (IHT6 (weakenTrace d37 H0) k52 (weaken_substhvl_ty H0 del)))) (fun (k51 : Hvl) (T1 : Ty) (wf0 : (wfTy k51 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k51 T2)) IHT6 {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (wfTy_tarr k52 (IHT5 (weakenTrace d37 H0) k52 (weaken_substhvl_ty H0 del)) (IHT6 (weakenTrace d37 H0) k52 (weaken_substhvl_ty H0 del)))) (fun (k51 : Hvl) (K : Kind) (wf0 : (wfKind k51 K)) (T : Ty) (wf1 : (wfTy (HS ty k51) T)) IHT5 {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (wfTy_tall k52 (substhvl_ty_wfKind k51 K wf0 (weaken_substhvl_ty H0 del)) (IHT5 (weakenTrace d37 (HS ty H0)) (HS ty k52) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfTm {k50 : Hvl} {s14 : Tm} (wf : (wfTm k50 s14)) : (forall (k51 : Hvl) ,
    (forall (s15 : Tm) (wf0 : (wfTm k51 s15)) ,
      (forall {d37 : (Trace tm)} {k52 : Hvl} ,
        (substhvl_tm k50 d37 k51 k52) -> (wfTm k52 (substTm d37 s14 s15))))) := (ind_wfTm (fun (k51 : Hvl) (s15 : Tm) (wf0 : (wfTm k51 s15)) =>
    (forall {d37 : (Trace tm)} {k52 : Hvl} ,
      (substhvl_tm k50 d37 k51 k52) -> (wfTm k52 (substTm d37 s14 s15)))) (fun (k51 : Hvl) {x52 : (Index tm)} (wfi : (wfindex k51 x52)) {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k51 : Hvl) (T : Ty) (wf0 : (wfTy k51 T)) (t : Tm) (wf1 : (wfTm (HS tm k51) t)) IHt94 {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (wfTm_abs k52 (substhvl_tm_wfTy k51 T wf0 (weaken_substhvl_tm H0 del)) (IHt94 (weakenTrace d37 (HS tm H0)) (HS tm k52) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k51 : Hvl) (t1 : Tm) (wf0 : (wfTm k51 t1)) IHt94 (t2 : Tm) (wf1 : (wfTm k51 t2)) IHt95 {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (wfTm_app k52 (IHt94 (weakenTrace d37 H0) k52 (weaken_substhvl_tm H0 del)) (IHt95 (weakenTrace d37 H0) k52 (weaken_substhvl_tm H0 del)))) (fun (k51 : Hvl) (K : Kind) (wf0 : (wfKind k51 K)) (t : Tm) (wf1 : (wfTm (HS ty k51) t)) IHt94 {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (wfTm_tyabs k52 (substhvl_tm_wfKind k51 K wf0 (weaken_substhvl_tm H0 del)) (IHt94 (weakenTrace d37 (HS ty H0)) (HS ty k52) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k51 : Hvl) (t : Tm) (wf0 : (wfTm k51 t)) IHt94 (T : Ty) (wf1 : (wfTy k51 T)) {d37 : (Trace tm)} {k52 : Hvl} (del : (substhvl_tm k50 d37 k51 k52)) =>
    (wfTm_tyapp k52 (IHt94 (weakenTrace d37 H0) k52 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k51 T wf1 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTm {k50 : Hvl} {S34 : Ty} (wf : (wfTy k50 S34)) : (forall (k51 : Hvl) ,
    (forall (s14 : Tm) (wf0 : (wfTm k51 s14)) ,
      (forall {d37 : (Trace ty)} {k52 : Hvl} ,
        (substhvl_ty k50 d37 k51 k52) -> (wfTm k52 (tsubstTm d37 S34 s14))))) := (ind_wfTm (fun (k51 : Hvl) (s14 : Tm) (wf0 : (wfTm k51 s14)) =>
    (forall {d37 : (Trace ty)} {k52 : Hvl} ,
      (substhvl_ty k50 d37 k51 k52) -> (wfTm k52 (tsubstTm d37 S34 s14)))) (fun (k51 : Hvl) {x52 : (Index tm)} (wfi : (wfindex k51 x52)) {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (wfTm_var k52 (substhvl_ty_wfindex_tm del wfi))) (fun (k51 : Hvl) (T : Ty) (wf0 : (wfTy k51 T)) (t : Tm) (wf1 : (wfTm (HS tm k51) t)) IHt94 {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (wfTm_abs k52 (substhvl_ty_wfTy wf k51 T wf0 (weaken_substhvl_ty H0 del)) (IHt94 (weakenTrace d37 (HS tm H0)) (HS tm k52) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k51 : Hvl) (t1 : Tm) (wf0 : (wfTm k51 t1)) IHt94 (t2 : Tm) (wf1 : (wfTm k51 t2)) IHt95 {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (wfTm_app k52 (IHt94 (weakenTrace d37 H0) k52 (weaken_substhvl_ty H0 del)) (IHt95 (weakenTrace d37 H0) k52 (weaken_substhvl_ty H0 del)))) (fun (k51 : Hvl) (K : Kind) (wf0 : (wfKind k51 K)) (t : Tm) (wf1 : (wfTm (HS ty k51) t)) IHt94 {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (wfTm_tyabs k52 (substhvl_ty_wfKind k51 K wf0 (weaken_substhvl_ty H0 del)) (IHt94 (weakenTrace d37 (HS ty H0)) (HS ty k52) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k51 : Hvl) (t : Tm) (wf0 : (wfTm k51 t)) IHt94 (T : Ty) (wf1 : (wfTy k51 T)) {d37 : (Trace ty)} {k52 : Hvl} (del : (substhvl_ty k50 d37 k51 k52)) =>
    (wfTm_tyapp k52 (IHt94 (weakenTrace d37 H0) k52 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k51 T wf1 (weaken_substhvl_ty H0 del))))).
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
  Fixpoint substEnv (d37 : (Trace tm)) (s14 : Tm) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d37 s14 G0) T)
      | (etvar G0 K) => (etvar (substEnv d37 s14 G0) K)
    end.
  Fixpoint tsubstEnv (d37 : (Trace ty)) (S34 : Ty) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d37 S34 G0) (tsubstTy (weakenTrace d37 (domainEnv G0)) S34 T))
      | (etvar G0 K) => (etvar (tsubstEnv d37 S34 G0) K)
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
    (forall (d37 : (Trace tm)) (s14 : Tm) (G : Env) ,
      ((domainEnv (substEnv d37 s14 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d37 : (Trace ty)) (S34 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d37 S34 G)) =
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
      (forall (d37 : (Trace tm)) (s14 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d37 s14 (appendEnv G G0)) =
        (appendEnv (substEnv d37 s14 G) (substEnv (weakenTrace d37 (domainEnv G)) s14 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d37 : (Trace ty)) (S34 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d37 S34 (appendEnv G G0)) =
        (appendEnv (tsubstEnv d37 S34 G) (tsubstEnv (weakenTrace d37 (domainEnv G)) S34 G0)))).
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
          {G : Env} {x52 : (Index tm)}
          {T79 : Ty} {T80 : Ty} :
          (lookup_evar G x52 T79) -> (lookup_evar (evar G T80) (IS x52) T79)
      | lookup_evar_there_etvar
          {G : Env} {x52 : (Index tm)}
          {T79 : Ty} {K32 : Kind} :
          (lookup_evar G x52 T79) -> (lookup_evar (etvar G K32) x52 (tshiftTy C0 T79)).
    Inductive lookup_etvar : Env -> (Index ty) -> Kind -> Prop :=
      | lookup_etvar_here {G : Env}
          {K32 : Kind} :
          (wfKind (domainEnv G) K32) -> (lookup_etvar (etvar G K32) I0 K32)
      | lookup_etvar_there_evar
          {G : Env} {X50 : (Index ty)}
          {K32 : Kind} {T79 : Ty} :
          (lookup_etvar G X50 K32) -> (lookup_etvar (evar G T79) X50 K32)
      | lookup_etvar_there_etvar
          {G : Env} {X50 : (Index ty)}
          {K32 : Kind} {K33 : Kind} :
          (lookup_etvar G X50 K32) -> (lookup_etvar (etvar G K33) (IS X50) K32).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (S34 : Ty) (S35 : Ty) ,
        (lookup_evar (evar G S34) I0 S35) -> (S34 =
        S35)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (K32 : Kind) (K33 : Kind) ,
        (lookup_etvar (etvar G K32) I0 K33) -> (K32 =
        K33)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x52 : (Index tm)} ,
        (forall {S34 : Ty} ,
          (lookup_evar G x52 S34) -> (forall {S35 : Ty} ,
            (lookup_evar G x52 S35) -> (S34 =
            S35)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X50 : (Index ty)} ,
        (forall {K32 : Kind} ,
          (lookup_etvar G X50 K32) -> (forall {K33 : Kind} ,
            (lookup_etvar G X50 K33) -> (K32 =
            K33)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x52 : (Index tm)} {S34 : Ty} ,
        (lookup_evar G x52 S34) -> (wfTy (domainEnv G) S34)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X50 : (Index ty)} {K32 : Kind} ,
        (lookup_etvar G X50 K32) -> (wfKind (domainEnv G) K32)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x52 : (Index tm)} {T79 : Ty} ,
        (lookup_evar G x52 T79) -> (lookup_evar (appendEnv G G0) (weakenIndextm x52 (domainEnv G0)) (weakenTy T79 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X50 : (Index ty)} {K32 : Kind} ,
        (lookup_etvar G X50 K32) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X50 (domainEnv G0)) (weakenKind K32 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x52 : (Index tm)} {S34 : Ty} ,
        (lookup_evar G x52 S34) -> (wfindex (domainEnv G) x52)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X50 : (Index ty)} {K33 : Kind} ,
        (lookup_etvar G X50 K33) -> (wfindex (domainEnv G) X50)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T79 : Ty} :
        (shift_evar C0 G (evar G T79))
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
        {K32 : Kind} :
        (shift_etvar C0 G (etvar G K32))
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
  Inductive subst_evar (G : Env) (T79 : Ty) (s14 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T79 s14 X0 (evar G T79) G)
    | subst_evar_there_evar
        {d37 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T79 s14 d37 G0 G1) -> (subst_evar G T79 s14 (XS tm d37) (evar G0 T) (evar G1 T))
    | subst_evar_there_etvar
        {d37 : (Trace tm)} {G0 : Env}
        {G1 : Env} {K : Kind} :
        (subst_evar G T79 s14 d37 G0 G1) -> (subst_evar G T79 s14 (XS ty d37) (etvar G0 K) (etvar G1 K)).
  Lemma weaken_subst_evar {G : Env} {T79 : Ty} {s14 : Tm} :
    (forall (G0 : Env) {d37 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T79 s14 d37 G1 G2) -> (subst_evar G T79 s14 (weakenTrace d37 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (K32 : Kind) (S34 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G K32 S34 X0 (etvar G K32) G)
    | subst_etvar_there_evar
        {d37 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G K32 S34 d37 G0 G1) -> (subst_etvar G K32 S34 (XS tm d37) (evar G0 T) (evar G1 (tsubstTy d37 S34 T)))
    | subst_etvar_there_etvar
        {d37 : (Trace ty)} {G0 : Env}
        {G1 : Env} {K : Kind} :
        (subst_etvar G K32 S34 d37 G0 G1) -> (subst_etvar G K32 S34 (XS ty d37) (etvar G0 K) (etvar G1 K)).
  Lemma weaken_subst_etvar {G : Env} {K32 : Kind} {S34 : Ty} :
    (forall (G0 : Env) {d37 : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G K32 S34 d37 G1 G2) -> (subst_etvar G K32 S34 (weakenTrace d37 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d37 S34 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s14 : Tm} {T79 : Ty} :
    (forall {d37 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T79 s14 d37 G0 G1) -> (substhvl_tm (domainEnv G) d37 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S34 : Ty} {K32 : Kind} :
    (forall {d37 : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G K32 S34 d37 G0 G1) -> (substhvl_ty (domainEnv G) d37 (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {K32 : Kind} (wf : (wfKind (domainEnv G) K32)) ,
    (lookup_etvar (appendEnv (etvar G K32) G0) (weakenIndexty I0 (domainEnv G0)) (weakenKind K32 (domainEnv G0)))).
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
  | H : (wfTy _ (tall _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H : (wfTm _ (var _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (abs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (app _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tyabs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tyapp _ _)) |- _ => inversion H; subst; clear H
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
  (forall {c12 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c12 G G0)) {x52 : (Index tm)} {T79 : Ty} ,
    (lookup_evar G x52 T79) -> (lookup_evar G0 (shiftIndex c12 x52) T79)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c12 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c12 G G0)) {X50 : (Index ty)} {K32 : Kind} ,
    (lookup_etvar G X50 K32) -> (lookup_etvar G0 X50 K32)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c12 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c12 G G0)) {x52 : (Index tm)} {T79 : Ty} ,
    (lookup_evar G x52 T79) -> (lookup_evar G0 x52 (tshiftTy c12 T79))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c12 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c12 G G0)) {X50 : (Index ty)} {K32 : Kind} ,
    (lookup_etvar G X50 K32) -> (lookup_etvar G0 (tshiftIndex c12 X50) K32)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} {T80 : Ty} {s14 : Tm} :
  (forall {d37 : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T80 s14 d37 G0 G1)) {X50 : (Index ty)} {K33 : Kind} ,
    (lookup_etvar G0 X50 K33) -> (lookup_etvar G1 X50 K33)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} {K33 : Kind} {S34 : Ty} (wf : (wfTy (domainEnv G) S34)) :
  (forall {d37 : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G K33 S34 d37 G0 G1)) {x52 : (Index tm)} {T80 : Ty} ,
    (lookup_evar G0 x52 T80) -> (lookup_evar G1 x52 (tsubstTy d37 S34 T80))).
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
    | (tall K0 T4) => (plus 1 (plus (size_Kind K0) (size_Ty T4)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} : nat :=
  match s with
    | (var x) => 1
    | (abs T t) => (plus 1 (plus (size_Ty T) (size_Tm t)))
    | (app t1 t2) => (plus 1 (plus (size_Tm t1) (size_Tm t2)))
    | (tyabs K t0) => (plus 1 (plus (size_Kind K) (size_Tm t0)))
    | (tyapp t3 T0) => (plus 1 (plus (size_Tm t3) (size_Ty T0)))
  end.
Lemma tshift_size_Ty  :
  (forall (S34 : Ty) (c9 : (Cutoff ty)) ,
    ((size_Ty (tshiftTy c9 S34)) =
    (size_Ty S34))).
Proof.
  apply_mutual_ind ind_Ty.
  - intros X44 c9.
  reflexivity.
  - intros K28 T69 IHT69.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHT69 (CS c10))).
  - intros T70 IHT70 T71 IHT71.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT70 c10)).
  + exact ((IHT71 c10)).
  - intros T72 IHT72 T73 IHT73.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT72 c10)).
  + exact ((IHT73 c10)).
  - intros K29 T74 IHT74.
  intros c10; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHT74 (CS c10))).
Qed.

Lemma shift_size_Tm  :
  (forall (s14 : Tm) (c10 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c10 s14)) =
    (size_Tm s14))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros x48 c10.
  reflexivity.
  - intros T75 t84 IHt84.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt84 (CS c11))).
  - intros t85 IHt85 t86 IHt86.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt85 c11)).
  + exact ((IHt86 c11)).
  - intros K30 t87 IHt87.
  intros c11; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt87 c11)).
  - intros t88 IHt88 T76.
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
  - intros X48 c11.
  reflexivity.
  - intros T77 t89 IHt89.
  pose proof ((tshift_size_Ty T77)) as IHT77.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT77 c12)).
  + exact ((IHt89 c12)).
  - intros t90 IHt90 t91 IHt91.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt90 c12)).
  + exact ((IHt91 c12)).
  - intros K31 t92 IHt92.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt92 (CS c12))).
  - intros t93 IHt93 T78.
  pose proof ((tshift_size_Ty T78)) as IHT78.
  intros c12; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt93 c12)).
  + exact ((IHT78 c12)).
Qed.

 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Kind  :
  (forall (k50 : Hvl) (K32 : Kind) ,
    ((size_Kind (weakenKind K32 k50)) =
    (size_Kind K32))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k50 : Hvl) (s14 : Tm) ,
    ((size_Tm (weakenTm s14 k50)) =
    (size_Tm s14))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k50 : Hvl) (S34 : Ty) ,
    ((size_Ty (weakenTy S34 k50)) =
    (size_Ty S34))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : weaken_size.