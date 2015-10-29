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
  Inductive Lab : Set :=
    | L0 
    | LS (l : Lab).
  Scheme ind_Lab := Induction for Lab Sort Prop.
  
  Inductive TRec : Set :=
    | tnil 
    | tcons (l : Lab) (T : Ty)
        (TS : TRec)
  with Ty : Set :=
    | tvar (X : (Index ty))
    | top 
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (T1 : Ty) (T2 : Ty)
    | trec (TS : TRec).
  Scheme ind_TRec := Induction for TRec Sort Prop
  with ind_Ty := Induction for Ty Sort Prop.
  Combined Scheme ind_TRec_Ty from ind_TRec, ind_Ty.
  
  Inductive Pat : Set :=
    | pvar (T : Ty)
    | prec (ps : PRec)
  with PRec : Set :=
    | pnil 
    | pcons (l : Lab) (p : Pat)
        (ps : PRec).
  Scheme ind_Pat := Induction for Pat Sort Prop
  with ind_PRec := Induction for PRec Sort Prop.
  Combined Scheme ind_Pat_PRec from ind_Pat, ind_PRec.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (T : Ty) (t : Tm)
    | tapp (t : Tm) (T : Ty)
    | rec (ts : Rec)
    | prj (t : Tm) (l : Lab)
    | lett (p : Pat) (t1 : Tm)
        (t2 : Tm)
  with Rec : Set :=
    | rnil 
    | rcons (l : Lab) (t : Tm)
        (ts : Rec).
  Scheme ind_Tm := Induction for Tm Sort Prop
  with ind_Rec := Induction for Rec Sort Prop.
  Combined Scheme ind_Tm_Rec from ind_Tm, ind_Rec.
End Terms.

Section Functions.
  Fixpoint bindPRec (ps : PRec) {struct ps} : Hvl :=
    match ps with
      | (pnil) => H0
      | (pcons l p ps) => (appendHvl (bindPat p) (appendHvl (bindPRec ps) H0))
    end
  with bindPat (p : Pat) {struct p} : Hvl :=
    match p with
      | (pvar T) => (appendHvl (HS tm H0) H0)
      | (prec ps) => (appendHvl (bindPRec ps) H0)
    end.
  Scheme ind_bindPRec_bindPat_PRec := Induction for PRec Sort Prop
  with ind_bindPRec_bindPat_Pat := Induction for Pat Sort Prop.
  Combined Scheme ind_bindPRec_bindPat_PRec_Pat from ind_bindPRec_bindPat_PRec, ind_bindPRec_bindPat_Pat.
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
  Fixpoint tshiftTRec (c : (Cutoff ty)) (SS : TRec) {struct SS} : TRec :=
    match SS with
      | (tnil) => (tnil)
      | (tcons l T TS) => (tcons l (tshiftTy (weakenCutoffty c H0) T) (tshiftTRec (weakenCutoffty c H0) TS))
    end
  with tshiftTy (c : (Cutoff ty)) (S0 : Ty) {struct S0} : Ty :=
    match S0 with
      | (tvar X) => (tvar (tshiftIndex c X))
      | (top) => (top)
      | (tarr T1 T2) => (tarr (tshiftTy (weakenCutoffty c H0) T1) (tshiftTy (weakenCutoffty c H0) T2))
      | (tall T0 T3) => (tall (tshiftTy (weakenCutoffty c H0) T0) (tshiftTy (weakenCutoffty c (appendHvl (HS ty H0) H0)) T3))
      | (trec TS) => (trec (tshiftTRec (weakenCutoffty c H0) TS))
    end.
  Fixpoint tshiftPat (c : (Cutoff ty)) (p : Pat) {struct p} : Pat :=
    match p with
      | (pvar T) => (pvar (tshiftTy (weakenCutoffty c H0) T))
      | (prec ps) => (prec (tshiftPRec (weakenCutoffty c H0) ps))
    end
  with tshiftPRec (c : (Cutoff ty)) (ps : PRec) {struct ps} : PRec :=
    match ps with
      | (pnil) => (pnil)
      | (pcons l p ps0) => (pcons l (tshiftPat (weakenCutoffty c H0) p) (tshiftPRec (weakenCutoffty c H0) ps0))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var (shiftIndex c x))
      | (abs T t) => (abs T (shiftTm (weakenCutofftm c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (shiftTm (weakenCutofftm c H0) t1) (shiftTm (weakenCutofftm c H0) t2))
      | (tabs T0 t0) => (tabs T0 (shiftTm (weakenCutofftm c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T1) => (tapp (shiftTm (weakenCutofftm c H0) t3) T1)
      | (rec ts) => (rec (shiftRec (weakenCutofftm c H0) ts))
      | (prj t4 l) => (prj (shiftTm (weakenCutofftm c H0) t4) l)
      | (lett p t5 t6) => (lett p (shiftTm (weakenCutofftm c H0) t5) (shiftTm (weakenCutofftm c (appendHvl (bindPat p) H0)) t6))
    end
  with shiftRec (c : (Cutoff tm)) (ss : Rec) {struct ss} : Rec :=
    match ss with
      | (rnil) => (rnil)
      | (rcons l t ts) => (rcons l (shiftTm (weakenCutofftm c H0) t) (shiftRec (weakenCutofftm c H0) ts))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tshiftTy (weakenCutoffty c H0) T) (tshiftTm (weakenCutoffty c (appendHvl (HS tm H0) H0)) t))
      | (app t1 t2) => (app (tshiftTm (weakenCutoffty c H0) t1) (tshiftTm (weakenCutoffty c H0) t2))
      | (tabs T0 t0) => (tabs (tshiftTy (weakenCutoffty c H0) T0) (tshiftTm (weakenCutoffty c (appendHvl (HS ty H0) H0)) t0))
      | (tapp t3 T1) => (tapp (tshiftTm (weakenCutoffty c H0) t3) (tshiftTy (weakenCutoffty c H0) T1))
      | (rec ts) => (rec (tshiftRec (weakenCutoffty c H0) ts))
      | (prj t4 l) => (prj (tshiftTm (weakenCutoffty c H0) t4) l)
      | (lett p t5 t6) => (lett (tshiftPat (weakenCutoffty c H0) p) (tshiftTm (weakenCutoffty c H0) t5) (tshiftTm (weakenCutoffty c (appendHvl (bindPat p) H0)) t6))
    end
  with tshiftRec (c : (Cutoff ty)) (ss : Rec) {struct ss} : Rec :=
    match ss with
      | (rnil) => (rnil)
      | (rcons l t ts) => (rcons l (tshiftTm (weakenCutoffty c H0) t) (tshiftRec (weakenCutoffty c H0) ts))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenLab (l : Lab) (k : Hvl) {struct k} : Lab :=
    match k with
      | (H0) => l
      | (HS tm k) => (weakenLab l k)
      | (HS ty k) => (weakenLab l k)
    end.
  Fixpoint weakenTRec (SS : TRec) (k : Hvl) {struct k} : TRec :=
    match k with
      | (H0) => SS
      | (HS tm k) => (weakenTRec SS k)
      | (HS ty k) => (tshiftTRec C0 (weakenTRec SS k))
    end.
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
  Fixpoint weakenPRec (ps : PRec) (k : Hvl) {struct k} : PRec :=
    match k with
      | (H0) => ps
      | (HS tm k) => (weakenPRec ps k)
      | (HS ty k) => (tshiftPRec C0 (weakenPRec ps k))
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} : Tm :=
    match k with
      | (H0) => s
      | (HS tm k) => (shiftTm C0 (weakenTm s k))
      | (HS ty k) => (tshiftTm C0 (weakenTm s k))
    end.
  Fixpoint weakenRec (ss : Rec) (k : Hvl) {struct k} : Rec :=
    match k with
      | (H0) => ss
      | (HS tm k) => (shiftRec C0 (weakenRec ss k))
      | (HS ty k) => (tshiftRec C0 (weakenRec ss k))
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
  Fixpoint tsubstTRec (d : (Trace ty)) (S0 : Ty) (SS : TRec) {struct SS} : TRec :=
    match SS with
      | (tnil) => (tnil)
      | (tcons l T TS) => (tcons l (tsubstTy d S0 T) (tsubstTRec d S0 TS))
    end
  with tsubstTy (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S1} : Ty :=
    match S1 with
      | (tvar X) => (tsubstIndex d S0 X)
      | (top) => (top)
      | (tarr T1 T2) => (tarr (tsubstTy d S0 T1) (tsubstTy d S0 T2))
      | (tall T0 T3) => (tall (tsubstTy d S0 T0) (tsubstTy (XS ty d) S0 T3))
      | (trec TS) => (trec (tsubstTRec d S0 TS))
    end.
  Fixpoint tsubstPat (d : (Trace ty)) (S0 : Ty) (p : Pat) {struct p} : Pat :=
    match p with
      | (pvar T) => (pvar (tsubstTy d S0 T))
      | (prec ps) => (prec (tsubstPRec d S0 ps))
    end
  with tsubstPRec (d : (Trace ty)) (S0 : Ty) (ps : PRec) {struct ps} : PRec :=
    match ps with
      | (pnil) => (pnil)
      | (pcons l p ps0) => (pcons l (tsubstPat d S0 p) (tsubstPRec d S0 ps0))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} : Tm :=
    match s0 with
      | (var x) => (substIndex d s x)
      | (abs T t) => (abs T (substTm (XS tm d) s t))
      | (app t1 t2) => (app (substTm d s t1) (substTm d s t2))
      | (tabs T0 t0) => (tabs T0 (substTm (XS ty d) s t0))
      | (tapp t3 T1) => (tapp (substTm d s t3) T1)
      | (rec ts) => (rec (substRec d s ts))
      | (prj t4 l) => (prj (substTm d s t4) l)
      | (lett p t5 t6) => (lett p (substTm d s t5) (substTm (weakenTrace d (bindPat p)) s t6))
    end
  with substRec (d : (Trace tm)) (s : Tm) (ss : Rec) {struct ss} : Rec :=
    match ss with
      | (rnil) => (rnil)
      | (rcons l t ts) => (rcons l (substTm d s t) (substRec d s ts))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} : Tm :=
    match s with
      | (var x) => (var x)
      | (abs T t) => (abs (tsubstTy d S0 T) (tsubstTm (XS tm d) S0 t))
      | (app t1 t2) => (app (tsubstTm d S0 t1) (tsubstTm d S0 t2))
      | (tabs T0 t0) => (tabs (tsubstTy d S0 T0) (tsubstTm (XS ty d) S0 t0))
      | (tapp t3 T1) => (tapp (tsubstTm d S0 t3) (tsubstTy d S0 T1))
      | (rec ts) => (rec (tsubstRec d S0 ts))
      | (prj t4 l) => (prj (tsubstTm d S0 t4) l)
      | (lett p t5 t6) => (lett (tsubstPat d S0 p) (tsubstTm d S0 t5) (tsubstTm (weakenTrace d (bindPat p)) S0 t6))
    end
  with tsubstRec (d : (Trace ty)) (S0 : Ty) (ss : Rec) {struct ss} : Rec :=
    match ss with
      | (rnil) => (rnil)
      | (rcons l t ts) => (rcons l (tsubstTm d S0 t) (tsubstRec d S0 ts))
    end.
End Subst.

Global Hint Resolve (f_equal (tshiftPRec C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftPat C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftRec C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftRec C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTRec C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : interaction.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : interaction.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_tshift_bindPRec_bindPat  :
  (forall (ps : PRec) ,
    (forall (c : (Cutoff ty)) ,
      ((bindPRec (tshiftPRec c ps)) =
      (bindPRec ps)))) /\
  (forall (p : Pat) ,
    (forall (c0 : (Cutoff ty)) ,
      ((bindPat (tshiftPat c0 p)) =
      (bindPat p)))).
Proof.
  apply_mutual_ind (ind_bindPRec_bindPat_PRec_Pat); simpl; intros; congruence .
Qed.
Lemma stability_tshift_bindPRec (ps0 : PRec) :
  (forall (c1 : (Cutoff ty)) ,
    ((bindPRec (tshiftPRec c1 ps0)) =
    (bindPRec ps0))).
Proof.
  intros; eapply (stability_tshift_bindPRec_bindPat).
Qed.
Lemma stability_tshift_bindPat (p0 : Pat) :
  (forall (c2 : (Cutoff ty)) ,
    ((bindPat (tshiftPat c2 p0)) =
    (bindPat p0))).
Proof.
  intros; eapply (stability_tshift_bindPRec_bindPat).
Qed.
 Hint Rewrite stability_tshift_bindPRec stability_tshift_bindPat : interaction.
 Hint Rewrite stability_tshift_bindPRec stability_tshift_bindPat : stability_shift.
Lemma stability_weaken_bindPat  :
  (forall (k : Hvl) (p1 : Pat) ,
    ((bindPat (weakenPat p1 k)) =
    (bindPat p1))).
Proof.
  needleGenericStabilityWeaken .
Qed.
Lemma stability_weaken_bindPRec  :
  (forall (k : Hvl) (ps1 : PRec) ,
    ((bindPRec (weakenPRec ps1 k)) =
    (bindPRec ps1))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bindPRec stability_weaken_bindPat : interaction.
 Hint Rewrite stability_weaken_bindPRec stability_weaken_bindPat : stability_weaken.
Lemma stability_tsubst_bindPRec_bindPat  :
  (forall (ps1 : PRec) ,
    (forall (d : (Trace ty)) (S0 : Ty) ,
      ((bindPRec (tsubstPRec d S0 ps1)) =
      (bindPRec ps1)))) /\
  (forall (p1 : Pat) ,
    (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((bindPat (tsubstPat d0 S1 p1)) =
      (bindPat p1)))).
Proof.
  apply_mutual_ind (ind_bindPRec_bindPat_PRec_Pat); simpl; intros; congruence .
Qed.
Lemma stability_tsubst_bindPRec (ps2 : PRec) :
  (forall (d1 : (Trace ty)) (S2 : Ty) ,
    ((bindPRec (tsubstPRec d1 S2 ps2)) =
    (bindPRec ps2))).
Proof.
  intros; eapply (stability_tsubst_bindPRec_bindPat).
Qed.
Lemma stability_tsubst_bindPat (p2 : Pat) :
  (forall (d2 : (Trace ty)) (S3 : Ty) ,
    ((bindPat (tsubstPat d2 S3 p2)) =
    (bindPat p2))).
Proof.
  intros; eapply (stability_tsubst_bindPRec_bindPat).
Qed.
 Hint Rewrite stability_tsubst_bindPRec stability_tsubst_bindPat : interaction.
 Hint Rewrite stability_tsubst_bindPRec stability_tsubst_bindPat : stability_subst.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k4 : Hvl) (x10 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k4) s (shiftIndex (weakenCutofftm C0 k4) x10)) =
      (var x10))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S4 : Ty) :
    (forall (k4 : Hvl) (X8 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k4) S4 (tshiftIndex (weakenCutoffty C0 k4) X8)) =
      (tvar X8))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Definition tsubst0_tshift0_TRec_Ty_reflection_ind := (ind_TRec_Ty (fun (SS : TRec) =>
    (forall (k7 : Hvl) (S6 : Ty) ,
      ((tsubstTRec (weakenTrace X0 k7) S6 (tshiftTRec (weakenCutoffty C0 k7) SS)) =
      SS))) (fun (S6 : Ty) =>
    (forall (k7 : Hvl) (S7 : Ty) ,
      ((tsubstTy (weakenTrace X0 k7) S7 (tshiftTy (weakenCutoffty C0 k7) S6)) =
      S6))) (fun (k7 : Hvl) (S6 : Ty) =>
    eq_refl) (fun (l : Lab) (T : Ty) IHT5 (TS : TRec) IHTS3 (k7 : Hvl) (S6 : Ty) =>
    (f_equal3 tcons eq_refl (IHT5 k7 S6) (IHTS3 k7 S6))) (fun (X14 : (Index ty)) =>
    (fun (k7 : Hvl) (S6 : Ty) =>
      (tsubstIndex0_tshiftIndex0_reflection_ind S6 k7 X14))) (fun (k7 : Hvl) (S6 : Ty) =>
    eq_refl) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k7 : Hvl) (S6 : Ty) =>
    (f_equal2 tarr (IHT5 k7 S6) (IHT6 k7 S6))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k7 : Hvl) (S6 : Ty) =>
    (f_equal2 tall (IHT5 k7 S6) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHT6 (HS ty k7) S6)))) (fun (TS : TRec) IHTS3 (k7 : Hvl) (S6 : Ty) =>
    (f_equal trec (IHTS3 k7 S6)))).
  Lemma tsubst0_tshift0_TRec_reflection_ind  :
    (forall (SS : TRec) ,
      (forall (k7 : Hvl) (S6 : Ty) ,
        ((tsubstTRec (weakenTrace X0 k7) S6 (tshiftTRec (weakenCutoffty C0 k7) SS)) =
        SS))).
  Proof.
    pose proof (tsubst0_tshift0_TRec_Ty_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Lemma tsubst0_tshift0_Ty_reflection_ind  :
    (forall (S6 : Ty) ,
      (forall (k7 : Hvl) (S7 : Ty) ,
        ((tsubstTy (weakenTrace X0 k7) S7 (tshiftTy (weakenCutoffty C0 k7) S6)) =
        S6))).
  Proof.
    pose proof (tsubst0_tshift0_TRec_Ty_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Definition tsubst0_tshift0_Pat_PRec_reflection_ind := (ind_Pat_PRec (fun (p11 : Pat) =>
    (forall (k7 : Hvl) (S6 : Ty) ,
      ((tsubstPat (weakenTrace X0 k7) S6 (tshiftPat (weakenCutoffty C0 k7) p11)) =
      p11))) (fun (ps7 : PRec) =>
    (forall (k7 : Hvl) (S6 : Ty) ,
      ((tsubstPRec (weakenTrace X0 k7) S6 (tshiftPRec (weakenCutoffty C0 k7) ps7)) =
      ps7))) (fun (T : Ty) (k7 : Hvl) (S6 : Ty) =>
    (f_equal pvar (let IHT5 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT5 k7 S6)))) (fun (ps : PRec) IHps (k7 : Hvl) (S6 : Ty) =>
    (f_equal prec (IHps k7 S6))) (fun (k7 : Hvl) (S6 : Ty) =>
    eq_refl) (fun (l : Lab) (p : Pat) IHp (ps : PRec) IHps (k7 : Hvl) (S6 : Ty) =>
    (f_equal3 pcons eq_refl (IHp k7 S6) (IHps k7 S6)))).
  Lemma tsubst0_tshift0_Pat_reflection_ind  :
    (forall (p11 : Pat) ,
      (forall (k7 : Hvl) (S6 : Ty) ,
        ((tsubstPat (weakenTrace X0 k7) S6 (tshiftPat (weakenCutoffty C0 k7) p11)) =
        p11))).
  Proof.
    pose proof (tsubst0_tshift0_Pat_PRec_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Lemma tsubst0_tshift0_PRec_reflection_ind  :
    (forall (ps7 : PRec) ,
      (forall (k7 : Hvl) (S6 : Ty) ,
        ((tsubstPRec (weakenTrace X0 k7) S6 (tshiftPRec (weakenCutoffty C0 k7) ps7)) =
        ps7))).
  Proof.
    pose proof (tsubst0_tshift0_Pat_PRec_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Definition subst0_shift0_Tm_Rec_reflection_ind := (ind_Tm_Rec (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (s1 : Tm) ,
      ((substTm (weakenTrace X0 k7) s1 (shiftTm (weakenCutofftm C0 k7) s0)) =
      s0))) (fun (ss : Rec) =>
    (forall (k7 : Hvl) (s0 : Tm) ,
      ((substRec (weakenTrace X0 k7) s0 (shiftRec (weakenCutofftm C0 k7) ss)) =
      ss))) (fun (x16 : (Index tm)) =>
    (fun (k7 : Hvl) (s0 : Tm) =>
      (substIndex0_shiftIndex0_reflection_ind s0 k7 x16))) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt53 (HS tm k7) s0)))) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 app (IHt53 k7 s0) (IHt54 k7 s0))) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt53 (HS ty k7) s0)))) (fun (t : Tm) IHt53 (T : Ty) (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 tapp (IHt53 k7 s0) eq_refl)) (fun (ts : Rec) IHts11 (k7 : Hvl) (s0 : Tm) =>
    (f_equal rec (IHts11 k7 s0))) (fun (t : Tm) IHt53 (l : Lab) (k7 : Hvl) (s0 : Tm) =>
    (f_equal2 prj (IHt53 k7 s0) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (s0 : Tm) =>
    (f_equal3 lett eq_refl (IHt53 k7 s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k7 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k7 (bindPat p)) eq_refl)) (IHt54 (appendHvl k7 (bindPat p)) s0)))) (fun (k7 : Hvl) (s0 : Tm) =>
    eq_refl) (fun (l : Lab) (t : Tm) IHt53 (ts : Rec) IHts11 (k7 : Hvl) (s0 : Tm) =>
    (f_equal3 rcons eq_refl (IHt53 k7 s0) (IHts11 k7 s0)))).
  Lemma subst0_shift0_Tm_reflection_ind  :
    (forall (s0 : Tm) ,
      (forall (k7 : Hvl) (s1 : Tm) ,
        ((substTm (weakenTrace X0 k7) s1 (shiftTm (weakenCutofftm C0 k7) s0)) =
        s0))).
  Proof.
    pose proof (subst0_shift0_Tm_Rec_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Lemma subst0_shift0_Rec_reflection_ind  :
    (forall (ss : Rec) ,
      (forall (k7 : Hvl) (s1 : Tm) ,
        ((substRec (weakenTrace X0 k7) s1 (shiftRec (weakenCutofftm C0 k7) ss)) =
        ss))).
  Proof.
    pose proof (subst0_shift0_Tm_Rec_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Definition tsubst0_tshift0_Tm_Rec_reflection_ind := (ind_Tm_Rec (fun (s0 : Tm) =>
    (forall (k7 : Hvl) (S6 : Ty) ,
      ((tsubstTm (weakenTrace X0 k7) S6 (tshiftTm (weakenCutoffty C0 k7) s0)) =
      s0))) (fun (ss : Rec) =>
    (forall (k7 : Hvl) (S6 : Ty) ,
      ((tsubstRec (weakenTrace X0 k7) S6 (tshiftRec (weakenCutoffty C0 k7) ss)) =
      ss))) (fun (x16 : (Index tm)) =>
    (fun (k7 : Hvl) (S6 : Ty) =>
      eq_refl)) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (S6 : Ty) =>
    (f_equal2 abs (let IHT5 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT5 k7 S6)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS tm H0)) eq_refl eq_refl) (IHt53 (HS tm k7) S6)))) (fun (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (S6 : Ty) =>
    (f_equal2 app (IHt53 k7 S6) (IHt54 k7 S6))) (fun (T : Ty) (t : Tm) IHt53 (k7 : Hvl) (S6 : Ty) =>
    (f_equal2 tabs (let IHT5 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT5 k7 S6)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k7 (HS ty H0)) eq_refl eq_refl) (IHt53 (HS ty k7) S6)))) (fun (t : Tm) IHt53 (T : Ty) (k7 : Hvl) (S6 : Ty) =>
    (f_equal2 tapp (IHt53 k7 S6) (let IHT5 := (tsubst0_tshift0_Ty_reflection_ind T) in
    (IHT5 k7 S6)))) (fun (ts : Rec) IHts11 (k7 : Hvl) (S6 : Ty) =>
    (f_equal rec (IHts11 k7 S6))) (fun (t : Tm) IHt53 (l : Lab) (k7 : Hvl) (S6 : Ty) =>
    (f_equal2 prj (IHt53 k7 S6) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt53 (t2 : Tm) IHt54 (k7 : Hvl) (S6 : Ty) =>
    (f_equal3 lett (let IHp := (tsubst0_tshift0_Pat_reflection_ind p) in
    (IHp k7 S6)) (IHt53 k7 S6) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenTrace_append ty X0 k7 (bindPat p))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k7 (bindPat p)) eq_refl)) (IHt54 (appendHvl k7 (bindPat p)) S6)))) (fun (k7 : Hvl) (S6 : Ty) =>
    eq_refl) (fun (l : Lab) (t : Tm) IHt53 (ts : Rec) IHts11 (k7 : Hvl) (S6 : Ty) =>
    (f_equal3 rcons eq_refl (IHt53 k7 S6) (IHts11 k7 S6)))).
  Lemma tsubst0_tshift0_Tm_reflection_ind  :
    (forall (s0 : Tm) ,
      (forall (k7 : Hvl) (S6 : Ty) ,
        ((tsubstTm (weakenTrace X0 k7) S6 (tshiftTm (weakenCutoffty C0 k7) s0)) =
        s0))).
  Proof.
    pose proof (tsubst0_tshift0_Tm_Rec_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Lemma tsubst0_tshift0_Rec_reflection_ind  :
    (forall (ss : Rec) ,
      (forall (k7 : Hvl) (S6 : Ty) ,
        ((tsubstRec (weakenTrace X0 k7) S6 (tshiftRec (weakenCutoffty C0 k7) ss)) =
        ss))).
  Proof.
    pose proof (tsubst0_tshift0_Tm_Rec_reflection_ind).
    destruct_conjs .
    easy .
  Qed.
  Definition tsubstTRec0_tshiftTRec0_reflection (SS : TRec) : (forall (S6 : Ty) ,
    ((tsubstTRec X0 S6 (tshiftTRec C0 SS)) =
    SS)) := (tsubst0_tshift0_TRec_reflection_ind SS H0).
  Definition tsubstTy0_tshiftTy0_reflection (S7 : Ty) : (forall (S6 : Ty) ,
    ((tsubstTy X0 S6 (tshiftTy C0 S7)) =
    S7)) := (tsubst0_tshift0_Ty_reflection_ind S7 H0).
  Definition tsubstPat0_tshiftPat0_reflection (p11 : Pat) : (forall (S6 : Ty) ,
    ((tsubstPat X0 S6 (tshiftPat C0 p11)) =
    p11)) := (tsubst0_tshift0_Pat_reflection_ind p11 H0).
  Definition tsubstPRec0_tshiftPRec0_reflection (ps7 : PRec) : (forall (S6 : Ty) ,
    ((tsubstPRec X0 S6 (tshiftPRec C0 ps7)) =
    ps7)) := (tsubst0_tshift0_PRec_reflection_ind ps7 H0).
  Definition substTm0_shiftTm0_reflection (s1 : Tm) : (forall (s0 : Tm) ,
    ((substTm X0 s0 (shiftTm C0 s1)) =
    s1)) := (subst0_shift0_Tm_reflection_ind s1 H0).
  Definition substRec0_shiftRec0_reflection (ss : Rec) : (forall (s0 : Tm) ,
    ((substRec X0 s0 (shiftRec C0 ss)) =
    ss)) := (subst0_shift0_Rec_reflection_ind ss H0).
  Definition tsubstTm0_tshiftTm0_reflection (s0 : Tm) : (forall (S6 : Ty) ,
    ((tsubstTm X0 S6 (tshiftTm C0 s0)) =
    s0)) := (tsubst0_tshift0_Tm_reflection_ind s0 H0).
  Definition tsubstRec0_tshiftRec0_reflection (ss : Rec) : (forall (S6 : Ty) ,
    ((tsubstRec X0 S6 (tshiftRec C0 ss)) =
    ss)) := (tsubst0_tshift0_Rec_reflection_ind ss H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c3 : (Cutoff tm)) (x : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c3) k) (shiftIndex (weakenCutofftm C0 k) x)) =
        (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c3 k) x)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c3 : (Cutoff ty)) (X : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c3) k) (tshiftIndex (weakenCutoffty C0 k) X)) =
        (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c3 k) X)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Definition tshift_tshift0_TRec_Ty_comm_ind := (ind_TRec_Ty (fun (SS : TRec) =>
      (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
        ((tshiftTRec (weakenCutoffty (CS c8) k4) (tshiftTRec (weakenCutoffty C0 k4) SS)) =
        (tshiftTRec (weakenCutoffty C0 k4) (tshiftTRec (weakenCutoffty c8 k4) SS))))) (fun (S4 : Ty) =>
      (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
        ((tshiftTy (weakenCutoffty (CS c8) k4) (tshiftTy (weakenCutoffty C0 k4) S4)) =
        (tshiftTy (weakenCutoffty C0 k4) (tshiftTy (weakenCutoffty c8 k4) S4))))) (fun (k4 : Hvl) (c8 : (Cutoff ty)) =>
      eq_refl) (fun (l : Lab) (T : Ty) IHT5 (TS : TRec) IHTS1 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal3 tcons eq_refl (IHT5 k4 c8) (IHTS1 k4 c8))) (fun (X8 : (Index ty)) =>
      (fun (k4 : Hvl) (c8 : (Cutoff ty)) =>
        (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k4 c8 X8)))) (fun (k4 : Hvl) (c8 : (Cutoff ty)) =>
      eq_refl) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 tarr (IHT5 k4 c8) (IHT6 k4 c8))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 tall (IHT5 k4 c8) (IHT6 (HS ty k4) c8))) (fun (TS : TRec) IHTS1 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal trec (IHTS1 k4 c8)))).
    Lemma tshift_tshift0_TRec_comm_ind  :
      (forall (SS : TRec) ,
        (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
          ((tshiftTRec (weakenCutoffty (CS c8) k4) (tshiftTRec (weakenCutoffty C0 k4) SS)) =
          (tshiftTRec (weakenCutoffty C0 k4) (tshiftTRec (weakenCutoffty c8 k4) SS))))).
    Proof.
      pose proof (tshift_tshift0_TRec_Ty_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_tshift0_Ty_comm_ind  :
      (forall (S4 : Ty) ,
        (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
          ((tshiftTy (weakenCutoffty (CS c8) k4) (tshiftTy (weakenCutoffty C0 k4) S4)) =
          (tshiftTy (weakenCutoffty C0 k4) (tshiftTy (weakenCutoffty c8 k4) S4))))).
    Proof.
      pose proof (tshift_tshift0_TRec_Ty_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_tshift0_Pat_PRec_comm_ind := (ind_Pat_PRec (fun (p8 : Pat) =>
      (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
        ((tshiftPat (weakenCutoffty (CS c8) k4) (tshiftPat (weakenCutoffty C0 k4) p8)) =
        (tshiftPat (weakenCutoffty C0 k4) (tshiftPat (weakenCutoffty c8 k4) p8))))) (fun (ps5 : PRec) =>
      (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
        ((tshiftPRec (weakenCutoffty (CS c8) k4) (tshiftPRec (weakenCutoffty C0 k4) ps5)) =
        (tshiftPRec (weakenCutoffty C0 k4) (tshiftPRec (weakenCutoffty c8 k4) ps5))))) (fun (T : Ty) (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal pvar (let IHT5 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT5 k4 c8)))) (fun (ps : PRec) IHps (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal prec (IHps k4 c8))) (fun (k4 : Hvl) (c8 : (Cutoff ty)) =>
      eq_refl) (fun (l : Lab) (p : Pat) IHp (ps : PRec) IHps (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal3 pcons eq_refl (IHp k4 c8) (IHps k4 c8)))).
    Lemma tshift_tshift0_Pat_comm_ind  :
      (forall (p8 : Pat) ,
        (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
          ((tshiftPat (weakenCutoffty (CS c8) k4) (tshiftPat (weakenCutoffty C0 k4) p8)) =
          (tshiftPat (weakenCutoffty C0 k4) (tshiftPat (weakenCutoffty c8 k4) p8))))).
    Proof.
      pose proof (tshift_tshift0_Pat_PRec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_tshift0_PRec_comm_ind  :
      (forall (ps5 : PRec) ,
        (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
          ((tshiftPRec (weakenCutoffty (CS c8) k4) (tshiftPRec (weakenCutoffty C0 k4) ps5)) =
          (tshiftPRec (weakenCutoffty C0 k4) (tshiftPRec (weakenCutoffty c8 k4) ps5))))).
    Proof.
      pose proof (tshift_tshift0_Pat_PRec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition shift_shift0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s : Tm) =>
      (forall (k4 : Hvl) (c8 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm (CS c8) k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c8 k4) s))))) (fun (ss : Rec) =>
      (forall (k4 : Hvl) (c8 : (Cutoff tm)) ,
        ((shiftRec (weakenCutofftm (CS c8) k4) (shiftRec (weakenCutofftm C0 k4) ss)) =
        (shiftRec (weakenCutofftm C0 k4) (shiftRec (weakenCutofftm c8 k4) ss))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c8 : (Cutoff tm)) =>
        (f_equal var (shiftIndex_shiftIndex0_comm_ind k4 c8 x10)))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt35 (HS tm k4) c8))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 app (IHt35 k4 c8) (IHt36 k4 c8))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 tabs eq_refl (IHt35 (HS ty k4) c8))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt35 k4 c8) eq_refl)) (fun (ts : Rec) IHts7 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal rec (IHts7 k4 c8))) (fun (t : Tm) IHt35 (l : Lab) (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 prj (IHt35 k4 c8) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal3 lett eq_refl (IHt35 k4 c8) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append (CS c8) k4 (bindPat p)) (f_equal2 shiftTm (weakenCutofftm_append C0 k4 (bindPat p)) eq_refl)) (eq_trans (IHt36 (appendHvl k4 (bindPat p)) c8) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k4 (bindPat p))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c8 k4 (bindPat p))) eq_refl)))))) (fun (k4 : Hvl) (c8 : (Cutoff tm)) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt35 (ts : Rec) IHts7 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal3 rcons eq_refl (IHt35 k4 c8) (IHts7 k4 c8)))).
    Lemma shift_shift0_Tm_comm_ind  :
      (forall (s : Tm) ,
        (forall (k4 : Hvl) (c8 : (Cutoff tm)) ,
          ((shiftTm (weakenCutofftm (CS c8) k4) (shiftTm (weakenCutofftm C0 k4) s)) =
          (shiftTm (weakenCutofftm C0 k4) (shiftTm (weakenCutofftm c8 k4) s))))).
    Proof.
      pose proof (shift_shift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma shift_shift0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k4 : Hvl) (c8 : (Cutoff tm)) ,
          ((shiftRec (weakenCutofftm (CS c8) k4) (shiftRec (weakenCutofftm C0 k4) ss)) =
          (shiftRec (weakenCutofftm C0 k4) (shiftRec (weakenCutofftm c8 k4) ss))))).
    Proof.
      pose proof (shift_shift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition shift_tshift0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s : Tm) =>
      (forall (k4 : Hvl) (c8 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm c8 k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (shiftTm (weakenCutofftm c8 k4) s))))) (fun (ss : Rec) =>
      (forall (k4 : Hvl) (c8 : (Cutoff tm)) ,
        ((shiftRec (weakenCutofftm c8 k4) (tshiftRec (weakenCutoffty C0 k4) ss)) =
        (tshiftRec (weakenCutoffty C0 k4) (shiftRec (weakenCutofftm c8 k4) ss))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c8 : (Cutoff tm)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt35 (HS tm k4) c8))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 app (IHt35 k4 c8) (IHt36 k4 c8))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 tabs eq_refl (IHt35 (HS ty k4) c8))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 tapp (IHt35 k4 c8) eq_refl)) (fun (ts : Rec) IHts7 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal rec (IHts7 k4 c8))) (fun (t : Tm) IHt35 (l : Lab) (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal2 prj (IHt35 k4 c8) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal3 lett eq_refl (IHt35 k4 c8) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenCutofftm_append c8 k4 (bindPat p))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k4 (bindPat p)) eq_refl)) (eq_trans (IHt36 (appendHvl k4 (bindPat p)) c8) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k4 (bindPat p))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c8 k4 (bindPat p))) eq_refl)))))) (fun (k4 : Hvl) (c8 : (Cutoff tm)) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt35 (ts : Rec) IHts7 (k4 : Hvl) (c8 : (Cutoff tm)) =>
      (f_equal3 rcons eq_refl (IHt35 k4 c8) (IHts7 k4 c8)))).
    Lemma shift_tshift0_Tm_comm_ind  :
      (forall (s : Tm) ,
        (forall (k4 : Hvl) (c8 : (Cutoff tm)) ,
          ((shiftTm (weakenCutofftm c8 k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
          (tshiftTm (weakenCutoffty C0 k4) (shiftTm (weakenCutofftm c8 k4) s))))).
    Proof.
      pose proof (shift_tshift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma shift_tshift0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k4 : Hvl) (c8 : (Cutoff tm)) ,
          ((shiftRec (weakenCutofftm c8 k4) (tshiftRec (weakenCutoffty C0 k4) ss)) =
          (tshiftRec (weakenCutoffty C0 k4) (shiftRec (weakenCutofftm c8 k4) ss))))).
    Proof.
      pose proof (shift_tshift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_shift0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s : Tm) =>
      (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty c8 k4) (shiftTm (weakenCutofftm C0 k4) s)) =
        (shiftTm (weakenCutofftm C0 k4) (tshiftTm (weakenCutoffty c8 k4) s))))) (fun (ss : Rec) =>
      (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
        ((tshiftRec (weakenCutoffty c8 k4) (shiftRec (weakenCutofftm C0 k4) ss)) =
        (shiftRec (weakenCutofftm C0 k4) (tshiftRec (weakenCutoffty c8 k4) ss))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c8 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 abs eq_refl (IHt35 (HS tm k4) c8))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 app (IHt35 k4 c8) (IHt36 k4 c8))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 tabs eq_refl (IHt35 (HS ty k4) c8))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt35 k4 c8) eq_refl)) (fun (ts : Rec) IHts7 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal rec (IHts7 k4 c8))) (fun (t : Tm) IHt35 (l : Lab) (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 prj (IHt35 k4 c8) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal3 lett eq_refl (IHt35 k4 c8) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c8 k4 (bindPat p)) (f_equal2 shiftTm (weakenCutofftm_append C0 k4 (bindPat p)) eq_refl)) (eq_trans (IHt36 (appendHvl k4 (bindPat p)) c8) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k4 (bindPat p))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c8 k4 (bindPat p))) eq_refl)))))) (fun (k4 : Hvl) (c8 : (Cutoff ty)) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt35 (ts : Rec) IHts7 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal3 rcons eq_refl (IHt35 k4 c8) (IHts7 k4 c8)))).
    Lemma tshift_shift0_Tm_comm_ind  :
      (forall (s : Tm) ,
        (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
          ((tshiftTm (weakenCutoffty c8 k4) (shiftTm (weakenCutofftm C0 k4) s)) =
          (shiftTm (weakenCutofftm C0 k4) (tshiftTm (weakenCutoffty c8 k4) s))))).
    Proof.
      pose proof (tshift_shift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_shift0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
          ((tshiftRec (weakenCutoffty c8 k4) (shiftRec (weakenCutofftm C0 k4) ss)) =
          (shiftRec (weakenCutofftm C0 k4) (tshiftRec (weakenCutoffty c8 k4) ss))))).
    Proof.
      pose proof (tshift_shift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_tshift0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s : Tm) =>
      (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
        ((tshiftTm (weakenCutoffty (CS c8) k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
        (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c8 k4) s))))) (fun (ss : Rec) =>
      (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
        ((tshiftRec (weakenCutoffty (CS c8) k4) (tshiftRec (weakenCutoffty C0 k4) ss)) =
        (tshiftRec (weakenCutoffty C0 k4) (tshiftRec (weakenCutoffty c8 k4) ss))))) (fun (x10 : (Index tm)) =>
      (fun (k4 : Hvl) (c8 : (Cutoff ty)) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 abs (let IHT5 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT5 k4 c8)) (IHt35 (HS tm k4) c8))) (fun (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 app (IHt35 k4 c8) (IHt36 k4 c8))) (fun (T : Ty) (t : Tm) IHt35 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 tabs (let IHT5 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT5 k4 c8)) (IHt35 (HS ty k4) c8))) (fun (t : Tm) IHt35 (T : Ty) (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 tapp (IHt35 k4 c8) (let IHT5 := (tshift_tshift0_Ty_comm_ind T) in
      (IHT5 k4 c8)))) (fun (ts : Rec) IHts7 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal rec (IHts7 k4 c8))) (fun (t : Tm) IHt35 (l : Lab) (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal2 prj (IHt35 k4 c8) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt35 (t2 : Tm) IHt36 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal3 lett (let IHp := (tshift_tshift0_Pat_comm_ind p) in
      (IHp k4 c8)) (IHt35 k4 c8) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenCutoffty_append (CS c8) k4 (bindPat p))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k4 (bindPat p)) eq_refl)) (eq_trans (IHt36 (appendHvl k4 (bindPat p)) c8) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k4 (bindPat p))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c8 k4 (bindPat p))) eq_refl)))))) (fun (k4 : Hvl) (c8 : (Cutoff ty)) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt35 (ts : Rec) IHts7 (k4 : Hvl) (c8 : (Cutoff ty)) =>
      (f_equal3 rcons eq_refl (IHt35 k4 c8) (IHts7 k4 c8)))).
    Lemma tshift_tshift0_Tm_comm_ind  :
      (forall (s : Tm) ,
        (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
          ((tshiftTm (weakenCutoffty (CS c8) k4) (tshiftTm (weakenCutoffty C0 k4) s)) =
          (tshiftTm (weakenCutoffty C0 k4) (tshiftTm (weakenCutoffty c8 k4) s))))).
    Proof.
      pose proof (tshift_tshift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_tshift0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k4 : Hvl) (c8 : (Cutoff ty)) ,
          ((tshiftRec (weakenCutoffty (CS c8) k4) (tshiftRec (weakenCutoffty C0 k4) ss)) =
          (tshiftRec (weakenCutoffty C0 k4) (tshiftRec (weakenCutoffty c8 k4) ss))))).
    Proof.
      pose proof (tshift_tshift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_TRec_comm (SS : TRec) : (forall (c8 : (Cutoff ty)) ,
      ((tshiftTRec (CS c8) (tshiftTRec C0 SS)) =
      (tshiftTRec C0 (tshiftTRec c8 SS)))) := (tshift_tshift0_TRec_comm_ind SS H0).
    Definition tshift_tshift0_Ty_comm (S4 : Ty) : (forall (c8 : (Cutoff ty)) ,
      ((tshiftTy (CS c8) (tshiftTy C0 S4)) =
      (tshiftTy C0 (tshiftTy c8 S4)))) := (tshift_tshift0_Ty_comm_ind S4 H0).
    Definition tshift_tshift0_Pat_comm (p8 : Pat) : (forall (c8 : (Cutoff ty)) ,
      ((tshiftPat (CS c8) (tshiftPat C0 p8)) =
      (tshiftPat C0 (tshiftPat c8 p8)))) := (tshift_tshift0_Pat_comm_ind p8 H0).
    Definition tshift_tshift0_PRec_comm (ps5 : PRec) : (forall (c8 : (Cutoff ty)) ,
      ((tshiftPRec (CS c8) (tshiftPRec C0 ps5)) =
      (tshiftPRec C0 (tshiftPRec c8 ps5)))) := (tshift_tshift0_PRec_comm_ind ps5 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c8 : (Cutoff tm)) ,
      ((shiftTm (CS c8) (shiftTm C0 s)) =
      (shiftTm C0 (shiftTm c8 s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_shift0_Rec_comm (ss : Rec) : (forall (c8 : (Cutoff tm)) ,
      ((shiftRec (CS c8) (shiftRec C0 ss)) =
      (shiftRec C0 (shiftRec c8 ss)))) := (shift_shift0_Rec_comm_ind ss H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c8 : (Cutoff tm)) ,
      ((shiftTm c8 (tshiftTm C0 s)) =
      (tshiftTm C0 (shiftTm c8 s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Rec_comm (ss : Rec) : (forall (c8 : (Cutoff tm)) ,
      ((shiftRec c8 (tshiftRec C0 ss)) =
      (tshiftRec C0 (shiftRec c8 ss)))) := (shift_tshift0_Rec_comm_ind ss H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c8 : (Cutoff ty)) ,
      ((tshiftTm c8 (shiftTm C0 s)) =
      (shiftTm C0 (tshiftTm c8 s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Rec_comm (ss : Rec) : (forall (c8 : (Cutoff ty)) ,
      ((tshiftRec c8 (shiftRec C0 ss)) =
      (shiftRec C0 (tshiftRec c8 ss)))) := (tshift_shift0_Rec_comm_ind ss H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c8 : (Cutoff ty)) ,
      ((tshiftTm (CS c8) (tshiftTm C0 s)) =
      (tshiftTm C0 (tshiftTm c8 s)))) := (tshift_tshift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Rec_comm (ss : Rec) : (forall (c8 : (Cutoff ty)) ,
      ((tshiftRec (CS c8) (tshiftRec C0 ss)) =
      (tshiftRec C0 (tshiftRec c8 ss)))) := (tshift_tshift0_Rec_comm_ind ss H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite tshift_tshift0_PRec_comm tshift_tshift0_Pat_comm shift_shift0_Rec_comm shift_tshift0_Rec_comm tshift_shift0_Rec_comm tshift_tshift0_Rec_comm tshift_tshift0_TRec_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite tshift_tshift0_PRec_comm tshift_tshift0_Pat_comm shift_shift0_Rec_comm shift_tshift0_Rec_comm tshift_shift0_Rec_comm tshift_tshift0_Rec_comm tshift_tshift0_TRec_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTRec_tshiftTRec  :
    (forall (k87 : Hvl) (c13 : (Cutoff ty)) (SS : TRec) ,
      ((weakenTRec (tshiftTRec c13 SS) k87) =
      (tshiftTRec (weakenCutoffty c13 k87) (weakenTRec SS k87)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_tshiftTy  :
    (forall (k87 : Hvl) (c13 : (Cutoff ty)) (S65 : Ty) ,
      ((weakenTy (tshiftTy c13 S65) k87) =
      (tshiftTy (weakenCutoffty c13 k87) (weakenTy S65 k87)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenPat_tshiftPat  :
    (forall (k87 : Hvl) (c13 : (Cutoff ty)) (p26 : Pat) ,
      ((weakenPat (tshiftPat c13 p26) k87) =
      (tshiftPat (weakenCutoffty c13 k87) (weakenPat p26 k87)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenPRec_tshiftPRec  :
    (forall (k87 : Hvl) (c13 : (Cutoff ty)) (ps15 : PRec) ,
      ((weakenPRec (tshiftPRec c13 ps15) k87) =
      (tshiftPRec (weakenCutoffty c13 k87) (weakenPRec ps15 k87)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k87 : Hvl) (c13 : (Cutoff tm)) (s24 : Tm) ,
      ((weakenTm (shiftTm c13 s24) k87) =
      (shiftTm (weakenCutofftm c13 k87) (weakenTm s24 k87)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenRec_shiftRec  :
    (forall (k87 : Hvl) (c13 : (Cutoff tm)) (ss : Rec) ,
      ((weakenRec (shiftRec c13 ss) k87) =
      (shiftRec (weakenCutofftm c13 k87) (weakenRec ss k87)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k87 : Hvl) (c13 : (Cutoff ty)) (s24 : Tm) ,
      ((weakenTm (tshiftTm c13 s24) k87) =
      (tshiftTm (weakenCutoffty c13 k87) (weakenTm s24 k87)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenRec_tshiftRec  :
    (forall (k87 : Hvl) (c13 : (Cutoff ty)) (ss : Rec) ,
      ((weakenRec (tshiftRec c13 ss) k87) =
      (tshiftRec (weakenCutoffty c13 k87) (weakenRec ss k87)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c8 : (Cutoff tm)) (s0 : Tm) :
      (forall (k7 : Hvl) (x16 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c8 k7) (substIndex (weakenTrace X0 k7) s0 x16)) =
        (substIndex (weakenTrace X0 k7) (shiftTm c8 s0) (shiftIndex (weakenCutofftm (CS c8) k7) x16)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c8 : (Cutoff ty)) (s0 : Tm) :
      (forall (k7 : Hvl) (x16 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c8 k7) (substIndex (weakenTrace X0 k7) s0 x16)) =
        (substIndex (weakenTrace X0 k7) (tshiftTm c8 s0) x16))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c8 : (Cutoff ty)) (S6 : Ty) :
      (forall (k7 : Hvl) (X14 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c8 k7) (tsubstIndex (weakenTrace X0 k7) S6 X14)) =
        (tsubstIndex (weakenTrace X0 k7) (tshiftTy c8 S6) (tshiftIndex (weakenCutoffty (CS c8) k7) X14)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Definition tshift_tsubst0_TRec_Ty_comm_ind := (ind_TRec_Ty (fun (SS : TRec) =>
      (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
        ((tshiftTRec (weakenCutoffty c13 k12) (tsubstTRec (weakenTrace X0 k12) S9 SS)) =
        (tsubstTRec (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftTRec (weakenCutoffty (CS c13) k12) SS))))) (fun (S9 : Ty) =>
      (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S10 : Ty) ,
        ((tshiftTy (weakenCutoffty c13 k12) (tsubstTy (weakenTrace X0 k12) S10 S9)) =
        (tsubstTy (weakenTrace X0 k12) (tshiftTy c13 S10) (tshiftTy (weakenCutoffty (CS c13) k12) S9))))) (fun (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      eq_refl) (fun (l : Lab) (T : Ty) IHT5 (TS : TRec) IHTS5 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal3 tcons eq_refl (IHT5 k12 c13 S9) (IHTS5 k12 c13 S9))) (fun (X21 : (Index ty)) =>
      (fun (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
        (tshiftTy_tsubstIndex0_comm_ind c13 S9 k12 X21))) (fun (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal2 tarr (IHT5 k12 c13 S9) (IHT6 k12 c13 S9))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal2 tall (IHT5 k12 c13 S9) (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT6 (HS ty k12) c13 S9) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (TS : TRec) IHTS5 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal trec (IHTS5 k12 c13 S9)))).
    Lemma tshift_tsubst0_TRec_comm_ind  :
      (forall (SS : TRec) ,
        (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
          ((tshiftTRec (weakenCutoffty c13 k12) (tsubstTRec (weakenTrace X0 k12) S9 SS)) =
          (tsubstTRec (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftTRec (weakenCutoffty (CS c13) k12) SS))))).
    Proof.
      pose proof (tshift_tsubst0_TRec_Ty_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_tsubst0_Ty_comm_ind  :
      (forall (S9 : Ty) ,
        (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S10 : Ty) ,
          ((tshiftTy (weakenCutoffty c13 k12) (tsubstTy (weakenTrace X0 k12) S10 S9)) =
          (tsubstTy (weakenTrace X0 k12) (tshiftTy c13 S10) (tshiftTy (weakenCutoffty (CS c13) k12) S9))))).
    Proof.
      pose proof (tshift_tsubst0_TRec_Ty_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_tsubst0_Pat_PRec_comm_ind := (ind_Pat_PRec (fun (p16 : Pat) =>
      (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
        ((tshiftPat (weakenCutoffty c13 k12) (tsubstPat (weakenTrace X0 k12) S9 p16)) =
        (tsubstPat (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftPat (weakenCutoffty (CS c13) k12) p16))))) (fun (ps9 : PRec) =>
      (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
        ((tshiftPRec (weakenCutoffty c13 k12) (tsubstPRec (weakenTrace X0 k12) S9 ps9)) =
        (tsubstPRec (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftPRec (weakenCutoffty (CS c13) k12) ps9))))) (fun (T : Ty) (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal pvar (let IHT5 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT5 k12 c13 S9)))) (fun (ps : PRec) IHps (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal prec (IHps k12 c13 S9))) (fun (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      eq_refl) (fun (l : Lab) (p : Pat) IHp (ps : PRec) IHps (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal3 pcons eq_refl (IHp k12 c13 S9) (IHps k12 c13 S9)))).
    Lemma tshift_tsubst0_Pat_comm_ind  :
      (forall (p16 : Pat) ,
        (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
          ((tshiftPat (weakenCutoffty c13 k12) (tsubstPat (weakenTrace X0 k12) S9 p16)) =
          (tsubstPat (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftPat (weakenCutoffty (CS c13) k12) p16))))).
    Proof.
      pose proof (tshift_tsubst0_Pat_PRec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_tsubst0_PRec_comm_ind  :
      (forall (ps9 : PRec) ,
        (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
          ((tshiftPRec (weakenCutoffty c13 k12) (tsubstPRec (weakenTrace X0 k12) S9 ps9)) =
          (tsubstPRec (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftPRec (weakenCutoffty (CS c13) k12) ps9))))).
    Proof.
      pose proof (tshift_tsubst0_Pat_PRec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition shift_subst0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c13 : (Cutoff tm)) (s3 : Tm) ,
        ((shiftTm (weakenCutofftm c13 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (shiftTm c13 s3) (shiftTm (weakenCutofftm (CS c13) k12) s2))))) (fun (ss : Rec) =>
      (forall (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) ,
        ((shiftRec (weakenCutofftm c13 k12) (substRec (weakenTrace X0 k12) s2 ss)) =
        (substRec (weakenTrace X0 k12) (shiftTm c13 s2) (shiftRec (weakenCutofftm (CS c13) k12) ss))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
        (shiftTm_substIndex0_comm_ind c13 s2 k12 x29))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c13 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 app (IHt89 k12 c13 s2) (IHt90 k12 c13 s2))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c13 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 tapp (IHt89 k12 c13 s2) eq_refl)) (fun (ts : Rec) IHts19 (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal rec (IHts19 k12 c13 s2))) (fun (t : Tm) IHt89 (l : Lab) (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal2 prj (IHt89 k12 c13 s2) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal3 lett eq_refl (IHt89 k12 c13 s2) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append c13 k12 (bindPat p)) (f_equal3 substTm (weakenTrace_append tm X0 k12 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt90 (appendHvl k12 (bindPat p)) c13 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (bindPat p))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c13) k12 (bindPat p))) eq_refl)))))) (fun (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt89 (ts : Rec) IHts19 (k12 : Hvl) (c13 : (Cutoff tm)) (s2 : Tm) =>
      (f_equal3 rcons eq_refl (IHt89 k12 c13 s2) (IHts19 k12 c13 s2)))).
    Lemma shift_subst0_Tm_comm_ind  :
      (forall (s2 : Tm) ,
        (forall (k12 : Hvl) (c13 : (Cutoff tm)) (s3 : Tm) ,
          ((shiftTm (weakenCutofftm c13 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
          (substTm (weakenTrace X0 k12) (shiftTm c13 s3) (shiftTm (weakenCutofftm (CS c13) k12) s2))))).
    Proof.
      pose proof (shift_subst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma shift_subst0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k12 : Hvl) (c13 : (Cutoff tm)) (s3 : Tm) ,
          ((shiftRec (weakenCutofftm c13 k12) (substRec (weakenTrace X0 k12) s3 ss)) =
          (substRec (weakenTrace X0 k12) (shiftTm c13 s3) (shiftRec (weakenCutofftm (CS c13) k12) ss))))).
    Proof.
      pose proof (shift_subst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition shift_tsubst0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) ,
        ((shiftTm (weakenCutofftm c13 k12) (tsubstTm (weakenTrace X0 k12) S9 s2)) =
        (tsubstTm (weakenTrace X0 k12) S9 (shiftTm (weakenCutofftm c13 k12) s2))))) (fun (ss : Rec) =>
      (forall (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) ,
        ((shiftRec (weakenCutofftm c13 k12) (tsubstRec (weakenTrace X0 k12) S9 ss)) =
        (tsubstRec (weakenTrace X0 k12) S9 (shiftRec (weakenCutofftm c13 k12) ss))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c13 S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
      (f_equal2 app (IHt89 k12 c13 S9) (IHt90 k12 c13 S9))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c13 S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
      (f_equal2 tapp (IHt89 k12 c13 S9) eq_refl)) (fun (ts : Rec) IHts19 (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
      (f_equal rec (IHts19 k12 c13 S9))) (fun (t : Tm) IHt89 (l : Lab) (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
      (f_equal2 prj (IHt89 k12 c13 S9) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
      (f_equal3 lett eq_refl (IHt89 k12 c13 S9) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenCutofftm_append c13 k12 (bindPat p))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt90 (appendHvl k12 (bindPat p)) c13 S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (bindPat p))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c13 k12 (bindPat p))) eq_refl)))))) (fun (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt89 (ts : Rec) IHts19 (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) =>
      (f_equal3 rcons eq_refl (IHt89 k12 c13 S9) (IHts19 k12 c13 S9)))).
    Lemma shift_tsubst0_Tm_comm_ind  :
      (forall (s2 : Tm) ,
        (forall (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) ,
          ((shiftTm (weakenCutofftm c13 k12) (tsubstTm (weakenTrace X0 k12) S9 s2)) =
          (tsubstTm (weakenTrace X0 k12) S9 (shiftTm (weakenCutofftm c13 k12) s2))))).
    Proof.
      pose proof (shift_tsubst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma shift_tsubst0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k12 : Hvl) (c13 : (Cutoff tm)) (S9 : Ty) ,
          ((shiftRec (weakenCutofftm c13 k12) (tsubstRec (weakenTrace X0 k12) S9 ss)) =
          (tsubstRec (weakenTrace X0 k12) S9 (shiftRec (weakenCutofftm c13 k12) ss))))).
    Proof.
      pose proof (shift_tsubst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_subst0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c13 : (Cutoff ty)) (s3 : Tm) ,
        ((tshiftTm (weakenCutoffty c13 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
        (substTm (weakenTrace X0 k12) (tshiftTm c13 s3) (tshiftTm (weakenCutoffty c13 k12) s2))))) (fun (ss : Rec) =>
      (forall (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) ,
        ((tshiftRec (weakenCutoffty c13 k12) (substRec (weakenTrace X0 k12) s2 ss)) =
        (substRec (weakenTrace X0 k12) (tshiftTm c13 s2) (tshiftRec (weakenCutoffty c13 k12) ss))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
        (tshiftTm_substIndex0_comm_ind c13 s2 k12 x29))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c13 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 app (IHt89 k12 c13 s2) (IHt90 k12 c13 s2))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c13 s2) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 tapp (IHt89 k12 c13 s2) eq_refl)) (fun (ts : Rec) IHts19 (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal rec (IHts19 k12 c13 s2))) (fun (t : Tm) IHt89 (l : Lab) (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal2 prj (IHt89 k12 c13 s2) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal3 lett eq_refl (IHt89 k12 c13 s2) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c13 k12 (bindPat p)) (f_equal3 substTm (weakenTrace_append tm X0 k12 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt90 (appendHvl k12 (bindPat p)) c13 s2) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k12 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c13 k12 (bindPat p))) eq_refl)))))) (fun (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt89 (ts : Rec) IHts19 (k12 : Hvl) (c13 : (Cutoff ty)) (s2 : Tm) =>
      (f_equal3 rcons eq_refl (IHt89 k12 c13 s2) (IHts19 k12 c13 s2)))).
    Lemma tshift_subst0_Tm_comm_ind  :
      (forall (s2 : Tm) ,
        (forall (k12 : Hvl) (c13 : (Cutoff ty)) (s3 : Tm) ,
          ((tshiftTm (weakenCutoffty c13 k12) (substTm (weakenTrace X0 k12) s3 s2)) =
          (substTm (weakenTrace X0 k12) (tshiftTm c13 s3) (tshiftTm (weakenCutoffty c13 k12) s2))))).
    Proof.
      pose proof (tshift_subst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_subst0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k12 : Hvl) (c13 : (Cutoff ty)) (s3 : Tm) ,
          ((tshiftRec (weakenCutoffty c13 k12) (substRec (weakenTrace X0 k12) s3 ss)) =
          (substRec (weakenTrace X0 k12) (tshiftTm c13 s3) (tshiftRec (weakenCutoffty c13 k12) ss))))).
    Proof.
      pose proof (tshift_subst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tshift_tsubst0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s2 : Tm) =>
      (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
        ((tshiftTm (weakenCutoffty c13 k12) (tsubstTm (weakenTrace X0 k12) S9 s2)) =
        (tsubstTm (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftTm (weakenCutoffty (CS c13) k12) s2))))) (fun (ss : Rec) =>
      (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
        ((tshiftRec (weakenCutoffty c13 k12) (tsubstRec (weakenTrace X0 k12) S9 ss)) =
        (tsubstRec (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftRec (weakenCutoffty (CS c13) k12) ss))))) (fun (x29 : (Index tm)) =>
      (fun (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal2 abs (let IHT5 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT5 k12 c13 S9)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS tm k12) c13 S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal2 app (IHt89 k12 c13 S9) (IHt90 k12 c13 S9))) (fun (T : Ty) (t : Tm) IHt89 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal2 tabs (let IHT5 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT5 k12 c13 S9)) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt89 (HS ty k12) c13 S9) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k12 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt89 (T : Ty) (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal2 tapp (IHt89 k12 c13 S9) (let IHT5 := (tshift_tsubst0_Ty_comm_ind T) in
      (IHT5 k12 c13 S9)))) (fun (ts : Rec) IHts19 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal rec (IHts19 k12 c13 S9))) (fun (t : Tm) IHt89 (l : Lab) (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal2 prj (IHt89 k12 c13 S9) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt89 (t2 : Tm) IHt90 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal3 lett (let IHp := (tshift_tsubst0_Pat_comm_ind p) in
      (IHp k12 c13 S9)) (IHt89 k12 c13 S9) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenCutoffty_append c13 k12 (bindPat p))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k12 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt90 (appendHvl k12 (bindPat p)) c13 S9) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k12 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0)))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append (CS c13) k12 (bindPat p))) eq_refl)))))) (fun (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt89 (ts : Rec) IHts19 (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) =>
      (f_equal3 rcons eq_refl (IHt89 k12 c13 S9) (IHts19 k12 c13 S9)))).
    Lemma tshift_tsubst0_Tm_comm_ind  :
      (forall (s2 : Tm) ,
        (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
          ((tshiftTm (weakenCutoffty c13 k12) (tsubstTm (weakenTrace X0 k12) S9 s2)) =
          (tsubstTm (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftTm (weakenCutoffty (CS c13) k12) s2))))).
    Proof.
      pose proof (tshift_tsubst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tshift_tsubst0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k12 : Hvl) (c13 : (Cutoff ty)) (S9 : Ty) ,
          ((tshiftRec (weakenCutoffty c13 k12) (tsubstRec (weakenTrace X0 k12) S9 ss)) =
          (tsubstRec (weakenTrace X0 k12) (tshiftTy c13 S9) (tshiftRec (weakenCutoffty (CS c13) k12) ss))))).
    Proof.
      pose proof (tshift_tsubst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTRec_tsubstTRec0_comm (SS : TRec) : (forall (c13 : (Cutoff ty)) (S9 : Ty) ,
      ((tshiftTRec c13 (tsubstTRec X0 S9 SS)) =
      (tsubstTRec X0 (tshiftTy c13 S9) (tshiftTRec (CS c13) SS)))) := (tshift_tsubst0_TRec_comm_ind SS H0).
    Definition tshiftTy_tsubstTy0_comm (S10 : Ty) : (forall (c13 : (Cutoff ty)) (S9 : Ty) ,
      ((tshiftTy c13 (tsubstTy X0 S9 S10)) =
      (tsubstTy X0 (tshiftTy c13 S9) (tshiftTy (CS c13) S10)))) := (tshift_tsubst0_Ty_comm_ind S10 H0).
    Definition tshiftPat_tsubstPat0_comm (p16 : Pat) : (forall (c13 : (Cutoff ty)) (S9 : Ty) ,
      ((tshiftPat c13 (tsubstPat X0 S9 p16)) =
      (tsubstPat X0 (tshiftTy c13 S9) (tshiftPat (CS c13) p16)))) := (tshift_tsubst0_Pat_comm_ind p16 H0).
    Definition tshiftPRec_tsubstPRec0_comm (ps9 : PRec) : (forall (c13 : (Cutoff ty)) (S9 : Ty) ,
      ((tshiftPRec c13 (tsubstPRec X0 S9 ps9)) =
      (tsubstPRec X0 (tshiftTy c13 S9) (tshiftPRec (CS c13) ps9)))) := (tshift_tsubst0_PRec_comm_ind ps9 H0).
    Definition shiftTm_substTm0_comm (s3 : Tm) : (forall (c13 : (Cutoff tm)) (s2 : Tm) ,
      ((shiftTm c13 (substTm X0 s2 s3)) =
      (substTm X0 (shiftTm c13 s2) (shiftTm (CS c13) s3)))) := (shift_subst0_Tm_comm_ind s3 H0).
    Definition shiftRec_substRec0_comm (ss : Rec) : (forall (c13 : (Cutoff tm)) (s2 : Tm) ,
      ((shiftRec c13 (substRec X0 s2 ss)) =
      (substRec X0 (shiftTm c13 s2) (shiftRec (CS c13) ss)))) := (shift_subst0_Rec_comm_ind ss H0).
    Definition shiftTm_tsubstTm0_comm (s2 : Tm) : (forall (c13 : (Cutoff tm)) (S9 : Ty) ,
      ((shiftTm c13 (tsubstTm X0 S9 s2)) =
      (tsubstTm X0 S9 (shiftTm c13 s2)))) := (shift_tsubst0_Tm_comm_ind s2 H0).
    Definition shiftRec_tsubstRec0_comm (ss : Rec) : (forall (c13 : (Cutoff tm)) (S9 : Ty) ,
      ((shiftRec c13 (tsubstRec X0 S9 ss)) =
      (tsubstRec X0 S9 (shiftRec c13 ss)))) := (shift_tsubst0_Rec_comm_ind ss H0).
    Definition tshiftTm_substTm0_comm (s3 : Tm) : (forall (c13 : (Cutoff ty)) (s2 : Tm) ,
      ((tshiftTm c13 (substTm X0 s2 s3)) =
      (substTm X0 (tshiftTm c13 s2) (tshiftTm c13 s3)))) := (tshift_subst0_Tm_comm_ind s3 H0).
    Definition tshiftRec_substRec0_comm (ss : Rec) : (forall (c13 : (Cutoff ty)) (s2 : Tm) ,
      ((tshiftRec c13 (substRec X0 s2 ss)) =
      (substRec X0 (tshiftTm c13 s2) (tshiftRec c13 ss)))) := (tshift_subst0_Rec_comm_ind ss H0).
    Definition tshiftTm_tsubstTm0_comm (s2 : Tm) : (forall (c13 : (Cutoff ty)) (S9 : Ty) ,
      ((tshiftTm c13 (tsubstTm X0 S9 s2)) =
      (tsubstTm X0 (tshiftTy c13 S9) (tshiftTm (CS c13) s2)))) := (tshift_tsubst0_Tm_comm_ind s2 H0).
    Definition tshiftRec_tsubstRec0_comm (ss : Rec) : (forall (c13 : (Cutoff ty)) (S9 : Ty) ,
      ((tshiftRec c13 (tsubstRec X0 S9 ss)) =
      (tsubstRec X0 (tshiftTy c13 S9) (tshiftRec (CS c13) ss)))) := (tshift_tsubst0_Rec_comm_ind ss H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d3 : (Trace tm)) (s2 : Tm) :
      (forall (k12 : Hvl) (x29 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d3) k12) s2 (shiftIndex (weakenCutofftm C0 k12) x29)) =
        (shiftTm (weakenCutofftm C0 k12) (substIndex (weakenTrace d3 k12) s2 x29)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d3 : (Trace tm)) (s2 : Tm) :
      (forall (k12 : Hvl) (x29 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d3) k12) s2 x29) =
        (tshiftTm (weakenCutoffty C0 k12) (substIndex (weakenTrace d3 k12) s2 x29)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d3 : (Trace ty)) (S9 : Ty) :
      (forall (k12 : Hvl) (X21 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d3) k12) S9 X21) =
        (tsubstIndex (weakenTrace d3 k12) S9 X21))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d3 : (Trace ty)) (S9 : Ty) :
      (forall (k12 : Hvl) (X21 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d3) k12) S9 (tshiftIndex (weakenCutoffty C0 k12) X21)) =
        (tshiftTy (weakenCutoffty C0 k12) (tsubstIndex (weakenTrace d3 k12) S9 X21)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Definition tsubst_tshift0_TRec_Ty_comm_ind := (ind_TRec_Ty (fun (SS : TRec) =>
      (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
        ((tsubstTRec (weakenTrace (XS ty d54) k63) S40 (tshiftTRec (weakenCutoffty C0 k63) SS)) =
        (tshiftTRec (weakenCutoffty C0 k63) (tsubstTRec (weakenTrace d54 k63) S40 SS))))) (fun (S40 : Ty) =>
      (forall (k63 : Hvl) (d54 : (Trace ty)) (S41 : Ty) ,
        ((tsubstTy (weakenTrace (XS ty d54) k63) S41 (tshiftTy (weakenCutoffty C0 k63) S40)) =
        (tshiftTy (weakenCutoffty C0 k63) (tsubstTy (weakenTrace d54 k63) S41 S40))))) (fun (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      eq_refl) (fun (l : Lab) (T : Ty) IHT5 (TS : TRec) IHTS7 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal3 tcons eq_refl (IHT5 k63 d54 S40) (IHTS7 k63 d54 S40))) (fun (X28 : (Index ty)) =>
      (fun (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
        (tsubstIndex_tshiftTy0_comm_ind d54 S40 k63 X28))) (fun (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 tarr (IHT5 k63 d54 S40) (IHT6 k63 d54 S40))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 tall (IHT5 k63 d54 S40) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d54) k63 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT6 (HS ty k63) d54 S40) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d54 k63 (HS ty H0))) eq_refl eq_refl)))))) (fun (TS : TRec) IHTS7 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal trec (IHTS7 k63 d54 S40)))).
    Lemma tsubst_tshift0_TRec_comm_ind  :
      (forall (SS : TRec) ,
        (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
          ((tsubstTRec (weakenTrace (XS ty d54) k63) S40 (tshiftTRec (weakenCutoffty C0 k63) SS)) =
          (tshiftTRec (weakenCutoffty C0 k63) (tsubstTRec (weakenTrace d54 k63) S40 SS))))).
    Proof.
      pose proof (tsubst_tshift0_TRec_Ty_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tshift0_Ty_comm_ind  :
      (forall (S40 : Ty) ,
        (forall (k63 : Hvl) (d54 : (Trace ty)) (S41 : Ty) ,
          ((tsubstTy (weakenTrace (XS ty d54) k63) S41 (tshiftTy (weakenCutoffty C0 k63) S40)) =
          (tshiftTy (weakenCutoffty C0 k63) (tsubstTy (weakenTrace d54 k63) S41 S40))))).
    Proof.
      pose proof (tsubst_tshift0_TRec_Ty_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_tshift0_Pat_PRec_comm_ind := (ind_Pat_PRec (fun (p21 : Pat) =>
      (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
        ((tsubstPat (weakenTrace (XS ty d54) k63) S40 (tshiftPat (weakenCutoffty C0 k63) p21)) =
        (tshiftPat (weakenCutoffty C0 k63) (tsubstPat (weakenTrace d54 k63) S40 p21))))) (fun (ps11 : PRec) =>
      (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
        ((tsubstPRec (weakenTrace (XS ty d54) k63) S40 (tshiftPRec (weakenCutoffty C0 k63) ps11)) =
        (tshiftPRec (weakenCutoffty C0 k63) (tsubstPRec (weakenTrace d54 k63) S40 ps11))))) (fun (T : Ty) (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal pvar (let IHT5 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT5 k63 d54 S40)))) (fun (ps : PRec) IHps (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal prec (IHps k63 d54 S40))) (fun (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      eq_refl) (fun (l : Lab) (p : Pat) IHp (ps : PRec) IHps (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal3 pcons eq_refl (IHp k63 d54 S40) (IHps k63 d54 S40)))).
    Lemma tsubst_tshift0_Pat_comm_ind  :
      (forall (p21 : Pat) ,
        (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
          ((tsubstPat (weakenTrace (XS ty d54) k63) S40 (tshiftPat (weakenCutoffty C0 k63) p21)) =
          (tshiftPat (weakenCutoffty C0 k63) (tsubstPat (weakenTrace d54 k63) S40 p21))))).
    Proof.
      pose proof (tsubst_tshift0_Pat_PRec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tshift0_PRec_comm_ind  :
      (forall (ps11 : PRec) ,
        (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
          ((tsubstPRec (weakenTrace (XS ty d54) k63) S40 (tshiftPRec (weakenCutoffty C0 k63) ps11)) =
          (tshiftPRec (weakenCutoffty C0 k63) (tsubstPRec (weakenTrace d54 k63) S40 ps11))))).
    Proof.
      pose proof (tsubst_tshift0_Pat_PRec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition subst_shift0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s22 : Tm) =>
      (forall (k63 : Hvl) (d54 : (Trace tm)) (s23 : Tm) ,
        ((substTm (weakenTrace (XS tm d54) k63) s23 (shiftTm (weakenCutofftm C0 k63) s22)) =
        (shiftTm (weakenCutofftm C0 k63) (substTm (weakenTrace d54 k63) s23 s22))))) (fun (ss : Rec) =>
      (forall (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) ,
        ((substRec (weakenTrace (XS tm d54) k63) s22 (shiftRec (weakenCutofftm C0 k63) ss)) =
        (shiftRec (weakenCutofftm C0 k63) (substRec (weakenTrace d54 k63) s22 ss))))) (fun (x42 : (Index tm)) =>
      (fun (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
        (substIndex_shiftTm0_comm_ind d54 s22 k63 x42))) (fun (T : Ty) (t : Tm) IHt125 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d54) k63 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k63) d54 s22) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d54 k63 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 app (IHt125 k63 d54 s22) (IHt126 k63 d54 s22))) (fun (T : Ty) (t : Tm) IHt125 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d54) k63 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k63) d54 s22) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d54 k63 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 tapp (IHt125 k63 d54 s22) eq_refl)) (fun (ts : Rec) IHts27 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal rec (IHts27 k63 d54 s22))) (fun (t : Tm) IHt125 (l : Lab) (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 prj (IHt125 k63 d54 s22) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal3 lett eq_refl (IHt125 k63 d54 s22) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d54) k63 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k63 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k63 (bindPat p)) d54 s22) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k63 (bindPat p))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d54 k63 (bindPat p))) eq_refl eq_refl)))))) (fun (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt125 (ts : Rec) IHts27 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal3 rcons eq_refl (IHt125 k63 d54 s22) (IHts27 k63 d54 s22)))).
    Lemma subst_shift0_Tm_comm_ind  :
      (forall (s22 : Tm) ,
        (forall (k63 : Hvl) (d54 : (Trace tm)) (s23 : Tm) ,
          ((substTm (weakenTrace (XS tm d54) k63) s23 (shiftTm (weakenCutofftm C0 k63) s22)) =
          (shiftTm (weakenCutofftm C0 k63) (substTm (weakenTrace d54 k63) s23 s22))))).
    Proof.
      pose proof (subst_shift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma subst_shift0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k63 : Hvl) (d54 : (Trace tm)) (s23 : Tm) ,
          ((substRec (weakenTrace (XS tm d54) k63) s23 (shiftRec (weakenCutofftm C0 k63) ss)) =
          (shiftRec (weakenCutofftm C0 k63) (substRec (weakenTrace d54 k63) s23 ss))))).
    Proof.
      pose proof (subst_shift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition subst_tshift0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s22 : Tm) =>
      (forall (k63 : Hvl) (d54 : (Trace tm)) (s23 : Tm) ,
        ((substTm (weakenTrace (XS ty d54) k63) s23 (tshiftTm (weakenCutoffty C0 k63) s22)) =
        (tshiftTm (weakenCutoffty C0 k63) (substTm (weakenTrace d54 k63) s23 s22))))) (fun (ss : Rec) =>
      (forall (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) ,
        ((substRec (weakenTrace (XS ty d54) k63) s22 (tshiftRec (weakenCutoffty C0 k63) ss)) =
        (tshiftRec (weakenCutoffty C0 k63) (substRec (weakenTrace d54 k63) s22 ss))))) (fun (x42 : (Index tm)) =>
      (fun (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
        (substIndex_tshiftTm0_comm_ind d54 s22 k63 x42))) (fun (T : Ty) (t : Tm) IHt125 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d54) k63 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k63) d54 s22) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d54 k63 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 app (IHt125 k63 d54 s22) (IHt126 k63 d54 s22))) (fun (T : Ty) (t : Tm) IHt125 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d54) k63 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k63) d54 s22) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d54 k63 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 tapp (IHt125 k63 d54 s22) eq_refl)) (fun (ts : Rec) IHts27 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal rec (IHts27 k63 d54 s22))) (fun (t : Tm) IHt125 (l : Lab) (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal2 prj (IHt125 k63 d54 s22) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal3 lett eq_refl (IHt125 k63 d54 s22) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenTrace_append tm (XS ty d54) k63 (bindPat p))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k63 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k63 (bindPat p)) d54 s22) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k63 (bindPat p))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d54 k63 (bindPat p))) eq_refl eq_refl)))))) (fun (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt125 (ts : Rec) IHts27 (k63 : Hvl) (d54 : (Trace tm)) (s22 : Tm) =>
      (f_equal3 rcons eq_refl (IHt125 k63 d54 s22) (IHts27 k63 d54 s22)))).
    Lemma subst_tshift0_Tm_comm_ind  :
      (forall (s22 : Tm) ,
        (forall (k63 : Hvl) (d54 : (Trace tm)) (s23 : Tm) ,
          ((substTm (weakenTrace (XS ty d54) k63) s23 (tshiftTm (weakenCutoffty C0 k63) s22)) =
          (tshiftTm (weakenCutoffty C0 k63) (substTm (weakenTrace d54 k63) s23 s22))))).
    Proof.
      pose proof (subst_tshift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma subst_tshift0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k63 : Hvl) (d54 : (Trace tm)) (s23 : Tm) ,
          ((substRec (weakenTrace (XS ty d54) k63) s23 (tshiftRec (weakenCutoffty C0 k63) ss)) =
          (tshiftRec (weakenCutoffty C0 k63) (substRec (weakenTrace d54 k63) s23 ss))))).
    Proof.
      pose proof (subst_tshift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_shift0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s22 : Tm) =>
      (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
        ((tsubstTm (weakenTrace d54 k63) S40 (shiftTm (weakenCutofftm C0 k63) s22)) =
        (shiftTm (weakenCutofftm C0 k63) (tsubstTm (weakenTrace d54 k63) S40 s22))))) (fun (ss : Rec) =>
      (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
        ((tsubstRec (weakenTrace d54 k63) S40 (shiftRec (weakenCutofftm C0 k63) ss)) =
        (shiftRec (weakenCutofftm C0 k63) (tsubstRec (weakenTrace d54 k63) S40 ss))))) (fun (x42 : (Index tm)) =>
      (fun (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt125 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d54 k63 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k63) d54 S40) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d54 k63 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 app (IHt125 k63 d54 S40) (IHt126 k63 d54 S40))) (fun (T : Ty) (t : Tm) IHt125 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d54 k63 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k63) d54 S40) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d54 k63 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 tapp (IHt125 k63 d54 S40) eq_refl)) (fun (ts : Rec) IHts27 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal rec (IHts27 k63 d54 S40))) (fun (t : Tm) IHt125 (l : Lab) (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 prj (IHt125 k63 d54 S40) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal3 lett eq_refl (IHt125 k63 d54 S40) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d54 k63 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k63 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k63 (bindPat p)) d54 S40) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k63 (bindPat p))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d54 k63 (bindPat p))) eq_refl eq_refl)))))) (fun (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt125 (ts : Rec) IHts27 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal3 rcons eq_refl (IHt125 k63 d54 S40) (IHts27 k63 d54 S40)))).
    Lemma tsubst_shift0_Tm_comm_ind  :
      (forall (s22 : Tm) ,
        (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
          ((tsubstTm (weakenTrace d54 k63) S40 (shiftTm (weakenCutofftm C0 k63) s22)) =
          (shiftTm (weakenCutofftm C0 k63) (tsubstTm (weakenTrace d54 k63) S40 s22))))).
    Proof.
      pose proof (tsubst_shift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_shift0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
          ((tsubstRec (weakenTrace d54 k63) S40 (shiftRec (weakenCutofftm C0 k63) ss)) =
          (shiftRec (weakenCutofftm C0 k63) (tsubstRec (weakenTrace d54 k63) S40 ss))))).
    Proof.
      pose proof (tsubst_shift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_tshift0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s22 : Tm) =>
      (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
        ((tsubstTm (weakenTrace (XS ty d54) k63) S40 (tshiftTm (weakenCutoffty C0 k63) s22)) =
        (tshiftTm (weakenCutoffty C0 k63) (tsubstTm (weakenTrace d54 k63) S40 s22))))) (fun (ss : Rec) =>
      (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
        ((tsubstRec (weakenTrace (XS ty d54) k63) S40 (tshiftRec (weakenCutoffty C0 k63) ss)) =
        (tshiftRec (weakenCutoffty C0 k63) (tsubstRec (weakenTrace d54 k63) S40 ss))))) (fun (x42 : (Index tm)) =>
      (fun (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt125 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 abs (let IHT5 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT5 k63 d54 S40)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d54) k63 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS tm k63) d54 S40) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d54 k63 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 app (IHt125 k63 d54 S40) (IHt126 k63 d54 S40))) (fun (T : Ty) (t : Tm) IHt125 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 tabs (let IHT5 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT5 k63 d54 S40)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d54) k63 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt125 (HS ty k63) d54 S40) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d54 k63 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt125 (T : Ty) (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 tapp (IHt125 k63 d54 S40) (let IHT5 := (tsubst_tshift0_Ty_comm_ind T) in
      (IHT5 k63 d54 S40)))) (fun (ts : Rec) IHts27 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal rec (IHts27 k63 d54 S40))) (fun (t : Tm) IHt125 (l : Lab) (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal2 prj (IHt125 k63 d54 S40) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt125 (t2 : Tm) IHt126 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal3 lett (let IHp := (tsubst_tshift0_Pat_comm_ind p) in
      (IHp k63 d54 S40)) (IHt125 k63 d54 S40) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tshift_bindPat _ _) (eq_refl H0))) (weakenTrace_append ty (XS ty d54) k63 (bindPat p))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k63 (bindPat p)) eq_refl)) (eq_trans (IHt126 (appendHvl k63 (bindPat p)) d54 S40) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k63 (bindPat p))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d54 k63 (bindPat p))) eq_refl eq_refl)))))) (fun (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt125 (ts : Rec) IHts27 (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) =>
      (f_equal3 rcons eq_refl (IHt125 k63 d54 S40) (IHts27 k63 d54 S40)))).
    Lemma tsubst_tshift0_Tm_comm_ind  :
      (forall (s22 : Tm) ,
        (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
          ((tsubstTm (weakenTrace (XS ty d54) k63) S40 (tshiftTm (weakenCutoffty C0 k63) s22)) =
          (tshiftTm (weakenCutoffty C0 k63) (tsubstTm (weakenTrace d54 k63) S40 s22))))).
    Proof.
      pose proof (tsubst_tshift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tshift0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k63 : Hvl) (d54 : (Trace ty)) (S40 : Ty) ,
          ((tsubstRec (weakenTrace (XS ty d54) k63) S40 (tshiftRec (weakenCutoffty C0 k63) ss)) =
          (tshiftRec (weakenCutoffty C0 k63) (tsubstRec (weakenTrace d54 k63) S40 ss))))).
    Proof.
      pose proof (tsubst_tshift0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTRec_tshiftTRec0_comm (SS : TRec) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstTRec (XS ty d75) S61 (tshiftTRec C0 SS)) =
      (tshiftTRec C0 (tsubstTRec d75 S61 SS)))) := (tsubst_tshift0_TRec_comm_ind SS H0).
    Definition tsubstTy_tshiftTy0_comm (S62 : Ty) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstTy (XS ty d75) S61 (tshiftTy C0 S62)) =
      (tshiftTy C0 (tsubstTy d75 S61 S62)))) := (tsubst_tshift0_Ty_comm_ind S62 H0).
    Definition tsubstPat_tshiftPat0_comm (p23 : Pat) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstPat (XS ty d75) S61 (tshiftPat C0 p23)) =
      (tshiftPat C0 (tsubstPat d75 S61 p23)))) := (tsubst_tshift0_Pat_comm_ind p23 H0).
    Definition tsubstPRec_tshiftPRec0_comm (ps13 : PRec) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstPRec (XS ty d75) S61 (tshiftPRec C0 ps13)) =
      (tshiftPRec C0 (tsubstPRec d75 S61 ps13)))) := (tsubst_tshift0_PRec_comm_ind ps13 H0).
    Definition substTm_shiftTm0_comm (s23 : Tm) : (forall (d75 : (Trace tm)) (s22 : Tm) ,
      ((substTm (XS tm d75) s22 (shiftTm C0 s23)) =
      (shiftTm C0 (substTm d75 s22 s23)))) := (subst_shift0_Tm_comm_ind s23 H0).
    Definition substRec_shiftRec0_comm (ss : Rec) : (forall (d75 : (Trace tm)) (s22 : Tm) ,
      ((substRec (XS tm d75) s22 (shiftRec C0 ss)) =
      (shiftRec C0 (substRec d75 s22 ss)))) := (subst_shift0_Rec_comm_ind ss H0).
    Definition substTm_tshiftTm0_comm (s23 : Tm) : (forall (d75 : (Trace tm)) (s22 : Tm) ,
      ((substTm (XS ty d75) s22 (tshiftTm C0 s23)) =
      (tshiftTm C0 (substTm d75 s22 s23)))) := (subst_tshift0_Tm_comm_ind s23 H0).
    Definition substRec_tshiftRec0_comm (ss : Rec) : (forall (d75 : (Trace tm)) (s22 : Tm) ,
      ((substRec (XS ty d75) s22 (tshiftRec C0 ss)) =
      (tshiftRec C0 (substRec d75 s22 ss)))) := (subst_tshift0_Rec_comm_ind ss H0).
    Definition tsubstTm_shiftTm0_comm (s22 : Tm) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstTm d75 S61 (shiftTm C0 s22)) =
      (shiftTm C0 (tsubstTm d75 S61 s22)))) := (tsubst_shift0_Tm_comm_ind s22 H0).
    Definition tsubstRec_shiftRec0_comm (ss : Rec) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstRec d75 S61 (shiftRec C0 ss)) =
      (shiftRec C0 (tsubstRec d75 S61 ss)))) := (tsubst_shift0_Rec_comm_ind ss H0).
    Definition tsubstTm_tshiftTm0_comm (s22 : Tm) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstTm (XS ty d75) S61 (tshiftTm C0 s22)) =
      (tshiftTm C0 (tsubstTm d75 S61 s22)))) := (tsubst_tshift0_Tm_comm_ind s22 H0).
    Definition tsubstRec_tshiftRec0_comm (ss : Rec) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstRec (XS ty d75) S61 (tshiftRec C0 ss)) =
      (tshiftRec C0 (tsubstRec d75 S61 ss)))) := (tsubst_tshift0_Rec_comm_ind ss H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Definition tsubst_tm_TRec_Ty_ind := (ind_TRec_Ty (fun (SS : TRec) =>
      (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
        ((tsubstTRec (weakenTrace (XS tm d75) k84) S61 SS) =
        (tsubstTRec (weakenTrace d75 k84) S61 SS)))) (fun (S61 : Ty) =>
      (forall (k84 : Hvl) (d75 : (Trace ty)) (S62 : Ty) ,
        ((tsubstTy (weakenTrace (XS tm d75) k84) S62 S61) =
        (tsubstTy (weakenTrace d75 k84) S62 S61)))) (fun (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      eq_refl) (fun (l : Lab) (T : Ty) IHT5 (TS : TRec) IHTS9 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal3 tcons eq_refl (IHT5 k84 d75 S61) (IHTS9 k84 d75 S61))) (fun (X32 : (Index ty)) =>
      (fun (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
        (tsubstIndex_shiftTy0_comm_ind d75 S61 k84 X32))) (fun (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal2 tarr (IHT5 k84 d75 S61) (IHT6 k84 d75 S61))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal2 tall (IHT5 k84 d75 S61) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d75) k84 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHT6 (HS ty k84) d75 S61) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d75 k84 (HS ty H0))) eq_refl eq_refl))))) (fun (TS : TRec) IHTS9 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal trec (IHTS9 k84 d75 S61)))).
    Lemma tsubst_tm_TRec_ind  :
      (forall (SS : TRec) ,
        (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
          ((tsubstTRec (weakenTrace (XS tm d75) k84) S61 SS) =
          (tsubstTRec (weakenTrace d75 k84) S61 SS)))).
    Proof.
      pose proof (tsubst_tm_TRec_Ty_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tm_Ty_ind  :
      (forall (S61 : Ty) ,
        (forall (k84 : Hvl) (d75 : (Trace ty)) (S62 : Ty) ,
          ((tsubstTy (weakenTrace (XS tm d75) k84) S62 S61) =
          (tsubstTy (weakenTrace d75 k84) S62 S61)))).
    Proof.
      pose proof (tsubst_tm_TRec_Ty_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_tm_Pat_PRec_ind := (ind_Pat_PRec (fun (p23 : Pat) =>
      (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
        ((tsubstPat (weakenTrace (XS tm d75) k84) S61 p23) =
        (tsubstPat (weakenTrace d75 k84) S61 p23)))) (fun (ps13 : PRec) =>
      (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
        ((tsubstPRec (weakenTrace (XS tm d75) k84) S61 ps13) =
        (tsubstPRec (weakenTrace d75 k84) S61 ps13)))) (fun (T : Ty) (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal pvar (let IHT5 := (tsubst_tm_Ty_ind T) in
      (IHT5 k84 d75 S61)))) (fun (ps : PRec) IHps (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal prec (IHps k84 d75 S61))) (fun (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      eq_refl) (fun (l : Lab) (p : Pat) IHp (ps : PRec) IHps (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal3 pcons eq_refl (IHp k84 d75 S61) (IHps k84 d75 S61)))).
    Lemma tsubst_tm_Pat_ind  :
      (forall (p23 : Pat) ,
        (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
          ((tsubstPat (weakenTrace (XS tm d75) k84) S61 p23) =
          (tsubstPat (weakenTrace d75 k84) S61 p23)))).
    Proof.
      pose proof (tsubst_tm_Pat_PRec_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tm_PRec_ind  :
      (forall (ps13 : PRec) ,
        (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
          ((tsubstPRec (weakenTrace (XS tm d75) k84) S61 ps13) =
          (tsubstPRec (weakenTrace d75 k84) S61 ps13)))).
    Proof.
      pose proof (tsubst_tm_Pat_PRec_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_tm_Tm_Rec_ind := (ind_Tm_Rec (fun (s22 : Tm) =>
      (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
        ((tsubstTm (weakenTrace (XS tm d75) k84) S61 s22) =
        (tsubstTm (weakenTrace d75 k84) S61 s22)))) (fun (ss : Rec) =>
      (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
        ((tsubstRec (weakenTrace (XS tm d75) k84) S61 ss) =
        (tsubstRec (weakenTrace d75 k84) S61 ss)))) (fun (x46 : (Index tm)) =>
      (fun (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt134 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal2 abs (let IHT5 := (tsubst_tm_Ty_ind T) in
      (IHT5 k84 d75 S61)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d75) k84 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt134 (HS tm k84) d75 S61) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d75 k84 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt134 (t2 : Tm) IHt135 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal2 app (IHt134 k84 d75 S61) (IHt135 k84 d75 S61))) (fun (T : Ty) (t : Tm) IHt134 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal2 tabs (let IHT5 := (tsubst_tm_Ty_ind T) in
      (IHT5 k84 d75 S61)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d75) k84 (HS ty H0)) eq_refl eq_refl) (eq_trans (IHt134 (HS ty k84) d75 S61) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d75 k84 (HS ty H0))) eq_refl eq_refl))))) (fun (t : Tm) IHt134 (T : Ty) (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal2 tapp (IHt134 k84 d75 S61) (let IHT5 := (tsubst_tm_Ty_ind T) in
      (IHT5 k84 d75 S61)))) (fun (ts : Rec) IHts29 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal rec (IHts29 k84 d75 S61))) (fun (t : Tm) IHt134 (l : Lab) (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal2 prj (IHt134 k84 d75 S61) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt134 (t2 : Tm) IHt135 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal3 lett (let IHp := (tsubst_tm_Pat_ind p) in
      (IHp k84 d75 S61)) (IHt134 k84 d75 S61) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d75) k84 (bindPat p)) eq_refl eq_refl) (eq_trans (IHt135 (appendHvl k84 (bindPat p)) d75 S61) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d75 k84 (bindPat p))) eq_refl eq_refl))))) (fun (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt134 (ts : Rec) IHts29 (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) =>
      (f_equal3 rcons eq_refl (IHt134 k84 d75 S61) (IHts29 k84 d75 S61)))).
    Lemma tsubst_tm_Tm_ind  :
      (forall (s22 : Tm) ,
        (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
          ((tsubstTm (weakenTrace (XS tm d75) k84) S61 s22) =
          (tsubstTm (weakenTrace d75 k84) S61 s22)))).
    Proof.
      pose proof (tsubst_tm_Tm_Rec_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tm_Rec_ind  :
      (forall (ss : Rec) ,
        (forall (k84 : Hvl) (d75 : (Trace ty)) (S61 : Ty) ,
          ((tsubstRec (weakenTrace (XS tm d75) k84) S61 ss) =
          (tsubstRec (weakenTrace d75 k84) S61 ss)))).
    Proof.
      pose proof (tsubst_tm_Tm_Rec_ind).
      destruct_conjs .
      easy .
    Qed.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTRec_tm (SS : TRec) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstTRec (XS tm d75) S61 SS) =
      (tsubstTRec d75 S61 SS))) := (tsubst_tm_TRec_ind SS H0).
    Definition tsubstTy_tm (S62 : Ty) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstTy (XS tm d75) S61 S62) =
      (tsubstTy d75 S61 S62))) := (tsubst_tm_Ty_ind S62 H0).
    Definition tsubstPat_tm (p23 : Pat) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstPat (XS tm d75) S61 p23) =
      (tsubstPat d75 S61 p23))) := (tsubst_tm_Pat_ind p23 H0).
    Definition tsubstPRec_tm (ps13 : PRec) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstPRec (XS tm d75) S61 ps13) =
      (tsubstPRec d75 S61 ps13))) := (tsubst_tm_PRec_ind ps13 H0).
    Definition tsubstTm_tm (s22 : Tm) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstTm (XS tm d75) S61 s22) =
      (tsubstTm d75 S61 s22))) := (tsubst_tm_Tm_ind s22 H0).
    Definition tsubstRec_tm (ss : Rec) : (forall (d75 : (Trace ty)) (S61 : Ty) ,
      ((tsubstRec (XS tm d75) S61 ss) =
      (tsubstRec d75 S61 ss))) := (tsubst_tm_Rec_ind ss H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite tsubstPRec0_tshiftPRec0_reflection tsubstPat0_tshiftPat0_reflection substRec0_shiftRec0_reflection tsubstRec0_tshiftRec0_reflection tsubstTRec0_tshiftTRec0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite tsubstPRec0_tshiftPRec0_reflection tsubstPat0_tshiftPat0_reflection substRec0_shiftRec0_reflection tsubstRec0_tshiftRec0_reflection tsubstTRec0_tshiftTRec0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite tsubstPRec_tshiftPRec0_comm tsubstPat_tshiftPat0_comm substRec_shiftRec0_comm substRec_tshiftRec0_comm tsubstRec_shiftRec0_comm tsubstRec_tshiftRec0_comm tsubstTRec_tshiftTRec0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite tsubstPRec_tshiftPRec0_comm tsubstPat_tshiftPat0_comm substRec_shiftRec0_comm substRec_tshiftRec0_comm tsubstRec_shiftRec0_comm tsubstRec_tshiftRec0_comm tsubstTRec_tshiftTRec0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstPRec_tm tsubstPat_tm tsubstRec_tm tsubstTRec_tm tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstPRec_tm tsubstPat_tm tsubstRec_tm tsubstTRec_tm tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite tshiftPRec_tsubstPRec0_comm tshiftPat_tsubstPat0_comm shiftRec_substRec0_comm shiftRec_tsubstRec0_comm tshiftRec_substRec0_comm tshiftRec_tsubstRec0_comm tshiftTRec_tsubstTRec0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite tshiftPRec_tsubstPRec0_comm tshiftPat_tsubstPat0_comm shiftRec_substRec0_comm shiftRec_tsubstRec0_comm tshiftRec_substRec0_comm tshiftRec_tsubstRec0_comm tshiftTRec_tsubstTRec0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d75 : (Trace tm)) (s22 : Tm) (s23 : Tm) :
      (forall (k84 : Hvl) (x46 : (Index tm)) ,
        ((substTm (weakenTrace d75 k84) s22 (substIndex (weakenTrace X0 k84) s23 x46)) =
        (substTm (weakenTrace X0 k84) (substTm d75 s22 s23) (substIndex (weakenTrace (XS tm d75) k84) s22 x46)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d75 : (Trace ty)) (S61 : Ty) (s22 : Tm) :
      (forall (k84 : Hvl) (x46 : (Index tm)) ,
        ((tsubstTm (weakenTrace d75 k84) S61 (substIndex (weakenTrace X0 k84) s22 x46)) =
        (substIndex (weakenTrace X0 k84) (tsubstTm d75 S61 s22) x46))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d75 : (Trace ty)) (S61 : Ty) (S62 : Ty) :
      (forall (k84 : Hvl) (X32 : (Index ty)) ,
        ((tsubstTy (weakenTrace d75 k84) S61 (tsubstIndex (weakenTrace X0 k84) S62 X32)) =
        (tsubstTy (weakenTrace X0 k84) (tsubstTy d75 S61 S62) (tsubstIndex (weakenTrace (XS ty d75) k84) S61 X32)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d75 : (Trace tm)) (s22 : Tm) (S61 : Ty) :
      (forall (k84 : Hvl) (x46 : (Index tm)) ,
        ((substIndex (weakenTrace d75 k84) s22 x46) =
        (tsubstTm (weakenTrace X0 k84) S61 (substIndex (weakenTrace (XS ty d75) k84) s22 x46)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition tsubst_tsubst0_TRec_Ty_comm_ind := (ind_TRec_Ty (fun (SS : TRec) =>
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
        ((tsubstTRec (weakenTrace d78 k87) S65 (tsubstTRec (weakenTrace X0 k87) S66 SS)) =
        (tsubstTRec (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstTRec (weakenTrace (XS ty d78) k87) S65 SS))))) (fun (S65 : Ty) =>
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S66 : Ty) (S67 : Ty) ,
        ((tsubstTy (weakenTrace d78 k87) S66 (tsubstTy (weakenTrace X0 k87) S67 S65)) =
        (tsubstTy (weakenTrace X0 k87) (tsubstTy d78 S66 S67) (tsubstTy (weakenTrace (XS ty d78) k87) S66 S65))))) (fun (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      eq_refl) (fun (l : Lab) (T : Ty) IHT5 (TS : TRec) IHTS11 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal3 tcons eq_refl (IHT5 k87 d78 S65 S66) (IHTS11 k87 d78 S65 S66))) (fun (X37 : (Index ty)) =>
      (fun (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
        (tsubstTy_tsubstIndex0_commright_ind d78 S65 S66 k87 X37))) (fun (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      eq_refl) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal2 tarr (IHT5 k87 d78 S65 S66) (IHT6 k87 d78 S65 S66))) (fun (T1 : Ty) IHT5 (T2 : Ty) IHT6 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal2 tall (IHT5 k87 d78 S65 S66) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d78 k87 (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k87 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHT6 (HS ty k87) d78 S65 S66) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k87 (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d78) k87 (HS ty H0))) eq_refl eq_refl)))))) (fun (TS : TRec) IHTS11 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal trec (IHTS11 k87 d78 S65 S66)))).
    Lemma tsubst_tsubst0_TRec_comm_ind  :
      (forall (SS : TRec) ,
        (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
          ((tsubstTRec (weakenTrace d78 k87) S65 (tsubstTRec (weakenTrace X0 k87) S66 SS)) =
          (tsubstTRec (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstTRec (weakenTrace (XS ty d78) k87) S65 SS))))).
    Proof.
      pose proof (tsubst_tsubst0_TRec_Ty_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tsubst0_Ty_comm_ind  :
      (forall (S65 : Ty) ,
        (forall (k87 : Hvl) (d78 : (Trace ty)) (S66 : Ty) (S67 : Ty) ,
          ((tsubstTy (weakenTrace d78 k87) S66 (tsubstTy (weakenTrace X0 k87) S67 S65)) =
          (tsubstTy (weakenTrace X0 k87) (tsubstTy d78 S66 S67) (tsubstTy (weakenTrace (XS ty d78) k87) S66 S65))))).
    Proof.
      pose proof (tsubst_tsubst0_TRec_Ty_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_tsubst0_Pat_PRec_comm_ind := (ind_Pat_PRec (fun (p26 : Pat) =>
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
        ((tsubstPat (weakenTrace d78 k87) S65 (tsubstPat (weakenTrace X0 k87) S66 p26)) =
        (tsubstPat (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstPat (weakenTrace (XS ty d78) k87) S65 p26))))) (fun (ps15 : PRec) =>
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
        ((tsubstPRec (weakenTrace d78 k87) S65 (tsubstPRec (weakenTrace X0 k87) S66 ps15)) =
        (tsubstPRec (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstPRec (weakenTrace (XS ty d78) k87) S65 ps15))))) (fun (T : Ty) (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal pvar (let IHT5 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT5 k87 d78 S65 S66)))) (fun (ps : PRec) IHps (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal prec (IHps k87 d78 S65 S66))) (fun (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      eq_refl) (fun (l : Lab) (p : Pat) IHp (ps : PRec) IHps (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal3 pcons eq_refl (IHp k87 d78 S65 S66) (IHps k87 d78 S65 S66)))).
    Lemma tsubst_tsubst0_Pat_comm_ind  :
      (forall (p26 : Pat) ,
        (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
          ((tsubstPat (weakenTrace d78 k87) S65 (tsubstPat (weakenTrace X0 k87) S66 p26)) =
          (tsubstPat (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstPat (weakenTrace (XS ty d78) k87) S65 p26))))).
    Proof.
      pose proof (tsubst_tsubst0_Pat_PRec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tsubst0_PRec_comm_ind  :
      (forall (ps15 : PRec) ,
        (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
          ((tsubstPRec (weakenTrace d78 k87) S65 (tsubstPRec (weakenTrace X0 k87) S66 ps15)) =
          (tsubstPRec (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstPRec (weakenTrace (XS ty d78) k87) S65 ps15))))).
    Proof.
      pose proof (tsubst_tsubst0_Pat_PRec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition subst_subst0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s24 : Tm) =>
      (forall (k87 : Hvl) (d78 : (Trace tm)) (s25 : Tm) (s26 : Tm) ,
        ((substTm (weakenTrace d78 k87) s25 (substTm (weakenTrace X0 k87) s26 s24)) =
        (substTm (weakenTrace X0 k87) (substTm d78 s25 s26) (substTm (weakenTrace (XS tm d78) k87) s25 s24))))) (fun (ss : Rec) =>
      (forall (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) ,
        ((substRec (weakenTrace d78 k87) s24 (substRec (weakenTrace X0 k87) s25 ss)) =
        (substRec (weakenTrace X0 k87) (substTm d78 s24 s25) (substRec (weakenTrace (XS tm d78) k87) s24 ss))))) (fun (x53 : (Index tm)) =>
      (fun (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
        (substTm_substIndex0_commright_ind d78 s24 s25 k87 x53))) (fun (T : Ty) (t : Tm) IHt152 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d78 k87 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k87 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k87) d78 s24 s25) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k87 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d78) k87 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
      (f_equal2 app (IHt152 k87 d78 s24 s25) (IHt153 k87 d78 s24 s25))) (fun (T : Ty) (t : Tm) IHt152 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d78 k87 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k87 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k87) d78 s24 s25) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k87 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d78) k87 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
      (f_equal2 tapp (IHt152 k87 d78 s24 s25) eq_refl)) (fun (ts : Rec) IHts33 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
      (f_equal rec (IHts33 k87 d78 s24 s25))) (fun (t : Tm) IHt152 (l : Lab) (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
      (f_equal2 prj (IHt152 k87 d78 s24 s25) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
      (f_equal3 lett eq_refl (IHt152 k87 d78 s24 s25) (eq_trans (f_equal3 substTm (weakenTrace_append tm d78 k87 (bindPat p)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k87 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k87 (bindPat p)) d78 s24 s25) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k87 (bindPat p))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d78) k87 (bindPat p))) eq_refl eq_refl)))))) (fun (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt152 (ts : Rec) IHts33 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) =>
      (f_equal3 rcons eq_refl (IHt152 k87 d78 s24 s25) (IHts33 k87 d78 s24 s25)))).
    Lemma subst_subst0_Tm_comm_ind  :
      (forall (s24 : Tm) ,
        (forall (k87 : Hvl) (d78 : (Trace tm)) (s25 : Tm) (s26 : Tm) ,
          ((substTm (weakenTrace d78 k87) s25 (substTm (weakenTrace X0 k87) s26 s24)) =
          (substTm (weakenTrace X0 k87) (substTm d78 s25 s26) (substTm (weakenTrace (XS tm d78) k87) s25 s24))))).
    Proof.
      pose proof (subst_subst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma subst_subst0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k87 : Hvl) (d78 : (Trace tm)) (s25 : Tm) (s26 : Tm) ,
          ((substRec (weakenTrace d78 k87) s25 (substRec (weakenTrace X0 k87) s26 ss)) =
          (substRec (weakenTrace X0 k87) (substTm d78 s25 s26) (substRec (weakenTrace (XS tm d78) k87) s25 ss))))).
    Proof.
      pose proof (subst_subst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition subst_tsubst0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s24 : Tm) =>
      (forall (k87 : Hvl) (d78 : (Trace tm)) (s25 : Tm) (S65 : Ty) ,
        ((substTm (weakenTrace d78 k87) s25 (tsubstTm (weakenTrace X0 k87) S65 s24)) =
        (tsubstTm (weakenTrace X0 k87) S65 (substTm (weakenTrace (XS ty d78) k87) s25 s24))))) (fun (ss : Rec) =>
      (forall (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) ,
        ((substRec (weakenTrace d78 k87) s24 (tsubstRec (weakenTrace X0 k87) S65 ss)) =
        (tsubstRec (weakenTrace X0 k87) S65 (substRec (weakenTrace (XS ty d78) k87) s24 ss))))) (fun (x53 : (Index tm)) =>
      (fun (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
        (substTy_tsubstIndex0_commleft_ind d78 s24 S65 k87 x53))) (fun (T : Ty) (t : Tm) IHt152 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d78 k87 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k87 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k87) d78 s24 S65) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k87 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d78) k87 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
      (f_equal2 app (IHt152 k87 d78 s24 S65) (IHt153 k87 d78 s24 S65))) (fun (T : Ty) (t : Tm) IHt152 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d78 k87 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k87 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k87) d78 s24 S65) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k87 (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d78) k87 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
      (f_equal2 tapp (IHt152 k87 d78 s24 S65) eq_refl)) (fun (ts : Rec) IHts33 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
      (f_equal rec (IHts33 k87 d78 s24 S65))) (fun (t : Tm) IHt152 (l : Lab) (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
      (f_equal2 prj (IHt152 k87 d78 s24 S65) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
      (f_equal3 lett eq_refl (IHt152 k87 d78 s24 S65) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenTrace_append tm d78 k87 (bindPat p))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k87 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k87 (bindPat p)) d78 s24 S65) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k87 (bindPat p))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d78) k87 (bindPat p))) eq_refl eq_refl)))))) (fun (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt152 (ts : Rec) IHts33 (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) =>
      (f_equal3 rcons eq_refl (IHt152 k87 d78 s24 S65) (IHts33 k87 d78 s24 S65)))).
    Lemma subst_tsubst0_Tm_comm_ind  :
      (forall (s24 : Tm) ,
        (forall (k87 : Hvl) (d78 : (Trace tm)) (s25 : Tm) (S65 : Ty) ,
          ((substTm (weakenTrace d78 k87) s25 (tsubstTm (weakenTrace X0 k87) S65 s24)) =
          (tsubstTm (weakenTrace X0 k87) S65 (substTm (weakenTrace (XS ty d78) k87) s25 s24))))).
    Proof.
      pose proof (subst_tsubst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma subst_tsubst0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k87 : Hvl) (d78 : (Trace tm)) (s25 : Tm) (S65 : Ty) ,
          ((substRec (weakenTrace d78 k87) s25 (tsubstRec (weakenTrace X0 k87) S65 ss)) =
          (tsubstRec (weakenTrace X0 k87) S65 (substRec (weakenTrace (XS ty d78) k87) s25 ss))))).
    Proof.
      pose proof (subst_tsubst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_subst0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s24 : Tm) =>
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s25 : Tm) ,
        ((tsubstTm (weakenTrace d78 k87) S65 (substTm (weakenTrace X0 k87) s25 s24)) =
        (substTm (weakenTrace X0 k87) (tsubstTm d78 S65 s25) (tsubstTm (weakenTrace d78 k87) S65 s24))))) (fun (ss : Rec) =>
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) ,
        ((tsubstRec (weakenTrace d78 k87) S65 (substRec (weakenTrace X0 k87) s24 ss)) =
        (substRec (weakenTrace X0 k87) (tsubstTm d78 S65 s24) (tsubstRec (weakenTrace d78 k87) S65 ss))))) (fun (x53 : (Index tm)) =>
      (fun (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
        (tsubstTm_substIndex0_commright_ind d78 S65 s24 k87 x53))) (fun (T : Ty) (t : Tm) IHt152 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d78 k87 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k87 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k87) d78 S65 s24) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k87 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d78 k87 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
      (f_equal2 app (IHt152 k87 d78 S65 s24) (IHt153 k87 d78 S65 s24))) (fun (T : Ty) (t : Tm) IHt152 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
      (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d78 k87 (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k87 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k87) d78 S65 s24) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k87 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d78 k87 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
      (f_equal2 tapp (IHt152 k87 d78 S65 s24) eq_refl)) (fun (ts : Rec) IHts33 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
      (f_equal rec (IHts33 k87 d78 S65 s24))) (fun (t : Tm) IHt152 (l : Lab) (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
      (f_equal2 prj (IHt152 k87 d78 S65 s24) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
      (f_equal3 lett eq_refl (IHt152 k87 d78 S65 s24) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d78 k87 (bindPat p)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k87 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k87 (bindPat p)) d78 S65 s24) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k87 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d78 k87 (bindPat p))) eq_refl eq_refl)))))) (fun (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt152 (ts : Rec) IHts33 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) =>
      (f_equal3 rcons eq_refl (IHt152 k87 d78 S65 s24) (IHts33 k87 d78 S65 s24)))).
    Lemma tsubst_subst0_Tm_comm_ind  :
      (forall (s24 : Tm) ,
        (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s25 : Tm) ,
          ((tsubstTm (weakenTrace d78 k87) S65 (substTm (weakenTrace X0 k87) s25 s24)) =
          (substTm (weakenTrace X0 k87) (tsubstTm d78 S65 s25) (tsubstTm (weakenTrace d78 k87) S65 s24))))).
    Proof.
      pose proof (tsubst_subst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_subst0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s25 : Tm) ,
          ((tsubstRec (weakenTrace d78 k87) S65 (substRec (weakenTrace X0 k87) s25 ss)) =
          (substRec (weakenTrace X0 k87) (tsubstTm d78 S65 s25) (tsubstRec (weakenTrace d78 k87) S65 ss))))).
    Proof.
      pose proof (tsubst_subst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Definition tsubst_tsubst0_Tm_Rec_comm_ind := (ind_Tm_Rec (fun (s24 : Tm) =>
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
        ((tsubstTm (weakenTrace d78 k87) S65 (tsubstTm (weakenTrace X0 k87) S66 s24)) =
        (tsubstTm (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstTm (weakenTrace (XS ty d78) k87) S65 s24))))) (fun (ss : Rec) =>
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
        ((tsubstRec (weakenTrace d78 k87) S65 (tsubstRec (weakenTrace X0 k87) S66 ss)) =
        (tsubstRec (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstRec (weakenTrace (XS ty d78) k87) S65 ss))))) (fun (x53 : (Index tm)) =>
      (fun (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
        eq_refl)) (fun (T : Ty) (t : Tm) IHt152 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal2 abs (let IHT5 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT5 k87 d78 S65 S66)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d78 k87 (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k87 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS tm k87) d78 S65 S66) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k87 (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d78) k87 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal2 app (IHt152 k87 d78 S65 S66) (IHt153 k87 d78 S65 S66))) (fun (T : Ty) (t : Tm) IHt152 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal2 tabs (let IHT5 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT5 k87 d78 S65 S66)) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d78 k87 (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k87 (HS ty H0)) eq_refl eq_refl)) (eq_trans (IHt152 (HS ty k87) d78 S65 S66) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k87 (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d78) k87 (HS ty H0))) eq_refl eq_refl)))))) (fun (t : Tm) IHt152 (T : Ty) (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal2 tapp (IHt152 k87 d78 S65 S66) (let IHT5 := (tsubst_tsubst0_Ty_comm_ind T) in
      (IHT5 k87 d78 S65 S66)))) (fun (ts : Rec) IHts33 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal rec (IHts33 k87 d78 S65 S66))) (fun (t : Tm) IHt152 (l : Lab) (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal2 prj (IHt152 k87 d78 S65 S66) eq_refl)) (fun (p : Pat) (t1 : Tm) IHt152 (t2 : Tm) IHt153 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal3 lett (let IHp := (tsubst_tsubst0_Pat_comm_ind p) in
      (IHp k87 d78 S65 S66)) (IHt152 k87 d78 S65 S66) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0))) (weakenTrace_append ty d78 k87 (bindPat p))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k87 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt153 (appendHvl k87 (bindPat p)) d78 S65 S66) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k87 (bindPat p))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d78) k87 (bindPat p))) eq_refl eq_refl)))))) (fun (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      eq_refl) (fun (l : Lab) (t : Tm) IHt152 (ts : Rec) IHts33 (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) =>
      (f_equal3 rcons eq_refl (IHt152 k87 d78 S65 S66) (IHts33 k87 d78 S65 S66)))).
    Lemma tsubst_tsubst0_Tm_comm_ind  :
      (forall (s24 : Tm) ,
        (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
          ((tsubstTm (weakenTrace d78 k87) S65 (tsubstTm (weakenTrace X0 k87) S66 s24)) =
          (tsubstTm (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstTm (weakenTrace (XS ty d78) k87) S65 s24))))).
    Proof.
      pose proof (tsubst_tsubst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
    Lemma tsubst_tsubst0_Rec_comm_ind  :
      (forall (ss : Rec) ,
        (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
          ((tsubstRec (weakenTrace d78 k87) S65 (tsubstRec (weakenTrace X0 k87) S66 ss)) =
          (tsubstRec (weakenTrace X0 k87) (tsubstTy d78 S65 S66) (tsubstRec (weakenTrace (XS ty d78) k87) S65 ss))))).
    Proof.
      pose proof (tsubst_tsubst0_Tm_Rec_comm_ind).
      destruct_conjs .
      easy .
    Qed.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTRec_tsubstTRec0_comm (SS : TRec) : (forall (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
      ((tsubstTRec d78 S65 (tsubstTRec X0 S66 SS)) =
      (tsubstTRec X0 (tsubstTy d78 S65 S66) (tsubstTRec (XS ty d78) S65 SS)))) := (tsubst_tsubst0_TRec_comm_ind SS H0).
    Definition tsubstTy_tsubstTy0_comm (S67 : Ty) : (forall (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
      ((tsubstTy d78 S65 (tsubstTy X0 S66 S67)) =
      (tsubstTy X0 (tsubstTy d78 S65 S66) (tsubstTy (XS ty d78) S65 S67)))) := (tsubst_tsubst0_Ty_comm_ind S67 H0).
    Definition tsubstPat_tsubstPat0_comm (p26 : Pat) : (forall (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
      ((tsubstPat d78 S65 (tsubstPat X0 S66 p26)) =
      (tsubstPat X0 (tsubstTy d78 S65 S66) (tsubstPat (XS ty d78) S65 p26)))) := (tsubst_tsubst0_Pat_comm_ind p26 H0).
    Definition tsubstPRec_tsubstPRec0_comm (ps15 : PRec) : (forall (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
      ((tsubstPRec d78 S65 (tsubstPRec X0 S66 ps15)) =
      (tsubstPRec X0 (tsubstTy d78 S65 S66) (tsubstPRec (XS ty d78) S65 ps15)))) := (tsubst_tsubst0_PRec_comm_ind ps15 H0).
    Definition substTm_substTm0_comm (s26 : Tm) : (forall (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) ,
      ((substTm d78 s24 (substTm X0 s25 s26)) =
      (substTm X0 (substTm d78 s24 s25) (substTm (XS tm d78) s24 s26)))) := (subst_subst0_Tm_comm_ind s26 H0).
    Definition substRec_substRec0_comm (ss : Rec) : (forall (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) ,
      ((substRec d78 s24 (substRec X0 s25 ss)) =
      (substRec X0 (substTm d78 s24 s25) (substRec (XS tm d78) s24 ss)))) := (subst_subst0_Rec_comm_ind ss H0).
    Definition substTm_tsubstTm0_comm (s25 : Tm) : (forall (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) ,
      ((substTm d78 s24 (tsubstTm X0 S65 s25)) =
      (tsubstTm X0 S65 (substTm (XS ty d78) s24 s25)))) := (subst_tsubst0_Tm_comm_ind s25 H0).
    Definition substRec_tsubstRec0_comm (ss : Rec) : (forall (d78 : (Trace tm)) (s24 : Tm) (S65 : Ty) ,
      ((substRec d78 s24 (tsubstRec X0 S65 ss)) =
      (tsubstRec X0 S65 (substRec (XS ty d78) s24 ss)))) := (subst_tsubst0_Rec_comm_ind ss H0).
    Definition tsubstTm_substTm0_comm (s25 : Tm) : (forall (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) ,
      ((tsubstTm d78 S65 (substTm X0 s24 s25)) =
      (substTm X0 (tsubstTm d78 S65 s24) (tsubstTm d78 S65 s25)))) := (tsubst_subst0_Tm_comm_ind s25 H0).
    Definition tsubstRec_substRec0_comm (ss : Rec) : (forall (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) ,
      ((tsubstRec d78 S65 (substRec X0 s24 ss)) =
      (substRec X0 (tsubstTm d78 S65 s24) (tsubstRec d78 S65 ss)))) := (tsubst_subst0_Rec_comm_ind ss H0).
    Definition tsubstTm_tsubstTm0_comm (s24 : Tm) : (forall (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
      ((tsubstTm d78 S65 (tsubstTm X0 S66 s24)) =
      (tsubstTm X0 (tsubstTy d78 S65 S66) (tsubstTm (XS ty d78) S65 s24)))) := (tsubst_tsubst0_Tm_comm_ind s24 H0).
    Definition tsubstRec_tsubstRec0_comm (ss : Rec) : (forall (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
      ((tsubstRec d78 S65 (tsubstRec X0 S66 ss)) =
      (tsubstRec X0 (tsubstTy d78 S65 S66) (tsubstRec (XS ty d78) S65 ss)))) := (tsubst_tsubst0_Rec_comm_ind ss H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTRec_tsubstTRec  :
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (SS : TRec) ,
        ((weakenTRec (tsubstTRec d78 S65 SS) k87) =
        (tsubstTRec (weakenTrace d78 k87) S65 (weakenTRec SS k87)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_tsubstTy  :
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (S66 : Ty) ,
        ((weakenTy (tsubstTy d78 S65 S66) k87) =
        (tsubstTy (weakenTrace d78 k87) S65 (weakenTy S66 k87)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPat_tsubstPat  :
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (p26 : Pat) ,
        ((weakenPat (tsubstPat d78 S65 p26) k87) =
        (tsubstPat (weakenTrace d78 k87) S65 (weakenPat p26 k87)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPRec_tsubstPRec  :
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (ps15 : PRec) ,
        ((weakenPRec (tsubstPRec d78 S65 ps15) k87) =
        (tsubstPRec (weakenTrace d78 k87) S65 (weakenPRec ps15 k87)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (s25 : Tm) ,
        ((weakenTm (substTm d78 s24 s25) k87) =
        (substTm (weakenTrace d78 k87) s24 (weakenTm s25 k87)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenRec_substRec  :
      (forall (k87 : Hvl) (d78 : (Trace tm)) (s24 : Tm) (ss : Rec) ,
        ((weakenRec (substRec d78 s24 ss) k87) =
        (substRec (weakenTrace d78 k87) s24 (weakenRec ss k87)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (s24 : Tm) ,
        ((weakenTm (tsubstTm d78 S65 s24) k87) =
        (tsubstTm (weakenTrace d78 k87) S65 (weakenTm s24 k87)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenRec_tsubstRec  :
      (forall (k87 : Hvl) (d78 : (Trace ty)) (S65 : Ty) (ss : Rec) ,
        ((weakenRec (tsubstRec d78 S65 ss) k87) =
        (tsubstRec (weakenTrace d78 k87) S65 (weakenRec ss k87)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenLab_append  :
      (forall (l45 : Lab) (k87 : Hvl) (k88 : Hvl) ,
        ((weakenLab (weakenLab l45 k87) k88) =
        (weakenLab l45 (appendHvl k87 k88)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTRec_append  :
      (forall (SS : TRec) (k87 : Hvl) (k88 : Hvl) ,
        ((weakenTRec (weakenTRec SS k87) k88) =
        (weakenTRec SS (appendHvl k87 k88)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTy_append  :
      (forall (S65 : Ty) (k87 : Hvl) (k88 : Hvl) ,
        ((weakenTy (weakenTy S65 k87) k88) =
        (weakenTy S65 (appendHvl k87 k88)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenPat_append  :
      (forall (p26 : Pat) (k87 : Hvl) (k88 : Hvl) ,
        ((weakenPat (weakenPat p26 k87) k88) =
        (weakenPat p26 (appendHvl k87 k88)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenPRec_append  :
      (forall (ps15 : PRec) (k87 : Hvl) (k88 : Hvl) ,
        ((weakenPRec (weakenPRec ps15 k87) k88) =
        (weakenPRec ps15 (appendHvl k87 k88)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s24 : Tm) (k87 : Hvl) (k88 : Hvl) ,
        ((weakenTm (weakenTm s24 k87) k88) =
        (weakenTm s24 (appendHvl k87 k88)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenRec_append  :
      (forall (ss : Rec) (k87 : Hvl) (k88 : Hvl) ,
        ((weakenRec (weakenRec ss k87) k88) =
        (weakenRec ss (appendHvl k87 k88)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
  End WeakenAppend.
End SubstSubstInteraction.
 Hint Rewrite tsubstPRec_tsubstPRec0_comm tsubstPat_tsubstPat0_comm substRec_substRec0_comm tsubstRec_tsubstRec0_comm tsubstTRec_tsubstTRec0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite tsubstPRec_tsubstPRec0_comm tsubstPat_tsubstPat0_comm substRec_substRec0_comm tsubstRec_tsubstRec0_comm tsubstTRec_tsubstTRec0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenPRec_tshiftPRec weakenPat_tshiftPat weakenRec_shiftRec weakenRec_tshiftRec weakenTRec_tshiftTRec weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenPRec_tsubstPRec weakenPat_tsubstPat weakenRec_substRec weakenRec_tsubstRec weakenTRec_tsubstTRec weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
Section WellFormed.
  Fixpoint wfindex {a : Namespace} (k87 : Hvl) (i : (Index a)) {struct k87} : Prop :=
    match k87 with
      | (H0) => False
      | (HS b k87) => match (eq_namespace_dec a b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k87 i)
        end
        | (right n) => (wfindex k87 i)
      end
    end.
  Inductive wfLab (k87 : Hvl) : Lab -> Prop :=
    | wfLab_L0 : (wfLab k87 (L0))
    | wfLab_LS {l51 : Lab}
        (wf : (wfLab k87 l51)) :
        (wfLab k87 (LS l51)).
  Inductive wfTRec (k87 : Hvl) : TRec -> Prop :=
    | wfTRec_tnil :
        (wfTRec k87 (tnil))
    | wfTRec_tcons {l51 : Lab}
        (wf : (wfLab k87 l51))
        {T98 : Ty}
        (wf0 : (wfTy k87 T98))
        {TS13 : TRec}
        (wf1 : (wfTRec k87 TS13)) :
        (wfTRec k87 (tcons l51 T98 TS13))
  with wfTy (k87 : Hvl) : Ty -> Prop :=
    | wfTy_tvar {X43 : (Index ty)}
        (wfi : (wfindex k87 X43)) :
        (wfTy k87 (tvar X43))
    | wfTy_top : (wfTy k87 (top))
    | wfTy_tarr {T98 : Ty}
        (wf : (wfTy k87 T98)) {T99 : Ty}
        (wf0 : (wfTy k87 T99)) :
        (wfTy k87 (tarr T98 T99))
    | wfTy_tall {T100 : Ty}
        (wf : (wfTy k87 T100))
        {T101 : Ty}
        (wf0 : (wfTy (HS ty k87) T101))
        : (wfTy k87 (tall T100 T101))
    | wfTy_trec {TS13 : TRec}
        (wf : (wfTRec k87 TS13)) :
        (wfTy k87 (trec TS13)).
  Inductive wfPat (k87 : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T98 : Ty}
        (wf : (wfTy k87 T98)) :
        (wfPat k87 (pvar T98))
    | wfPat_prec {ps17 : PRec}
        (wf : (wfPRec k87 ps17)) :
        (wfPat k87 (prec ps17))
  with wfPRec (k87 : Hvl) : PRec -> Prop :=
    | wfPRec_pnil :
        (wfPRec k87 (pnil))
    | wfPRec_pcons {l51 : Lab}
        (wf : (wfLab k87 l51))
        {p29 : Pat}
        (wf0 : (wfPat k87 p29))
        {ps17 : PRec}
        (wf1 : (wfPRec k87 ps17)) :
        (wfPRec k87 (pcons l51 p29 ps17)).
  Inductive wfTm (k87 : Hvl) : Tm -> Prop :=
    | wfTm_var {x59 : (Index tm)}
        (wfi : (wfindex k87 x59)) :
        (wfTm k87 (var x59))
    | wfTm_abs {T98 : Ty}
        (wf : (wfTy k87 T98))
        {t170 : Tm}
        (wf0 : (wfTm (HS tm k87) t170))
        : (wfTm k87 (abs T98 t170))
    | wfTm_app {t171 : Tm}
        (wf : (wfTm k87 t171))
        {t172 : Tm}
        (wf0 : (wfTm k87 t172)) :
        (wfTm k87 (app t171 t172))
    | wfTm_tabs {T99 : Ty}
        (wf : (wfTy k87 T99))
        {t173 : Tm}
        (wf0 : (wfTm (HS ty k87) t173))
        : (wfTm k87 (tabs T99 t173))
    | wfTm_tapp {t174 : Tm}
        (wf : (wfTm k87 t174))
        {T100 : Ty}
        (wf0 : (wfTy k87 T100)) :
        (wfTm k87 (tapp t174 T100))
    | wfTm_rec {ts37 : Rec}
        (wf : (wfRec k87 ts37)) :
        (wfTm k87 (rec ts37))
    | wfTm_prj {t175 : Tm}
        (wf : (wfTm k87 t175))
        {l51 : Lab}
        (wf0 : (wfLab k87 l51)) :
        (wfTm k87 (prj t175 l51))
    | wfTm_lett {p29 : Pat}
        (wf : (wfPat k87 p29))
        {t176 : Tm}
        (wf0 : (wfTm k87 t176))
        {t177 : Tm}
        (wf1 : (wfTm (appendHvl k87 (bindPat p29)) t177))
        :
        (wfTm k87 (lett p29 t176 t177))
  with wfRec (k87 : Hvl) : Rec -> Prop :=
    | wfRec_rnil :
        (wfRec k87 (rnil))
    | wfRec_rcons {l51 : Lab}
        (wf : (wfLab k87 l51))
        {t170 : Tm}
        (wf0 : (wfTm k87 t170))
        {ts37 : Rec}
        (wf1 : (wfRec k87 ts37)) :
        (wfRec k87 (rcons l51 t170 ts37)).
  Scheme ind_wfLab := Induction for wfLab Sort Prop.
  Scheme ind_wfTRec := Induction for wfTRec Sort Prop
  with ind_wfTy := Induction for wfTy Sort Prop.
  Combined Scheme ind_wfTRec_Ty from ind_wfTRec, ind_wfTy.
  Scheme ind_wfPat := Induction for wfPat Sort Prop
  with ind_wfPRec := Induction for wfPRec Sort Prop.
  Combined Scheme ind_wfPat_PRec from ind_wfPat, ind_wfPRec.
  Scheme ind_wfTm := Induction for wfTm Sort Prop
  with ind_wfRec := Induction for wfRec Sort Prop.
  Combined Scheme ind_wfTm_Rec from ind_wfTm, ind_wfRec.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c16 : (Cutoff tm)) (k87 : Hvl) (k88 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k87 : Hvl)
        :
        (shifthvl_tm C0 k87 (HS tm k87))
    | shifthvl_tm_there_tm
        (c16 : (Cutoff tm)) (k87 : Hvl)
        (k88 : Hvl) :
        (shifthvl_tm c16 k87 k88) -> (shifthvl_tm (CS c16) (HS tm k87) (HS tm k88))
    | shifthvl_tm_there_ty
        (c16 : (Cutoff tm)) (k87 : Hvl)
        (k88 : Hvl) :
        (shifthvl_tm c16 k87 k88) -> (shifthvl_tm c16 (HS ty k87) (HS ty k88)).
  Inductive shifthvl_ty : (forall (c16 : (Cutoff ty)) (k87 : Hvl) (k88 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k87 : Hvl)
        :
        (shifthvl_ty C0 k87 (HS ty k87))
    | shifthvl_ty_there_tm
        (c16 : (Cutoff ty)) (k87 : Hvl)
        (k88 : Hvl) :
        (shifthvl_ty c16 k87 k88) -> (shifthvl_ty c16 (HS tm k87) (HS tm k88))
    | shifthvl_ty_there_ty
        (c16 : (Cutoff ty)) (k87 : Hvl)
        (k88 : Hvl) :
        (shifthvl_ty c16 k87 k88) -> (shifthvl_ty (CS c16) (HS ty k87) (HS ty k88)).
  Lemma weaken_shifthvl_tm  :
    (forall (k87 : Hvl) {c16 : (Cutoff tm)} {k88 : Hvl} {k89 : Hvl} ,
      (shifthvl_tm c16 k88 k89) -> (shifthvl_tm (weakenCutofftm c16 k87) (appendHvl k88 k87) (appendHvl k89 k87))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k87 : Hvl) {c16 : (Cutoff ty)} {k88 : Hvl} {k89 : Hvl} ,
      (shifthvl_ty c16 k88 k89) -> (shifthvl_ty (weakenCutoffty c16 k87) (appendHvl k88 k87) (appendHvl k89 k87))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c16 : (Cutoff tm)) (k87 : Hvl) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) (x59 : (Index tm)) ,
      (wfindex k87 x59) -> (wfindex k88 (shiftIndex c16 x59))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c16 : (Cutoff tm)) (k87 : Hvl) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) (X43 : (Index ty)) ,
      (wfindex k87 X43) -> (wfindex k88 X43)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c16 : (Cutoff ty)) (k87 : Hvl) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) (x59 : (Index tm)) ,
      (wfindex k87 x59) -> (wfindex k88 x59)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c16 : (Cutoff ty)) (k87 : Hvl) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) (X43 : (Index ty)) ,
      (wfindex k87 X43) -> (wfindex k88 (tshiftIndex c16 X43))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfLab : (forall (k87 : Hvl) ,
    (forall (l51 : Lab) (wf : (wfLab k87 l51)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfLab k88 l51)))) := (fun (k87 : Hvl) =>
    (ind_wfLab k87 (fun (l51 : Lab) (wf : (wfLab k87 l51)) =>
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfLab k88 l51))) (fun (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
      (wfLab_L0 k88)) (fun (l : Lab) (wf : (wfLab k87 l)) IHl (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
      (wfLab_LS k88 (IHl c16 k88 (weaken_shifthvl_tm H0 ins)))))).
  Definition tshift_wfLab : (forall (k87 : Hvl) ,
    (forall (l51 : Lab) (wf : (wfLab k87 l51)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfLab k88 l51)))) := (fun (k87 : Hvl) =>
    (ind_wfLab k87 (fun (l51 : Lab) (wf : (wfLab k87 l51)) =>
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfLab k88 l51))) (fun (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
      (wfLab_L0 k88)) (fun (l : Lab) (wf : (wfLab k87 l)) IHl (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
      (wfLab_LS k88 (IHl c16 k88 (weaken_shifthvl_ty H0 ins)))))).
  Definition shift_wfTRec_Ty : (forall (k87 : Hvl) ,
    (forall (SS : TRec) (wf : (wfTRec k87 SS)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfTRec k88 SS))) /\
    (forall (S65 : Ty) (wf : (wfTy k87 S65)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfTy k88 S65)))) := (ind_wfTRec_Ty (fun (k87 : Hvl) (SS : TRec) (wf : (wfTRec k87 SS)) =>
    (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
      (shifthvl_tm c16 k87 k88) -> (wfTRec k88 SS))) (fun (k87 : Hvl) (S65 : Ty) (wf : (wfTy k87 S65)) =>
    (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
      (shifthvl_tm c16 k87 k88) -> (wfTy k88 S65))) (fun (k87 : Hvl) (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTRec_tnil k88)) (fun (k87 : Hvl) (l : Lab) (wf : (wfLab k87 l)) (T : Ty) (wf0 : (wfTy k87 T)) IHT5 (TS : TRec) (wf1 : (wfTRec k87 TS)) IHTS13 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTRec_tcons k88 (shift_wfLab k87 l wf c16 k88 (weaken_shifthvl_tm H0 ins)) (IHT5 c16 k88 (weaken_shifthvl_tm H0 ins)) (IHTS13 c16 k88 (weaken_shifthvl_tm H0 ins)))) (fun (k87 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k87 X43)) (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTy_tvar k88 (shift_wfindex_ty c16 k87 k88 ins X43 wfi))) (fun (k87 : Hvl) (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTy_top k88)) (fun (k87 : Hvl) (T1 : Ty) (wf : (wfTy k87 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k87 T2)) IHT6 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTy_tarr k88 (IHT5 c16 k88 (weaken_shifthvl_tm H0 ins)) (IHT6 c16 k88 (weaken_shifthvl_tm H0 ins)))) (fun (k87 : Hvl) (T1 : Ty) (wf : (wfTy k87 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy (HS ty k87) T2)) IHT6 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTy_tall k88 (IHT5 c16 k88 (weaken_shifthvl_tm H0 ins)) (IHT6 c16 (HS ty k88) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k87 : Hvl) (TS : TRec) (wf : (wfTRec k87 TS)) IHTS13 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTy_trec k88 (IHTS13 c16 k88 (weaken_shifthvl_tm H0 ins))))).
  Lemma shift_wfTRec (k87 : Hvl) :
    (forall (SS : TRec) (wf : (wfTRec k87 SS)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfTRec k88 SS))).
  Proof.
    pose proof ((shift_wfTRec_Ty k87)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_wfTy (k87 : Hvl) :
    (forall (S65 : Ty) (wf0 : (wfTy k87 S65)) ,
      (forall (c17 : (Cutoff tm)) (k89 : Hvl) ,
        (shifthvl_tm c17 k87 k89) -> (wfTy k89 S65))).
  Proof.
    pose proof ((shift_wfTRec_Ty k87)).
    destruct_conjs .
    easy .
  Qed.
  Definition tshift_wfTRec_Ty : (forall (k87 : Hvl) ,
    (forall (SS : TRec) (wf : (wfTRec k87 SS)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfTRec k88 (tshiftTRec c16 SS)))) /\
    (forall (S65 : Ty) (wf : (wfTy k87 S65)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfTy k88 (tshiftTy c16 S65))))) := (ind_wfTRec_Ty (fun (k87 : Hvl) (SS : TRec) (wf : (wfTRec k87 SS)) =>
    (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
      (shifthvl_ty c16 k87 k88) -> (wfTRec k88 (tshiftTRec c16 SS)))) (fun (k87 : Hvl) (S65 : Ty) (wf : (wfTy k87 S65)) =>
    (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
      (shifthvl_ty c16 k87 k88) -> (wfTy k88 (tshiftTy c16 S65)))) (fun (k87 : Hvl) (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTRec_tnil k88)) (fun (k87 : Hvl) (l : Lab) (wf : (wfLab k87 l)) (T : Ty) (wf0 : (wfTy k87 T)) IHT5 (TS : TRec) (wf1 : (wfTRec k87 TS)) IHTS13 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTRec_tcons k88 (tshift_wfLab k87 l wf c16 k88 (weaken_shifthvl_ty H0 ins)) (IHT5 c16 k88 (weaken_shifthvl_ty H0 ins)) (IHTS13 c16 k88 (weaken_shifthvl_ty H0 ins)))) (fun (k87 : Hvl) (X43 : (Index ty)) (wfi : (wfindex k87 X43)) (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTy_tvar k88 (tshift_wfindex_ty c16 k87 k88 ins X43 wfi))) (fun (k87 : Hvl) (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTy_top k88)) (fun (k87 : Hvl) (T1 : Ty) (wf : (wfTy k87 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy k87 T2)) IHT6 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTy_tarr k88 (IHT5 c16 k88 (weaken_shifthvl_ty H0 ins)) (IHT6 c16 k88 (weaken_shifthvl_ty H0 ins)))) (fun (k87 : Hvl) (T1 : Ty) (wf : (wfTy k87 T1)) IHT5 (T2 : Ty) (wf0 : (wfTy (HS ty k87) T2)) IHT6 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTy_tall k88 (IHT5 c16 k88 (weaken_shifthvl_ty H0 ins)) (IHT6 (CS c16) (HS ty k88) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k87 : Hvl) (TS : TRec) (wf : (wfTRec k87 TS)) IHTS13 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTy_trec k88 (IHTS13 c16 k88 (weaken_shifthvl_ty H0 ins))))).
  Lemma tshift_wfTRec (k87 : Hvl) :
    (forall (SS : TRec) (wf : (wfTRec k87 SS)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfTRec k88 (tshiftTRec c16 SS)))).
  Proof.
    pose proof ((tshift_wfTRec_Ty k87)).
    destruct_conjs .
    easy .
  Qed.
  Lemma tshift_wfTy (k87 : Hvl) :
    (forall (S65 : Ty) (wf0 : (wfTy k87 S65)) ,
      (forall (c17 : (Cutoff ty)) (k89 : Hvl) ,
        (shifthvl_ty c17 k87 k89) -> (wfTy k89 (tshiftTy c17 S65)))).
  Proof.
    pose proof ((tshift_wfTRec_Ty k87)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_wfPat_PRec : (forall (k87 : Hvl) ,
    (forall (p29 : Pat) (wf : (wfPat k87 p29)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfPat k88 p29))) /\
    (forall (ps17 : PRec) (wf : (wfPRec k87 ps17)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfPRec k88 ps17)))) := (fun (k87 : Hvl) =>
    (ind_wfPat_PRec k87 (fun (p29 : Pat) (wf : (wfPat k87 p29)) =>
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfPat k88 p29))) (fun (ps17 : PRec) (wf : (wfPRec k87 ps17)) =>
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfPRec k88 ps17))) (fun (T : Ty) (wf : (wfTy k87 T)) (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
      (wfPat_pvar k88 (shift_wfTy k87 T wf c16 k88 (weaken_shifthvl_tm H0 ins)))) (fun (ps : PRec) (wf : (wfPRec k87 ps)) IHps (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
      (wfPat_prec k88 (IHps c16 k88 (weaken_shifthvl_tm H0 ins)))) (fun (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
      (wfPRec_pnil k88)) (fun (l : Lab) (wf : (wfLab k87 l)) (p : Pat) (wf0 : (wfPat k87 p)) IHp (ps : PRec) (wf1 : (wfPRec k87 ps)) IHps (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
      (wfPRec_pcons k88 (shift_wfLab k87 l wf c16 k88 (weaken_shifthvl_tm H0 ins)) (IHp c16 k88 (weaken_shifthvl_tm H0 ins)) (IHps c16 k88 (weaken_shifthvl_tm H0 ins)))))).
  Lemma shift_wfPat (k87 : Hvl) :
    (forall (p29 : Pat) (wf : (wfPat k87 p29)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfPat k88 p29))).
  Proof.
    pose proof ((shift_wfPat_PRec k87)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_wfPRec (k87 : Hvl) :
    (forall (ps17 : PRec) (wf0 : (wfPRec k87 ps17)) ,
      (forall (c17 : (Cutoff tm)) (k89 : Hvl) ,
        (shifthvl_tm c17 k87 k89) -> (wfPRec k89 ps17))).
  Proof.
    pose proof ((shift_wfPat_PRec k87)).
    destruct_conjs .
    easy .
  Qed.
  Definition tshift_wfPat_PRec : (forall (k87 : Hvl) ,
    (forall (p29 : Pat) (wf : (wfPat k87 p29)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfPat k88 (tshiftPat c16 p29)))) /\
    (forall (ps17 : PRec) (wf : (wfPRec k87 ps17)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfPRec k88 (tshiftPRec c16 ps17))))) := (fun (k87 : Hvl) =>
    (ind_wfPat_PRec k87 (fun (p29 : Pat) (wf : (wfPat k87 p29)) =>
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfPat k88 (tshiftPat c16 p29)))) (fun (ps17 : PRec) (wf : (wfPRec k87 ps17)) =>
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfPRec k88 (tshiftPRec c16 ps17)))) (fun (T : Ty) (wf : (wfTy k87 T)) (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
      (wfPat_pvar k88 (tshift_wfTy k87 T wf c16 k88 (weaken_shifthvl_ty H0 ins)))) (fun (ps : PRec) (wf : (wfPRec k87 ps)) IHps (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
      (wfPat_prec k88 (IHps c16 k88 (weaken_shifthvl_ty H0 ins)))) (fun (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
      (wfPRec_pnil k88)) (fun (l : Lab) (wf : (wfLab k87 l)) (p : Pat) (wf0 : (wfPat k87 p)) IHp (ps : PRec) (wf1 : (wfPRec k87 ps)) IHps (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
      (wfPRec_pcons k88 (tshift_wfLab k87 l wf c16 k88 (weaken_shifthvl_ty H0 ins)) (IHp c16 k88 (weaken_shifthvl_ty H0 ins)) (IHps c16 k88 (weaken_shifthvl_ty H0 ins)))))).
  Lemma tshift_wfPat (k87 : Hvl) :
    (forall (p29 : Pat) (wf : (wfPat k87 p29)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfPat k88 (tshiftPat c16 p29)))).
  Proof.
    pose proof ((tshift_wfPat_PRec k87)).
    destruct_conjs .
    easy .
  Qed.
  Lemma tshift_wfPRec (k87 : Hvl) :
    (forall (ps17 : PRec) (wf0 : (wfPRec k87 ps17)) ,
      (forall (c17 : (Cutoff ty)) (k89 : Hvl) ,
        (shifthvl_ty c17 k87 k89) -> (wfPRec k89 (tshiftPRec c17 ps17)))).
  Proof.
    pose proof ((tshift_wfPat_PRec k87)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_wfTm_Rec : (forall (k87 : Hvl) ,
    (forall (s24 : Tm) (wf : (wfTm k87 s24)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfTm k88 (shiftTm c16 s24)))) /\
    (forall (ss : Rec) (wf : (wfRec k87 ss)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfRec k88 (shiftRec c16 ss))))) := (ind_wfTm_Rec (fun (k87 : Hvl) (s24 : Tm) (wf : (wfTm k87 s24)) =>
    (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
      (shifthvl_tm c16 k87 k88) -> (wfTm k88 (shiftTm c16 s24)))) (fun (k87 : Hvl) (ss : Rec) (wf : (wfRec k87 ss)) =>
    (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
      (shifthvl_tm c16 k87 k88) -> (wfRec k88 (shiftRec c16 ss)))) (fun (k87 : Hvl) (x59 : (Index tm)) (wfi : (wfindex k87 x59)) (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTm_var k88 (shift_wfindex_tm c16 k87 k88 ins x59 wfi))) (fun (k87 : Hvl) (T : Ty) (wf : (wfTy k87 T)) (t : Tm) (wf0 : (wfTm (HS tm k87) t)) IHt170 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTm_abs k88 (shift_wfTy k87 T wf c16 k88 (weaken_shifthvl_tm H0 ins)) (IHt170 (CS c16) (HS tm k88) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k87 : Hvl) (t1 : Tm) (wf : (wfTm k87 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k87 t2)) IHt171 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTm_app k88 (IHt170 c16 k88 (weaken_shifthvl_tm H0 ins)) (IHt171 c16 k88 (weaken_shifthvl_tm H0 ins)))) (fun (k87 : Hvl) (T : Ty) (wf : (wfTy k87 T)) (t : Tm) (wf0 : (wfTm (HS ty k87) t)) IHt170 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTm_tabs k88 (shift_wfTy k87 T wf c16 k88 (weaken_shifthvl_tm H0 ins)) (IHt170 c16 (HS ty k88) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k87 : Hvl) (t : Tm) (wf : (wfTm k87 t)) IHt170 (T : Ty) (wf0 : (wfTy k87 T)) (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTm_tapp k88 (IHt170 c16 k88 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k87 T wf0 c16 k88 (weaken_shifthvl_tm H0 ins)))) (fun (k87 : Hvl) (ts : Rec) (wf : (wfRec k87 ts)) IHts37 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTm_rec k88 (IHts37 c16 k88 (weaken_shifthvl_tm H0 ins)))) (fun (k87 : Hvl) (t : Tm) (wf : (wfTm k87 t)) IHt170 (l : Lab) (wf0 : (wfLab k87 l)) (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTm_prj k88 (IHt170 c16 k88 (weaken_shifthvl_tm H0 ins)) (shift_wfLab k87 l wf0 c16 k88 (weaken_shifthvl_tm H0 ins)))) (fun (k87 : Hvl) (p : Pat) (wf : (wfPat k87 p)) (t1 : Tm) (wf0 : (wfTm k87 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm (appendHvl k87 (bindPat p)) t2)) IHt171 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfTm_lett k88 (shift_wfPat k87 p wf c16 k88 (weaken_shifthvl_tm H0 ins)) (IHt170 c16 k88 (weaken_shifthvl_tm H0 ins)) (IHt171 (weakenCutofftm c16 (bindPat p)) (appendHvl k88 (bindPat p)) (weaken_shifthvl_tm (bindPat p) ins)))) (fun (k87 : Hvl) (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfRec_rnil k88)) (fun (k87 : Hvl) (l : Lab) (wf : (wfLab k87 l)) (t : Tm) (wf0 : (wfTm k87 t)) IHt170 (ts : Rec) (wf1 : (wfRec k87 ts)) IHts37 (c16 : (Cutoff tm)) (k88 : Hvl) (ins : (shifthvl_tm c16 k87 k88)) =>
    (wfRec_rcons k88 (shift_wfLab k87 l wf c16 k88 (weaken_shifthvl_tm H0 ins)) (IHt170 c16 k88 (weaken_shifthvl_tm H0 ins)) (IHts37 c16 k88 (weaken_shifthvl_tm H0 ins))))).
  Lemma shift_wfTm (k87 : Hvl) :
    (forall (s24 : Tm) (wf : (wfTm k87 s24)) ,
      (forall (c16 : (Cutoff tm)) (k88 : Hvl) ,
        (shifthvl_tm c16 k87 k88) -> (wfTm k88 (shiftTm c16 s24)))).
  Proof.
    pose proof ((shift_wfTm_Rec k87)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_wfRec (k87 : Hvl) :
    (forall (ss : Rec) (wf0 : (wfRec k87 ss)) ,
      (forall (c17 : (Cutoff tm)) (k89 : Hvl) ,
        (shifthvl_tm c17 k87 k89) -> (wfRec k89 (shiftRec c17 ss)))).
  Proof.
    pose proof ((shift_wfTm_Rec k87)).
    destruct_conjs .
    easy .
  Qed.
  Definition tshift_wfTm_Rec : (forall (k87 : Hvl) ,
    (forall (s24 : Tm) (wf : (wfTm k87 s24)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfTm k88 (tshiftTm c16 s24)))) /\
    (forall (ss : Rec) (wf : (wfRec k87 ss)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfRec k88 (tshiftRec c16 ss))))) := (ind_wfTm_Rec (fun (k87 : Hvl) (s24 : Tm) (wf : (wfTm k87 s24)) =>
    (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
      (shifthvl_ty c16 k87 k88) -> (wfTm k88 (tshiftTm c16 s24)))) (fun (k87 : Hvl) (ss : Rec) (wf : (wfRec k87 ss)) =>
    (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
      (shifthvl_ty c16 k87 k88) -> (wfRec k88 (tshiftRec c16 ss)))) (fun (k87 : Hvl) (x59 : (Index tm)) (wfi : (wfindex k87 x59)) (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTm_var k88 (tshift_wfindex_tm c16 k87 k88 ins x59 wfi))) (fun (k87 : Hvl) (T : Ty) (wf : (wfTy k87 T)) (t : Tm) (wf0 : (wfTm (HS tm k87) t)) IHt170 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTm_abs k88 (tshift_wfTy k87 T wf c16 k88 (weaken_shifthvl_ty H0 ins)) (IHt170 c16 (HS tm k88) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k87 : Hvl) (t1 : Tm) (wf : (wfTm k87 t1)) IHt170 (t2 : Tm) (wf0 : (wfTm k87 t2)) IHt171 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTm_app k88 (IHt170 c16 k88 (weaken_shifthvl_ty H0 ins)) (IHt171 c16 k88 (weaken_shifthvl_ty H0 ins)))) (fun (k87 : Hvl) (T : Ty) (wf : (wfTy k87 T)) (t : Tm) (wf0 : (wfTm (HS ty k87) t)) IHt170 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTm_tabs k88 (tshift_wfTy k87 T wf c16 k88 (weaken_shifthvl_ty H0 ins)) (IHt170 (CS c16) (HS ty k88) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k87 : Hvl) (t : Tm) (wf : (wfTm k87 t)) IHt170 (T : Ty) (wf0 : (wfTy k87 T)) (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTm_tapp k88 (IHt170 c16 k88 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k87 T wf0 c16 k88 (weaken_shifthvl_ty H0 ins)))) (fun (k87 : Hvl) (ts : Rec) (wf : (wfRec k87 ts)) IHts37 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTm_rec k88 (IHts37 c16 k88 (weaken_shifthvl_ty H0 ins)))) (fun (k87 : Hvl) (t : Tm) (wf : (wfTm k87 t)) IHt170 (l : Lab) (wf0 : (wfLab k87 l)) (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTm_prj k88 (IHt170 c16 k88 (weaken_shifthvl_ty H0 ins)) (tshift_wfLab k87 l wf0 c16 k88 (weaken_shifthvl_ty H0 ins)))) (fun (k87 : Hvl) (p : Pat) (wf : (wfPat k87 p)) (t1 : Tm) (wf0 : (wfTm k87 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm (appendHvl k87 (bindPat p)) t2)) IHt171 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfTm_lett k88 (tshift_wfPat k87 p wf c16 k88 (weaken_shifthvl_ty H0 ins)) (IHt170 c16 k88 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k88) (f_equal2 appendHvl (eq_sym (stability_tshift_bindPat _ _)) (eq_refl H0))) eq_refl (IHt171 (weakenCutoffty c16 (bindPat p)) (appendHvl k88 (bindPat p)) (weaken_shifthvl_ty (bindPat p) ins))))) (fun (k87 : Hvl) (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfRec_rnil k88)) (fun (k87 : Hvl) (l : Lab) (wf : (wfLab k87 l)) (t : Tm) (wf0 : (wfTm k87 t)) IHt170 (ts : Rec) (wf1 : (wfRec k87 ts)) IHts37 (c16 : (Cutoff ty)) (k88 : Hvl) (ins : (shifthvl_ty c16 k87 k88)) =>
    (wfRec_rcons k88 (tshift_wfLab k87 l wf c16 k88 (weaken_shifthvl_ty H0 ins)) (IHt170 c16 k88 (weaken_shifthvl_ty H0 ins)) (IHts37 c16 k88 (weaken_shifthvl_ty H0 ins))))).
  Lemma tshift_wfTm (k87 : Hvl) :
    (forall (s24 : Tm) (wf : (wfTm k87 s24)) ,
      (forall (c16 : (Cutoff ty)) (k88 : Hvl) ,
        (shifthvl_ty c16 k87 k88) -> (wfTm k88 (tshiftTm c16 s24)))).
  Proof.
    pose proof ((tshift_wfTm_Rec k87)).
    destruct_conjs .
    easy .
  Qed.
  Lemma tshift_wfRec (k87 : Hvl) :
    (forall (ss : Rec) (wf0 : (wfRec k87 ss)) ,
      (forall (c17 : (Cutoff ty)) (k89 : Hvl) ,
        (shifthvl_ty c17 k87 k89) -> (wfRec k89 (tshiftRec c17 ss)))).
  Proof.
    pose proof ((tshift_wfTm_Rec k87)).
    destruct_conjs .
    easy .
  Qed.
End ShiftWellFormed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfLab shift_wfPRec shift_wfPat shift_wfRec shift_wfTRec shift_wfTm shift_wfTy tshift_wfLab tshift_wfPRec tshift_wfPat tshift_wfRec tshift_wfTRec tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfLab shift_wfPRec shift_wfPat shift_wfRec shift_wfTRec shift_wfTm shift_wfTy tshift_wfLab tshift_wfPRec tshift_wfPat tshift_wfRec tshift_wfTRec tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfLab shift_wfPRec shift_wfPat shift_wfRec shift_wfTRec shift_wfTm shift_wfTy tshift_wfLab tshift_wfPRec tshift_wfPat tshift_wfRec tshift_wfTRec tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfLab shift_wfPRec shift_wfPat shift_wfRec shift_wfTRec shift_wfTm shift_wfTy tshift_wfLab tshift_wfPRec tshift_wfPat tshift_wfRec tshift_wfTRec tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_tm (k87 : Hvl) : (forall (d78 : (Trace tm)) (k88 : Hvl) (k89 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k87 X0 (HS tm k87) k87)
    | substhvl_tm_there_tm
        {d78 : (Trace tm)} {k88 : Hvl}
        {k89 : Hvl} :
        (substhvl_tm k87 d78 k88 k89) -> (substhvl_tm k87 (XS tm d78) (HS tm k88) (HS tm k89))
    | substhvl_tm_there_ty
        {d78 : (Trace tm)} {k88 : Hvl}
        {k89 : Hvl} :
        (substhvl_tm k87 d78 k88 k89) -> (substhvl_tm k87 (XS ty d78) (HS ty k88) (HS ty k89)).
  Inductive substhvl_ty (k87 : Hvl) : (forall (d78 : (Trace ty)) (k88 : Hvl) (k89 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k87 X0 (HS ty k87) k87)
    | substhvl_ty_there_tm
        {d78 : (Trace ty)} {k88 : Hvl}
        {k89 : Hvl} :
        (substhvl_ty k87 d78 k88 k89) -> (substhvl_ty k87 (XS tm d78) (HS tm k88) (HS tm k89))
    | substhvl_ty_there_ty
        {d78 : (Trace ty)} {k88 : Hvl}
        {k89 : Hvl} :
        (substhvl_ty k87 d78 k88 k89) -> (substhvl_ty k87 (XS ty d78) (HS ty k88) (HS ty k89)).
  Lemma weaken_substhvl_tm  :
    (forall {k88 : Hvl} (k87 : Hvl) {d78 : (Trace tm)} {k89 : Hvl} {k90 : Hvl} ,
      (substhvl_tm k88 d78 k89 k90) -> (substhvl_tm k88 (weakenTrace d78 k87) (appendHvl k89 k87) (appendHvl k90 k87))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k88 : Hvl} (k87 : Hvl) {d78 : (Trace ty)} {k89 : Hvl} {k90 : Hvl} ,
      (substhvl_ty k88 d78 k89 k90) -> (substhvl_ty k88 (weakenTrace d78 k87) (appendHvl k89 k87) (appendHvl k90 k87))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k97 : Hvl} {s24 : Tm} (wft : (wfTm k97 s24)) :
    (forall {d78 : (Trace tm)} {k98 : Hvl} {k99 : Hvl} ,
      (substhvl_tm k97 d78 k98 k99) -> (forall {x59 : (Index tm)} ,
        (wfindex k98 x59) -> (wfTm k99 (substIndex d78 s24 x59)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k97 : Hvl} {S66 : Ty} (wft : (wfTy k97 S66)) :
    (forall {d78 : (Trace ty)} {k98 : Hvl} {k99 : Hvl} ,
      (substhvl_ty k97 d78 k98 k99) -> (forall {X43 : (Index ty)} ,
        (wfindex k98 X43) -> (wfTy k99 (tsubstIndex d78 S66 X43)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k97 : Hvl} :
    (forall {d78 : (Trace tm)} {k98 : Hvl} {k99 : Hvl} ,
      (substhvl_tm k97 d78 k98 k99) -> (forall {X43 : (Index ty)} ,
        (wfindex k98 X43) -> (wfindex k99 X43))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k97 : Hvl} :
    (forall {d78 : (Trace ty)} {k98 : Hvl} {k99 : Hvl} ,
      (substhvl_ty k97 d78 k98 k99) -> (forall {x59 : (Index tm)} ,
        (wfindex k98 x59) -> (wfindex k99 x59))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfLab {k97 : Hvl} : (forall (k98 : Hvl) ,
    (forall (l52 : Lab) (wf0 : (wfLab k98 l52)) ,
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfLab k99 l52)))) := (fun (k98 : Hvl) =>
    (ind_wfLab k98 (fun (l52 : Lab) (wf0 : (wfLab k98 l52)) =>
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfLab k99 l52))) (fun {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
      (wfLab_L0 k99)) (fun (l : Lab) (wf0 : (wfLab k98 l)) IHl {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
      (wfLab_LS k99 (IHl (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_ty_wfLab {k97 : Hvl} : (forall (k98 : Hvl) ,
    (forall (l52 : Lab) (wf0 : (wfLab k98 l52)) ,
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfLab k99 l52)))) := (fun (k98 : Hvl) =>
    (ind_wfLab k98 (fun (l52 : Lab) (wf0 : (wfLab k98 l52)) =>
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfLab k99 l52))) (fun {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
      (wfLab_L0 k99)) (fun (l : Lab) (wf0 : (wfLab k98 l)) IHl {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
      (wfLab_LS k99 (IHl (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)))))).
  Definition substhvl_tm_wfTRec_Ty {k97 : Hvl} : (forall (k98 : Hvl) ,
    (forall (SS0 : TRec) (wf0 : (wfTRec k98 SS0)) ,
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfTRec k99 SS0))) /\
    (forall (S66 : Ty) (wf0 : (wfTy k98 S66)) ,
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfTy k99 S66)))) := (ind_wfTRec_Ty (fun (k98 : Hvl) (SS0 : TRec) (wf0 : (wfTRec k98 SS0)) =>
    (forall {d78 : (Trace tm)} {k99 : Hvl} ,
      (substhvl_tm k97 d78 k98 k99) -> (wfTRec k99 SS0))) (fun (k98 : Hvl) (S66 : Ty) (wf0 : (wfTy k98 S66)) =>
    (forall {d78 : (Trace tm)} {k99 : Hvl} ,
      (substhvl_tm k97 d78 k98 k99) -> (wfTy k99 S66))) (fun (k98 : Hvl) {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTRec_tnil k99)) (fun (k98 : Hvl) (l : Lab) (wf0 : (wfLab k98 l)) (T : Ty) (wf1 : (wfTy k98 T)) IHT5 (TS : TRec) (wf2 : (wfTRec k98 TS)) IHTS13 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTRec_tcons k99 (substhvl_tm_wfLab k98 l wf0 (weaken_substhvl_tm H0 del)) (IHT5 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)) (IHTS13 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)))) (fun (k98 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k98 X43)) {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTy_tvar k99 (substhvl_tm_wfindex_ty del wfi))) (fun (k98 : Hvl) {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTy_top k99)) (fun (k98 : Hvl) (T1 : Ty) (wf0 : (wfTy k98 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k98 T2)) IHT6 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTy_tarr k99 (IHT5 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)) (IHT6 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)))) (fun (k98 : Hvl) (T1 : Ty) (wf0 : (wfTy k98 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy (HS ty k98) T2)) IHT6 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTy_tall k99 (IHT5 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)) (IHT6 (weakenTrace d78 (HS ty H0)) (HS ty k99) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k98 : Hvl) (TS : TRec) (wf0 : (wfTRec k98 TS)) IHTS13 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTy_trec k99 (IHTS13 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del))))).
  Lemma substhvl_tm_wfTRec {k97 : Hvl} (k98 : Hvl) (SS0 : TRec) (wf0 : (wfTRec k98 SS0)) :
    (forall {d78 : (Trace tm)} {k99 : Hvl} ,
      (substhvl_tm k97 d78 k98 k99) -> (wfTRec k99 SS0)).
  Proof.
    apply ((substhvl_tm_wfTRec_Ty k98)).
    auto .
  Qed.
  Lemma substhvl_tm_wfTy {k97 : Hvl} (k98 : Hvl) (S66 : Ty) (wf1 : (wfTy k98 S66)) :
    (forall {d79 : (Trace tm)} {k100 : Hvl} ,
      (substhvl_tm k97 d79 k98 k100) -> (wfTy k100 S66)).
  Proof.
    apply ((substhvl_tm_wfTRec_Ty k98)).
    auto .
  Qed.
  Definition substhvl_ty_wfTRec_Ty {k97 : Hvl} {S66 : Ty} (wf : (wfTy k97 S66)) : (forall (k98 : Hvl) ,
    (forall (SS0 : TRec) (wf0 : (wfTRec k98 SS0)) ,
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfTRec k99 (tsubstTRec d78 S66 SS0)))) /\
    (forall (S67 : Ty) (wf0 : (wfTy k98 S67)) ,
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfTy k99 (tsubstTy d78 S66 S67))))) := (ind_wfTRec_Ty (fun (k98 : Hvl) (SS0 : TRec) (wf0 : (wfTRec k98 SS0)) =>
    (forall {d78 : (Trace ty)} {k99 : Hvl} ,
      (substhvl_ty k97 d78 k98 k99) -> (wfTRec k99 (tsubstTRec d78 S66 SS0)))) (fun (k98 : Hvl) (S67 : Ty) (wf0 : (wfTy k98 S67)) =>
    (forall {d78 : (Trace ty)} {k99 : Hvl} ,
      (substhvl_ty k97 d78 k98 k99) -> (wfTy k99 (tsubstTy d78 S66 S67)))) (fun (k98 : Hvl) {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTRec_tnil k99)) (fun (k98 : Hvl) (l : Lab) (wf0 : (wfLab k98 l)) (T : Ty) (wf1 : (wfTy k98 T)) IHT5 (TS : TRec) (wf2 : (wfTRec k98 TS)) IHTS13 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTRec_tcons k99 (substhvl_ty_wfLab k98 l wf0 (weaken_substhvl_ty H0 del)) (IHT5 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)) (IHTS13 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)))) (fun (k98 : Hvl) {X43 : (Index ty)} (wfi : (wfindex k98 X43)) {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k98 : Hvl) {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTy_top k99)) (fun (k98 : Hvl) (T1 : Ty) (wf0 : (wfTy k98 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy k98 T2)) IHT6 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTy_tarr k99 (IHT5 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)) (IHT6 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)))) (fun (k98 : Hvl) (T1 : Ty) (wf0 : (wfTy k98 T1)) IHT5 (T2 : Ty) (wf1 : (wfTy (HS ty k98) T2)) IHT6 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTy_tall k99 (IHT5 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)) (IHT6 (weakenTrace d78 (HS ty H0)) (HS ty k99) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k98 : Hvl) (TS : TRec) (wf0 : (wfTRec k98 TS)) IHTS13 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTy_trec k99 (IHTS13 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del))))).
  Lemma substhvl_ty_wfTRec {k97 : Hvl} {S66 : Ty} (wf : (wfTy k97 S66)) (k98 : Hvl) (SS0 : TRec) (wf0 : (wfTRec k98 SS0)) :
    (forall {d78 : (Trace ty)} {k99 : Hvl} ,
      (substhvl_ty k97 d78 k98 k99) -> (wfTRec k99 (tsubstTRec d78 S66 SS0))).
  Proof.
    apply ((substhvl_ty_wfTRec_Ty wf k98)).
    auto .
  Qed.
  Lemma substhvl_ty_wfTy {k97 : Hvl} {S66 : Ty} (wf : (wfTy k97 S66)) (k98 : Hvl) (S67 : Ty) (wf1 : (wfTy k98 S67)) :
    (forall {d79 : (Trace ty)} {k100 : Hvl} ,
      (substhvl_ty k97 d79 k98 k100) -> (wfTy k100 (tsubstTy d79 S66 S67))).
  Proof.
    apply ((substhvl_ty_wfTRec_Ty wf k98)).
    auto .
  Qed.
  Definition substhvl_tm_wfPat_PRec {k97 : Hvl} : (forall (k98 : Hvl) ,
    (forall (p30 : Pat) (wf0 : (wfPat k98 p30)) ,
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfPat k99 p30))) /\
    (forall (ps18 : PRec) (wf0 : (wfPRec k98 ps18)) ,
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfPRec k99 ps18)))) := (fun (k98 : Hvl) =>
    (ind_wfPat_PRec k98 (fun (p30 : Pat) (wf0 : (wfPat k98 p30)) =>
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfPat k99 p30))) (fun (ps18 : PRec) (wf0 : (wfPRec k98 ps18)) =>
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfPRec k99 ps18))) (fun (T : Ty) (wf0 : (wfTy k98 T)) {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
      (wfPat_pvar k99 (substhvl_tm_wfTy k98 T wf0 (weaken_substhvl_tm H0 del)))) (fun (ps : PRec) (wf0 : (wfPRec k98 ps)) IHps {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
      (wfPat_prec k99 (IHps (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)))) (fun {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
      (wfPRec_pnil k99)) (fun (l : Lab) (wf0 : (wfLab k98 l)) (p : Pat) (wf1 : (wfPat k98 p)) IHp (ps : PRec) (wf2 : (wfPRec k98 ps)) IHps {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
      (wfPRec_pcons k99 (substhvl_tm_wfLab k98 l wf0 (weaken_substhvl_tm H0 del)) (IHp (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)) (IHps (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)))))).
  Lemma substhvl_tm_wfPat {k97 : Hvl} (k98 : Hvl) (p30 : Pat) (wf0 : (wfPat k98 p30)) :
    (forall {d78 : (Trace tm)} {k99 : Hvl} ,
      (substhvl_tm k97 d78 k98 k99) -> (wfPat k99 p30)).
  Proof.
    apply ((substhvl_tm_wfPat_PRec k98)).
    auto .
  Qed.
  Lemma substhvl_tm_wfPRec {k97 : Hvl} (k98 : Hvl) (ps18 : PRec) (wf1 : (wfPRec k98 ps18)) :
    (forall {d79 : (Trace tm)} {k100 : Hvl} ,
      (substhvl_tm k97 d79 k98 k100) -> (wfPRec k100 ps18)).
  Proof.
    apply ((substhvl_tm_wfPat_PRec k98)).
    auto .
  Qed.
  Definition substhvl_ty_wfPat_PRec {k97 : Hvl} {S66 : Ty} (wf : (wfTy k97 S66)) : (forall (k98 : Hvl) ,
    (forall (p30 : Pat) (wf0 : (wfPat k98 p30)) ,
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfPat k99 (tsubstPat d78 S66 p30)))) /\
    (forall (ps18 : PRec) (wf0 : (wfPRec k98 ps18)) ,
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfPRec k99 (tsubstPRec d78 S66 ps18))))) := (fun (k98 : Hvl) =>
    (ind_wfPat_PRec k98 (fun (p30 : Pat) (wf0 : (wfPat k98 p30)) =>
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfPat k99 (tsubstPat d78 S66 p30)))) (fun (ps18 : PRec) (wf0 : (wfPRec k98 ps18)) =>
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfPRec k99 (tsubstPRec d78 S66 ps18)))) (fun (T : Ty) (wf0 : (wfTy k98 T)) {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
      (wfPat_pvar k99 (substhvl_ty_wfTy wf k98 T wf0 (weaken_substhvl_ty H0 del)))) (fun (ps : PRec) (wf0 : (wfPRec k98 ps)) IHps {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
      (wfPat_prec k99 (IHps (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)))) (fun {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
      (wfPRec_pnil k99)) (fun (l : Lab) (wf0 : (wfLab k98 l)) (p : Pat) (wf1 : (wfPat k98 p)) IHp (ps : PRec) (wf2 : (wfPRec k98 ps)) IHps {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
      (wfPRec_pcons k99 (substhvl_ty_wfLab k98 l wf0 (weaken_substhvl_ty H0 del)) (IHp (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)) (IHps (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)))))).
  Lemma substhvl_ty_wfPat {k97 : Hvl} {S66 : Ty} (wf : (wfTy k97 S66)) (k98 : Hvl) (p30 : Pat) (wf0 : (wfPat k98 p30)) :
    (forall {d78 : (Trace ty)} {k99 : Hvl} ,
      (substhvl_ty k97 d78 k98 k99) -> (wfPat k99 (tsubstPat d78 S66 p30))).
  Proof.
    apply ((substhvl_ty_wfPat_PRec wf k98)).
    auto .
  Qed.
  Lemma substhvl_ty_wfPRec {k97 : Hvl} {S66 : Ty} (wf : (wfTy k97 S66)) (k98 : Hvl) (ps18 : PRec) (wf1 : (wfPRec k98 ps18)) :
    (forall {d79 : (Trace ty)} {k100 : Hvl} ,
      (substhvl_ty k97 d79 k98 k100) -> (wfPRec k100 (tsubstPRec d79 S66 ps18))).
  Proof.
    apply ((substhvl_ty_wfPat_PRec wf k98)).
    auto .
  Qed.
  Definition substhvl_tm_wfTm_Rec {k97 : Hvl} {s24 : Tm} (wf : (wfTm k97 s24)) : (forall (k98 : Hvl) ,
    (forall (s25 : Tm) (wf0 : (wfTm k98 s25)) ,
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfTm k99 (substTm d78 s24 s25)))) /\
    (forall (ss : Rec) (wf0 : (wfRec k98 ss)) ,
      (forall {d78 : (Trace tm)} {k99 : Hvl} ,
        (substhvl_tm k97 d78 k98 k99) -> (wfRec k99 (substRec d78 s24 ss))))) := (ind_wfTm_Rec (fun (k98 : Hvl) (s25 : Tm) (wf0 : (wfTm k98 s25)) =>
    (forall {d78 : (Trace tm)} {k99 : Hvl} ,
      (substhvl_tm k97 d78 k98 k99) -> (wfTm k99 (substTm d78 s24 s25)))) (fun (k98 : Hvl) (ss : Rec) (wf0 : (wfRec k98 ss)) =>
    (forall {d78 : (Trace tm)} {k99 : Hvl} ,
      (substhvl_tm k97 d78 k98 k99) -> (wfRec k99 (substRec d78 s24 ss)))) (fun (k98 : Hvl) {x59 : (Index tm)} (wfi : (wfindex k98 x59)) {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k98 : Hvl) (T : Ty) (wf0 : (wfTy k98 T)) (t : Tm) (wf1 : (wfTm (HS tm k98) t)) IHt170 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTm_abs k99 (substhvl_tm_wfTy k98 T wf0 (weaken_substhvl_tm H0 del)) (IHt170 (weakenTrace d78 (HS tm H0)) (HS tm k99) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k98 : Hvl) (t1 : Tm) (wf0 : (wfTm k98 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k98 t2)) IHt171 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTm_app k99 (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)) (IHt171 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)))) (fun (k98 : Hvl) (T : Ty) (wf0 : (wfTy k98 T)) (t : Tm) (wf1 : (wfTm (HS ty k98) t)) IHt170 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTm_tabs k99 (substhvl_tm_wfTy k98 T wf0 (weaken_substhvl_tm H0 del)) (IHt170 (weakenTrace d78 (HS ty H0)) (HS ty k99) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k98 : Hvl) (t : Tm) (wf0 : (wfTm k98 t)) IHt170 (T : Ty) (wf1 : (wfTy k98 T)) {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTm_tapp k99 (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k98 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k98 : Hvl) (ts : Rec) (wf0 : (wfRec k98 ts)) IHts37 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTm_rec k99 (IHts37 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)))) (fun (k98 : Hvl) (t : Tm) (wf0 : (wfTm k98 t)) IHt170 (l : Lab) (wf1 : (wfLab k98 l)) {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTm_prj k99 (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfLab k98 l wf1 (weaken_substhvl_tm H0 del)))) (fun (k98 : Hvl) (p : Pat) (wf0 : (wfPat k98 p)) (t1 : Tm) (wf1 : (wfTm k98 t1)) IHt170 (t2 : Tm) (wf2 : (wfTm (appendHvl k98 (bindPat p)) t2)) IHt171 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfTm_lett k99 (substhvl_tm_wfPat k98 p wf0 (weaken_substhvl_tm H0 del)) (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)) (IHt171 (weakenTrace d78 (bindPat p)) (appendHvl k99 (bindPat p)) (weaken_substhvl_tm (bindPat p) del)))) (fun (k98 : Hvl) {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfRec_rnil k99)) (fun (k98 : Hvl) (l : Lab) (wf0 : (wfLab k98 l)) (t : Tm) (wf1 : (wfTm k98 t)) IHt170 (ts : Rec) (wf2 : (wfRec k98 ts)) IHts37 {d78 : (Trace tm)} {k99 : Hvl} (del : (substhvl_tm k97 d78 k98 k99)) =>
    (wfRec_rcons k99 (substhvl_tm_wfLab k98 l wf0 (weaken_substhvl_tm H0 del)) (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del)) (IHts37 (weakenTrace d78 H0) k99 (weaken_substhvl_tm H0 del))))).
  Lemma substhvl_tm_wfTm {k97 : Hvl} {s24 : Tm} (wf : (wfTm k97 s24)) (k98 : Hvl) (s25 : Tm) (wf0 : (wfTm k98 s25)) :
    (forall {d78 : (Trace tm)} {k99 : Hvl} ,
      (substhvl_tm k97 d78 k98 k99) -> (wfTm k99 (substTm d78 s24 s25))).
  Proof.
    apply ((substhvl_tm_wfTm_Rec wf k98)).
    auto .
  Qed.
  Lemma substhvl_tm_wfRec {k97 : Hvl} {s24 : Tm} (wf : (wfTm k97 s24)) (k98 : Hvl) (ss : Rec) (wf1 : (wfRec k98 ss)) :
    (forall {d79 : (Trace tm)} {k100 : Hvl} ,
      (substhvl_tm k97 d79 k98 k100) -> (wfRec k100 (substRec d79 s24 ss))).
  Proof.
    apply ((substhvl_tm_wfTm_Rec wf k98)).
    auto .
  Qed.
  Definition substhvl_ty_wfTm_Rec {k97 : Hvl} {S66 : Ty} (wf : (wfTy k97 S66)) : (forall (k98 : Hvl) ,
    (forall (s24 : Tm) (wf0 : (wfTm k98 s24)) ,
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfTm k99 (tsubstTm d78 S66 s24)))) /\
    (forall (ss : Rec) (wf0 : (wfRec k98 ss)) ,
      (forall {d78 : (Trace ty)} {k99 : Hvl} ,
        (substhvl_ty k97 d78 k98 k99) -> (wfRec k99 (tsubstRec d78 S66 ss))))) := (ind_wfTm_Rec (fun (k98 : Hvl) (s24 : Tm) (wf0 : (wfTm k98 s24)) =>
    (forall {d78 : (Trace ty)} {k99 : Hvl} ,
      (substhvl_ty k97 d78 k98 k99) -> (wfTm k99 (tsubstTm d78 S66 s24)))) (fun (k98 : Hvl) (ss : Rec) (wf0 : (wfRec k98 ss)) =>
    (forall {d78 : (Trace ty)} {k99 : Hvl} ,
      (substhvl_ty k97 d78 k98 k99) -> (wfRec k99 (tsubstRec d78 S66 ss)))) (fun (k98 : Hvl) {x59 : (Index tm)} (wfi : (wfindex k98 x59)) {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTm_var k99 (substhvl_ty_wfindex_tm del wfi))) (fun (k98 : Hvl) (T : Ty) (wf0 : (wfTy k98 T)) (t : Tm) (wf1 : (wfTm (HS tm k98) t)) IHt170 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTm_abs k99 (substhvl_ty_wfTy wf k98 T wf0 (weaken_substhvl_ty H0 del)) (IHt170 (weakenTrace d78 (HS tm H0)) (HS tm k99) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k98 : Hvl) (t1 : Tm) (wf0 : (wfTm k98 t1)) IHt170 (t2 : Tm) (wf1 : (wfTm k98 t2)) IHt171 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTm_app k99 (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)) (IHt171 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)))) (fun (k98 : Hvl) (T : Ty) (wf0 : (wfTy k98 T)) (t : Tm) (wf1 : (wfTm (HS ty k98) t)) IHt170 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTm_tabs k99 (substhvl_ty_wfTy wf k98 T wf0 (weaken_substhvl_ty H0 del)) (IHt170 (weakenTrace d78 (HS ty H0)) (HS ty k99) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k98 : Hvl) (t : Tm) (wf0 : (wfTm k98 t)) IHt170 (T : Ty) (wf1 : (wfTy k98 T)) {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTm_tapp k99 (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k98 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k98 : Hvl) (ts : Rec) (wf0 : (wfRec k98 ts)) IHts37 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTm_rec k99 (IHts37 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)))) (fun (k98 : Hvl) (t : Tm) (wf0 : (wfTm k98 t)) IHt170 (l : Lab) (wf1 : (wfLab k98 l)) {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTm_prj k99 (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfLab k98 l wf1 (weaken_substhvl_ty H0 del)))) (fun (k98 : Hvl) (p : Pat) (wf0 : (wfPat k98 p)) (t1 : Tm) (wf1 : (wfTm k98 t1)) IHt170 (t2 : Tm) (wf2 : (wfTm (appendHvl k98 (bindPat p)) t2)) IHt171 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfTm_lett k99 (substhvl_ty_wfPat wf k98 p wf0 (weaken_substhvl_ty H0 del)) (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k99) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))) eq_refl (IHt171 (weakenTrace d78 (bindPat p)) (appendHvl k99 (bindPat p)) (weaken_substhvl_ty (bindPat p) del))))) (fun (k98 : Hvl) {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfRec_rnil k99)) (fun (k98 : Hvl) (l : Lab) (wf0 : (wfLab k98 l)) (t : Tm) (wf1 : (wfTm k98 t)) IHt170 (ts : Rec) (wf2 : (wfRec k98 ts)) IHts37 {d78 : (Trace ty)} {k99 : Hvl} (del : (substhvl_ty k97 d78 k98 k99)) =>
    (wfRec_rcons k99 (substhvl_ty_wfLab k98 l wf0 (weaken_substhvl_ty H0 del)) (IHt170 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del)) (IHts37 (weakenTrace d78 H0) k99 (weaken_substhvl_ty H0 del))))).
  Lemma substhvl_ty_wfTm {k97 : Hvl} {S66 : Ty} (wf : (wfTy k97 S66)) (k98 : Hvl) (s24 : Tm) (wf0 : (wfTm k98 s24)) :
    (forall {d78 : (Trace ty)} {k99 : Hvl} ,
      (substhvl_ty k97 d78 k98 k99) -> (wfTm k99 (tsubstTm d78 S66 s24))).
  Proof.
    apply ((substhvl_ty_wfTm_Rec wf k98)).
    auto .
  Qed.
  Lemma substhvl_ty_wfRec {k97 : Hvl} {S66 : Ty} (wf : (wfTy k97 S66)) (k98 : Hvl) (ss : Rec) (wf1 : (wfRec k98 ss)) :
    (forall {d79 : (Trace ty)} {k100 : Hvl} ,
      (substhvl_ty k97 d79 k98 k100) -> (wfRec k100 (tsubstRec d79 S66 ss))).
  Proof.
    apply ((substhvl_ty_wfTm_Rec wf k98)).
    auto .
  Qed.
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfLab substhvl_tm_wfPRec substhvl_tm_wfPat substhvl_tm_wfRec substhvl_tm_wfTRec substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfLab substhvl_ty_wfPRec substhvl_ty_wfPat substhvl_ty_wfRec substhvl_ty_wfTRec substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfLab substhvl_tm_wfPRec substhvl_tm_wfPat substhvl_tm_wfRec substhvl_tm_wfTRec substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfLab substhvl_ty_wfPRec substhvl_ty_wfPat substhvl_ty_wfRec substhvl_ty_wfTRec substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfLab substhvl_tm_wfPRec substhvl_tm_wfPat substhvl_tm_wfRec substhvl_tm_wfTRec substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfLab substhvl_ty_wfPRec substhvl_ty_wfPat substhvl_ty_wfRec substhvl_ty_wfTRec substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfLab substhvl_tm_wfPRec substhvl_tm_wfPat substhvl_tm_wfRec substhvl_tm_wfTRec substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfLab substhvl_ty_wfPRec substhvl_ty_wfPat substhvl_ty_wfRec substhvl_ty_wfTRec substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Fixpoint subhvl_tm (k97 : Hvl) {struct k97} : Prop :=
  match k97 with
    | (H0) => True
    | (HS a k97) => match a with
      | (tm) => (subhvl_tm k97)
      | _ => False
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k97 : Hvl) (k98 : Hvl) ,
    (subhvl_tm k97) -> (subhvl_tm k98) -> (subhvl_tm (appendHvl k97 k98))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfLab_strengthen_subhvl_tm  :
  (forall (k88 : Hvl) (k87 : Hvl) (l51 : Lab) ,
    (subhvl_tm k88) -> (wfLab (appendHvl k87 k88) (weakenLab l51 k88)) -> (wfLab k87 l51)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfPRec_strengthen_subhvl_tm  :
  (forall (k90 : Hvl) (k89 : Hvl) (ps17 : PRec) ,
    (subhvl_tm k90) -> (wfPRec (appendHvl k89 k90) (weakenPRec ps17 k90)) -> (wfPRec k89 ps17)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfPat_strengthen_subhvl_tm  :
  (forall (k92 : Hvl) (k91 : Hvl) (p29 : Pat) ,
    (subhvl_tm k92) -> (wfPat (appendHvl k91 k92) (weakenPat p29 k92)) -> (wfPat k91 p29)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTRec_strengthen_subhvl_tm  :
  (forall (k94 : Hvl) (k93 : Hvl) (SS : TRec) ,
    (subhvl_tm k94) -> (wfTRec (appendHvl k93 k94) (weakenTRec SS k94)) -> (wfTRec k93 SS)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k96 : Hvl) (k95 : Hvl) (S65 : Ty) ,
    (subhvl_tm k96) -> (wfTy (appendHvl k95 k96) (weakenTy S65 k96)) -> (wfTy k95 S65)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfLab _ _)) => match goal with
  | H : (wfLab (appendHvl _ _) (weakenLab _ _)) |- _ => apply (wfLab_strengthen_subhvl_tm) in H
end : infra wf.
 Hint Extern 2 ((wfPRec _ _)) => match goal with
  | H0 : (wfPRec (appendHvl _ _) (weakenPRec _ _)) |- _ => apply (wfPRec_strengthen_subhvl_tm) in H0
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H1 : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_tm) in H1
end : infra wf.
 Hint Extern 2 ((wfTRec _ _)) => match goal with
  | H2 : (wfTRec (appendHvl _ _) (weakenTRec _ _)) |- _ => apply (wfTRec_strengthen_subhvl_tm) in H2
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H3 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_tm) in H3
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
  Fixpoint shiftEnv (c16 : (Cutoff tm)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftEnv c16 G0) T)
      | (etvar G0 T) => (etvar (shiftEnv c16 G0) T)
    end.
  Fixpoint tshiftEnv (c16 : (Cutoff ty)) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c16 G0) (tshiftTy (weakenCutoffty c16 (domainEnv G0)) T))
      | (etvar G0 T) => (etvar (tshiftEnv c16 G0) (tshiftTy (weakenCutoffty c16 (domainEnv G0)) T))
    end.
  Fixpoint substEnv (d78 : (Trace tm)) (s24 : Tm) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d78 s24 G0) T)
      | (etvar G0 T) => (etvar (substEnv d78 s24 G0) T)
    end.
  Fixpoint tsubstEnv (d78 : (Trace ty)) (S66 : Ty) (G : Env) : Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d78 S66 G0) (tsubstTy (weakenTrace d78 (domainEnv G0)) S66 T))
      | (etvar G0 T) => (etvar (tsubstEnv d78 S66 G0) (tsubstTy (weakenTrace d78 (domainEnv G0)) S66 T))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c16 : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c16 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c16 : (Cutoff ty)) (G : Env) ,
      ((domainEnv (tshiftEnv c16 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d78 : (Trace tm)) (s24 : Tm) (G : Env) ,
      ((domainEnv (substEnv d78 s24 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d78 : (Trace ty)) (S66 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d78 S66 G)) =
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
      (forall (c16 : (Cutoff tm)) (G : Env) (G0 : Env) ,
        ((shiftEnv c16 (appendEnv G G0)) =
        (appendEnv (shiftEnv c16 G) (shiftEnv (weakenCutofftm c16 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftEnv_appendEnv  :
      (forall (c16 : (Cutoff ty)) (G : Env) (G0 : Env) ,
        ((tshiftEnv c16 (appendEnv G G0)) =
        (appendEnv (tshiftEnv c16 G) (tshiftEnv (weakenCutoffty c16 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d78 : (Trace tm)) (s24 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d78 s24 (appendEnv G G0)) =
        (appendEnv (substEnv d78 s24 G) (substEnv (weakenTrace d78 (domainEnv G)) s24 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d78 : (Trace ty)) (S66 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d78 S66 (appendEnv G G0)) =
        (appendEnv (tsubstEnv d78 S66 G) (tsubstEnv (weakenTrace d78 (domainEnv G)) S66 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          {T98 : Ty} :
          (wfTy (domainEnv G) T98) -> (lookup_evar (evar G T98) I0 T98)
      | lookup_evar_there_evar
          {G : Env} {x59 : (Index tm)}
          {T98 : Ty} {T99 : Ty} :
          (lookup_evar G x59 T98) -> (lookup_evar (evar G T99) (IS x59) T98)
      | lookup_evar_there_etvar
          {G : Env} {x59 : (Index tm)}
          {T98 : Ty} {T99 : Ty} :
          (lookup_evar G x59 T98) -> (lookup_evar (etvar G T99) x59 (tshiftTy C0 T98)).
    Inductive lookup_etvar : Env -> (Index ty) -> Ty -> Prop :=
      | lookup_etvar_here {G : Env}
          {T98 : Ty} :
          (wfTy (domainEnv G) T98) -> (lookup_etvar (etvar G T98) I0 (tshiftTy C0 T98))
      | lookup_etvar_there_evar
          {G : Env} {X43 : (Index ty)}
          {T98 : Ty} {T99 : Ty} :
          (lookup_etvar G X43 T98) -> (lookup_etvar (evar G T99) X43 T98)
      | lookup_etvar_there_etvar
          {G : Env} {X43 : (Index ty)}
          {T98 : Ty} {T99 : Ty} :
          (lookup_etvar G X43 T98) -> (lookup_etvar (etvar G T99) (IS X43) (tshiftTy C0 T98)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (S66 : Ty) (S67 : Ty) ,
        (lookup_evar (evar G S66) I0 S67) -> (S66 =
        S67)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (S66 : Ty) (S67 : Ty) ,
        (lookup_etvar (etvar G S66) I0 S67) -> ((tshiftTy C0 S66) =
        S67)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x59 : (Index tm)} ,
        (forall {S66 : Ty} ,
          (lookup_evar G x59 S66) -> (forall {S67 : Ty} ,
            (lookup_evar G x59 S67) -> (S66 =
            S67)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X43 : (Index ty)} ,
        (forall {S66 : Ty} ,
          (lookup_etvar G X43 S66) -> (forall {S67 : Ty} ,
            (lookup_etvar G X43 S67) -> (S66 =
            S67)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x59 : (Index tm)} {S66 : Ty} ,
        (lookup_evar G x59 S66) -> (wfTy (domainEnv G) S66)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X43 : (Index ty)} {S66 : Ty} ,
        (lookup_etvar G X43 S66) -> (wfTy (domainEnv G) S66)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x59 : (Index tm)} {T98 : Ty} ,
        (lookup_evar G x59 T98) -> (lookup_evar (appendEnv G G0) (weakenIndextm x59 (domainEnv G0)) (weakenTy T98 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X43 : (Index ty)} {T98 : Ty} ,
        (lookup_etvar G X43 T98) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X43 (domainEnv G0)) (weakenTy T98 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x59 : (Index tm)} {S66 : Ty} ,
        (lookup_evar G x59 S66) -> (wfindex (domainEnv G) x59)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X43 : (Index ty)} {S66 : Ty} ,
        (lookup_etvar G X43 S66) -> (wfindex (domainEnv G) X43)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T98 : Ty} :
        (shift_evar C0 G (evar G T98))
    | shiftevar_there_evar
        {c16 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c16 G G0) -> (shift_evar (CS c16) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c16 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c16 G G0) -> (shift_evar c16 (etvar G T) (etvar G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c16 : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c16 G0 G1) -> (shift_evar (weakenCutofftm c16 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {T98 : Ty} :
        (shift_etvar C0 G (etvar G T98))
    | shiftetvar_there_evar
        {c16 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c16 G G0) -> (shift_etvar c16 (evar G T) (evar G0 (tshiftTy c16 T)))
    | shiftetvar_there_etvar
        {c16 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c16 G G0) -> (shift_etvar (CS c16) (etvar G T) (etvar G0 (tshiftTy c16 T))).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c16 : (Cutoff ty)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c16 G0 G1) -> (shift_etvar (weakenCutoffty c16 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (tshiftEnv c16 G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c16 : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c16 G G0) -> (shifthvl_tm c16 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c16 : (Cutoff ty)} {G : Env} {G0 : Env} ,
      (shift_etvar c16 G G0) -> (shifthvl_ty c16 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T98 : Ty) (s24 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T98 s24 X0 (evar G T98) G)
    | subst_evar_there_evar
        {d78 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T98 s24 d78 G0 G1) -> (subst_evar G T98 s24 (XS tm d78) (evar G0 T) (evar G1 T))
    | subst_evar_there_etvar
        {d78 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T98 s24 d78 G0 G1) -> (subst_evar G T98 s24 (XS ty d78) (etvar G0 T) (etvar G1 T)).
  Lemma weaken_subst_evar {G : Env} {T98 : Ty} {s24 : Tm} :
    (forall (G0 : Env) {d78 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T98 s24 d78 G1 G2) -> (subst_evar G T98 s24 (weakenTrace d78 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (T98 : Ty) (S66 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G T98 S66 X0 (etvar G T98) G)
    | subst_etvar_there_evar
        {d78 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G T98 S66 d78 G0 G1) -> (subst_etvar G T98 S66 (XS tm d78) (evar G0 T) (evar G1 (tsubstTy d78 S66 T)))
    | subst_etvar_there_etvar
        {d78 : (Trace ty)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_etvar G T98 S66 d78 G0 G1) -> (subst_etvar G T98 S66 (XS ty d78) (etvar G0 T) (etvar G1 (tsubstTy d78 S66 T))).
  Lemma weaken_subst_etvar {G : Env} {T98 : Ty} {S66 : Ty} :
    (forall (G0 : Env) {d78 : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G T98 S66 d78 G1 G2) -> (subst_etvar G T98 S66 (weakenTrace d78 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d78 S66 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s24 : Tm} {T98 : Ty} :
    (forall {d78 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T98 s24 d78 G0 G1) -> (substhvl_tm (domainEnv G) d78 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S66 : Ty} {T99 : Ty} :
    (forall {d78 : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G T99 S66 d78 G0 G1) -> (substhvl_ty (domainEnv G) d78 (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T98 : Ty} (wf : (wfTy (domainEnv G) T98)) ,
    (lookup_evar (appendEnv (evar G T98) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T98 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {T98 : Ty} (wf : (wfTy (domainEnv G) T98)) ,
    (lookup_etvar (appendEnv (etvar G T98) G0) (weakenIndexty I0 (domainEnv G0)) (weakenTy (tshiftTy C0 T98) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfLab wfPRec wfPat wfRec wfTRec wfTm wfTy : infra.
 Hint Constructors wfLab wfPRec wfPat wfRec wfTRec wfTm wfTy : wf.
 Hint Extern 10 ((wfLab _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfPRec _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfRec _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTRec _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfLab _ _)) => match goal with
  | H : (wfLab _ (L0)) |- _ => inversion H; subst; clear H
  | H : (wfLab _ (LS _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfTRec _ _)) => match goal with
  | H : (wfTRec _ (tnil)) |- _ => inversion H; subst; clear H
  | H : (wfTRec _ (tcons _ _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H : (wfTy _ (tvar _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (top)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tarr _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (tall _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTy _ (trec _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H : (wfPat _ (pvar _)) |- _ => inversion H; subst; clear H
  | H : (wfPat _ (prec _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfPRec _ _)) => match goal with
  | H : (wfPRec _ (pnil)) |- _ => inversion H; subst; clear H
  | H : (wfPRec _ (pcons _ _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H : (wfTm _ (var _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (abs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (app _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tabs _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (tapp _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (rec _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (prj _ _)) |- _ => inversion H; subst; clear H
  | H : (wfTm _ (lett _ _ _)) |- _ => inversion H; subst; clear H
end : infra wf.
 Hint Extern 2 ((wfRec _ _)) => match goal with
  | H : (wfRec _ (rnil)) |- _ => inversion H; subst; clear H
  | H : (wfRec _ (rcons _ _ _)) |- _ => inversion H; subst; clear H
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
  (forall {c16 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c16 G G0)) {x59 : (Index tm)} {T98 : Ty} ,
    (lookup_evar G x59 T98) -> (lookup_evar G0 (shiftIndex c16 x59) T98)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c16 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c16 G G0)) {X43 : (Index ty)} {T98 : Ty} ,
    (lookup_etvar G X43 T98) -> (lookup_etvar G0 X43 T98)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c16 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c16 G G0)) {x59 : (Index tm)} {T98 : Ty} ,
    (lookup_evar G x59 T98) -> (lookup_evar G0 x59 (tshiftTy c16 T98))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c16 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c16 G G0)) {X43 : (Index ty)} {T98 : Ty} ,
    (lookup_etvar G X43 T98) -> (lookup_etvar G0 (tshiftIndex c16 X43) (tshiftTy c16 T98))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} {T100 : Ty} {s24 : Tm} :
  (forall {d78 : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T100 s24 d78 G0 G1)) {X43 : (Index ty)} {T101 : Ty} ,
    (lookup_etvar G0 X43 T101) -> (lookup_etvar G1 X43 T101)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} {T100 : Ty} {S66 : Ty} (wf : (wfTy (domainEnv G) S66)) :
  (forall {d78 : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G T100 S66 d78 G0 G1)) {x59 : (Index tm)} {T101 : Ty} ,
    (lookup_evar G0 x59 T101) -> (lookup_evar G1 x59 (tsubstTy d78 S66 T101))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Lab (l : Lab) {struct l} : nat :=
  match l with
    | (L0) => 1
    | (LS l0) => (plus 1 (size_Lab l0))
  end.
Fixpoint size_TRec (SS : TRec) {struct SS} : nat :=
  match SS with
    | (tnil) => 1
    | (tcons l T TS) => (plus 1 (plus (size_Lab l) (plus (size_Ty T) (size_TRec TS))))
  end
with size_Ty (S0 : Ty) {struct S0} : nat :=
  match S0 with
    | (tvar X) => 1
    | (top) => 1
    | (tarr T1 T2) => (plus 1 (plus (size_Ty T1) (size_Ty T2)))
    | (tall T0 T3) => (plus 1 (plus (size_Ty T0) (size_Ty T3)))
    | (trec TS) => (plus 1 (size_TRec TS))
  end.
Fixpoint size_Pat (p : Pat) {struct p} : nat :=
  match p with
    | (pvar T) => (plus 1 (size_Ty T))
    | (prec ps) => (plus 1 (size_PRec ps))
  end
with size_PRec (ps : PRec) {struct ps} : nat :=
  match ps with
    | (pnil) => 1
    | (pcons l p ps0) => (plus 1 (plus (size_Lab l) (plus (size_Pat p) (size_PRec ps0))))
  end.
Fixpoint size_Tm (s : Tm) {struct s} : nat :=
  match s with
    | (var x) => 1
    | (abs T t) => (plus 1 (plus (size_Ty T) (size_Tm t)))
    | (app t1 t2) => (plus 1 (plus (size_Tm t1) (size_Tm t2)))
    | (tabs T0 t0) => (plus 1 (plus (size_Ty T0) (size_Tm t0)))
    | (tapp t3 T1) => (plus 1 (plus (size_Tm t3) (size_Ty T1)))
    | (rec ts) => (plus 1 (size_Rec ts))
    | (prj t4 l) => (plus 1 (plus (size_Tm t4) (size_Lab l)))
    | (lett p t5 t6) => (plus 1 (plus (size_Pat p) (plus (size_Tm t5) (size_Tm t6))))
  end
with size_Rec (ss : Rec) {struct ss} : nat :=
  match ss with
    | (rnil) => 1
    | (rcons l t ts) => (plus 1 (plus (size_Lab l) (plus (size_Tm t) (size_Rec ts))))
  end.
Lemma tshift_size_TRec_Ty  :
  (forall (SS : TRec) (c13 : (Cutoff ty)) ,
    ((size_TRec (tshiftTRec c13 SS)) =
    (size_TRec SS))) /\
  (forall (S65 : Ty) (c13 : (Cutoff ty)) ,
    ((size_Ty (tshiftTy c13 S65)) =
    (size_Ty S65))).
Proof.
  apply_mutual_ind ind_TRec_Ty.
  - intros c13; simpl; apply ((f_equal S)); reflexivity.
  - intros l45 T86 IHT86 TS11 IHTS11.
  intros c13; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHT86 c13)).
  + exact ((IHTS11 c13)).
  - intros X38 c13.
  reflexivity.
  - intros c14; simpl; apply ((f_equal S)); reflexivity.
  - intros T87 IHT87 T88 IHT88.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT87 c14)).
  + exact ((IHT88 c14)).
  - intros T89 IHT89 T90 IHT90.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT89 c14)).
  + exact ((IHT90 (CS c14))).
  - intros TS12 IHTS12.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHTS12 c14)).
Qed.

Lemma tshift_size_TRec  :
  (forall (SS : TRec) (c14 : (Cutoff ty)) ,
    ((size_TRec (tshiftTRec c14 SS)) =
    (size_TRec SS))).
Proof.
  pose proof (tshift_size_TRec_Ty).
  destruct_conjs .
  easy .
Qed.
Lemma tshift_size_Ty  :
  (forall (S65 : Ty) (c14 : (Cutoff ty)) ,
    ((size_Ty (tshiftTy c14 S65)) =
    (size_Ty S65))).
Proof.
  pose proof (tshift_size_TRec_Ty).
  destruct_conjs .
  easy .
Qed.
Lemma tshift_size_Pat_PRec  :
  (forall (p26 : Pat) (c14 : (Cutoff ty)) ,
    ((size_Pat (tshiftPat c14 p26)) =
    (size_Pat p26))) /\
  (forall (ps15 : PRec) (c14 : (Cutoff ty)) ,
    ((size_PRec (tshiftPRec c14 ps15)) =
    (size_PRec ps15))).
Proof.
  apply_mutual_ind ind_Pat_PRec.
  - intros T91.
  pose proof ((tshift_size_Ty T91)) as IHT91.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT91 c14)).
  - intros ps15 IHps15.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHps15 c14)).
  - intros c14; simpl; apply ((f_equal S)); reflexivity.
  - intros l46 p26 IHp26 ps16 IHps16.
  intros c14; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHp26 c14)).
  + exact ((IHps16 c14)).
Qed.

Lemma tshift_size_Pat  :
  (forall (p27 : Pat) (c14 : (Cutoff ty)) ,
    ((size_Pat (tshiftPat c14 p27)) =
    (size_Pat p27))).
Proof.
  pose proof (tshift_size_Pat_PRec).
  destruct_conjs .
  easy .
Qed.
Lemma tshift_size_PRec  :
  (forall (ps17 : PRec) (c14 : (Cutoff ty)) ,
    ((size_PRec (tshiftPRec c14 ps17)) =
    (size_PRec ps17))).
Proof.
  pose proof (tshift_size_Pat_PRec).
  destruct_conjs .
  easy .
Qed.
Lemma shift_size_Tm_Rec  :
  (forall (s24 : Tm) (c14 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c14 s24)) =
    (size_Tm s24))) /\
  (forall (ss : Rec) (c14 : (Cutoff tm)) ,
    ((size_Rec (shiftRec c14 ss)) =
    (size_Rec ss))).
Proof.
  apply_mutual_ind ind_Tm_Rec.
  - intros x55 c14.
  reflexivity.
  - intros T92 t152 IHt152.
  intros c15; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt152 (CS c15))).
  - intros t153 IHt153 t154 IHt154.
  intros c15; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt153 c15)).
  + exact ((IHt154 c15)).
  - intros T93 t155 IHt155.
  intros c15; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt155 c15)).
  - intros t156 IHt156 T94.
  intros c15; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt156 c15)).
  + reflexivity.
  - intros ts33 IHts33.
  intros c15; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHts33 c15)).
  - intros t157 IHt157 l47.
  intros c15; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt157 c15)).
  + reflexivity.
  - intros p27 t158 IHt158 t159 IHt159.
  intros c15; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt158 c15)).
  + exact ((IHt159 (weakenCutofftm c15 (bindPat p27)))).
  - intros c15; simpl; apply ((f_equal S)); reflexivity.
  - intros l48 t160 IHt160 ts34 IHts34.
  intros c15; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt160 c15)).
  + exact ((IHts34 c15)).
Qed.

Lemma shift_size_Tm  :
  (forall (s24 : Tm) (c15 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c15 s24)) =
    (size_Tm s24))).
Proof.
  pose proof (shift_size_Tm_Rec).
  destruct_conjs .
  easy .
Qed.
Lemma shift_size_Rec  :
  (forall (ss : Rec) (c15 : (Cutoff tm)) ,
    ((size_Rec (shiftRec c15 ss)) =
    (size_Rec ss))).
Proof.
  pose proof (shift_size_Tm_Rec).
  destruct_conjs .
  easy .
Qed.
Lemma tshift_size_Tm_Rec  :
  (forall (s24 : Tm) (c15 : (Cutoff ty)) ,
    ((size_Tm (tshiftTm c15 s24)) =
    (size_Tm s24))) /\
  (forall (ss : Rec) (c15 : (Cutoff ty)) ,
    ((size_Rec (tshiftRec c15 ss)) =
    (size_Rec ss))).
Proof.
  apply_mutual_ind ind_Tm_Rec.
  - intros X41 c15.
  reflexivity.
  - intros T95 t161 IHt161.
  pose proof ((tshift_size_Ty T95)) as IHT95.
  intros c16; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT95 c16)).
  + exact ((IHt161 c16)).
  - intros t162 IHt162 t163 IHt163.
  intros c16; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt162 c16)).
  + exact ((IHt163 c16)).
  - intros T96 t164 IHt164.
  pose proof ((tshift_size_Ty T96)) as IHT96.
  intros c16; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHT96 c16)).
  + exact ((IHt164 (CS c16))).
  - intros t165 IHt165 T97.
  pose proof ((tshift_size_Ty T97)) as IHT97.
  intros c16; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt165 c16)).
  + exact ((IHT97 c16)).
  - intros ts35 IHts35.
  intros c16; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHts35 c16)).
  - intros t166 IHt166 l49.
  intros c16; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt166 c16)).
  + reflexivity.
  - intros p28 t167 IHt167 t168 IHt168.
  pose proof ((tshift_size_Pat p28)) as IHp28.
  intros c16; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHp28 c16)).
  + exact ((IHt167 c16)).
  + exact ((IHt168 (weakenCutoffty c16 (bindPat p28)))).
  - intros c16; simpl; apply ((f_equal S)); reflexivity.
  - intros l50 t169 IHt169 ts36 IHts36.
  intros c16; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt169 c16)).
  + exact ((IHts36 c16)).
Qed.

Lemma tshift_size_Tm  :
  (forall (s24 : Tm) (c16 : (Cutoff ty)) ,
    ((size_Tm (tshiftTm c16 s24)) =
    (size_Tm s24))).
Proof.
  pose proof (tshift_size_Tm_Rec).
  destruct_conjs .
  easy .
Qed.
Lemma tshift_size_Rec  :
  (forall (ss : Rec) (c16 : (Cutoff ty)) ,
    ((size_Rec (tshiftRec c16 ss)) =
    (size_Rec ss))).
Proof.
  pose proof (tshift_size_Tm_Rec).
  destruct_conjs .
  easy .
Qed.
 Hint Rewrite tshift_size_PRec tshift_size_Pat shift_size_Rec tshift_size_Rec tshift_size_TRec shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite tshift_size_PRec tshift_size_Pat shift_size_Rec tshift_size_Rec tshift_size_TRec shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Lab  :
  (forall (k87 : Hvl) (l51 : Lab) ,
    ((size_Lab (weakenLab l51 k87)) =
    (size_Lab l51))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_PRec  :
  (forall (k87 : Hvl) (ps17 : PRec) ,
    ((size_PRec (weakenPRec ps17 k87)) =
    (size_PRec ps17))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Pat  :
  (forall (k87 : Hvl) (p29 : Pat) ,
    ((size_Pat (weakenPat p29 k87)) =
    (size_Pat p29))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Rec  :
  (forall (k87 : Hvl) (ss : Rec) ,
    ((size_Rec (weakenRec ss k87)) =
    (size_Rec ss))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_TRec  :
  (forall (k87 : Hvl) (SS : TRec) ,
    ((size_TRec (weakenTRec SS k87)) =
    (size_TRec SS))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k87 : Hvl) (s24 : Tm) ,
    ((size_Tm (weakenTm s24 k87)) =
    (size_Tm s24))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k87 : Hvl) (S65 : Ty) ,
    ((size_Ty (weakenTy S65 k87)) =
    (size_Ty S65))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Lab weaken_size_PRec weaken_size_Pat weaken_size_Rec weaken_size_TRec weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Lab weaken_size_PRec weaken_size_Pat weaken_size_Rec weaken_size_TRec weaken_size_Tm weaken_size_Ty : weaken_size.