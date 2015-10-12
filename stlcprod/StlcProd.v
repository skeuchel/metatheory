Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.
Require Export Coq.Unicode.Utf8.
Require Export Needle.
Section Namespace.
  Inductive Namespace : Type :=
    | tm .
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
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x k) k0) =
      (weakenIndextm x (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | tunit 
    | tarr (T1 : Ty) (T2 : Ty)
    | tprod (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Pat : Set :=
    | pvar (T : Ty)
    | pprod (p1 : Pat) (p2 : Pat).
  Scheme ind_Pat := Induction for Pat Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | tt 
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | prod (t1 : Tm) (t2 : Tm)
    | lett (p : Pat) (t1 : Tm)
        (t2 : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  Fixpoint bindPat (p : Pat) {struct p} : Hvl :=
    match p with
      | pvar T => (appendHvl (HS tm H0) H0)
      | pprod p1 p2 => (appendHvl (bindPat p1) (appendHvl (bindPat p2) H0))
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
      | H0 => c
      | HS a k => match a with
        | tm => (CS (weakenCutofftm c k))
      end
    end.
  
  Lemma weakenCutofftm_append  :
    (forall (c : (Cutoff tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutofftm (weakenCutofftm c k) k0) =
      (weakenCutofftm c (appendHvl k k0)))).
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
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} : Tm :=
    match s with
      | var x => (var (shiftIndex c x))
      | tt => (tt)
      | abs T t => (abs T (shiftTm (weakenCutofftm c (appendHvl (HS tm H0) H0)) t))
      | app t1 t2 => (app (shiftTm (weakenCutofftm c H0) t1) (shiftTm (weakenCutofftm c H0) t2))
      | prod t0 t3 => (prod (shiftTm (weakenCutofftm c H0) t0) (shiftTm (weakenCutofftm c H0) t3))
      | lett p t4 t5 => (lett p (shiftTm (weakenCutofftm c H0) t4) (shiftTm (weakenCutofftm c (appendHvl (bindPat p) H0)) t5))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} : Ty :=
    match k with
      | H0 => S0
      | HS tm k => (weakenTy S0 k)
    end.
  Fixpoint weakenPat (p : Pat) (k : Hvl) {struct k} : Pat :=
    match k with
      | H0 => p
      | HS tm k => (weakenPat p k)
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} : Tm :=
    match k with
      | H0 => s
      | HS tm k => (shiftTm C0 (weakenTm s k))
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
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} : Tm :=
    match s0 with
      | var x => (substIndex d s x)
      | tt => (tt)
      | abs T t => (abs T (substTm (XS tm d) s t))
      | app t1 t2 => (app (substTm d s t1) (substTm d s t2))
      | prod t0 t3 => (prod (substTm d s t0) (substTm d s t3))
      | lett p t4 t5 => (lett p (substTm d s t4) (substTm (weakenTrace d (bindPat p)) s t5))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append : interaction.
 Hint Rewrite weakenCutofftm_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : interaction.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_weaken_bindPat  :
  (forall (k : Hvl) (p : Pat) ,
    ((bindPat (weakenPat p k)) =
    (bindPat p))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bindPat : interaction.
 Hint Rewrite stability_weaken_bindPat : stability_weaken.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k0 : Hvl) (x2 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k0) s (shiftIndex (weakenCutofftm C0 k0) x2)) =
      (var x2))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Definition subst0_shift0_Tm_reflection_ind := (ind_Tm (fun (s0 : Tm) =>
    (forall (k1 : Hvl) (s1 : Tm) ,
      ((substTm (weakenTrace X0 k1) s1 (shiftTm (weakenCutofftm C0 k1) s0)) =
      s0))) (fun (x5 : (Index tm)) =>
    (fun (k1 : Hvl) (s0 : Tm) =>
      (substIndex0_shiftIndex0_reflection_ind s0 k1 x5))) (fun (k1 : Hvl) (s0 : Tm) =>
    eq_refl) (fun (T : Ty) (t : Tm) IHt13 (k1 : Hvl) (s0 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k1 (HS tm H0)) eq_refl eq_refl) (IHt13 (HS tm k1) s0)))) (fun (t1 : Tm) IHt13 (t2 : Tm) IHt14 (k1 : Hvl) (s0 : Tm) =>
    (f_equal2 app (IHt13 k1 s0) (IHt14 k1 s0))) (fun (t1 : Tm) IHt13 (t2 : Tm) IHt14 (k1 : Hvl) (s0 : Tm) =>
    (f_equal2 prod (IHt13 k1 s0) (IHt14 k1 s0))) (fun (p : Pat) (t1 : Tm) IHt13 (t2 : Tm) IHt14 (k1 : Hvl) (s0 : Tm) =>
    (f_equal3 lett eq_refl (IHt13 k1 s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k1 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k1 (bindPat p)) eq_refl)) (IHt14 (appendHvl k1 (bindPat p)) s0))))).
  Definition substTm0_shiftTm0_reflection (s1 : Tm) : (forall (s0 : Tm) ,
    ((substTm X0 s0 (shiftTm C0 s1)) =
    s1)) := (subst0_shift0_Tm_reflection_ind s1 H0).
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
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Definition shift_shift0_Tm_comm_ind := (ind_Tm (fun (s : Tm) =>
      (forall (k0 : Hvl) (c0 : (Cutoff tm)) ,
        ((shiftTm (weakenCutofftm (CS c0) k0) (shiftTm (weakenCutofftm C0 k0) s)) =
        (shiftTm (weakenCutofftm C0 k0) (shiftTm (weakenCutofftm c0 k0) s))))) (fun (x2 : (Index tm)) =>
      (fun (k0 : Hvl) (c0 : (Cutoff tm)) =>
        (f_equal var (shiftIndex_shiftIndex0_comm_ind k0 c0 x2)))) (fun (k0 : Hvl) (c0 : (Cutoff tm)) =>
      eq_refl) (fun (T : Ty) (t : Tm) IHt6 (k0 : Hvl) (c0 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt6 (HS tm k0) c0))) (fun (t1 : Tm) IHt6 (t2 : Tm) IHt7 (k0 : Hvl) (c0 : (Cutoff tm)) =>
      (f_equal2 app (IHt6 k0 c0) (IHt7 k0 c0))) (fun (t1 : Tm) IHt6 (t2 : Tm) IHt7 (k0 : Hvl) (c0 : (Cutoff tm)) =>
      (f_equal2 prod (IHt6 k0 c0) (IHt7 k0 c0))) (fun (p : Pat) (t1 : Tm) IHt6 (t2 : Tm) IHt7 (k0 : Hvl) (c0 : (Cutoff tm)) =>
      (f_equal3 lett eq_refl (IHt6 k0 c0) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append (CS c0) k0 (bindPat p)) (f_equal2 shiftTm (weakenCutofftm_append C0 k0 (bindPat p)) eq_refl)) (eq_trans (IHt7 (appendHvl k0 (bindPat p)) c0) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k0 (bindPat p))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k0 (bindPat p))) eq_refl))))))).
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff tm)) ,
      ((shiftTm (CS c0) (shiftTm C0 s)) =
      (shiftTm C0 (shiftTm c0 s)))) := (shift_shift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Tm_comm : interaction.
 Hint Rewrite shift_shift0_Tm_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTm_shiftTm  :
    (forall (k9 : Hvl) (c1 : (Cutoff tm)) (s9 : Tm) ,
      ((weakenTm (shiftTm c1 s9) k9) =
      (shiftTm (weakenCutofftm c1 k9) (weakenTm s9 k9)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c0 : (Cutoff tm)) (s0 : Tm) :
      (forall (k1 : Hvl) (x5 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c0 k1) (substIndex (weakenTrace X0 k1) s0 x5)) =
        (substIndex (weakenTrace X0 k1) (shiftTm c0 s0) (shiftIndex (weakenCutofftm (CS c0) k1) x5)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Definition shift_subst0_Tm_comm_ind := (ind_Tm (fun (s1 : Tm) =>
      (forall (k2 : Hvl) (c1 : (Cutoff tm)) (s2 : Tm) ,
        ((shiftTm (weakenCutofftm c1 k2) (substTm (weakenTrace X0 k2) s2 s1)) =
        (substTm (weakenTrace X0 k2) (shiftTm c1 s2) (shiftTm (weakenCutofftm (CS c1) k2) s1))))) (fun (x8 : (Index tm)) =>
      (fun (k2 : Hvl) (c1 : (Cutoff tm)) (s1 : Tm) =>
        (shiftTm_substIndex0_comm_ind c1 s1 k2 x8))) (fun (k2 : Hvl) (c1 : (Cutoff tm)) (s1 : Tm) =>
      eq_refl) (fun (T : Ty) (t : Tm) IHt20 (k2 : Hvl) (c1 : (Cutoff tm)) (s1 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k2 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt20 (HS tm k2) c1 s1) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k2 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt20 (t2 : Tm) IHt21 (k2 : Hvl) (c1 : (Cutoff tm)) (s1 : Tm) =>
      (f_equal2 app (IHt20 k2 c1 s1) (IHt21 k2 c1 s1))) (fun (t1 : Tm) IHt20 (t2 : Tm) IHt21 (k2 : Hvl) (c1 : (Cutoff tm)) (s1 : Tm) =>
      (f_equal2 prod (IHt20 k2 c1 s1) (IHt21 k2 c1 s1))) (fun (p : Pat) (t1 : Tm) IHt20 (t2 : Tm) IHt21 (k2 : Hvl) (c1 : (Cutoff tm)) (s1 : Tm) =>
      (f_equal3 lett eq_refl (IHt20 k2 c1 s1) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append c1 k2 (bindPat p)) (f_equal3 substTm (weakenTrace_append tm X0 k2 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt21 (appendHvl k2 (bindPat p)) c1 s1) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k2 (bindPat p))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c1) k2 (bindPat p))) eq_refl))))))).
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shiftTm_substTm0_comm (s2 : Tm) : (forall (c1 : (Cutoff tm)) (s1 : Tm) ,
      ((shiftTm c1 (substTm X0 s1 s2)) =
      (substTm X0 (shiftTm c1 s1) (shiftTm (CS c1) s2)))) := (shift_subst0_Tm_comm_ind s2 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace tm)) (s1 : Tm) :
      (forall (k2 : Hvl) (x8 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d) k2) s1 (shiftIndex (weakenCutofftm C0 k2) x8)) =
        (shiftTm (weakenCutofftm C0 k2) (substIndex (weakenTrace d k2) s1 x8)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Definition subst_shift0_Tm_comm_ind := (ind_Tm (fun (s7 : Tm) =>
      (forall (k8 : Hvl) (d5 : (Trace tm)) (s8 : Tm) ,
        ((substTm (weakenTrace (XS tm d5) k8) s8 (shiftTm (weakenCutofftm C0 k8) s7)) =
        (shiftTm (weakenCutofftm C0 k8) (substTm (weakenTrace d5 k8) s8 s7))))) (fun (x11 : (Index tm)) =>
      (fun (k8 : Hvl) (d5 : (Trace tm)) (s7 : Tm) =>
        (substIndex_shiftTm0_comm_ind d5 s7 k8 x11))) (fun (k8 : Hvl) (d5 : (Trace tm)) (s7 : Tm) =>
      eq_refl) (fun (T : Ty) (t : Tm) IHt27 (k8 : Hvl) (d5 : (Trace tm)) (s7 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d5) k8 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt27 (HS tm k8) d5 s7) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d5 k8 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt27 (t2 : Tm) IHt28 (k8 : Hvl) (d5 : (Trace tm)) (s7 : Tm) =>
      (f_equal2 app (IHt27 k8 d5 s7) (IHt28 k8 d5 s7))) (fun (t1 : Tm) IHt27 (t2 : Tm) IHt28 (k8 : Hvl) (d5 : (Trace tm)) (s7 : Tm) =>
      (f_equal2 prod (IHt27 k8 d5 s7) (IHt28 k8 d5 s7))) (fun (p : Pat) (t1 : Tm) IHt27 (t2 : Tm) IHt28 (k8 : Hvl) (d5 : (Trace tm)) (s7 : Tm) =>
      (f_equal3 lett eq_refl (IHt27 k8 d5 s7) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d5) k8 (bindPat p)) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k8 (bindPat p)) eq_refl)) (eq_trans (IHt28 (appendHvl k8 (bindPat p)) d5 s7) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k8 (bindPat p))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d5 k8 (bindPat p))) eq_refl eq_refl))))))).
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition substTm_shiftTm0_comm (s8 : Tm) : (forall (d5 : (Trace tm)) (s7 : Tm) ,
      ((substTm (XS tm d5) s7 (shiftTm C0 s8)) =
      (shiftTm C0 (substTm d5 s7 s8)))) := (subst_shift0_Tm_comm_ind s8 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substTm0_shiftTm0_reflection : interaction.
 Hint Rewrite substTm0_shiftTm0_reflection : reflection.
 Hint Rewrite substTm_shiftTm0_comm : interaction.
 Hint Rewrite substTm_shiftTm0_comm : subst_shift0.
 Hint Rewrite shiftTm_substTm0_comm : interaction.
 Hint Rewrite shiftTm_substTm0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d5 : (Trace tm)) (s7 : Tm) (s8 : Tm) :
      (forall (k8 : Hvl) (x11 : (Index tm)) ,
        ((substTm (weakenTrace d5 k8) s7 (substIndex (weakenTrace X0 k8) s8 x11)) =
        (substTm (weakenTrace X0 k8) (substTm d5 s7 s8) (substIndex (weakenTrace (XS tm d5) k8) s7 x11)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition subst_subst0_Tm_comm_ind := (ind_Tm (fun (s9 : Tm) =>
      (forall (k9 : Hvl) (d6 : (Trace tm)) (s10 : Tm) (s11 : Tm) ,
        ((substTm (weakenTrace d6 k9) s10 (substTm (weakenTrace X0 k9) s11 s9)) =
        (substTm (weakenTrace X0 k9) (substTm d6 s10 s11) (substTm (weakenTrace (XS tm d6) k9) s10 s9))))) (fun (x14 : (Index tm)) =>
      (fun (k9 : Hvl) (d6 : (Trace tm)) (s9 : Tm) (s10 : Tm) =>
        (substTm_substIndex0_commright_ind d6 s9 s10 k9 x14))) (fun (k9 : Hvl) (d6 : (Trace tm)) (s9 : Tm) (s10 : Tm) =>
      eq_refl) (fun (T : Ty) (t : Tm) IHt34 (k9 : Hvl) (d6 : (Trace tm)) (s9 : Tm) (s10 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d6 k9 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k9 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt34 (HS tm k9) d6 s9 s10) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k9 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d6) k9 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt34 (t2 : Tm) IHt35 (k9 : Hvl) (d6 : (Trace tm)) (s9 : Tm) (s10 : Tm) =>
      (f_equal2 app (IHt34 k9 d6 s9 s10) (IHt35 k9 d6 s9 s10))) (fun (t1 : Tm) IHt34 (t2 : Tm) IHt35 (k9 : Hvl) (d6 : (Trace tm)) (s9 : Tm) (s10 : Tm) =>
      (f_equal2 prod (IHt34 k9 d6 s9 s10) (IHt35 k9 d6 s9 s10))) (fun (p : Pat) (t1 : Tm) IHt34 (t2 : Tm) IHt35 (k9 : Hvl) (d6 : (Trace tm)) (s9 : Tm) (s10 : Tm) =>
      (f_equal3 lett eq_refl (IHt34 k9 d6 s9 s10) (eq_trans (f_equal3 substTm (weakenTrace_append tm d6 k9 (bindPat p)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k9 (bindPat p)) eq_refl eq_refl)) (eq_trans (IHt35 (appendHvl k9 (bindPat p)) d6 s9 s10) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k9 (bindPat p))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d6) k9 (bindPat p))) eq_refl eq_refl))))))).
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition substTm_substTm0_comm (s11 : Tm) : (forall (d6 : (Trace tm)) (s9 : Tm) (s10 : Tm) ,
      ((substTm d6 s9 (substTm X0 s10 s11)) =
      (substTm X0 (substTm d6 s9 s10) (substTm (XS tm d6) s9 s11)))) := (subst_subst0_Tm_comm_ind s11 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTm_substTm  :
      (forall (k9 : Hvl) (d6 : (Trace tm)) (s9 : Tm) (s10 : Tm) ,
        ((weakenTm (substTm d6 s9 s10) k9) =
        (substTm (weakenTrace d6 k9) s9 (weakenTm s10 k9)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenTy_append  :
      (forall (S0 : Ty) (k9 : Hvl) (k10 : Hvl) ,
        ((weakenTy (weakenTy S0 k9) k10) =
        (weakenTy S0 (appendHvl k9 k10)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenPat_append  :
      (forall (p4 : Pat) (k9 : Hvl) (k10 : Hvl) ,
        ((weakenPat (weakenPat p4 k9) k10) =
        (weakenPat p4 (appendHvl k9 k10)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s9 : Tm) (k9 : Hvl) (k10 : Hvl) ,
        ((weakenTm (weakenTm s9 k9) k10) =
        (weakenTm s9 (appendHvl k9 k10)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
  End WeakenAppend.
End SubstSubstInteraction.
 Hint Rewrite substTm_substTm0_comm : interaction.
 Hint Rewrite substTm_substTm0_comm : subst_subst0.
 Hint Rewrite weakenTm_shiftTm : weaken_shift.
 Hint Rewrite weakenTm_substTm : weaken_subst.
Section WellFormed.
  Fixpoint wfindex {a : Namespace} (k9 : Hvl) (i : (Index a)) {struct k9} : Prop :=
    match k9 with
      | H0 => False
      | HS b k9 => match (eq_namespace_dec a b) with
        | left e => match i with
          | I0 => True
          | IS i => (wfindex k9 i)
        end
        | right n => (wfindex k9 i)
      end
    end.
  Inductive wfTy (k9 : Hvl) : Ty -> Prop :=
    | wfTy_tunit :
        (wfTy k9 (tunit))
    | wfTy_tarr {T5 : Ty}
        (wf : (wfTy k9 T5)) {T6 : Ty}
        (wf0 : (wfTy k9 T6)) :
        (wfTy k9 (tarr T5 T6))
    | wfTy_tprod {T7 : Ty}
        (wf : (wfTy k9 T7)) {T8 : Ty}
        (wf0 : (wfTy k9 T8)) :
        (wfTy k9 (tprod T7 T8)).
  Inductive wfPat (k9 : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T5 : Ty}
        (wf : (wfTy k9 T5)) :
        (wfPat k9 (pvar T5))
    | wfPat_pprod {p5 : Pat}
        (wf : (wfPat k9 p5)) {p6 : Pat}
        (wf0 : (wfPat k9 p6)) :
        (wfPat k9 (pprod p5 p6)).
  Inductive wfTm (k9 : Hvl) : Tm -> Prop :=
    | wfTm_var {x17 : (Index tm)}
        (wfi : (wfindex k9 x17)) :
        (wfTm k9 (var x17))
    | wfTm_tt : (wfTm k9 (tt))
    | wfTm_abs {T5 : Ty}
        (wf : (wfTy k9 T5)) {t41 : Tm}
        (wf0 : (wfTm (HS tm k9) t41)) :
        (wfTm k9 (abs T5 t41))
    | wfTm_app {t42 : Tm}
        (wf : (wfTm k9 t42)) {t43 : Tm}
        (wf0 : (wfTm k9 t43)) :
        (wfTm k9 (app t42 t43))
    | wfTm_prod {t44 : Tm}
        (wf : (wfTm k9 t44)) {t45 : Tm}
        (wf0 : (wfTm k9 t45)) :
        (wfTm k9 (prod t44 t45))
    | wfTm_lett {p5 : Pat}
        (wf : (wfPat k9 p5)) {t46 : Tm}
        (wf0 : (wfTm k9 t46)) {t47 : Tm}
        (wf1 : (wfTm (appendHvl k9 (bindPat p5)) t47))
        : (wfTm k9 (lett p5 t46 t47)).
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c2 : (Cutoff tm)) (k9 : Hvl) (k10 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k9 : Hvl)
        : (shifthvl_tm C0 k9 (HS tm k9))
    | shifthvl_tm_there_tm
        (c2 : (Cutoff tm)) (k9 : Hvl)
        (k10 : Hvl) :
        (shifthvl_tm c2 k9 k10) -> (shifthvl_tm (CS c2) (HS tm k9) (HS tm k10)).
  Lemma weaken_shifthvl_tm  :
    (forall (k9 : Hvl) {c2 : (Cutoff tm)} {k10 : Hvl} {k11 : Hvl} ,
      (shifthvl_tm c2 k10 k11) -> (shifthvl_tm (weakenCutofftm c2 k9) (appendHvl k10 k9) (appendHvl k11 k9))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c2 : (Cutoff tm)) (k9 : Hvl) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) (x17 : (Index tm)) ,
      (wfindex k9 x17) -> (wfindex k10 (shiftIndex c2 x17))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k9 : Hvl) ,
    (forall (S0 : Ty) (wf : (wfTy k9 S0)) ,
      (forall (c2 : (Cutoff tm)) (k10 : Hvl) ,
        (shifthvl_tm c2 k9 k10) -> (wfTy k10 S0)))) := (fun (k9 : Hvl) =>
    (ind_wfTy k9 (fun (S0 : Ty) (wf : (wfTy k9 S0)) =>
      (forall (c2 : (Cutoff tm)) (k10 : Hvl) ,
        (shifthvl_tm c2 k9 k10) -> (wfTy k10 S0))) (fun (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
      (wfTy_tunit k10)) (fun (T1 : Ty) (wf : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k9 T2)) IHT2 (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
      (wfTy_tarr k10 (IHT1 c2 k10 (weaken_shifthvl_tm H0 ins)) (IHT2 c2 k10 (weaken_shifthvl_tm H0 ins)))) (fun (T1 : Ty) (wf : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k9 T2)) IHT2 (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
      (wfTy_tprod k10 (IHT1 c2 k10 (weaken_shifthvl_tm H0 ins)) (IHT2 c2 k10 (weaken_shifthvl_tm H0 ins)))))).
  Definition shift_wfPat : (forall (k9 : Hvl) ,
    (forall (p5 : Pat) (wf : (wfPat k9 p5)) ,
      (forall (c2 : (Cutoff tm)) (k10 : Hvl) ,
        (shifthvl_tm c2 k9 k10) -> (wfPat k10 p5)))) := (fun (k9 : Hvl) =>
    (ind_wfPat k9 (fun (p5 : Pat) (wf : (wfPat k9 p5)) =>
      (forall (c2 : (Cutoff tm)) (k10 : Hvl) ,
        (shifthvl_tm c2 k9 k10) -> (wfPat k10 p5))) (fun (T : Ty) (wf : (wfTy k9 T)) (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
      (wfPat_pvar k10 (shift_wfTy k9 T wf c2 k10 (weaken_shifthvl_tm H0 ins)))) (fun (p1 : Pat) (wf : (wfPat k9 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat k9 p2)) IHp2 (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
      (wfPat_pprod k10 (IHp1 c2 k10 (weaken_shifthvl_tm H0 ins)) (IHp2 c2 k10 (weaken_shifthvl_tm H0 ins)))))).
  Definition shift_wfTm : (forall (k9 : Hvl) ,
    (forall (s9 : Tm) (wf : (wfTm k9 s9)) ,
      (forall (c2 : (Cutoff tm)) (k10 : Hvl) ,
        (shifthvl_tm c2 k9 k10) -> (wfTm k10 (shiftTm c2 s9))))) := (ind_wfTm (fun (k9 : Hvl) (s9 : Tm) (wf : (wfTm k9 s9)) =>
    (forall (c2 : (Cutoff tm)) (k10 : Hvl) ,
      (shifthvl_tm c2 k9 k10) -> (wfTm k10 (shiftTm c2 s9)))) (fun (k9 : Hvl) (x17 : (Index tm)) (wfi : (wfindex k9 x17)) (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
    (wfTm_var k10 (shift_wfindex_tm c2 k9 k10 ins x17 wfi))) (fun (k9 : Hvl) (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
    (wfTm_tt k10)) (fun (k9 : Hvl) (T : Ty) (wf : (wfTy k9 T)) (t : Tm) (wf0 : (wfTm (HS tm k9) t)) IHt41 (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
    (wfTm_abs k10 (shift_wfTy k9 T wf c2 k10 (weaken_shifthvl_tm H0 ins)) (IHt41 (CS c2) (HS tm k10) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k9 : Hvl) (t1 : Tm) (wf : (wfTm k9 t1)) IHt41 (t2 : Tm) (wf0 : (wfTm k9 t2)) IHt42 (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
    (wfTm_app k10 (IHt41 c2 k10 (weaken_shifthvl_tm H0 ins)) (IHt42 c2 k10 (weaken_shifthvl_tm H0 ins)))) (fun (k9 : Hvl) (t1 : Tm) (wf : (wfTm k9 t1)) IHt41 (t2 : Tm) (wf0 : (wfTm k9 t2)) IHt42 (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
    (wfTm_prod k10 (IHt41 c2 k10 (weaken_shifthvl_tm H0 ins)) (IHt42 c2 k10 (weaken_shifthvl_tm H0 ins)))) (fun (k9 : Hvl) (p : Pat) (wf : (wfPat k9 p)) (t1 : Tm) (wf0 : (wfTm k9 t1)) IHt41 (t2 : Tm) (wf1 : (wfTm (appendHvl k9 (bindPat p)) t2)) IHt42 (c2 : (Cutoff tm)) (k10 : Hvl) (ins : (shifthvl_tm c2 k9 k10)) =>
    (wfTm_lett k10 (shift_wfPat k9 p wf c2 k10 (weaken_shifthvl_tm H0 ins)) (IHt41 c2 k10 (weaken_shifthvl_tm H0 ins)) (IHt42 (weakenCutofftm c2 (bindPat p)) (appendHvl k10 (bindPat p)) (weaken_shifthvl_tm (bindPat p) ins))))).
End ShiftWellFormed.
 Hint Resolve shift_wfindex_tm : infra.
 Hint Resolve shift_wfindex_tm : shift.
 Hint Resolve shift_wfindex_tm : shift_wf.
 Hint Resolve shift_wfindex_tm : wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy : infra.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy : shift.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy : shift_wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy : wf.
 Hint Constructors shifthvl_tm : infra.
 Hint Constructors shifthvl_tm : shift.
 Hint Constructors shifthvl_tm : shift_wf.
 Hint Constructors shifthvl_tm : wf.
 Hint Resolve weaken_shifthvl_tm : infra.
 Hint Resolve weaken_shifthvl_tm : shift.
 Hint Resolve weaken_shifthvl_tm : shift_wf.
 Hint Resolve weaken_shifthvl_tm : weaken.
 Hint Resolve weaken_shifthvl_tm : wf.
Section SubstWellFormed.
  Inductive substhvl_tm (k9 : Hvl) : (forall (d6 : (Trace tm)) (k10 : Hvl) (k11 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k9 X0 (HS tm k9) k9)
    | substhvl_tm_there_tm
        {d6 : (Trace tm)} {k10 : Hvl}
        {k11 : Hvl} :
        (substhvl_tm k9 d6 k10 k11) -> (substhvl_tm k9 (XS tm d6) (HS tm k10) (HS tm k11)).
  Lemma weaken_substhvl_tm  :
    (forall {k10 : Hvl} (k9 : Hvl) {d6 : (Trace tm)} {k11 : Hvl} {k12 : Hvl} ,
      (substhvl_tm k10 d6 k11 k12) -> (substhvl_tm k10 (weakenTrace d6 k9) (appendHvl k11 k9) (appendHvl k12 k9))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k9 : Hvl} {s9 : Tm} (wft : (wfTm k9 s9)) :
    (forall {d6 : (Trace tm)} {k10 : Hvl} {k11 : Hvl} ,
      (substhvl_tm k9 d6 k10 k11) -> (forall {x17 : (Index tm)} ,
        (wfindex k10 x17) -> (wfTm k11 (substIndex d6 s9 x17)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Definition substhvl_tm_wfTy {k9 : Hvl} : (forall (k10 : Hvl) ,
    (forall (S0 : Ty) (wf0 : (wfTy k10 S0)) ,
      (forall {d6 : (Trace tm)} {k11 : Hvl} ,
        (substhvl_tm k9 d6 k10 k11) -> (wfTy k11 S0)))) := (fun (k10 : Hvl) =>
    (ind_wfTy k10 (fun (S0 : Ty) (wf0 : (wfTy k10 S0)) =>
      (forall {d6 : (Trace tm)} {k11 : Hvl} ,
        (substhvl_tm k9 d6 k10 k11) -> (wfTy k11 S0))) (fun {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
      (wfTy_tunit k11)) (fun (T1 : Ty) (wf0 : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k10 T2)) IHT2 {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
      (wfTy_tarr k11 (IHT1 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)))) (fun (T1 : Ty) (wf0 : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k10 T2)) IHT2 {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
      (wfTy_tprod k11 (IHT1 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_tm_wfPat {k9 : Hvl} : (forall (k10 : Hvl) ,
    (forall (p5 : Pat) (wf0 : (wfPat k10 p5)) ,
      (forall {d6 : (Trace tm)} {k11 : Hvl} ,
        (substhvl_tm k9 d6 k10 k11) -> (wfPat k11 p5)))) := (fun (k10 : Hvl) =>
    (ind_wfPat k10 (fun (p5 : Pat) (wf0 : (wfPat k10 p5)) =>
      (forall {d6 : (Trace tm)} {k11 : Hvl} ,
        (substhvl_tm k9 d6 k10 k11) -> (wfPat k11 p5))) (fun (T : Ty) (wf0 : (wfTy k10 T)) {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
      (wfPat_pvar k11 (substhvl_tm_wfTy k10 T wf0 (weaken_substhvl_tm H0 del)))) (fun (p1 : Pat) (wf0 : (wfPat k10 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat k10 p2)) IHp2 {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
      (wfPat_pprod k11 (IHp1 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)) (IHp2 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_tm_wfTm {k9 : Hvl} {s9 : Tm} (wf : (wfTm k9 s9)) : (forall (k10 : Hvl) ,
    (forall (s10 : Tm) (wf0 : (wfTm k10 s10)) ,
      (forall {d6 : (Trace tm)} {k11 : Hvl} ,
        (substhvl_tm k9 d6 k10 k11) -> (wfTm k11 (substTm d6 s9 s10))))) := (ind_wfTm (fun (k10 : Hvl) (s10 : Tm) (wf0 : (wfTm k10 s10)) =>
    (forall {d6 : (Trace tm)} {k11 : Hvl} ,
      (substhvl_tm k9 d6 k10 k11) -> (wfTm k11 (substTm d6 s9 s10)))) (fun (k10 : Hvl) {x17 : (Index tm)} (wfi : (wfindex k10 x17)) {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k10 : Hvl) {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
    (wfTm_tt k11)) (fun (k10 : Hvl) (T : Ty) (wf0 : (wfTy k10 T)) (t : Tm) (wf1 : (wfTm (HS tm k10) t)) IHt41 {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
    (wfTm_abs k11 (substhvl_tm_wfTy k10 T wf0 (weaken_substhvl_tm H0 del)) (IHt41 (weakenTrace d6 (HS tm H0)) (HS tm k11) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k10 : Hvl) (t1 : Tm) (wf0 : (wfTm k10 t1)) IHt41 (t2 : Tm) (wf1 : (wfTm k10 t2)) IHt42 {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
    (wfTm_app k11 (IHt41 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)) (IHt42 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)))) (fun (k10 : Hvl) (t1 : Tm) (wf0 : (wfTm k10 t1)) IHt41 (t2 : Tm) (wf1 : (wfTm k10 t2)) IHt42 {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
    (wfTm_prod k11 (IHt41 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)) (IHt42 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)))) (fun (k10 : Hvl) (p : Pat) (wf0 : (wfPat k10 p)) (t1 : Tm) (wf1 : (wfTm k10 t1)) IHt41 (t2 : Tm) (wf2 : (wfTm (appendHvl k10 (bindPat p)) t2)) IHt42 {d6 : (Trace tm)} {k11 : Hvl} (del : (substhvl_tm k9 d6 k10 k11)) =>
    (wfTm_lett k11 (substhvl_tm_wfPat k10 p wf0 (weaken_substhvl_tm H0 del)) (IHt41 (weakenTrace d6 H0) k11 (weaken_substhvl_tm H0 del)) (IHt42 (weakenTrace d6 (bindPat p)) (appendHvl k11 (bindPat p)) (weaken_substhvl_tm (bindPat p) del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm : infra.
 Hint Resolve substhvl_tm_wfindex_tm : subst.
 Hint Resolve substhvl_tm_wfindex_tm : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm : wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy : infra.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy : subst.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy : wf.
 Hint Constructors substhvl_tm : infra.
 Hint Constructors substhvl_tm : subst.
 Hint Constructors substhvl_tm : subst_wf.
 Hint Constructors substhvl_tm : wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G : Env) (T : Ty).
  Fixpoint appendEnv (G : Env) (G0 : Env) : Env :=
    match G0 with
      | empty => G
      | evar G1 T => (evar (appendEnv G G1) T)
    end.
  Fixpoint domainEnv (G : Env) : Hvl :=
    match G with
      | empty => H0
      | evar G0 T => (HS tm (domainEnv G0))
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
  Fixpoint shiftEnv (c2 : (Cutoff tm)) (G : Env) : Env :=
    match G with
      | empty => empty
      | evar G0 T => (evar (shiftEnv c2 G0) T)
    end.
  Fixpoint substEnv (d6 : (Trace tm)) (s9 : Tm) (G : Env) : Env :=
    match G with
      | empty => empty
      | evar G0 T => (evar (substEnv d6 s9 G0) T)
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c2 : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c2 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d6 : (Trace tm)) (s9 : Tm) (G : Env) ,
      ((domainEnv (substEnv d6 s9 G)) =
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
      (forall (c2 : (Cutoff tm)) (G : Env) (G0 : Env) ,
        ((shiftEnv c2 (appendEnv G G0)) =
        (appendEnv (shiftEnv c2 G) (shiftEnv (weakenCutofftm c2 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d6 : (Trace tm)) (s9 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d6 s9 (appendEnv G G0)) =
        (appendEnv (substEnv d6 s9 G) (substEnv (weakenTrace d6 (domainEnv G)) s9 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          {T5 : Ty} :
          (wfTy (domainEnv G) T5) -> (lookup_evar (evar G T5) I0 T5)
      | lookup_evar_there_evar
          {G : Env} {x17 : (Index tm)}
          {T5 : Ty} {T6 : Ty} :
          (lookup_evar G x17 T5) -> (lookup_evar (evar G T6) (IS x17) T5).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (S0 : Ty) (S1 : Ty) ,
        (lookup_evar (evar G S0) I0 S1) -> (S0 =
        S1)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x17 : (Index tm)} ,
        (forall {S0 : Ty} ,
          (lookup_evar G x17 S0) -> (forall {S1 : Ty} ,
            (lookup_evar G x17 S1) -> (S0 =
            S1)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x17 : (Index tm)} {S0 : Ty} ,
        (lookup_evar G x17 S0) -> (wfTy (domainEnv G) S0)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x17 : (Index tm)} {T5 : Ty} ,
        (lookup_evar G x17 T5) -> (lookup_evar (appendEnv G G0) (weakenIndextm x17 (domainEnv G0)) (weakenTy T5 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x17 : (Index tm)} {S0 : Ty} ,
        (lookup_evar G x17 S0) -> (wfindex (domainEnv G) x17)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T5 : Ty} :
        (shift_evar C0 G (evar G T5))
    | shiftevar_there_evar
        {c2 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c2 G G0) -> (shift_evar (CS c2) (evar G T) (evar G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c2 : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c2 G0 G1) -> (shift_evar (weakenCutofftm c2 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c2 : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c2 G G0) -> (shifthvl_tm c2 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T5 : Ty) (s9 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T5 s9 X0 (evar G T5) G)
    | subst_evar_there_evar
        {d6 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T5 s9 d6 G0 G1) -> (subst_evar G T5 s9 (XS tm d6) (evar G0 T) (evar G1 T)).
  Lemma weaken_subst_evar {G : Env} {T5 : Ty} {s9 : Tm} :
    (forall (G0 : Env) {d6 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T5 s9 d6 G1 G2) -> (subst_evar G T5 s9 (weakenTrace d6 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s9 : Tm} {T5 : Ty} :
    (forall {d6 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T5 s9 d6 G0 G1) -> (substhvl_tm (domainEnv G) d6 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Constructors lookup_evar : infra.
 Hint Constructors lookup_evar : lookup.
 Hint Constructors lookup_evar : shift.
 Hint Constructors lookup_evar : subst.
 Hint Resolve weaken_lookup_evar : infra.
 Hint Resolve weaken_lookup_evar : lookup.
 Hint Resolve weaken_lookup_evar : shift.
 Hint Resolve weaken_lookup_evar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Env} (G0 : Env) {T5 : Ty} (wf : (wfTy (domainEnv G) T5)) ,
    (lookup_evar (appendEnv (evar G T5) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T5 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfPat wfTm wfTy : infra.
 Hint Constructors wfPat wfTm wfTy : wf.
 Hint Resolve lookup_evar_wf : infra.
 Hint Resolve lookup_evar_wf : wf.
 Hint Resolve lookup_evar_wfindex : infra.
 Hint Resolve lookup_evar_wfindex : lookup.
 Hint Resolve lookup_evar_wfindex : wf.
 Hint Constructors shift_evar : infra.
 Hint Constructors shift_evar : shift.
 Hint Constructors shift_evar : subst.
 Hint Resolve weaken_shift_evar : infra.
 Hint Resolve weaken_shift_evar : shift.
 Hint Resolve shift_evar_shifthvl_tm : infra.
 Hint Resolve shift_evar_shifthvl_tm : shift.
 Hint Resolve shift_evar_shifthvl_tm : shift_wf.
 Hint Resolve shift_evar_shifthvl_tm : wf.
 Hint Constructors subst_evar : infra.
 Hint Constructors subst_evar : subst.
 Hint Resolve weaken_subst_evar : infra.
 Hint Resolve weaken_subst_evar : subst.
 Hint Resolve subst_evar_substhvl_tm : infra.
 Hint Resolve subst_evar_substhvl_tm : subst.
 Hint Resolve subst_evar_substhvl_tm : subst_wf.
 Hint Resolve subst_evar_substhvl_tm : wf.
 Hint Resolve subst_evar_substhvl_tm : substenv_substhvl.
Lemma shift_evar_lookup_evar  :
  (forall {c2 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c2 G G0)) {x17 : (Index tm)} {T5 : Ty} ,
    (lookup_evar G x17 T5) -> (lookup_evar G0 (shiftIndex c2 x17) T5)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar : infra.
 Hint Resolve shift_evar_lookup_evar : lookup.
 Hint Resolve shift_evar_lookup_evar : shift.
Fixpoint size_Ty (S0 : Ty) {struct S0} : nat :=
  match S0 with
    | tunit => 1
    | tarr T1 T2 => (plus 1 (plus (size_Ty T1) (size_Ty T2)))
    | tprod T0 T3 => (plus 1 (plus (size_Ty T0) (size_Ty T3)))
  end.
Fixpoint size_Pat (p : Pat) {struct p} : nat :=
  match p with
    | pvar T => (plus 1 (size_Ty T))
    | pprod p1 p2 => (plus 1 (plus (size_Pat p1) (size_Pat p2)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} : nat :=
  match s with
    | var x => 1
    | tt => 1
    | abs T t => (plus 1 (plus (size_Ty T) (size_Tm t)))
    | app t1 t2 => (plus 1 (plus (size_Tm t1) (size_Tm t2)))
    | prod t0 t3 => (plus 1 (plus (size_Tm t0) (size_Tm t3)))
    | lett p t4 t5 => (plus 1 (plus (size_Pat p) (plus (size_Tm t4) (size_Tm t5))))
  end.
Lemma shift_size_Tm  :
  (forall (s9 : Tm) (c1 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c1 s9)) =
    (size_Tm s9))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros x15 c1.
  reflexivity.
  - intros c2; simpl; apply ((f_equal S)); reflexivity.
  - intros T4 t34 IHt34.
  intros c2; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt34 (CS c2))).
  - intros t35 IHt35 t36 IHt36.
  intros c2; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt35 c2)).
  + exact ((IHt36 c2)).
  - intros t37 IHt37 t38 IHt38.
  intros c2; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt37 c2)).
  + exact ((IHt38 c2)).
  - intros p4 t39 IHt39 t40 IHt40.
  intros c2; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt39 c2)).
  + exact ((IHt40 (weakenCutofftm c2 (bindPat p4)))).
Qed.

 Hint Rewrite shift_size_Tm : interaction.
 Hint Rewrite shift_size_Tm : shift_size.
Lemma weaken_size_Pat  :
  (forall (k9 : Hvl) (p5 : Pat) ,
    ((size_Pat (weakenPat p5 k9)) =
    (size_Pat p5))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k9 : Hvl) (s9 : Tm) ,
    ((size_Tm (weakenTm s9 k9)) =
    (size_Tm s9))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k9 : Hvl) (S0 : Ty) ,
    ((size_Ty (weakenTy S0 k9)) =
    (size_Ty S0))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : weaken_size.