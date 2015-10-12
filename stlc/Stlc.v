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
    | tarr (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | tt 
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
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} : Ty :=
    match k with
      | H0 => S0
      | HS tm k => (weakenTy S0 k)
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
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append : interaction.
 Hint Rewrite weakenCutofftm_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : interaction.
 Hint Rewrite weakenTrace_append : weakentrace_append.
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
    eq_refl) (fun (T : Ty) (t : Tm) IHt5 (k1 : Hvl) (s0 : Tm) =>
    (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k1 (HS tm H0)) eq_refl eq_refl) (IHt5 (HS tm k1) s0)))) (fun (t1 : Tm) IHt5 (t2 : Tm) IHt6 (k1 : Hvl) (s0 : Tm) =>
    (f_equal2 app (IHt5 k1 s0) (IHt6 k1 s0)))).
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
      eq_refl) (fun (T : Ty) (t : Tm) IHt0 (k0 : Hvl) (c0 : (Cutoff tm)) =>
      (f_equal2 abs eq_refl (IHt0 (HS tm k0) c0))) (fun (t1 : Tm) IHt0 (t2 : Tm) IHt3 (k0 : Hvl) (c0 : (Cutoff tm)) =>
      (f_equal2 app (IHt0 k0 c0) (IHt3 k0 c0)))).
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
    (forall (k7 : Hvl) (c1 : (Cutoff tm)) (s7 : Tm) ,
      ((weakenTm (shiftTm c1 s7) k7) =
      (shiftTm (weakenCutofftm c1 k7) (weakenTm s7 k7)))).
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
      eq_refl) (fun (T : Ty) (t : Tm) IHt8 (k2 : Hvl) (c1 : (Cutoff tm)) (s1 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k2 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt8 (HS tm k2) c1 s1) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k2 (HS tm H0))) eq_refl eq_refl))))) (fun (t1 : Tm) IHt8 (t2 : Tm) IHt9 (k2 : Hvl) (c1 : (Cutoff tm)) (s1 : Tm) =>
      (f_equal2 app (IHt8 k2 c1 s1) (IHt9 k2 c1 s1)))).
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
    Definition subst_shift0_Tm_comm_ind := (ind_Tm (fun (s5 : Tm) =>
      (forall (k6 : Hvl) (d3 : (Trace tm)) (s6 : Tm) ,
        ((substTm (weakenTrace (XS tm d3) k6) s6 (shiftTm (weakenCutofftm C0 k6) s5)) =
        (shiftTm (weakenCutofftm C0 k6) (substTm (weakenTrace d3 k6) s6 s5))))) (fun (x11 : (Index tm)) =>
      (fun (k6 : Hvl) (d3 : (Trace tm)) (s5 : Tm) =>
        (substIndex_shiftTm0_comm_ind d3 s5 k6 x11))) (fun (k6 : Hvl) (d3 : (Trace tm)) (s5 : Tm) =>
      eq_refl) (fun (T : Ty) (t : Tm) IHt11 (k6 : Hvl) (d3 : (Trace tm)) (s5 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d3) k6 (HS tm H0)) eq_refl eq_refl) (eq_trans (IHt11 (HS tm k6) d3 s5) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d3 k6 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt11 (t2 : Tm) IHt12 (k6 : Hvl) (d3 : (Trace tm)) (s5 : Tm) =>
      (f_equal2 app (IHt11 k6 d3 s5) (IHt12 k6 d3 s5)))).
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition substTm_shiftTm0_comm (s6 : Tm) : (forall (d3 : (Trace tm)) (s5 : Tm) ,
      ((substTm (XS tm d3) s5 (shiftTm C0 s6)) =
      (shiftTm C0 (substTm d3 s5 s6)))) := (subst_shift0_Tm_comm_ind s6 H0).
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
    Lemma substTm_substIndex0_commright_ind (d3 : (Trace tm)) (s5 : Tm) (s6 : Tm) :
      (forall (k6 : Hvl) (x11 : (Index tm)) ,
        ((substTm (weakenTrace d3 k6) s5 (substIndex (weakenTrace X0 k6) s6 x11)) =
        (substTm (weakenTrace X0 k6) (substTm d3 s5 s6) (substIndex (weakenTrace (XS tm d3) k6) s5 x11)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Definition subst_subst0_Tm_comm_ind := (ind_Tm (fun (s7 : Tm) =>
      (forall (k7 : Hvl) (d4 : (Trace tm)) (s8 : Tm) (s9 : Tm) ,
        ((substTm (weakenTrace d4 k7) s8 (substTm (weakenTrace X0 k7) s9 s7)) =
        (substTm (weakenTrace X0 k7) (substTm d4 s8 s9) (substTm (weakenTrace (XS tm d4) k7) s8 s7))))) (fun (x14 : (Index tm)) =>
      (fun (k7 : Hvl) (d4 : (Trace tm)) (s7 : Tm) (s8 : Tm) =>
        (substTm_substIndex0_commright_ind d4 s7 s8 k7 x14))) (fun (k7 : Hvl) (d4 : (Trace tm)) (s7 : Tm) (s8 : Tm) =>
      eq_refl) (fun (T : Ty) (t : Tm) IHt14 (k7 : Hvl) (d4 : (Trace tm)) (s7 : Tm) (s8 : Tm) =>
      (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d4 k7 (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k7 (HS tm H0)) eq_refl eq_refl)) (eq_trans (IHt14 (HS tm k7) d4 s7 s8) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k7 (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d4) k7 (HS tm H0))) eq_refl eq_refl)))))) (fun (t1 : Tm) IHt14 (t2 : Tm) IHt15 (k7 : Hvl) (d4 : (Trace tm)) (s7 : Tm) (s8 : Tm) =>
      (f_equal2 app (IHt14 k7 d4 s7 s8) (IHt15 k7 d4 s7 s8)))).
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition substTm_substTm0_comm (s9 : Tm) : (forall (d4 : (Trace tm)) (s7 : Tm) (s8 : Tm) ,
      ((substTm d4 s7 (substTm X0 s8 s9)) =
      (substTm X0 (substTm d4 s7 s8) (substTm (XS tm d4) s7 s9)))) := (subst_subst0_Tm_comm_ind s9 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTm_substTm  :
      (forall (k7 : Hvl) (d4 : (Trace tm)) (s7 : Tm) (s8 : Tm) ,
        ((weakenTm (substTm d4 s7 s8) k7) =
        (substTm (weakenTrace d4 k7) s7 (weakenTm s8 k7)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
  Section WeakenAppend.
    Lemma weakenTy_append  :
      (forall (S0 : Ty) (k7 : Hvl) (k8 : Hvl) ,
        ((weakenTy (weakenTy S0 k7) k8) =
        (weakenTy S0 (appendHvl k7 k8)))).
    Proof.
      needleGenericWeakenAppend .
    Qed.
    Lemma weakenTm_append  :
      (forall (s7 : Tm) (k7 : Hvl) (k8 : Hvl) ,
        ((weakenTm (weakenTm s7 k7) k8) =
        (weakenTm s7 (appendHvl k7 k8)))).
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
  Fixpoint wfindex {a : Namespace} (k7 : Hvl) (i : (Index a)) {struct k7} : Prop :=
    match k7 with
      | H0 => False
      | HS b k7 => match (eq_namespace_dec a b) with
        | left e => match i with
          | I0 => True
          | IS i => (wfindex k7 i)
        end
        | right n => (wfindex k7 i)
      end
    end.
  Inductive wfTy (k7 : Hvl) : Ty -> Prop :=
    | wfTy_tunit :
        (wfTy k7 (tunit))
    | wfTy_tarr {T5 : Ty}
        (wf : (wfTy k7 T5)) {T6 : Ty}
        (wf0 : (wfTy k7 T6)) :
        (wfTy k7 (tarr T5 T6)).
  Inductive wfTm (k7 : Hvl) : Tm -> Prop :=
    | wfTm_var {x17 : (Index tm)}
        (wfi : (wfindex k7 x17)) :
        (wfTm k7 (var x17))
    | wfTm_tt : (wfTm k7 (tt))
    | wfTm_abs {T5 : Ty}
        (wf : (wfTy k7 T5)) {t17 : Tm}
        (wf0 : (wfTm (HS tm k7) t17)) :
        (wfTm k7 (abs T5 t17))
    | wfTm_app {t18 : Tm}
        (wf : (wfTm k7 t18)) {t19 : Tm}
        (wf0 : (wfTm k7 t19)) :
        (wfTm k7 (app t18 t19)).
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c2 : (Cutoff tm)) (k7 : Hvl) (k8 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k7 : Hvl)
        : (shifthvl_tm C0 k7 (HS tm k7))
    | shifthvl_tm_there_tm
        (c2 : (Cutoff tm)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_tm c2 k7 k8) -> (shifthvl_tm (CS c2) (HS tm k7) (HS tm k8)).
  Lemma weaken_shifthvl_tm  :
    (forall (k7 : Hvl) {c2 : (Cutoff tm)} {k8 : Hvl} {k9 : Hvl} ,
      (shifthvl_tm c2 k8 k9) -> (shifthvl_tm (weakenCutofftm c2 k7) (appendHvl k8 k7) (appendHvl k9 k7))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c2 : (Cutoff tm)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_tm c2 k7 k8)) (x17 : (Index tm)) ,
      (wfindex k7 x17) -> (wfindex k8 (shiftIndex c2 x17))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k7 : Hvl) ,
    (forall (S0 : Ty) (wf : (wfTy k7 S0)) ,
      (forall (c2 : (Cutoff tm)) (k8 : Hvl) ,
        (shifthvl_tm c2 k7 k8) -> (wfTy k8 S0)))) := (fun (k7 : Hvl) =>
    (ind_wfTy k7 (fun (S0 : Ty) (wf : (wfTy k7 S0)) =>
      (forall (c2 : (Cutoff tm)) (k8 : Hvl) ,
        (shifthvl_tm c2 k7 k8) -> (wfTy k8 S0))) (fun (c2 : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c2 k7 k8)) =>
      (wfTy_tunit k8)) (fun (T1 : Ty) (wf : (wfTy k7 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k7 T2)) IHT2 (c2 : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c2 k7 k8)) =>
      (wfTy_tarr k8 (IHT1 c2 k8 (weaken_shifthvl_tm H0 ins)) (IHT2 c2 k8 (weaken_shifthvl_tm H0 ins)))))).
  Definition shift_wfTm : (forall (k7 : Hvl) ,
    (forall (s7 : Tm) (wf : (wfTm k7 s7)) ,
      (forall (c2 : (Cutoff tm)) (k8 : Hvl) ,
        (shifthvl_tm c2 k7 k8) -> (wfTm k8 (shiftTm c2 s7))))) := (ind_wfTm (fun (k7 : Hvl) (s7 : Tm) (wf : (wfTm k7 s7)) =>
    (forall (c2 : (Cutoff tm)) (k8 : Hvl) ,
      (shifthvl_tm c2 k7 k8) -> (wfTm k8 (shiftTm c2 s7)))) (fun (k7 : Hvl) (x17 : (Index tm)) (wfi : (wfindex k7 x17)) (c2 : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c2 k7 k8)) =>
    (wfTm_var k8 (shift_wfindex_tm c2 k7 k8 ins x17 wfi))) (fun (k7 : Hvl) (c2 : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c2 k7 k8)) =>
    (wfTm_tt k8)) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) (t : Tm) (wf0 : (wfTm (HS tm k7) t)) IHt17 (c2 : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c2 k7 k8)) =>
    (wfTm_abs k8 (shift_wfTy k7 T wf c2 k8 (weaken_shifthvl_tm H0 ins)) (IHt17 (CS c2) (HS tm k8) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k7 : Hvl) (t1 : Tm) (wf : (wfTm k7 t1)) IHt17 (t2 : Tm) (wf0 : (wfTm k7 t2)) IHt18 (c2 : (Cutoff tm)) (k8 : Hvl) (ins : (shifthvl_tm c2 k7 k8)) =>
    (wfTm_app k8 (IHt17 c2 k8 (weaken_shifthvl_tm H0 ins)) (IHt18 c2 k8 (weaken_shifthvl_tm H0 ins))))).
End ShiftWellFormed.
 Hint Resolve shift_wfindex_tm : infra.
 Hint Resolve shift_wfindex_tm : shift.
 Hint Resolve shift_wfindex_tm : shift_wf.
 Hint Resolve shift_wfindex_tm : wf.
 Hint Resolve shift_wfTm shift_wfTy : infra.
 Hint Resolve shift_wfTm shift_wfTy : shift.
 Hint Resolve shift_wfTm shift_wfTy : shift_wf.
 Hint Resolve shift_wfTm shift_wfTy : wf.
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
  Inductive substhvl_tm (k7 : Hvl) : (forall (d4 : (Trace tm)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k7 X0 (HS tm k7) k7)
    | substhvl_tm_there_tm
        {d4 : (Trace tm)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_tm k7 d4 k8 k9) -> (substhvl_tm k7 (XS tm d4) (HS tm k8) (HS tm k9)).
  Lemma weaken_substhvl_tm  :
    (forall {k8 : Hvl} (k7 : Hvl) {d4 : (Trace tm)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_tm k8 d4 k9 k10) -> (substhvl_tm k8 (weakenTrace d4 k7) (appendHvl k9 k7) (appendHvl k10 k7))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k7 : Hvl} {s7 : Tm} (wft : (wfTm k7 s7)) :
    (forall {d4 : (Trace tm)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_tm k7 d4 k8 k9) -> (forall {x17 : (Index tm)} ,
        (wfindex k8 x17) -> (wfTm k9 (substIndex d4 s7 x17)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Definition substhvl_tm_wfTy {k7 : Hvl} : (forall (k8 : Hvl) ,
    (forall (S0 : Ty) (wf0 : (wfTy k8 S0)) ,
      (forall {d4 : (Trace tm)} {k9 : Hvl} ,
        (substhvl_tm k7 d4 k8 k9) -> (wfTy k9 S0)))) := (fun (k8 : Hvl) =>
    (ind_wfTy k8 (fun (S0 : Ty) (wf0 : (wfTy k8 S0)) =>
      (forall {d4 : (Trace tm)} {k9 : Hvl} ,
        (substhvl_tm k7 d4 k8 k9) -> (wfTy k9 S0))) (fun {d4 : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d4 k8 k9)) =>
      (wfTy_tunit k9)) (fun (T1 : Ty) (wf0 : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k8 T2)) IHT2 {d4 : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d4 k8 k9)) =>
      (wfTy_tarr k9 (IHT1 (weakenTrace d4 H0) k9 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d4 H0) k9 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_tm_wfTm {k7 : Hvl} {s7 : Tm} (wf : (wfTm k7 s7)) : (forall (k8 : Hvl) ,
    (forall (s8 : Tm) (wf0 : (wfTm k8 s8)) ,
      (forall {d4 : (Trace tm)} {k9 : Hvl} ,
        (substhvl_tm k7 d4 k8 k9) -> (wfTm k9 (substTm d4 s7 s8))))) := (ind_wfTm (fun (k8 : Hvl) (s8 : Tm) (wf0 : (wfTm k8 s8)) =>
    (forall {d4 : (Trace tm)} {k9 : Hvl} ,
      (substhvl_tm k7 d4 k8 k9) -> (wfTm k9 (substTm d4 s7 s8)))) (fun (k8 : Hvl) {x17 : (Index tm)} (wfi : (wfindex k8 x17)) {d4 : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d4 k8 k9)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k8 : Hvl) {d4 : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d4 k8 k9)) =>
    (wfTm_tt k9)) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy k8 T)) (t : Tm) (wf1 : (wfTm (HS tm k8) t)) IHt17 {d4 : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d4 k8 k9)) =>
    (wfTm_abs k9 (substhvl_tm_wfTy k8 T wf0 (weaken_substhvl_tm H0 del)) (IHt17 (weakenTrace d4 (HS tm H0)) (HS tm k9) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k8 : Hvl) (t1 : Tm) (wf0 : (wfTm k8 t1)) IHt17 (t2 : Tm) (wf1 : (wfTm k8 t2)) IHt18 {d4 : (Trace tm)} {k9 : Hvl} (del : (substhvl_tm k7 d4 k8 k9)) =>
    (wfTm_app k9 (IHt17 (weakenTrace d4 H0) k9 (weaken_substhvl_tm H0 del)) (IHt18 (weakenTrace d4 H0) k9 (weaken_substhvl_tm H0 del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm : infra.
 Hint Resolve substhvl_tm_wfindex_tm : subst.
 Hint Resolve substhvl_tm_wfindex_tm : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm : wf.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy : infra.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy : subst.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfTm substhvl_tm_wfTy : wf.
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
  Fixpoint substEnv (d4 : (Trace tm)) (s7 : Tm) (G : Env) : Env :=
    match G with
      | empty => empty
      | evar G0 T => (evar (substEnv d4 s7 G0) T)
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c2 : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c2 G)) =
      (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d4 : (Trace tm)) (s7 : Tm) (G : Env) ,
      ((domainEnv (substEnv d4 s7 G)) =
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
      (forall (d4 : (Trace tm)) (s7 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d4 s7 (appendEnv G G0)) =
        (appendEnv (substEnv d4 s7 G) (substEnv (weakenTrace d4 (domainEnv G)) s7 G0)))).
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
  Inductive subst_evar (G : Env) (T5 : Ty) (s7 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T5 s7 X0 (evar G T5) G)
    | subst_evar_there_evar
        {d4 : (Trace tm)} {G0 : Env}
        {G1 : Env} {T : Ty} :
        (subst_evar G T5 s7 d4 G0 G1) -> (subst_evar G T5 s7 (XS tm d4) (evar G0 T) (evar G1 T)).
  Lemma weaken_subst_evar {G : Env} {T5 : Ty} {s7 : Tm} :
    (forall (G0 : Env) {d4 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T5 s7 d4 G1 G2) -> (subst_evar G T5 s7 (weakenTrace d4 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s7 : Tm} {T5 : Ty} :
    (forall {d4 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T5 s7 d4 G0 G1) -> (substhvl_tm (domainEnv G) d4 (domainEnv G0) (domainEnv G1))).
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
 Hint Constructors wfTm wfTy : infra.
 Hint Constructors wfTm wfTy : wf.
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
  end.
Fixpoint size_Tm (s : Tm) {struct s} : nat :=
  match s with
    | var x => 1
    | tt => 1
    | abs T t => (plus 1 (plus (size_Ty T) (size_Tm t)))
    | app t1 t2 => (plus 1 (plus (size_Tm t1) (size_Tm t2)))
  end.
Lemma shift_size_Tm  :
  (forall (s7 : Tm) (c1 : (Cutoff tm)) ,
    ((size_Tm (shiftTm c1 s7)) =
    (size_Tm s7))).
Proof.
  apply_mutual_ind ind_Tm.
  - intros x15 c1.
  reflexivity.
  - intros c2; simpl; apply ((f_equal S)); reflexivity.
  - intros T4 t14 IHt14.
  intros c2; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + reflexivity.
  + exact ((IHt14 (CS c2))).
  - intros t15 IHt15 t16 IHt16.
  intros c2; simpl; apply ((f_equal S)); repeat (apply ((f_equal2 plus))).
  + exact ((IHt15 c2)).
  + exact ((IHt16 c2)).
Qed.

 Hint Rewrite shift_size_Tm : interaction.
 Hint Rewrite shift_size_Tm : shift_size.
Lemma weaken_size_Tm  :
  (forall (k7 : Hvl) (s7 : Tm) ,
    ((size_Tm (weakenTm s7 k7)) =
    (size_Tm s7))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k7 : Hvl) (S0 : Ty) ,
    ((size_Ty (weakenTy S0 k7)) =
    (size_Ty S0))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : weaken_size.