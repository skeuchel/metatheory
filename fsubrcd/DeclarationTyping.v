Require Export FSubRcd.
Set Implicit Arguments.

(******************************************************************************)
(* Record lookups                                                             *)
(******************************************************************************)

Lemma eq_lab_dec (l k: Lab) : {l = k} + {l ≠ k}.
Proof.
  decide equality .
Qed.

Fixpoint trec_get (Tr : TRec) (l : Lab) : option Ty :=
  match Tr with
  | tcons k T Tr => if eq_lab_dec l k then Some T else trec_get Tr l
  | tnil         => None
  end.
Coercion trec_get : TRec >-> Funclass.

Fixpoint rec_get (tr : Rec) (l : Lab) : (option Tm) :=
  match tr with
  | rcons k t tr => if eq_lab_dec l k then Some t else rec_get tr l
  | rnil         => None
  end.

Coercion rec_get : Rec >-> Funclass.

Fixpoint prec_get (pr : PRec) (l : Lab) : (option Pat) :=
  match pr with
  | pcons k p pr => if eq_lab_dec l k then Some p else prec_get pr l
  | pnil         => None
  end.

Coercion prec_get : PRec >-> Funclass.

(******************************************************************************)
(* Subtyping relation                                                         *)
(******************************************************************************)

Inductive Sub (Γ: Env) : Ty → Ty → Prop :=
  | SA_Top {S} (wf_S: wfTy (domainEnv Γ) S) :
      Sub Γ S top
  | SA_Refl_TVar {X} :
      wfindex (domainEnv Γ) X → Sub Γ (tvar X) (tvar X)
  | SA_Trans_TVar {X T U} :
      lookup_etvar Γ X U → Sub Γ U T → Sub Γ (tvar X) T
  | SA_Arrow {T1 T2 S1 S2} :
      Sub Γ T1 S1 → Sub Γ S2 T2 → Sub Γ (tarr S1 S2) (tarr T1 T2)
  | SA_All {T1 T2 S1 S2} :
      Sub Γ T1 S1 → Sub (etvar Γ T1) S2 T2 → Sub Γ (tall S1 S2) (tall T1 T2)
  | SA_Rcd {Sr Tr : TRec}
      (wSr: wfTRec (domainEnv Γ) Sr)
      (wTr: wfTRec (domainEnv Γ) Tr)
      (incl: ∀ l T, Tr l = Some T → ∃ S, Sr l = Some S)
      (subs: ∀ l S T, Tr l = Some T → Sr l = Some S → Sub Γ S T) :
      Sub Γ (trec Sr) (trec Tr).

(******************************************************************************)
(* Typing relation.                                                           *)
(******************************************************************************)

Inductive PTyping (Γ: Env) : Pat → Ty → Env → Prop :=
  | P_Var {T} (wT: wfTy (domainEnv Γ) T) :
      PTyping Γ (pvar T) T (evar empty T)
  | P_Rcd {Δ pr Tr} :
      PRTyping Γ pr Tr Δ →
      PTyping Γ (prec pr) (trec Tr) Δ
with PRTyping (Γ : Env) : PRec → TRec → Env → Prop :=
  | P_Rcd_Cons {Δp Δpr l p pr Tp Tr} :
      PTyping Γ p Tp Δp →
      PRTyping
        (appendEnv Γ Δp)
        (weakenPRec pr (domainEnv Δp))
        (weakenTRec Tr (domainEnv Δp)) Δpr →
      Tr l = None →
      PRTyping Γ (pcons l p pr) (tcons l Tp Tr) (appendEnv Δp Δpr)
  | P_Rcd_Nil :
      PRTyping Γ pnil tnil (empty).

Scheme ind_ptyping := Induction for PTyping Sort Prop
with ind_prtyping := Induction for PRTyping Sort Prop.
Combined Scheme ind_ptyping_prtyping from
  ind_ptyping, ind_prtyping.

Inductive Typing (Γ : Env) : Tm → Ty → Prop :=
  | T_Var {y T} :
      lookup_evar Γ y T → Typing Γ (var y) T
  | T_Abs {t T1 T2} (wf_T1: wfTy (domainEnv Γ) T1) :
      Typing (evar Γ T1) t T2 →
      Typing Γ (abs T1 t) (tarr T1 T2)
  | T_App {t1 t2 T11 T12} :
      Typing Γ t1 (tarr T11 T12) → Typing Γ t2 T11 →
      Typing Γ (FSubRcd.app t1 t2) T12
  | T_Tabs {t T1 T2} (wf_T1: wfTy (domainEnv Γ) T1) :
      Typing (etvar Γ T1) t T2 →
      Typing Γ (tabs T1 t) (tall T1 T2)
  | T_Tapp {t1 T11 T12 T2} :
      Typing Γ t1 (tall T11 T12) → Sub Γ T2 T11 →
      Typing Γ (tapp t1 T2) (tsubstTy X0 T2 T12)
  | T_Let {p t1 t2 T1 T2 Δ} :
      Typing Γ t1 T1 → PTyping Γ p T1 Δ →
      Typing (appendEnv Γ Δ) t2 (weakenTy T2 (domainEnv Δ)) →
      Typing Γ (lett p t1 t2) T2
  | T_Rcd {tr Tr} :
      RTyping Γ tr Tr →
      Typing Γ (rec tr) (trec Tr)
  | T_Proj {tr l T} {Tr: TRec} (lIn: Tr l = Some T) :
      Typing Γ tr (trec Tr) →
      Typing Γ (prj tr l) T
  | T_Sub {t T1 T2} :
      Typing Γ t T1 → Sub Γ T1 T2 →
      Typing Γ t T2
with RTyping (Γ : Env) : Rec → TRec → Prop :=
  | T_Rcd_Nil :
      RTyping Γ rnil tnil
  | T_Rcd_Cons {l t T tr Tr} :
      Typing Γ t T →
      RTyping Γ tr Tr →
      (*tr l = None →
      Tr l = None → *)
      RTyping Γ (rcons l t tr) (tcons l T Tr).

Scheme ind_typing := Induction for Typing Sort Prop
with ind_rtyping := Induction for RTyping Sort Prop.
Combined Scheme ind_typing_rtyping from
  ind_typing, ind_rtyping.
