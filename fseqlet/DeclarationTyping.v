Require Export Coq.Unicode.Utf8.
Require Export FSeqLet.
Set Implicit Arguments.

(******************************************************************************)
(* Typing relation.                                                           *)
(******************************************************************************)

Inductive Typing (Γ : Env) : Tm → Ty → Prop :=
  | T_Var {y T} :
      lookup_evar Γ y T → Typing Γ (var y) T
  | T_Abs {t T1 T2} (wT1: wfTy (domainEnv Γ) T1) :
      Typing (evar Γ T1) t T2 →
      Typing Γ (abs T1 t) (tarr T1 T2)
  | T_App {t1 t2 T11 T12} :
      Typing Γ t1 (tarr T11 T12) → Typing Γ t2 T11 →
      Typing Γ (app t1 t2) T12
  | T_Tabs {t T} :
      Typing (etvar Γ) t T → Typing Γ (tabs t) (tall T)
  | T_Tapp {t1 T12 T2} :
      Typing Γ t1 (tall T12) → wfTy (domainEnv Γ) T2 →
      Typing Γ (tapp t1 T2) (tsubstTy X0 T2 T12)
  | T_Let {ds t T Δ} :
      DTyping Γ ds Δ →
      Typing (appendEnv Γ Δ) t (weakenTy T (domainEnv Δ)) →
      Typing Γ (lett ds t) T
with DTyping (Γ : Env) : Decls → Env → Prop :=
  | T_Dnil :
      DTyping Γ dnil empty
  | T_DCons {Δ t T ds} :
      Typing Γ t T → DTyping (evar Γ T) ds Δ →
      DTyping Γ (dcons t ds) (appendEnv (evar empty T) Δ).

Scheme ind_typing := Induction for Typing Sort Prop
with ind_dtyping := Induction for DTyping Sort Prop.

Combined Scheme ind_typing_dtyping from
  ind_typing, ind_dtyping.
