Require Export FProd.
Set Implicit Arguments.

(******************************************************************************)
(* Typing relation.                                                           *)
(******************************************************************************)

Inductive PTyping (Γ: Env) : Pat → Ty → Env → Prop :=
  | P_Var {T} (wfT: wfTy (domainEnv Γ) T) :
      PTyping Γ (pvar T) T (evar empty T)
  | P_Prod {p1 T1 Δ1 p2 T2 Δ2} :
      PTyping Γ p1 T1 Δ1 →
      PTyping (appendEnv Γ Δ1) (weakenPat p2 (domainEnv Δ1))
        (weakenTy T2 (domainEnv Δ1)) Δ2 →
      PTyping Γ (pprod p1 p2) (tprod T1 T2) (appendEnv Δ1 Δ2).

Inductive Typing (Γ: Env) : Tm → Ty → Prop :=
  | T_Var {y T} :
      lookup_evar Γ y T → Typing Γ (var y) T
  | T_Abs {t T1 T2} (wf_T1: wfTy (domainEnv Γ) T1) :
      Typing (evar Γ T1) t T2 →
      Typing Γ (abs T1 t) (tarr T1 T2)
  | T_App {t1 t2 T11 T12} :
      Typing Γ t1 (tarr T11 T12) → Typing Γ t2 T11 →
      Typing Γ (app t1 t2) T12
  | T_Tabs {t T} :
      Typing (etvar Γ) t T →  Typing Γ (tabs t) (tall T)
  | T_Tapp {t1 T12 T2} :
      Typing Γ t1 (tall T12) → wfTy (domainEnv Γ) T2 →
      Typing Γ (tapp t1 T2) (tsubstTy X0 T2 T12)
  | T_Prod {t1 T1 t2 T2} :
      Typing Γ t1 T1 → Typing Γ t2 T2 →
      Typing Γ (prod t1 t2) (tprod T1 T2)
  | T_Let {p t1 t2 T1 T2 Δ} :
      Typing Γ t1 T1 → PTyping Γ p T1 Δ →
      Typing (appendEnv Γ Δ) t2 (weakenTy T2 (domainEnv Δ)) →
      Typing Γ (lett p t1 t2) T2.
