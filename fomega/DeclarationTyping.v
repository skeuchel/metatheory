Require Export FOmega.
Set Implicit Arguments.

(******************************************************************************)
(* Kinding relation                                                           *)
(******************************************************************************)

Inductive Kinding (Γ : Env) : Ty → Kind → Prop :=
  | K_TVar {X K} :
      lookup_etvar Γ X K → Kinding Γ (tvar X) K
  | K_Abs {K1 K2 T2} :
      Kinding (etvar Γ K1) T2 K2 →
      Kinding Γ (tabs K1 T2) (karr K1 K2)
  | K_App {K11 K12 T1 T2} :
      Kinding Γ T1 (karr K11 K12) → Kinding Γ T2 K11 →
      Kinding Γ (tapp T1 T2) K12
  | K_Arr {T1 T2} :
      Kinding Γ T1 star → Kinding Γ T2 star →
      Kinding Γ (tarr T1 T2) star
  | K_All {K1 T2} :
      Kinding (etvar Γ K1) T2 star →
      Kinding Γ (tall K1 T2) star.


(******************************************************************************)
(* Type equivalence relation.                                                 *)
(******************************************************************************)

Inductive TyEq (Γ : Env) : Ty → Ty → Kind → Prop :=
  | Q_Arrow {S1 T1 S2 T2} :
      TyEq Γ S1 T1 star → TyEq Γ S2 T2 star →
      TyEq Γ (tarr S1 S2) (tarr T1 T2) star
  | Q_Abs {K1 K2 S2 T2} :
      TyEq (etvar Γ K1) S2 T2 K2 →
      TyEq Γ (tabs K1 S2) (tabs K1 T2) (karr K1 K2)
  | Q_App {K1 K2 S1 T1 S2 T2} :
      TyEq Γ S1 T1 (karr K1 K2) → TyEq Γ S2 T2 K1 →
      TyEq Γ (tapp S1 S2) (tapp T1 T2) K2
  | Q_All {K1 S2 T2} :
      TyEq (etvar Γ K1) S2 T2 star →
      TyEq Γ (tall K1 S2) (tall K1 T2) star
  | Q_AppAbs {K11 K12 T12 T2} :
      Kinding (etvar Γ K11) T12 K12 → Kinding Γ T2 K11 →
      TyEq Γ (tapp (tabs K11 T12) T2) (tsubstTy X0 T2 T12) K12
  | Q_Refl {T K} :
      Kinding Γ T K → TyEq Γ T T K
  | Q_Symm {T S K} :
      TyEq Γ T S K → TyEq Γ S T K
  | Q_Trans {S U T K} :
      TyEq Γ S U K → TyEq Γ U T K → TyEq Γ S T K.

(******************************************************************************)
(* Typing relation.                                                           *)
(******************************************************************************)

Inductive Typing (Γ : Env) : Tm → Ty → Prop :=
  | T_Var {y T} :
      lookup_evar Γ y T → Typing Γ (var y) T
  | T_Abs {t T1 T2} :
      Kinding Γ T1 star → Typing (evar Γ T1) t T2 →
      Typing Γ (abs T1 t) (tarr T1 T2)
  | T_App {t1 t2 T11 T12} :
      Typing Γ t1 (tarr T11 T12) → Typing Γ t2 T11 →
      Typing Γ (app t1 t2) T12
  | T_TAbs {K t T} :
      Typing (etvar Γ K) t T →
      Typing Γ (tyabs K t) (tall K T)
  | T_TApp {t1 K11 T12 T2} :
      Typing Γ t1 (tall K11 T12) → Kinding Γ T2 K11 →
      Typing Γ (tyapp t1 T2) (tsubstTy X0 T2 T12)
  | T_Eq {t S T} :
      Typing Γ t S → TyEq Γ S T star →
      Typing Γ t T.

(******************************************************************************)
(* Type reduction relation.                                                   *)
(******************************************************************************)

Inductive TRed (Γ : Env) : Ty → Ty → Kind → Prop :=
  | QR_Var {X K} :
      lookup_etvar Γ X K →
      TRed Γ (tvar X) (tvar X) K
  | QR_Arrow {S1 T1 S2 T2} :
      TRed Γ S1 T1 star → TRed Γ S2 T2 star →
      TRed Γ (tarr S1 S2) (tarr T1 T2) star
  | QR_Abs {S2 T2 K1 K2} :
      TRed (etvar Γ K1) S2 T2 K2 →
      TRed Γ (tabs K1 S2) (tabs K1 T2) (karr K1 K2)
  | QR_App {S1 T1 S2 T2 K1 K2} :
      TRed Γ S1 T1 (karr K2 K1) → TRed Γ S2 T2 K2 →
      TRed Γ (tapp S1 S2) (tapp T1 T2) K1
  | QR_All {K1 S2 T2} :
      TRed (etvar Γ K1) S2 T2 star →
      TRed Γ (tall K1 S2) (tall K1 T2) star
  | QR_AppAbs {S1 T1 S2 T2 K1 K2} :
      TRed (etvar Γ K2) S1 T1 K1 → TRed Γ S2 T2 K2 →
      TRed Γ (tapp (tabs K2 S1) S2) (tsubstTy X0 T2 T1) K1.

Inductive TRedStar (Γ : Env) : Ty → Ty → Kind → Prop :=
  | QRS_Nil {T K} :
      Kinding Γ T K → TRedStar Γ T T K
  | QRS_Cons {S T U K} :
      TRedStar Γ S T K → TRed Γ T U K → TRedStar Γ S U K.
