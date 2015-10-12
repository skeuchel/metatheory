Require Export FOmega.
Set Implicit Arguments.

(*************************************************************************)
(* Evaluation.                                                           *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
    | abs _ _  => True
    | tyabs _ _ => True
    | _        => False
  end.

Inductive red : Tm → Tm → Prop :=
  | appfun {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (app t1 t2) (app t1 t2')
  | appabs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm X0 t2 t12)
  | typefun {t1 t1' T2} :
      red t1 t1' → red (tyapp t1 T2) (tyapp t1' T2)
  | tapptabs {K11 T2 t12} :
      red (tyapp (tyabs K11 t12) T2) (tsubstTm X0 T2 t12).
