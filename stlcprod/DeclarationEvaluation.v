Require Export Coq.Unicode.Utf8.
Require Export StlcProd.

(*************************************************************************)
(* Reduction relation                                                    *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
    | tt       => True
    | abs _ _  => True
    | prod x y => Value x ∧ Value y
    | _        => False
  end.

Inductive Match : Pat → Tm → Tm → Tm → Prop :=
  | M_Var {T v t} :
      Match (pvar T) v t (substTm X0 v t)
  | M_Prod {p1 p2 v1 v2 t t' t''} :
      Match p2 (weakenTm v2 (bindPat p1)) t t' →
      Match p1 v1 t' t'' →
      Match (pprod p1 p2) (prod v1 v2) t t''.

Inductive red : Tm → Tm → Prop :=
  | appabs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm X0 t2 t12)
  | appfun {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (app t1 t2) (app t1 t2')
  | prodl {t1 t1' t2} :
      red t1 t1' → red (prod t1 t2) (prod t1' t2)
  | prodr {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (prod t1 t2) (prod t1 t2')
  | lettp {p t1 t1' t2} :
      red t1 t1' → red (lett p t1 t2) (lett p t1' t2)
  | lettv {p t1 t3 t2} :
      Value t1 → Match p t1 t2 t3 → red (lett p t1 t2) t3.
