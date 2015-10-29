Require Export Coq.Unicode.Utf8.
Require Export FSeqLet.
Set Implicit Arguments.

(*************************************************************************)
(* Reduction relation                                                    *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
  | abs _ _  => True
  | tabs _   => True
  | _        => False
  end.

Fixpoint ValueH (ds : Decls) : Prop :=
  match ds with
    | dnil       => True
    | dcons t ds => Value t
  end.

Inductive Match : Decls (* Γ,Δ *) → Tm (* Γ,Δ *) → Tm (* Γ *) → Prop :=
  | M_DNil {t} :
      Match dnil t t
  | M_DCons {v vs (* Γ,x,Δ *) t (* Γ,x,Δ *) t' (* Γ,x *)} :
      Match vs t t' →
      Match (dcons v vs) t (substTm X0 v t').

Inductive red : Tm → Tm → Prop :=
  | appabs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm X0 t2 t12)
  | tapptabs {T2 t12} :
      red (tapp (tabs t12) T2) (tsubstTm X0 T2 t12)
  | appfun {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (app t1 t2) (app t1 t2')
  | typefun {t1 t1' T2} :
      red t1 t1' → red (tapp t1 T2) (tapp t1' T2)
  | lett_dnil {t1} :
      red (lett dnil t1) t1
  | lett_dconsv {ds t1 t2} :
      Value t1 →
      red
        (lett (dcons t1 ds) t2)
        (lett (substDecls X0 t1 ds) (substTm (weakenTrace X0 (bind ds)) t1 t2))
  | lett_dconsr {ds ds' t2} :
      redds' ds ds' → red (lett ds t2) (lett ds' t2)
with redds' : Decls → Decls → Prop :=
  | dconsr {t t' ds} :
      red t t' → redds' (dcons t ds) (dcons t' ds).
