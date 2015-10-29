Require Export DeclarationTyping.

(*************************************************************************)
(* Reduction relation                                                    *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
  | abs _ _   => True
  | tabs _ _  => True
  | rec tr    => RValue tr
  | _         => False
  end
with RValue (tr : Rec) : Prop :=
  match tr with
  | rcons _ t tr => Value t /\ RValue tr
  | rnil         => True
  end.

Inductive Match : Pat → Tm → Tm → Tm → Prop :=
  | M_Var {T v t} :
      Match (pvar T) v t (substTm X0 v t)
  | M_Rcd {pr vr t t'} :
      RMatch pr vr t t' →
      Match (prec pr) (rec vr) t t'
with RMatch : PRec → Rec → Tm → Tm → Prop :=
  | RM_Nil {vr t} :
      RMatch pnil vr t t
  | RM_Cons {l p pr} {vr: Rec} {v t t' t''} (vIn: vr l = Some v) :
      RMatch (weakenPRec pr (bindPat p)) (weakenRec vr (bindPat p)) t t' →
      Match p v t' t'' →
      RMatch (pcons l p pr) vr t t''.

Inductive red : Tm → Tm → Prop :=
  | appabs {T11 t12 t2} :
      Value t2 → red (FSubRcd.app (abs T11 t12) t2) (substTm X0 t2 t12)
  | tapptabs {T11 T2 t12} :
      red (tapp (tabs T11 t12) T2) (tsubstTm X0 T2 t12)
  | appfun {t1 t1' t2} :
      red t1 t1' → red (FSubRcd.app t1 t2) (FSubRcd.app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (FSubRcd.app t1 t2) (FSubRcd.app t1 t2')
  | typefun {t1 t1' T2} :
      red t1 t1' → red (tapp t1 T2) (tapp t1' T2)
  | E_Rec {tr tr'} :
      rred tr tr' → red (rec tr) (rec tr')
  | E_Let {p t1 t1' t2} :
      red t1 t1' → red (lett p t1 t2) (lett p t1' t2)
  | E_LetV {p t1 t2 t2'} :
      Value t1 → Match p t1 t2 t2' → red (lett p t1 t2) t2'
  | E_Proj {t t' l} :
      red t t' →
      red (prj t l) (prj t' l)
  | E_ProjRcd {tr t l} :
      RValue tr → tr l = Some t →
      red (prj (rec tr) l) t
with rred : Rec → Rec → Prop :=
  | rred_here {l t t' tr} :
      red t t' → rred (rcons l t tr) (rcons l t' tr)
  | rred_there {l t tr tr'} :
      Value t → rred tr tr' → rred (rcons l t tr) (rcons l t tr').
