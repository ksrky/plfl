import Init.Data.List.Basic

mutual
inductive Val : Type
  | num : Int → Val
  | var : String → Val
  | lam : List String → Exp → Val
  | tuple : List Val → Val

inductive Exp : Type
  -- | letVal : String → Val → Exp → Exp
  | letProj {n : Nat} : String → Fin n → Val → Exp → Exp
  | app : Val → List Val → Exp
  | halt : Val → Exp
end

mutual
def Val.subst (x : String) (s : Val) : Val → Val
  | .var y => if x = y then s else Val.var y
  | .lam ys e => .lam ys (if ys.elem x then e else Exp.subst x s e)
  | v => v

def Val.substs (x : String) (s : Val) (vs : List Val) : List Val :=
  vs.map (Val.subst x s)

def Exp.subst (x : String) (s : Val) : Exp → Exp
  -- | .letVal y v e => .letVal y (Val.subst x s v) (Exp.subst x s e)
  | .letProj y i v t => .letProj y i (Val.subst x s v) (Exp.subst x s t)
  | .app v us => .app (Val.subst x s v) (Val.substs x s us)
  | .halt v => .halt (Val.subst x s v)
end
termination_by
  Val.subst _ _ v => sizeOf v
  Val.substs _ _ vs => Nat.sum (List.map sizeOf vs)
  Exp.subst _ _ e => sizeOf e

notation:90 "[" x "↦" s "]" e:80 => Exp.subst x s e

def Exp.msubst (subs : List (String × Val)) : Exp → Exp
  | e => subs.foldl (λ e ⟨x, s⟩ => [x ↦ s] e) e

inductive Step : Exp → Exp → Prop
  | app_abs {xs e vs} : Step (.app (.lam xs e) vs) (e.msubst (List.zip xs vs))
  | halt {v} : Step (.halt v) (.halt v)
  | letProj_tuple {x vs e} {i : Fin vs.length} : Step (.letProj x i (Val.tuple vs) e) ([x ↦ vs.get i] e)
