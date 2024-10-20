inductive Ty : Type
  | bool : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq

notation "bool" => Ty.bool
infixr:70 " ⇒ " => Ty.arr

inductive Tm : Type
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : String -> Ty → Tm → Tm
  | tru : Tm
  | fls : Tm
  | ite : Tm → Tm → Tm → Tm

notation "true"  => Tm.tru
notation "false" => Tm.fls
prefix:90 "% "   => Tm.var
notation:60 "λ" x ":" τ:71 "⇒" e:60 => Tm.lam x τ e
infixl:70 " ⬝ "  => Tm.app
notation:60 "if" e₁ "then" e₂ "else" e₃ => Tm.ite e₁ e₂ e₃

inductive Val : Tm → Prop
  | lam {x τ t} : Val (λ x : τ ⇒ t)
  | tru : Val true
  | fls : Val false

/- inductive Step : Tm → Tm → Prop
  | app_abs {x τ t v} : Val v → Step ((λ x : τ ⇒ t) ⬝ v) ([x ↦ v] t)
  | app₁ {t₁ t₁' t₂} : Step t₁ t₁' → Step (t₁ ⬝ t₂) (t₁' ⬝ t₂)
  | app₂ {v₁ t₂ t₂'} : Val v₁ → Step t₂ t₂' → Step (v₁ ⬝ t₂) (v₁ ⬝ t₂')
  | iftru {t₁ t₂} : Step (if true then t₁ else t₂) t₁
  | iffls {t₁ t₂} : Step (if false then t₁ else t₂) t₂
  | ite {t₁ t₁' t₂ t₃} : Step t₁ t₁' → Step (if t₁ then t₂ else t₃) (if t₁' then t₂ else t₃)

infix:40 " ——→ " => Step -/
