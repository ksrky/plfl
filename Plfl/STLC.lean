/-
  Types and terms of the simply typed lambda calculus
-/
inductive Ty : Type
  | bool : Ty
  | arr : Ty → Ty → Ty

notation "bool" => Ty.bool
infixr:70 " ⇒ " => Ty.arr

-- Decidable equality of types
instance Ty.decEq : DecidableEq Ty
  | bool , bool => isTrue rfl
  | bool , _ ⇒ _ => isFalse Ty.noConfusion
  | _ ⇒ _ , Ty.bool => isFalse Ty.noConfusion
  | a₁ ⇒ a₂ , b₁ ⇒ b₂ =>
      match decEq a₁ b₁ with
      | isTrue h₁ =>
          match decEq a₂ b₂ with
          | isTrue h₂ => by rw [h₁, h₂]; apply isTrue; rfl
          | isFalse h₂ => by rw [h₁]; apply isFalse; intro h; cases h; apply h₂; rfl
      | isFalse h₁ => by apply isFalse; intro h; cases h; apply h₁; rfl

inductive Tm : Type
  | var : String → Tm
  | app : Tm → Tm → Tm
  | lam : String → Ty → Tm → Tm
  | tru : Tm
  | fls : Tm
  | ite : Tm → Tm → Tm → Tm

notation "true"  => Tm.tru
notation "false" => Tm.fls
prefix:90 "% "   => Tm.var
notation:60 "λ" x ":" τ:71 "⇒" t:60 => Tm.lam x τ t
infixl:70 " ⬝ "  => Tm.app
notation:60 "if" t₁ "then" t₂ "else" t₃ => Tm.ite t₁ t₂ t₃

def notB : Tm := if true then false else true

-- Values
inductive Val : Tm → Prop
  | lam {x τ t} : Val (λ x : τ ⇒ t)
  | tru : Val true
  | fls : Val false

-- Substitution
def subst (x : String) (s : Tm) : Tm → Tm
  | Tm.var y => if x = y then s else Tm.var y
  | Tm.app t₁ t₂ => subst x s t₁ ⬝ subst x s t₂
  | Tm.lam y τ t => λ y : τ ⇒ if x = y then t else subst x s t
  | Tm.tru => true
  | Tm.fls => false
  | Tm.ite t₁ t₂ t₃ => if subst x s t₁ then subst x s t₂ else subst x s t₃

notation:90 "[" x "↦" s "]" t:80 => subst x s t

/-
  Evaluation step
-/
inductive Step : Tm → Tm → Prop
  | app_abs {x τ t v} : Val v → Step ((λ x : τ ⇒ t) ⬝ v) ([x ↦ v] t)
  | app₁ {t₁ t₁' t₂} : Step t₁ t₁' → Step (t₁ ⬝ t₂) (t₁' ⬝ t₂)
  | app₂ {v₁ t₂ t₂'} : Val v₁ → Step t₂ t₂' → Step (v₁ ⬝ t₂) (v₁ ⬝ t₂')
  | iftru {t₁ t₂} : Step (if true then t₁ else t₂) t₁
  | iffls {t₁ t₂} : Step (if false then t₁ else t₂) t₂
  | ite {t₁ t₁' t₂ t₃} : Step t₁ t₁' → Step (if t₁ then t₂ else t₃) (if t₁' then t₂ else t₃)

infix:40 " ——→ " => Step

/- Reflexive and transitive closure of Step -/
inductive Steps : Tm → Tm → Prop
  | refl {t}        : Steps t t
  | step {t t' t''} : Step t t' → Steps t' t'' → Steps t t''

infix:40 " ——→* " => Steps

def halts (e : Tm) : Prop := ∃ e', e ——→* e' ∧ Val e'

postfix:80 " ⇓" => halts

/-
  Context management
-/
inductive Context : Type
  | empty : Context
  | cons : Context → String → Ty → Context

notation "∅" => Context.empty
notation:40 Γ ";" x ":" τ:50 => Context.cons Γ x τ

inductive Lookup : Context → String → Ty → Prop
  | here {Γ x τ} : Lookup (Γ ; x : τ) x τ
  | there {Γ x y τ τ'} : x ≠ y → Lookup Γ x τ → Lookup (Γ ; y : τ') x τ

notation:40 Γ "∋" x ":" τ:50 => Lookup Γ x τ

/- Typing judgements -/
inductive Typing : Context → Tm → Ty → Prop
  | var {Γ x τ} : Γ ∋ x : τ → Typing Γ (%x) τ
  | app {Γ t₁ t₂ τ τ'} : Typing Γ t₁ (τ ⇒ τ') → Typing Γ t₂ τ →
                          Typing Γ (t₁ ⬝ t₂) τ'
  | lam {Γ x τ t τ'} : Typing (Γ ; x : τ) t τ' → Typing Γ (λ x : τ ⇒ t) (τ ⇒ τ')
  | tru {Γ} : Typing Γ Tm.tru bool
  | fls {Γ} : Typing Γ Tm.fls bool
  | ite {Γ t₁ t₂ t₃ τ} : Typing Γ t₁ bool → Typing Γ t₂ τ → Typing Γ t₃ τ →
                          Typing Γ (if t₁ then t₂ else t₃) τ

notation:40 Γ "⊢" t "∶" τ:50 => Typing Γ t τ

theorem lookup_is_functional {Γ x τ τ'} : Γ ∋ x : τ → Γ ∋ x : τ' → τ = τ'
  | Lookup.here , Lookup.here => rfl
  | Lookup.here , Lookup.there ne _ => False.elim (ne rfl)
  | Lookup.there ne _  , Lookup.here => False.elim (ne rfl)
  | Lookup.there _ xisin , Lookup.there _ xisin' => lookup_is_functional xisin xisin'
