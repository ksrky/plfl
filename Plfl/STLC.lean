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

notation:90 t "[" x "↦" s "]" => subst x s t

/-
  Reduction
-/
inductive Reduction : Tm → Tm → Prop
  | app_abs {x τ t v} : Val v → Reduction ((λ x : τ ⇒ t) ⬝ v) (t [x ↦ v])
  | app₁ {t₁ t₁' t₂} : Reduction t₁ t₁' → Reduction (t₁ ⬝ t₂) (t₁' ⬝ t₂)
  | app₂ {v₁ t₂ t₂'} : Val v₁ → Reduction t₂ t₂' → Reduction (v₁ ⬝ t₂) (v₁ ⬝ t₂')
  | tru {t₁ t₂} : Reduction (if true then t₁ else t₂) t₁
  | fls {t₁ t₂} : Reduction (if false then t₁ else t₂) t₂
  | ite {t₁ t₁' t₂ t₃} : Reduction t₁ t₁' → Reduction (if t₁ then t₂ else t₃) (if t₁' then t₂ else t₃)

infix:40 " —⟶ " => Reduction

/-
  Context management
-/
inductive Context : Type
  | empty : Context
  | cons : Context → String → Ty → Context

notation "∅" => Context.empty
notation:50 Γ ";" x ":" τ:50 => Context.cons Γ x τ

inductive Lookup : Context → String → Ty → Prop
  | here {Γ x τ} : Lookup (Γ ; x : τ) x τ
  | there {Γ x y τ τ'} : x ≠ y → Lookup Γ x τ → Lookup (Γ ; y : τ') x τ

notation:40 Γ "∋" x ":" τ:50 => Lookup Γ x τ

/-
  Typing judgements
-/
inductive Judgement : Context → Tm → Ty → Prop
  | var {Γ x τ} : Γ ∋ x : τ → Judgement Γ (%x) τ
  | app {Γ t₁ t₂ τ τ'} : Judgement Γ t₁ (τ ⇒ τ') → Judgement Γ t₂ τ → Judgement Γ (t₁ ⬝ t₂) τ'
  | lam {Γ x τ t τ'} : Judgement (Γ ; x : τ) t τ' → Judgement Γ (λ x : τ ⇒ t) (τ ⇒ τ')
  | tru {Γ} : Judgement Γ Tm.tru bool
  | fls {Γ} : Judgement Γ Tm.fls bool
  | ite {Γ t₁ t₂ t₃ τ} : Judgement Γ t₁ bool → Judgement Γ t₂ τ → Judgement Γ t₃ τ → Judgement Γ (if t₁ then t₂ else t₃) τ

notation:40 Γ "⊢" t ":" τ:50 => Judgement Γ t τ

theorem lookup_is_functional {Γ x τ τ'} : Γ ∋ x : τ → Γ ∋ x : τ' → τ = τ'
  | Lookup.here , Lookup.here => rfl
  | Lookup.here , Lookup.there ne _ => False.elim (ne rfl)
  | Lookup.there ne _  , Lookup.here => False.elim (ne rfl)
  | Lookup.there _ xisin , Lookup.there _ xisin' => lookup_is_functional xisin xisin'
