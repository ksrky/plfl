inductive Ty : Type
  | bool : Ty
  | arr : Ty → Ty → Ty

instance Ty.decEq : DecidableEq Ty
  | Ty.bool , Ty.bool => isTrue rfl
  | Ty.bool , Ty.arr _ _ => isFalse Ty.noConfusion
  | Ty.arr _ _ , Ty.bool => isFalse Ty.noConfusion
  | Ty.arr a₁ a₂ , Ty.arr b₁ b₂ =>
      match decEq a₁ b₁ with
      | isTrue h₁ =>
          match decEq a₂ b₂ with
          | isTrue h₂ => by rw [h₁, h₂]; apply isTrue; rfl
          | isFalse h₂ => by rw [h₁]; apply isFalse; intro h; cases h; apply h₂; rfl
      | isFalse h₁ => by apply isFalse; intro h; cases h; apply h₁; rfl

notation "bool" => Ty.bool
notation:7 τ₁ "⇒" τ₂ => Ty.arr τ₁ τ₂

inductive Tm : Type
  | var : String → Tm
  | app : Tm → Tm → Tm
  | lam : String → Ty → Tm → Tm
  | tru : Tm
  | fls : Tm
  | ite : Tm → Tm → Tm → Tm

notation "true" => Tm.tru
notation "false" => Tm.fls
notation:5 "λ" x ":" τ:8 "⇒" t:5 => Tm.lam x τ t
notation:7 t₁:7 "⬝" t₂:8 => Tm.app t₁ t₂
notation "if" t₁ "then" t₂ "else" t₃ => Tm.ite t₁ t₂ t₃

def notB : Tm := if true then false else true

inductive Val : Tm → Prop
  | lam {x τ t} : Val (λ x : τ ⇒ t)
  | tru : Val Tm.tru
  | fls : Val Tm.fls

def subst (x : String) (s : Tm) : Tm → Tm
  | Tm.var y => if x = y then s else Tm.var y
  | Tm.app t₁ t₂ => subst x s t₁ ⬝ subst x s t₂
  | Tm.lam y τ t => λ y : τ ⇒ if x = y then t else subst x s t
  | Tm.tru => true
  | Tm.fls => false
  | Tm.ite t₁ t₂ t₃ => if subst x s t₁ then subst x s t₂ else subst x s t₃


notation:9 t "[" x "↦" s "]" => subst x s t

inductive Context : Type
  | empty : Context
  | cons : Context → String → Ty → Context

notation "∅" => Context.empty
notation:5 Γ ";" x ":" τ => Context.cons Γ x τ

inductive Lookup : Context → String → Ty → Prop
  | here {Γ x τ} : Lookup (Γ ; x : τ) x τ
  | there {Γ x y τ τ'} : x ≠ y → Lookup Γ x τ → Lookup (Γ ; y : τ') x τ

notation:4 Γ "∋" x ":" τ => Lookup Γ x τ

inductive Judgement : Context → Tm → Ty → Type
  | var {Γ x τ} : (Γ ∋ x : τ) → Judgement Γ (Tm.var x) τ
  | app {Γ t₁ t₂ τ τ'} : Judgement Γ t₁ (τ ⇒ τ') → Judgement Γ t₂ τ → Judgement Γ (t₁ ⬝ t₂) τ'
  | lam {Γ x τ t τ'} : Judgement (Γ ; x : τ) t τ' → Judgement Γ (λ x : τ ⇒ t) (τ ⇒ τ')
  | tru {Γ} : Judgement Γ Tm.tru bool
  | fls {Γ} : Judgement Γ Tm.fls bool
  | ite {Γ t₁ t₂ t₃ τ} : Judgement Γ t₁ bool → Judgement Γ t₂ τ → Judgement Γ t₃ τ → Judgement Γ (if t₁ then t₂ else t₃) τ

notation:4 Γ "⊢" t ":" τ => Judgement Γ t τ

theorem lookup_is_functional {Γ x τ τ'} : (Γ ∋ x : τ) → (Γ ∋ x : τ') → τ = τ'
  | Lookup.here , Lookup.here => rfl
  | Lookup.here , Lookup.there ne _ => False.elim (ne rfl)
  | Lookup.there ne _  , Lookup.here => False.elim (ne rfl)
  | Lookup.there _ xisin , Lookup.there _ xisin' => lookup_is_functional xisin xisin'
