inductive Ty : Type
  | bool : Ty
  | arr : Ty → Ty → Ty

notation "bool" => Ty.bool
notation:70 τ₁ "⇒" τ₂ => Ty.arr τ₁ τ₂

inductive Context : Type
  | empty : Context
  | cons : Context → Ty → Context

notation "∅" => Context.empty
notation:50 Γ ";" τ => Context.cons Γ τ

inductive Lookup : Context → Ty → Prop
  | here {Γ τ} : Lookup (Γ ; τ) τ
  | there {Γ τ τ'} : Lookup Γ τ → Lookup (Γ ; τ') τ

notation:40 Γ "∋" τ:40 => Lookup Γ τ

inductive Judgement : Context → Ty → Type
  | var {Γ τ} : Γ ∋ τ → Judgement Γ τ
  | app {Γ τ τ'} : Judgement Γ (τ ⇒ τ') → Judgement Γ τ → Judgement Γ τ'
  | lam {Γ τ τ'} : Judgement (Γ ; τ) τ' → Judgement Γ (τ ⇒ τ')
  | tru {Γ} : Judgement Γ bool
  | fls {Γ} : Judgement Γ bool
  | ite {Γ τ} : Judgement Γ bool → Judgement Γ τ → Judgement Γ τ → Judgement Γ τ

notation:40 Γ "⊢" τ:40 => Judgement Γ τ
notation "true"  => Judgement.tru
notation "false" => Judgement.fls
prefix:90 "$ "   => Judgement.var
notation:50 "λ" t:50 => Judgement.lam t
infix:70 " ⬝ "   => Judgement.app
notation "if" c "then" t₁ "else" t₂ => Judgement.ite c t₁ t₂

def length : Context → Nat
  | Context.empty => 0
  | Context.cons Γ _ => length Γ + 1

def lookup : ∀ {Γ : Context} {n : Nat}, (h : n < length Γ) → Ty
  | Context.cons _ τ,     0, _ => τ
  | Context.cons _ _, _ + 1, h => lookup (Nat.lt_of_succ_lt h)

def count : ∀ {Γ : Context} {n : Nat}, (h : n < length Γ) → Γ ∋ lookup h
  | Context.cons _ τ,     0, _ => Lookup.here
  | Context.cons _ _, _ + 1, h => Lookup.there (count (Nat.lt_of_succ_lt h))
/-
def ex : ∅ ⊢ (bool ⇒ bool) ⇒ bool ⇒ bool
  := λ λ (ref 1 · (ref 1 · ref 0))
-/

def ref {Γ : Context} : (n : Nat) → (h : n + 1 < length Γ) → Γ ∋ lookup h
  | _ , h => count h

def ex : ∅ ⊢ (bool ⇒ bool) ⇒ bool ⇒ bool := by sorry
