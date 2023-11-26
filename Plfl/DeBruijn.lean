inductive Ty : Type
  | bool : Ty
  | arr : Ty → Ty → Ty

notation "bool" => Ty.bool
notation:70 τ₁ "⇒" τ₂ => Ty.arr τ₁ τ₂

inductive Context : Type
  | empty : Context
  | cons : Context → Ty → Context

notation "∅" => Context.empty
notation:40 Γ ";" τ:50 => Context.cons Γ τ

inductive Lookup : Context → Ty → Prop
  | here {Γ τ} : Lookup (Γ ; τ) τ
  | there {Γ τ τ'} : Lookup Γ τ → Lookup (Γ ; τ') τ

notation:40 Γ "∋" τ:40 => Lookup Γ τ

inductive Typing : Context → Ty → Type
  | var {Γ τ} : Γ ∋ τ → Typing Γ τ
  | app {Γ τ τ'} : Typing Γ (τ ⇒ τ') → Typing Γ τ → Typing Γ τ'
  | lam {Γ τ τ'} : Typing (Γ ; τ) τ' → Typing Γ (τ ⇒ τ')
  | tru {Γ} : Typing Γ bool
  | fls {Γ} : Typing Γ bool
  | ite {Γ τ} : Typing Γ bool → Typing Γ τ → Typing Γ τ → Typing Γ τ

notation:40 Γ "⊢" τ:50 => Typing Γ τ
notation "true"  => Typing.tru
notation "false" => Typing.fls
prefix:90 "` "   => Typing.var
notation:60 "λ" t:60 => Typing.lam t
infixl:70 " ⬝ "   => Typing.app
notation:60 "if" c "then" t₁ "else" t₂ => Typing.ite c t₁ t₂

def Context.length : Context → Nat
  | Context.empty => 0
  | Context.cons Γ _ => length Γ + 1

def lookup : ∀ {Γ : Context} {n : Nat}, (h : n < Γ.length) → Ty
  | Context.cons _ τ,     0, _ => τ
  | Context.cons _ _, _ + 1, h => lookup (Nat.lt_of_succ_lt_succ h)

def count : ∀ {Γ : Context} {n : Nat}, (h : n < Γ.length) → Γ ∋ lookup h
  | Context.cons _ _,     0, _ => Lookup.here
  | Context.cons _ _, _ + 1, h => Lookup.there (count (Nat.lt_of_succ_lt_succ h))

/-
def ex : ∅ ⊢ (bool ⇒ bool) ⇒ bool ⇒ bool
  := λ λ (ref 1 · (ref 1 · ref 0))
-/

def lookup_at {Γ : Context} : (n : Nat) → {h : n < Γ.length} → Γ ⊢ lookup h
  | _ , h => ` count h

prefix:90 "# " => lookup_at

/- def ex : ∅ ⊢ (bool ⇒ bool) ⇒ bool ⇒ bool :=
  λ λ (# 1 ⬝ (# 1 ⬝ # 0)) -/

theorem extend {Γ Δ} : (∀ {τ}, Γ ∋ τ → Δ ∋ τ)
  → ∀ {τ τ'}, Γ; τ' ∋ τ → Δ; τ' ∋ τ := by
    intros ρ τ τ' h
    cases h with
    | here => apply Lookup.here
    | there h => apply Lookup.there (ρ h)

theorem rename {Γ Δ} : (∀ {τ}, Γ ∋ τ → Δ ∋ τ) → (∀ {τ}, Γ ⊢ τ → Δ ⊢ τ)
  | ρ, _, Typing.var h => Typing.var (ρ h)
  | ρ, _, Typing.app t₁ t₂ => Typing.app (rename ρ t₁) (rename ρ t₂)
  | ρ, _, Typing.lam t => Typing.lam (rename (extend ρ) t)
  | _, _, Typing.tru => Typing.tru
  | _, _, Typing.fls => Typing.fls
  | ρ, _, Typing.ite c t₁ t₂ => Typing.ite (rename ρ c) (rename ρ t₁) (rename ρ t₂)

