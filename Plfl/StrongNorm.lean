/-
  Strong Normalization of Simply Typed Lambda Calculus
-/

import Plfl.STLC

-- Trivial fact
theorem value_halts : ∀ v, Val v → v ⇓ := by
  intros v h
  simp [halts]
  apply Exists.intro v
  apply And.intro Steps.refl h

/-
-- Does not work: It violates the strict positivity requirement for inductive definitions.
inductive SN : Ty → Tm → Prop
  | bool {e} : ∅ ⊢ e ∶ bool → e ⇓ → SN bool t
  | arrow {τ₁ τ₂ e} : ∅ ⊢ e ∶ τ₁ ⇒ τ₂ → e ⇓ → (∀ e', SN τ₁ e' → SN τ₂ (e ⬝ e')) → SN (τ₁ ⇒ τ₂) e
-/

def SN : Ty → Tm → Prop
  | .bool, e => (∀ {Γ}, Γ ⊢ e ∶ bool) ∧ e ⇓
  | .arr τ₁ τ₂, e => (∀ {Γ}, Γ ⊢ e ∶ τ₁ ⇒ τ₂) ∧ e ⇓ ∧ ∀ e', SN τ₁ e' → SN τ₂ (e ⬝ e')

abbrev Substs := List (String × Tm)

-- Multi substitution
def msubst (γ : Substs) (e : Tm) : Tm :=
  match γ with
  | .nil => e
  | (x, s) :: γ' => msubst γ' ([x ↦ s] e)

notation γ "⟦" e "⟧" => msubst γ e

def Substs.dom (γ : Substs) : List String :=
  γ.map Prod.fst

def Context.dom (Γ : Context) : List String :=
  match Γ with
  | Context.empty => []
  | Γ' ; x : _ => x :: Γ'.dom

def substs_satisfies_context (γ : Substs) (Γ : Context) : Prop :=
  γ.dom = Γ.dom ∧ ∀ x τ, Γ ∋ x : τ → SN τ (γ ⟦ %x ⟧)

infix:50 " ⊨ " => substs_satisfies_context

theorem empty_substs_satisfies_empty_context : [] ⊨ ∅ := by
  simp [substs_satisfies_context]
  apply And.intro rfl
  intros x τ h
  cases h

theorem msubst_preserves_typing {Γ e τ γ} : Γ ⊢ e ∶ τ → γ ⊨ Γ → ∅ ⊢ γ ⟦ e ⟧ ∶ τ := by
  intro h h'
  sorry

theorem sn_preserves_by_reduction {e τ} : ∅  ⊢ e ∶ τ → e ——→ e' → (SN τ e ↔ SN τ e') := by
  intros h h'
  apply Iff.intro
  intro hsn
  sorry

theorem sn_membership_with_subst {Γ e τ γ} : γ ⊨ Γ → Γ ⊢ e ∶ τ → SN τ (γ ⟦ e ⟧) := by
  intros h h'
  induction h' generalizing γ
  case tru =>
  sorry

theorem sn_membership {e τ} : ∅ ⊢ e ∶ τ → SN τ e :=
  sn_membership_with_subst empty_substs_satisfies_empty_context

theorem sn_member_is_normalizing {e τ} : SN τ e → e ⇓ := by
  intro h
  induction τ
  . apply h.2
  . apply h.2.1

theorem strong_normalization : ∀ {e τ}, ∅ ⊢ e ∶ τ → e ⇓ :=
  λ h => sn_member_is_normalizing (sn_membership h)
