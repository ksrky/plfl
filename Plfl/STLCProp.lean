import Plfl.STLC

/-
  Theorem: Canonical Forms

  If Γ ⊢ t : τ and t is a value, then one of the following holds:

  1. t = true
  2. t = false
  3. t = λx:τ'.t'
-/
theorem canonical_forms_bool
  : ∀ t, ∅ ⊢ t : bool → Val t → t = true ∨ t = false
  := by
    intros t ht hv
    cases hv with
    | tru => simp
    | fls => simp
    | lam => cases ht

theorem canonical_forms_lam
  : ∀ t τ₁ τ₂, ∅ ⊢ t : τ₁ ⇒ τ₂ → Val t → ∃ x t', t = λ x : τ₁ ⇒ t'
  := by
    intros t τ₁ τ₂ ht hv
    cases hv with
    | tru => cases ht
    | fls => cases ht
    | @lam x _ t =>
        simp
        cases ht
        apply (Exists.intro x ∘ Exists.intro t)
        simp

/- Theorem: Progress -/
theorem progress {t τ} : ∅ ⊢ t : τ → Val t ∨ (∃ t', t —⟶ t')
  | Typing.var x => by contradiction
  | Typing.app ht₁ ht₂ => by
      have ht₁' := progress ht₁
      cases ht₁' with
      | inl hv₁ =>
          have ht₂' := progress ht₂
          cases ht₂' with
          | inl hv₂ =>
              apply Or.inr
              cases hv₁ with
              | lam =>
                  apply Exists.intro _ (Step.app_abs hv₂)
              | tru | fls => cases ht₁
          | inr hstep₂ =>
              apply Or.inr
              have ⟨t₂', hstep₂'⟩ := hstep₂
              apply Exists.intro _ (Step.app₂ hv₁ hstep₂')
      | inr hstep₁ =>
          apply Or.inr
          have ⟨t₁', hstep₁'⟩ := hstep₁
          apply Exists.intro _ (Step.app₁ hstep₁')
  | Typing.lam ht => by apply Or.inl Val.lam
  | Typing.tru => by apply Or.inl Val.tru
  | Typing.fls => by apply Or.inl Val.fls
  | Typing.ite ht₁ ht₂ ht₃ => by
      have ht₁' := progress ht₁
      cases ht₁' with
      | inl hv₁ =>
          apply Or.inr
          cases hv₁ with
          | tru => apply Exists.intro _ Step.iftru
          | fls => apply Exists.intro _ Step.iffls
          | lam => cases ht₁
      | inr hstep₁ =>
          apply Or.inr
          have ⟨t₁', hstep₁'⟩ := hstep₁
          apply Exists.intro _ (Step.ite hstep₁')

/- Lemma: Extension -/
theorem extend {Γ Δ} : (∀ {x τ}, Γ ∋ x : τ → Δ ∋ x : τ)
  → (∀ {x y τ τ'}, Γ; y : τ' ∋ x : τ → Δ; y : τ' ∋ x : τ) := by
    intros ρ x y τ τ' hxy
    cases hxy with
    | here => apply Lookup.here
    | there xney h => apply Lookup.there xney (ρ h)

/- Lemma: Renaming -/
theorem rename {Γ Δ} : (∀ {x τ}, Γ ∋ x : τ → Δ ∋ x : τ)
  → (∀ {t τ}, Γ ⊢ t : τ → Δ ⊢ t : τ)
  | ρ, _, _, Typing.var hx => Typing.var (ρ hx)
  | ρ, _, _, Typing.app ht₁ ht₂ => Typing.app (rename ρ ht₁) (rename ρ ht₂)
  | ρ, _, _, Typing.lam ht => Typing.lam (rename (extend ρ) ht)
  | _, _, _, Typing.tru => Typing.tru
  | _, _, _, Typing.fls => Typing.fls
  | ρ, _, _, Typing.ite ht₁ ht₂ ht₃ =>
              Typing.ite (rename ρ ht₁) (rename ρ ht₂) (rename ρ ht₃)

/- Lemma: Weakening -/
theorem weaken {Γ t τ} : ∅ ⊢ t : τ → Γ ⊢ t : τ := rename ρ
  where
    ρ : ∀ {x τ}, ∅ ∋ x : τ → Γ ∋ x : τ := by
      intros
      contradiction

theorem drop {Γ x τ₁ τ₂ τ₃} : Γ; x : τ₁; x : τ₂ ⊢ t : τ₃ → Γ; x : τ₂ ⊢ t : τ₃
  := rename ρ
  where
    ρ : ∀ {y τ₃}, Γ; x : τ₁; x : τ₂ ∋ y : τ₃ → Γ; x : τ₂ ∋ y : τ₃ := by
      intros y τ₃ hxy
      cases hxy with
      | here => apply Lookup.here
      | there xney hy =>
          apply Lookup.there xney
          cases hy with
          | here => contradiction
          | there => assumption

theorem swap {Γ x y τ₁ τ₂ τ₃} (ynex : y ≠ x) : Γ; y : τ₂; x : τ₁ ⊢ t : τ₃
  → Γ; x : τ₁; y : τ₂ ⊢ t : τ₃ := rename ρ
  where
    ρ : ∀ {z τ₃}, Γ; y : τ₂; x : τ₁ ∋ z : τ₃ → Γ; x : τ₁; y : τ₂ ∋ z : τ₃ := by
      intros z τ₃ hyx
      cases hyx with
      | here => apply Lookup.there (Ne.symm ynex) Lookup.here
      | there znex hy =>
          cases hy with
          | here => apply Lookup.here
          | there zney =>
              apply Lookup.there zney
              apply Lookup.there znex
              assumption

/- Lemma: Preservation of types under substitution -/
theorem subst_preserve {Γ x t v τ₁ τ₂} :
  ∅ ⊢ v : τ₁ → Γ; x : τ₁ ⊢ t : τ₂ → Γ ⊢ [x ↦ v] t : τ₂ := by
    intros hv ht
    cases ht with
    | @var _ y _ hy => cases hy with
      | here => simp [subst]; apply weaken hv
      | there xney hy' =>
          simp [subst]; split;
          case inl => simp [*] at xney
          case inr => apply Typing.var hy'
    | app ht₁ ht₂ =>
        have ht₁' := subst_preserve hv ht₁
        have ht₂' := subst_preserve hv ht₂
        apply Typing.app ht₁' ht₂'
    | @lam _ y _ _ _ ht' =>
        apply Typing.lam
        split
        case inl xeqy => simp [xeqy] at *; apply drop ht'
        case inr xney => apply subst_preserve hv (swap xney ht')
    | tru => apply Typing.tru
    | fls => apply Typing.fls
    | ite ht₁ ht₂ ht₃ =>
        have ht₁' := subst_preserve hv ht₁
        have ht₂' := subst_preserve hv ht₂
        have ht₃' := subst_preserve hv ht₃
        apply Typing.ite ht₁' ht₂' ht₃'

/-
  Theorem: Preservation of types
  If ∅ ⊢ t : τ and t —⟶ t', then ∅ ⊢ t' : τ.
-/
theorem preserve {t t' τ} : ∅ ⊢ t : τ → t —⟶ t' → ∅ ⊢ t' : τ
  | Typing.var x, h => by contradiction
  | Typing.app ht₁ ht₂, h => by
      cases h with
      | app_abs _ =>
        cases ht₁ with
        | lam ht => apply subst_preserve ht₂ ht
      | app₁ ht₁' => apply Typing.app (preserve ht₁ ht₁') ht₂
      | app₂ hv₁ ht₂' => apply Typing.app ht₁ (preserve ht₂ ht₂')
  | Typing.lam ht, h => by contradiction
  | Typing.tru, h => by contradiction
  | Typing.fls, h => by contradiction
  | Typing.ite ht₁ ht₂ ht₃, h => by
      cases h with
      | iftru | iffls => assumption
      | ite h' =>
          have ht₁' := preserve ht₁ h'
          apply Typing.ite ht₁' ht₂ ht₃
