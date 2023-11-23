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
  | @Typing.app _ t₁ t₂ τ₁ _ ht₁ ht₂ => by
      have ht₁' := progress ht₁
      cases ht₁' with
      | inl hv₁ =>
          have ht₂' := progress ht₂
          cases ht₂' with
          | inl hv₂ =>
              apply Or.inr
              cases hv₁ with
              | @lam x _ t =>
                  exists [x ↦ t₂] t
                  apply (Step.app_abs hv₂)
              | tru | fls => cases ht₁
          | inr hstep₂ =>
              apply Or.inr
              have ⟨t₂', hstep₂'⟩ := hstep₂
              exists t₁ ⬝ t₂'
              apply (Step.app₂ hv₁ hstep₂')
      | inr hstep₁ =>
          apply Or.inr
          have ⟨t₁', hstep₁'⟩ := hstep₁
          exists t₁' ⬝ t₂
          apply (Step.app₁ hstep₁')
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

/- Lemma: Extending -/
theorem extend {Γ Δ} : (∀ {x τ}, Γ ∋ x : τ → Δ ∋ x : τ)
  → (∀ {x y τ τ'}, Γ; y : τ' ∋ x : τ → Δ; y : τ' ∋ x : τ) := by
    intros ρ x y τ τ' hxy
    cases hxy with
    | here => apply Lookup.here
    | there xney h => apply Lookup.there xney (ρ h)

/- Permutation -/
theorem permutation {Γ x y τ₁ τ₂ t τ} :
  Γ; x:τ₁; y:τ₂ ⊢ t : τ → Γ; y:τ₂; x:τ₁ ⊢ t : τ
    | Typing.var h => by
        cases h with
        | here => sorry
        | there xney h => sorry
    | Typing.app ht₁ ht₂ => Typing.app (permutation ht₁) (permutation ht₂)
    | Typing.lam ht => sorry
    | Typing.tru => Typing.tru
    | Typing.fls => Typing.fls
    | Typing.ite ht₁ ht₂ ht₃ =>
        Typing.ite (permutation ht₁) (permutation ht₂) (permutation ht₃)

/- Lemma: Weekening -/
theorem weakening {Γ t τ}: ∅ ⊢ t : τ → Γ ⊢ t : τ
  | Typing.var x => by contradiction
  | Typing.app ht₁ ht₂ => Typing.app (weakening ht₁) (weakening ht₂)
  | Typing.lam ht => by
      apply Typing.lam
      sorry
  | Typing.tru => Typing.tru
  | Typing.fls => Typing.fls
  | Typing.ite ht₁ ht₂ ht₃ =>
      Typing.ite (weakening ht₁) (weakening ht₂) (weakening ht₃)

/- Lemma: Preservation of types under substitution -/
theorem subst_preservation {Γ x t v τ₁ τ₂} :
  ∅ ⊢ v : τ₁ → Γ; x : τ₁ ⊢ t : τ₂ → Γ ⊢ [x ↦ v] t : τ₂ := by
    intros hv ht
    cases ht with
    | @var _ y _ hy => cases hy with
      | here => simp [subst]; apply weakening hv
      | there xney hy' =>
          simp [subst]; split;
          case inl => simp [*] at xney
          case inr => apply Typing.var hy'
    | app ht₁ ht₂ =>
        have ht₁' := subst_preservation hv ht₁
        have ht₂' := subst_preservation hv ht₂
        apply Typing.app ht₁' ht₂'
    | lam ht =>
        sorry
    | tru => apply Typing.tru
    | fls => apply Typing.fls
    | ite ht₁ ht₂ ht₃ => sorry

/-
  Theorem: Preservation of types
  If Γ ⊢ t : τ and t —⟶ t', then Γ ⊢ t' : τ.
-/
theorem preservation {t t' τ} : ∅ ⊢ t : τ → t —⟶ t' → ∅ ⊢ t' : τ
  | Typing.var x, h => by contradiction
  | Typing.app ht₁ ht₂, h => by
      cases h with
      | app_abs hv => sorry
      | app₁ ht₁' => sorry
      | app₂ hv₁ ht₂' => sorry
  | Typing.lam ht, h => by contradiction
  | Typing.tru, h => by contradiction
  | Typing.fls, h => by contradiction
  | Typing.ite ht₁ ht₂ ht₃, h => by
      cases h with
      | iftru | iffls => assumption
      | ite h' =>
          have ht₁' := preservation ht₁ h'
          apply Typing.ite ht₁' ht₂ ht₃
