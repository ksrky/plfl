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

/- Theorem progress : ∀ t T,
  empty |-- t \in T →
  value t ∨ ∃ t', t --> t'. -/
def progress_measure : Tm → Nat
  | Tm.var _ => 1
  | Tm.app t₁ t₂ => progress_measure t₁ + progress_measure t₂ + 1
  | Tm.lam _ _ t => progress_measure t + 1
  | Tm.tru => 1
  | Tm.fls => 1
  | Tm.ite t₁ t₂ _ => progress_measure t₁ + progress_measure t₂ + 1

theorem progress : ∀ {t τ}, ∅ ⊢ t : τ → Val t ∨ (∃ t', t —⟶ t') := by
  intro t τ ht
  cases ht with
  | var x =>
      apply Or.inl
      contradiction
  | @app _ t₁ t₂ τ₁ _ ht₁ ht₂ =>
      have ht₁' := progress ht₁
      cases ht₁' with
      | inl hv₁ =>
          have ht₂' := progress ht₂
          cases ht₂' with
          | inl hv₂ =>
              apply Or.inr
              cases hv₁ with
              | @lam x _ t =>
                  exists t [x ↦ t₂]
                  apply (Reduction.app_abs hv₂)
              | tru => cases ht₁
              | fls => cases ht₁
          | inr hstep₂ =>
              apply Or.inr
              have ⟨t₂', hstep₂'⟩ := hstep₂
              exists t₁ ⬝ t₂'
              apply (Reduction.app₂ hv₁ hstep₂')
      | inr hstep₁ =>
          apply Or.inr
          have ⟨t₁', hstep₁'⟩ := hstep₁
          exists t₁' ⬝ t₂
          apply (Reduction.app₁ hstep₁')
  | lam ht => apply Or.inl Val.lam
  | tru => apply Or.inl Val.tru
  | fls => apply Or.inl Val.fls
  | @ite _ t₁ t₂ t₃ _ ht₁ ht₂ ht₃ =>
      have ht₁' := progress ht₁
      cases ht₁' with
      | inl hv₁ =>
          cases hv₁ with
          | tru => apply Or.inr (Exists.intro t₂ Reduction.tru)
          | fls => apply Or.inr (Exists.intro t₃ Reduction.fls)
          | lam => cases ht₁
      | inr hstep₁ =>
          apply Or.inr
          have ⟨t₁', hstep₁'⟩ := hstep₁
          apply (Exists.intro (if t₁' then t₂ else t₃) (Reduction.ite hstep₁'))
-- termination_by _ t _ _ => progress_measure t

-- Lemma: Weekening
theorem weakening : ∀ {Γ t τ}, ∅ ⊢ t : τ → Γ ⊢ t : τ := by
  intro Γ t τ ht
  cases ht with
  | var x => contradiction
  | @app Γ' t₁ t₂ τ₁ τ₂ ht₁ ht₂ => sorry
  | lam ht => sorry
  | tru => apply Judgement.tru
  | fls => apply Judgement.fls
  | @ite t₁ t₂ t₃ ht₁ ht₂ ht₃ => sorry

theorem substitution_preseserves
  : ∀ {Γ x t v τ₁ τ₂}, ∅ ⊢ v : τ₁ → Γ; x : τ₁ ⊢ t : τ₂ → Γ ⊢ t [x ↦ v] : τ₂
  := sorry

/-
  Theorem: Preservation

  If Γ ⊢ t : τ and t —⟶ t', then Γ ⊢ t' : τ.
-/
theorem preservation : ∀ t t' τ, ∅ ⊢ t : τ → t —⟶ t' → ∅ ⊢ t' : τ := by
  intro t t' τ ht hstep
  cases ht with
  | var x => cases hstep
  | app ht₁ ht₂ =>
      cases hstep with
      | app_abs hv => sorry
      | app₁ ht₁' => sorry
      | app₂ hv₁ ht₂' => sorry
  | lam ht => cases hstep
  | tru => cases hstep
  | fls => cases hstep
  | ite t₁ t₂ t₃ => sorry
