inductive Tm : Type :=
  | tru : Tm
  | fls : Tm
  | ite : Tm -> Tm -> Tm -> Tm
  | zro : Tm
  | suc : Tm -> Tm
  | prd : Tm -> Tm
  | iszro : Tm -> Tm

notation "true"  => Tm.tru
notation "false" => Tm.fls
notation:60 "if" t₁ "then" t₂ "else" t₃ => Tm.ite t₁ t₂ t₃
notation "zero"   => Tm.zro
prefix:70 "succ " => Tm.suc
prefix:70 "pred " => Tm.prd
prefix:70 "iszero " => Tm.iszro

inductive Val : Tm → Prop :=
  | tru  : Val true
  | fls  : Val false
  | zro : Val zero
  | suc {n} : Val n -> Val (succ n)

inductive Step : Tm → Tm → Prop
  | iftru {t₂ t₃}     : Step (if true then t₂ else t₃) t₂
  | iffls {t₂ t₃}     : Step (if false then t₂ else t₃) t₃
  | ite {t₁ t₁' t₂ t₃} : Step t₁ t₁' → Step (if t₁ then t₂ else t₃) (if t₁' then t₂ else t₃)
  | suc {t t'}        : Step t t' → Step (succ t) (succ t')
  | prdzro            : Step (pred zero) zero
  | prdsuc {t}        : Step (pred (succ t)) t
  | prd {t t'}        : Step t t' → Step (pred t) (pred t')
  | iszrozro          : Step (iszero zero) true
  | iszrosuc {t}      : Step t zero → Step (iszero (succ t)) false
  | iszro {t t'}      : Step t t' → Step (iszero t) (iszero t')

infix:40 " —→ " => Step

theorem sample : ∀ n, n = m ∧ m = 0 → n = 0
  | n , ⟨hn, hm⟩ => by rw [hn, hm]

/- Theorem: Decidability of one-step evaluation -/
theorem dec_one_step : t —→ t' ∧ t —→ t'' → t' = t''
  | ⟨Step.iftru, Step.iftru⟩ => rfl
  | ⟨Step.iftru, Step.ite _⟩ => by contradiction
  | ⟨Step.iffls, Step.iffls⟩ => rfl
  | ⟨Step.iffls, Step.ite _⟩ => by contradiction
  | ⟨Step.ite _, Step.iftru⟩ => by contradiction
  | ⟨Step.ite _, Step.iffls⟩ => by contradiction
  | ⟨Step.ite ht₁, Step.ite ht₁'⟩ => by simp [dec_one_step ⟨ht₁, ht₁'⟩]
  | ⟨Step.suc ht, Step.suc ht'⟩ => by simp [dec_one_step ⟨ht, ht'⟩]
  | ⟨Step.prdzro, Step.prdzro⟩ => rfl
  | ⟨Step.prdzro, Step.prd _⟩ => by contradiction
  | ⟨Step.prdsuc, Step.prdsuc⟩ => rfl
  | ⟨Step.prdsuc, Step.prd ht'⟩ => by sorry
  | ⟨Step.prd ht, Step.prdsuc⟩ => by sorry
  | ⟨Step.prd ht, Step.prd ht'⟩ => by simp [dec_one_step ⟨ht, ht'⟩]
  | ⟨Step.iszrozro, Step.iszrozro⟩ => rfl
  | ⟨Step.iszrozro, Step.iszro _⟩ => by contradiction
  | ⟨Step.iszrosuc _, Step.iszrosuc _⟩ => rfl
  | ⟨Step.iszrosuc ht, Step.iszro ht'⟩ => by sorry
  | ⟨Step.iszro ht, Step.iszrosuc ht'⟩ => by sorry
  | ⟨Step.iszro ht, Step.iszro ht'⟩ => by simp [dec_one_step ⟨ht, ht'⟩]

/- Definition: Normal form -/
def is_norm (t : Tm) : Prop := ∀ t', ¬ t —→ t'

/- Theorem: All values are normal form -/
def val_is_norm : ∀ {t}, Val t → is_norm t
  | true , _ => by simp [is_norm]; intros t h; contradiction
  | false, _ => by simp [is_norm]; intros t h; contradiction
  | zero , _ => by simp [is_norm]; intros t h; contradiction
  | succ n, Val.suc hn => by
      simp [is_norm]; intros t h;
      cases h with
      | @suc _ t' h =>
          have p := val_is_norm hn
          simp [is_norm] at p
          have p' := p t'
          contradiction

def norm_is_val : ∀ {t}, is_norm t → Val t
  | true , hn => Val.tru
  | false, hn => Val.fls
  | Tm.ite t₁ t₂ t₃, hn => by simp [is_norm] at hn; sorry
  | zero , hn => Val.zro
  | succ n, hn => Val.suc (norm_is_val (by simp [is_norm] at *; sorry))
  | pred n, hn => by simp [is_norm] at hn; sorry
  | iszero n, hn => sorry

/- Definition: Reflexive and transitive closure of Step -/
inductive Steps : Tm → Tm → Prop
  | single : t —→ t' → Steps t t'
  | refl   : ∀ t, Steps t t
  | trans  : Steps t t' → Steps t' t'' → Steps t t''

infix:40 " —→* " => Steps

/- Theorem: Uniqueness of normalform -/
theorem uniq_norm : t —→* u → t —→* u' → is_norm u → is_norm u' → u = u' := by
  intros ht ht' hn hn'
  simp [is_norm] at hn hn'
  induction ht generalizing u' with
  | single h => induction ht' generalizing u with
      | single h' => simp [dec_one_step ⟨h, h'⟩]
      | refl => sorry
      | trans h₁ h₂ => sorry
  | refl => sorry
  | trans h₁ h₂ => sorry

/- Theorem: Termination of evaluation -/
theorem terminate_steps : ∀ t, ∃ t', is_norm t' ∧ t —→* t' := by
  intro t
  induction t with
  | tru => sorry
  | fls => exact ⟨false, Steps.refl _⟩
  | ite t₁ t₂ t₃ =>
      induction t₁ with
      | tru => exact ⟨t₂, Steps.single Step.iftru⟩
      | fls => exact ⟨t₃, Steps.single Step.iffls⟩
      | _ => sorry
  | zro => exact ⟨zero, Steps.refl _⟩
  | suc t => sorry
  | prd t => sorry
  | iszro t => sorry
