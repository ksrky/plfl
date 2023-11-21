/-
  Arith: Simple untyped language with boolean and arithmetic operation
  Refering to "Types and Programming Languages", chap 3
-/

/- Terms -/
inductive Tm : Type :=
  | tru : Tm
  | fls : Tm
  | ite : Tm -> Tm -> Tm -> Tm
  | zro : Tm
  | suc : Tm -> Tm
  | prd : Tm -> Tm
  | iszro : Tm -> Tm
  deriving Repr

notation "true"  => Tm.tru
notation "false" => Tm.fls
notation:60 "if" t₁ "then" t₂ "else" t₃ => Tm.ite t₁ t₂ t₃
notation "zero"   => Tm.zro
prefix:70 "succ " => Tm.suc
prefix:70 "pred " => Tm.prd
prefix:70 "iszero " => Tm.iszro

#eval if iszero (pred (succ zero)) then succ zero else zero

/- Values -/
inductive Val : Tm → Prop :=
  | tru  : Val true
  | fls  : Val false
  | zro : Val zero
  | suc {n} : Val n -> Val (succ n)

/- Evaluation step -/
inductive Step : Tm → Tm → Prop
  | iftru {t₂ t₃}      : Step (if true then t₂ else t₃) t₂
  | iffls {t₂ t₃}      : Step (if false then t₂ else t₃) t₃
  | ite {t₁ t₁' t₂ t₃} : Step t₁ t₁' →
                          Step (if t₁ then t₂ else t₃) (if t₁' then t₂ else t₃)
  | suc {t t'}         : Step t t' → Step (succ t) (succ t')
  | prdzro             : Step (pred zero) zero
  | prdsuc {t}         : Val t → Step (pred (succ t)) t
  | prd {t t'}         : Step t t' → Step (pred t) (pred t')
  | iszrozro           : Step (iszero zero) true
  | iszrosuc {t}       : Val t → Step (iszero (succ t)) false
  | iszro {t t'}       : Step t t' → Step (iszero t) (iszero t')

infix:40 " —⟶  " => Step

/- Definition: Normal form -/
def is_norm (t : Tm) : Prop := ∀ t', ¬ t —⟶ t'

/- Lemma: Contradiction of normal form -/
theorem contra_step_norm : t —⟶ t' → is_norm t → False := by
  intro h hn
  simp [is_norm] at hn
  have hn := hn t'
  contradiction

/- Theorem: All values are normal form -/
theorem val_is_norm : ∀ {t}, Val t → is_norm t
  | true , _ => by simp [is_norm]; intros t h; contradiction
  | false, _ => by simp [is_norm]; intros t h; contradiction
  | zero , _ => by simp [is_norm]; intros t h; contradiction
  | succ _, Val.suc hv => by
      simp [is_norm]; intros t h;
      cases h with
      | @suc _ t' h =>
          have hn := val_is_norm hv
          simp [contra_step_norm h hn]

/- Theorem: Decidability of each evaluation step -/
theorem dec_eval_step : t —⟶ t' → t —⟶ t'' → t' = t''
  | Step.iftru, Step.iftru | Step.iffls, Step.iffls => rfl
  | Step.iftru, Step.ite _ | Step.iffls, Step.ite _
  | Step.ite _, Step.iftru | Step.ite _, Step.iffls => by contradiction
  | Step.ite ht₁, Step.ite ht₁' => by simp [dec_eval_step ht₁ ht₁']
  | Step.suc ht, Step.suc ht' => by simp [dec_eval_step ht ht']
  | Step.prdzro, Step.prdzro => rfl
  | Step.prdzro, Step.prd _ => by contradiction
  | Step.prdsuc _, Step.prdsuc _ => rfl
  | Step.prdsuc hv, @Step.prd _ u ht' => by
      have hn := val_is_norm (Val.suc hv)
      apply False.elim (contra_step_norm ht' hn)
  | @Step.prd _ u ht, Step.prdsuc hv' => by
      have hn := val_is_norm (Val.suc hv')
      apply False.elim (contra_step_norm ht hn)
  | Step.prd ht, Step.prd ht' => by simp [dec_eval_step ht ht']
  | Step.iszrozro, Step.iszrozro => rfl
  | Step.iszrozro, Step.iszro _ => by contradiction
  | Step.iszrosuc _, Step.iszrosuc _ => rfl
  | Step.iszrosuc hv, @Step.iszro _ u ht' => by
      have hn := val_is_norm (Val.suc hv)
      apply False.elim (contra_step_norm ht' hn)
  | @Step.iszro _ u ht, Step.iszrosuc ht' => by
      have hn := val_is_norm (Val.suc ht')
      apply False.elim (contra_step_norm ht hn)
  | Step.iszro ht, Step.iszro ht' => by simp [dec_eval_step ht ht']

/- Definition: Reflexive and transitive closure of Step -/
inductive Steps : Tm → Tm → Prop
  | single : t —⟶ t' → Steps t t'
  | refl   : ∀ {t}, Steps t t
  | trans  : Steps t t' → Steps t' t'' → Steps t t''

infix:40 " —⟶* " => Steps

/- Theorem: Uniqueness of normalform -/
theorem uniq_norm : t —⟶* u → t —⟶* u' → is_norm u → is_norm u' → u = u'
  | Steps.single h, Steps.single h', _, _ => by
      simp [dec_eval_step h h']
  | Steps.single h, Steps.refl, _, hn' => by
      apply False.elim (contra_step_norm h hn')
  | Steps.single h, Steps.trans h₁ h₂, hn, hn' => by
      apply dec_eval_step h
      sorry
  | Steps.refl, Steps.single h', hn, _ => by
      apply False.elim (contra_step_norm h' hn)
  | Steps.refl, Steps.refl, _, _ => rfl
  | Steps.refl, Steps.trans h₁' h₂', hn, hn' => sorry
  | Steps.trans h₁ h₂, Steps.single h', hn, hn' => sorry
  | Steps.trans h₁ h₂, Steps.refl, hn, hn' => sorry
  | Steps.trans h₁ h₂, Steps.trans h₁' h₂', hn, hn' => sorry

/- Theorem: Termination of evaluation -/
theorem terminate_steps : ∀ t, ∃ t', is_norm t' ∧ t —⟶* t' := by
  intro t
  induction t with
  | tru => exists true; apply And.intro (val_is_norm Val.tru) Steps.refl
  | fls => exists false; apply And.intro (val_is_norm Val.fls) Steps.refl
  | ite t₁ t₂ t₃ ht₁ ht₂ ht₃ =>
      induction t₁ with
      | tru =>
          have ⟨t₂', ht₂⟩ := ht₂
          exists t₂'
          apply And.intro ht₂.left
          sorry
      | fls => sorry
      | _ => sorry
  | zro =>
      exists zero
      apply And.intro (val_is_norm Val.zro) Steps.refl
  | suc t ht =>
      induction ht with
      | intro t' ht' =>
          exists (succ t')
          apply And.intro
          case left => sorry
          case right => sorry
  | prd t ht =>
      induction ht with
      | intro t' ht' =>
          exists (pred t')
          apply And.intro
          case left => sorry
          case right => sorry
  | iszro t ht =>
      induction ht with
      | intro t' ht' =>
          exists (iszero t')
          apply And.intro
          case left => sorry
          case right =>  sorry
