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
  | ite {t₁ t₁' t₂ t₃} : Step t₁ t₁' → Step (if t₁ then t₂ else t₃) (if t₁' then t₂ else t₃)
  | suc {t t'}         : Step t t' → Step (succ t) (succ t')
  | prdzro             : Step (pred zero) zero
  | prdsuc {t}         : Step (pred (succ t)) t
  | prd {t t'}         : Step t t' → Step (pred t) (pred t')
  | iszrozro           : Step (iszero zero) true
  | iszrosuc {t}       : Step t zero → Step (iszero (succ t)) false
  | iszro {t t'}       : Step t t' → Step (iszero t) (iszero t')

infix:40 " —→ " => Step

/- Theorem: Decidability of an evaluation step -/
theorem dec_eval_step : t —→ t' ∧ t —→ t'' → t' = t''
  | ⟨Step.iftru, Step.iftru⟩ => rfl
  | ⟨Step.iftru, Step.ite _⟩ => by contradiction
  | ⟨Step.iffls, Step.iffls⟩ => rfl
  | ⟨Step.iffls, Step.ite _⟩ => by contradiction
  | ⟨Step.ite _, Step.iftru⟩ => by contradiction
  | ⟨Step.ite _, Step.iffls⟩ => by contradiction
  | ⟨Step.ite ht₁, Step.ite ht₁'⟩ => by simp [dec_eval_step ⟨ht₁, ht₁'⟩]
  | ⟨Step.suc ht, Step.suc ht'⟩ => by simp [dec_eval_step ⟨ht, ht'⟩]
  | ⟨Step.prdzro, Step.prdzro⟩ => rfl
  | ⟨Step.prdzro, Step.prd _⟩ => by contradiction
  | ⟨Step.prdsuc, Step.prdsuc⟩ => rfl
  | ⟨Step.prdsuc, Step.prd ht'⟩ => by
      have ht' := Step.prd ht'
      apply @dec_eval_step (pred (succ t'))
      apply And.intro Step.prdsuc ht'
  | ⟨Step.prd ht, Step.prdsuc⟩ => by
      have ht := Step.prd ht
      apply @dec_eval_step (pred (succ t''))
      apply And.intro ht Step.prdsuc
  | ⟨Step.prd ht, Step.prd ht'⟩ => by simp [dec_eval_step ⟨ht, ht'⟩]
  | ⟨Step.iszrozro, Step.iszrozro⟩ => rfl
  | ⟨Step.iszrozro, Step.iszro _⟩ => by contradiction
  | ⟨Step.iszrosuc _, Step.iszrosuc _⟩ => rfl
  | ⟨Step.iszrosuc ht, Step.iszro ht'⟩ => by
      have ht' := Step.iszro ht'
      apply @dec_eval_step (iszero (succ _))
      apply And.intro (Step.iszrosuc ht) ht'
  | ⟨Step.iszro ht, Step.iszrosuc ht'⟩ => by
      have ht := Step.iszro ht
      apply @dec_eval_step (iszero (succ _))
      apply And.intro ht (Step.iszrosuc ht')
  | ⟨Step.iszro ht, Step.iszro ht'⟩ => by simp [dec_eval_step ⟨ht, ht'⟩]

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

/- Definition: Reflexive and transitive closure of Step -/
inductive Steps : Tm → Tm → Prop
  | single : t —→ t' → Steps t t'
  | refl   : ∀ {t}, Steps t t
  | trans  : Steps t t' → Steps t' t'' → Steps t t''

infix:40 " —→* " => Steps

/- Theorem: Uniqueness of normalform -/
theorem uniq_norm : t —→* u → t —→* u' → is_norm u → is_norm u' → u = u' := by
  intros ht ht' hn hn'
  simp [is_norm] at hn hn'
  induction ht generalizing u' with
  | single h => induction ht' generalizing u with
      | single h' => simp [dec_eval_step ⟨h, h'⟩]
      | refl => sorry
      | trans h₁ h₂ => sorry
  | refl => sorry
  | trans h₁ h₂ => sorry

/- Theorem: Termination of evaluation -/
theorem terminate_steps : ∀ t, ∃ t', is_norm t' ∧ t —→* t' := by
  intro t
  induction t with
  | tru =>
      exists true;
      apply And.intro (val_is_norm Val.tru) Steps.refl
  | fls =>
      exists false;
      apply And.intro (val_is_norm Val.fls) Steps.refl
  | ite t₁ t₂ t₃ ht₁ ht₂ ht₃ =>
      induction t₁ with
      | tru => sorry
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
