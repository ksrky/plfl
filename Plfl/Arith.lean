/-
  Arith: Simple untyped language with boolean and arithmetic operation
  Referring to "Types and Programming Languages", chap 3
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
      | suc h =>
          have hn := val_is_norm hv
          simp [contra_step_norm h hn]

/- Lemma: Induction with normal form -/
theorem norm_suc {t} : is_norm t → is_norm (succ t)
  | hn => by
      simp [is_norm]; intros t' h;
      cases h; apply hn; assumption

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
  | Step.prdsuc hv, Step.prd ht' => by
      have hn := val_is_norm (Val.suc hv)
      apply False.elim (contra_step_norm ht' hn)
  | Step.prd ht, Step.prdsuc hv' => by
      have hn := val_is_norm (Val.suc hv')
      apply False.elim (contra_step_norm ht hn)
  | Step.prd ht, Step.prd ht' => by simp [dec_eval_step ht ht']
  | Step.iszrozro, Step.iszrozro => rfl
  | Step.iszrozro, Step.iszro _ => by contradiction
  | Step.iszrosuc _, Step.iszrosuc _ => rfl
  | Step.iszrosuc hv, Step.iszro ht' => by
      have hn := val_is_norm (Val.suc hv)
      apply False.elim (contra_step_norm ht' hn)
  | Step.iszro ht, Step.iszrosuc ht' => by
      have hn := val_is_norm (Val.suc ht')
      apply False.elim (contra_step_norm ht hn)
  | Step.iszro ht, Step.iszro ht' => by simp [dec_eval_step ht ht']

/- Definition: Reflexive and transitive closure of Step -/
inductive Steps : Tm → Tm → Prop
  | single : t —⟶ t' → Steps t t'
  | refl   : ∀ {t}, Steps t t
  | trans  : Steps t t' → Steps t' t'' → Steps t t''

infix:40 " —⟶* " => Steps

/- Definition: Steps for the simplicity of proofs -/
inductive Steps' : Tm → Tm → Type
  | refl {t}         : Val t → Steps' t t
  | trans {t t' t''} : Step t t' → Steps' t' t'' → Steps' t t''

infix:40 " —⟶*' " => Steps'

theorem uniq_norm' : t —⟶*' u → t —⟶*' u' → u = u'
  | Steps'.refl _, Steps'.refl _ => rfl
  | Steps'.refl hv, @Steps'.trans _ t' _ h₁' h₂' => by
      have hn := val_is_norm hv
      simp [is_norm] at hn
      have hn := hn t'
      contradiction
  | @Steps'.trans _ t' _  h₁ h₂, Steps'.refl hv' => by
      have hn := val_is_norm hv'
      simp [is_norm] at hn
      have hn := hn t'
      contradiction
  | Steps'.trans h₁ h₂, Steps'.trans h₁' h₂' => by
      have h := dec_eval_step h₁ h₁'
      rw [h] at h₂
      exact uniq_norm' h₂ h₂'

/-
TODO: Simulate Steps by Steps'
Defintion of Step (original definition of reflexive and transitive closure) is
not suitable for induction. So we define Steps' for the simplicity of proofs,
and then simulate the proof of Steps by Steps'.
might be helpful: https://plfa.inf.ed.ac.uk/Bisimulation/
-/

theorem SimSteps {t t'} : t —⟶* t' → t —⟶*' t' → Type := sorry
