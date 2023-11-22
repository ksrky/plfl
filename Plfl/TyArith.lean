/-
  TyArith: Simple typed language with boolean and arithmetic operation
  Referring to "Types and Programming Languages", chap 8
-/

import Plfl.Arith

/- Types -/
inductive Ty : Type :=
  | bool : Ty
  | nat  : Ty
  deriving Repr

notation "bool" => Ty.bool
notation "nat"  => Ty.nat

/- Typing judgements -/
inductive Typing : Tm → Ty → Prop :=
  | tru       : Typing true bool
  | fls       : Typing false bool
  | ite {t₁ t₂ t₃ τ} : Typing t₁ bool -> Typing t₂ τ -> Typing t₃ τ ->
                        Typing (if t₁ then t₂ else t₃) τ
  | zro       : Typing zero nat
  | suc {t}   : Typing t nat -> Typing (succ t) nat
  | prd {t}   : Typing t nat -> Typing (pred t) nat
  | iszro {t} : Typing t nat -> Typing (iszero t) bool

notation:40 "⊢" t ":" τ:50 => Typing t τ

/- Lemma: Inversion of typing relation -/
theorem inv_true {τ} : ⊢ true : τ → τ = bool := by intro h; cases h; rfl
theorem inv_false {τ} : ⊢ false : τ → τ = bool := by intro h; cases h; rfl
theorem inv_ite {t₁ : Tm} {t₂ t₃ τ} : ⊢ if t₁ then t₂ else t₃ : τ →
  ⊢ t₁ : bool ∧ ⊢ t₂ : τ ∧ ⊢ t₃ : τ :=
  by intro h; cases h; apply And.intro; assumption; apply And.intro; assumption; assumption
theorem inv_zero {τ} : ⊢ zero : τ → τ = nat := by intro h; cases h; rfl
theorem inv_succ {t τ} : ⊢ succ t : τ → τ = nat ∧ ⊢ t : nat :=
  by intro h; cases h; apply And.intro rfl; assumption
theorem inv_pred {t τ} : ⊢ pred t : τ → τ = nat ∧ ⊢ t : nat :=
  by intro h; cases h; apply And.intro rfl; assumption
theorem inv_iszero : ⊢ iszero t : τ → τ = bool ∧ ⊢ t : nat :=
  by intro h; cases h; apply And.intro rfl; assumption

/- Lemma: Caononical form -/
theorem canon_bool {t} : Val t → ⊢ t : bool → t = true ∨ t = false
  | Val.tru,   h => Or.inl rfl
  | Val.fls,   h => Or.inr rfl
  | Val.zro,   h => by apply Or.inl; contradiction
  | Val.suc _, h => by apply Or.inl; contradiction

theorem canon_nat {t} : Val t → ⊢ t : nat → ∃ n, t = n
  | Val.tru, _ | Val.fls, _ => by contradiction
  | Val.zro, _ => by exists zero
  | @Val.suc n' _, _ => by exists (succ n')

theorem progress : ∀ {t τ}, ⊢ t : τ → Val t ∨ (∃ t', t —⟶ t') := by
  intro t τ h
  cases h with
  | tru => apply Or.inl Val.tru
  | fls => apply Or.inl Val.fls
  | @ite t₁ t₂ t₃ _ ht₁ ht₂ ht₃ =>
      have ht₁' := progress ht₁
      cases ht₁' with
      | inl hv₁ =>
          apply Or.inr
          cases hv₁ with
          | tru => exists t₂; apply Step.iftru
          | fls => exists t₃; apply Step.iffls
          | zro | suc _ => contradiction
      | inr hstep₁ =>
          apply Or.inr; have ⟨t₁', hstep₁'⟩ := hstep₁
          exists if t₁' then t₂ else t₃; apply Step.ite hstep₁'
  | zro => apply Or.inl Val.zro
  | suc ht =>
      have ht' := progress ht
      cases ht' with
      | inl hv => apply Or.inl (Val.suc hv)
      | inr hstep =>
          apply Or.inr; have ⟨u, hstep'⟩ := hstep
          exists (succ u); apply Step.suc hstep'
  | prd ht   =>
      have ht' := progress ht
      cases ht' with
      | inl hv =>
          apply Or.inr
          cases hv with
          | tru => exists (pred true)
          | fls => exists (pred false)
          | zro => apply Exists.intro zero Step.prdzro
          | suc hv' => apply Exists.intro _ (Step.prdsuc hv')
      | inr hstep =>
          apply Or.inr; have ⟨u, hstep'⟩ := hstep
          exists (pred u); apply Step.prd hstep'
  | iszro ht =>
      have ht' := progress ht
      cases ht' with
      | inl hv =>
          apply Or.inr
          cases hv with
          | tru | fls => contradiction
          | zro => exists true; apply Step.iszrozro
          | suc hv' => exists false; apply Step.iszrosuc hv'
      | inr hstep =>
          apply Or.inr; have ⟨u, hstep'⟩ := hstep
          exists (iszero u); apply Step.iszro hstep'
