/-
  TyArith: Simple untyped language with boolean and arithmetic operation
  Refering to "Types and Programming Languages", chap 3
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

/- Lemma: Inversion of typing relation -/
theorem inv_true {τ} : Typing true τ -> τ = bool := by intro h; cases h; rfl
theorem inv_false {τ} : Typing false τ -> τ = bool := by intro h; cases h; rfl
theorem inv_ite {t₁ : Tm} {t₂ t₃ τ} : Typing (if t₁ then t₂ else t₃) τ ->
  Typing t₁ bool ∧ Typing t₂ τ ∧ Typing t₃ τ :=
  by intro h; cases h; apply And.intro; assumption; apply And.intro; assumption; assumption
theorem inv_zro {τ} : Typing zero τ -> τ = nat := by intro h; cases h; rfl
theorem inv_suc {t τ} : Typing (succ t) τ -> τ = nat ∧ Typing t nat :=
  by intro h; cases h; apply And.intro rfl; assumption
