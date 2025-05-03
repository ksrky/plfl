import Plfl.Unification.Category

namespace FOU

open CategoryTheory

/--
  A term is a symbolic expression built from variables and operators.
  The terms in a variable set $X$ over an operator domain $\Sigma$,
  the set of which we denote by $Tm_\Sigma(X)$.
  In this formalization, we only use `leaf` and `fork` for elements of $\Sigma$.
  Hence, we define $Tm(X)$ inductively as follows:
-/
inductive Tm : Type → Type
  /-- Variables -/
  | var  : X → Tm X
  /-- Operator -/
  | leaf : Tm X
  /-- Binary operator -/
  | fork : Tm X → Tm X → Tm X

def Tm.bind (t : Tm X) (f : X → Tm Y) : Tm Y := match t with
  | .var x => f x
  | .leaf => .leaf
  | .fork s t => .fork (Tm.bind s f) (Tm.bind t f)

instance : Bind Tm where
  bind := Tm.bind

theorem bind_var_identical {t : Tm X} : t.bind .var = t := by
  induction t with
  | var => simp [Tm.bind]
  | leaf => simp [Tm.bind]
  | fork _ _ h1 h2 => simp [Tm.bind]; exact And.intro h1 h2

-- abbrev Eqn (X : Type) := Sub.Parallel Unit X

/-- Variables are represented as finite set of naturals. -/
inductive Fin : Nat → Type
  | zero : {n : Nat} → Fin (n + 1)
  | succ : {n : Nat} → Fin n → Fin (n + 1)
/--
  `Term` is a category of terms whose objects are finite sets and
  whose morphisms are term substitutions.
-/
abbrev Term (n : Nat) := Tm (Fin n)

-- abbrev Equation (n : Nat) := Eqn (Term n)
-- abbrev Equations (n : Nat) := List (Equation n)

/-- Partial inverse to `thin`. -/
def thick : {n : Nat} → Fin (n + 1) → Fin (n + 1) → Option (Fin n)
  | _, .zero, .zero => none
  | _, .zero, .succ y => some y
  | _ + 1, .succ _, .zero => some .zero
  | _ + 1, .succ x, .succ y => .succ <$> thick x y

def Tm.subs (x : Fin (n + 1)) (t : Term n) : Fin (n + 1) → Term n := fun y =>
  match thick x y with
  | .none => t
  | .some y' => .var y'

inductive AList : Nat → Nat → Type
  | nil  : AList n n
  | snoc : AList m n → Fin (m + 1) →  Term m → AList (m + 1) n

def AList.append : AList m n → AList l m → AList l n
  | ρ, .nil => ρ
  | ρ, .snoc σ t x => snoc (append ρ σ) t x

theorem AList.identity₁ {f : AList m n} : append f nil = f := by simp [append]

theorem AList.identity₂ {f : AList m n} : append nil f = f := by
  induction f with
  | nil => simp [append]
  | snoc _ _ _ ih => simp [append]; exact ih

theorem AList.assoc {f : AList k l} {g : AList l m} {h : AList m n} : append (append h g) f = append h (append g f) := by
  induction f with
  | nil => simp [append]
  | snoc _ _ _ ih => simp [append]; exact ih (g := g)

def Subs : Category where
  Obj := Nat
  Hom := AList
  id := AList.nil
  comp := AList.append
  identity₁ := AList.identity₁
  identity₂ := AList.identity₂
  assoc := AList.assoc

def AList.subs {m n} : AList m n → Fin m → Term n
  | .nil => Tm.var
  | .snoc σ x t => fun y => .bind (.subs x t y) σ.subs

def Mgu (σ : AList m n) (s : Term m) (t : Term m) : Prop :=
  s.bind σ.subs = t.bind σ.subs ∧ ∀ {l : Nat}, ∀ σ' : AList m l, ∃ ρ : AList n l, σ' = ρ.append σ

def aunify {m : Nat} : (s : Term m) → (t : Term m) → (acc : Sigma (AList m)) → Option (Σ n, Σ σ : AList m n, Decidable (Mgu σ s t))
  | .leaf, .fork _ _, _ => none
  | .fork _ _, .leaf, _ => none
  | _, _, _ => sorry

def unify (s : Term m) (t : Term m) : Option (Σ n, Σ σ : AList m n, Decidable (Mgu σ s t)) :=
  aunify s t ⟨m, .nil⟩

end FOU

/-
/-- Renaming into substitution -/
def Subs.embed (f : X → Y) : Subs X Y := Tm.var ∘ f

def Subs.trivial : Type → Type := Subs Unit

def thin : {n : Nat} → Var (n + 1) → Var n → Var (n + 1)
  | _, .zero, y => .succ y
  | _ + 1, .succ _, .zero => .zero
  | _ + 1, .succ x, .succ y => .succ (thin x y)

theorem thick_none_eq : {n : Nat} → (x y : Var (n + 1)) → thick x y = none → x = y
  | _, .zero, .zero, _ => rfl
  | _, .zero, .succ y, h => by simp [thick] at h
  | _+ 1, .succ _, .zero, h => by simp [thick] at h
  | _+ 1, .succ x, .succ y, h => by simp [thick] at h; simp; apply thick_none_eq x y h

theorem thick_same_none : {n : Nat} → (x : Var (n + 1)) → thick x x = none
  | _, .zero => by simp [thick]
  | _ + 1, .succ x => by simp [thick]; apply thick_same_none

def occurs : Var (n + 1) → Term (n + 1) → Option (Term n)
  | x, .var y => .var <$> thick x y
  | _, .leaf => .some .leaf
  | x, .fork s t => .fork <$> occurs x s <*> occurs x t

notation "[" x "↦" t "]" => subs x t

def AList.append : AList m n → AList l m → AList l n
  | ρ, .nil => ρ
  | ρ, .snoc σ t x => snoc (append ρ σ) t x

def flexFlex : {m : Nat} → (x : Var m) → (y : Var m) → Σ n, Σ σ : AList m n, Decidable (σ.sub x = σ.sub y)
  | m + 1, x, y =>
      match h : thick x y with
      | .none =>
          let eq := congrArg (AList.sub .nil) (thick_none_eq x y h)
          ⟨m + 1, .nil, isTrue eq⟩
      | .some y' =>
          let eq := by simp [AList.sub, subs, thick_same_none]; rw [h]
          ⟨m, .snoc .nil x (.var y'), isTrue eq⟩

def flexRigid : {m : Nat} → (x : Var m) → (t : Term m) → Option (Σ n, Σ σ : AList m n, Decidable (σ.sub x = σ.sub.app t))
  | m + 1, x, t =>
      match h : occurs x t with
      | .none => none
      | .some t' =>
          have eq : (AList.nil.snoc x t').sub x = (AList.nil.snoc x t').sub.app t := by
            sorry
          some ⟨m, .snoc .nil x t', isTrue eq⟩

def amgu {m : Nat} : (s : Term m) → (t : Term m) → (acc : Sigma (AList m))
  → Option (Σ n, Σ σ : AList m n, Decidable (σ.sub.app s = σ.sub.app t))
  | .leaf, .leaf, ⟨n, σ⟩ => some ⟨n, σ, isTrue (congrArg (Subs.app σ.sub) rfl)⟩
  | .leaf, .fork _ _, _ => none
  | .fork _ _, .leaf, _ => none
  | .fork s₁ s₂, .fork t₁ t₂, acc => do
      let ⟨n₁, σ₁, dec₁⟩ ← amgu s₁ t₁ acc
      let ⟨n₂, σ₂, dec₂⟩ ← amgu s₂ t₂ ⟨n₁, σ₁⟩
      match dec₁, dec₂ with
      | isTrue eq₁, isTrue eq₂ =>
          let eq : σ₂.sub.app (.fork s₁ s₂) = σ₂.sub.app (.fork t₁ t₂) := by
            simp [Subs.app]
            sorry
          some ⟨n₂, σ₂, isTrue eq⟩
      | isFalse _, _ | _, isFalse _ => none
  | .var x, .var y, ⟨_, .nil⟩ => some (flexFlex x y)
  | .var x, t, ⟨_, .nil⟩ => flexRigid x t
  | s, .var x, ⟨_, .nil⟩ => do
      let ⟨n, σ, dec⟩ ← flexRigid x s
      match dec with
      | isTrue eq => some ⟨n, σ, isTrue (Eq.symm eq)⟩
      | isFalse _ => none
  | s, t, ⟨n, .snoc σ z r⟩ =>
      match amgu ([z ↦ r].app s) ([z ↦ r].app t) ⟨n, σ⟩ with
      | .none => none
      | .some ⟨n', σ', eq⟩ => sorry -- some ⟨n', .snoc σ' z r, eq⟩
-/
