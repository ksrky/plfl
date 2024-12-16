import Init.Data.Fin.Basic

/--
  A term is a symbolic expression built from variables and operators.
  The terms in a variable set $X$ over an operator domain $\Omega$,
  the set of which we denote by $Tm_\Omega(X)$.
  In this formalization, we only use `leaf` and `fork` for $\Omega$.
  We define $Tm(X)$ inductively as follows:
-/
inductive Tm : Type → Type
  /-- Variables -/
  | var  : X → Tm X
  /-- Constant operator -/
  | leaf : Tm X
  /-- Binary operator -/
  | fork : Tm X → Tm X → Tm X

/-- A function $f : X \rightarrow Tm(Y)$ is called term substitution from set $X$ to set $Y$.-/
abbrev Subs (X Y : Type) := X → Tm Y

/-- Renaming into substitution -/
def Subs.embed (f : X → Y) : Subs X Y := Tm.var ∘ f

def Subs.id : Subs X X := Tm.var

/-- Monad law of $Tm$. -/
def Subs.app (f : Subs X Y) : Tm X → Tm Y
  | .var x => f x
  | .leaf => .leaf
  | .fork s t => .fork (Subs.app f s) (Subs.app f t)

/-- Composition of term substitutions -/
def Subs.comp (g : Subs Y Z) (f : Subs X Y) : Subs X Z :=
  Subs.app g ∘ f

def Subs.trivial : Type → Type := Subs Unit

/-- Variables are represented as finite set of naturals. -/
inductive Var : Nat → Type
  | zero : {n : Nat} → Var (n + 1)
  | succ : {n : Nat} → Var n → Var (n + 1)

/--
  `Term` is a category of terms whose objects are finite sets and
  whose morphisms are term substitutions.
-/
abbrev Term n := Tm (Var n)

abbrev Subst m n := Subs (Var m) (Var n)

def thin : {n : Nat} → Var (n + 1) → Var n → Var (n + 1)
  | _, .zero, y => .succ y
  | _ + 1, .succ _, .zero => .zero
  | _ + 1, .succ x, .succ y => .succ (thin x y)

/-- Partial inverse to `thin`. -/
def thick : {n : Nat} → Var (n + 1) → Var (n + 1) → Option (Var n)
  | _, .zero, .zero => none
  | _, .zero, .succ y => some y
  | _ + 1, .succ _, .zero => some .zero
  | _ + 1, .succ x, .succ y => .succ <$> thick x y

def occurs : Var (n + 1) → Term (n + 1) → Option (Term n)
  | x, .var y => .var <$> thick x y
  | _, .leaf => .some .leaf
  | x, .fork s t => .fork <$> occurs x s <*> occurs x t

def subs (x : Var (n + 1)) (t : Term n) : Subst (n + 1) n := fun y =>
  match thick x y with
  | .none => t
  | .some y' => .var y'

notation "[" x "↦" t "]" => subs x t

inductive AList : Nat → Nat → Type
  | nil  : AList n n
  | snoc : AList m n → Var (m + 1) →  Term m →AList (m + 1) n

def AList.sub {m n} : AList m n → Subst m n
  | .nil => Subs.id
  | .snoc σ x t => Subs.comp (AList.sub σ) (subs x t)

def AList.append : AList m n → AList l m → AList l n
  | ρ, .nil => ρ
  | ρ, .snoc σ t x => snoc (append ρ σ) t x

def flexFlex : {m : Nat} → Var m → Var m → Sigma (AList m)
  | m + 1, x, y =>
      match thick x y with
      | .none => ⟨m + 1, .nil⟩
      | .some y' => ⟨m, .snoc .nil x (.var y')⟩

def flexRigid : {m : Nat} → Var m → Term m → Option (Sigma (AList m))
  | m + 1, x, t =>
      match occurs x t with
      | .none => none
      | .some t' => some ⟨m, .snoc .nil x t'⟩

def amgu {m : Nat} : Term m → Term m → Sigma (AList m) → Option (Sigma (AList m))
  | .leaf, .leaf, acc => some acc
  | .leaf, .fork _ _, _ => none
  | .fork _ _, .leaf, _ => none
  | .fork s₁ s₂, .fork t₁ t₂, acc => amgu s₁ t₁ acc >>= amgu s₂ t₂
  | .var x, .var y, ⟨_, .nil⟩ => some (flexFlex x y)
  | .var x, t, ⟨_, .nil⟩ => flexRigid x t
  | s, .var x, ⟨_, .nil⟩ => flexRigid x s
  | s, t, ⟨n, .snoc σ z r⟩ =>
      match amgu ([z ↦ r].app s) ([z ↦ r].app t) ⟨n, σ⟩ with
      | .none => none
      | .some ⟨n', σ'⟩ => some ⟨n', .snoc σ' z r⟩
termination_by s => (m, sizeOf s)

def mgu (s : Term m) (t : Term m) : Option (Sigma (AList m)) :=
  amgu s t ⟨m, .nil⟩
