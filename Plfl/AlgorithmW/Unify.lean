import Plfl.AlgorithmW.Syntax

namespace AlgorithmW
abbrev Subst (m n : Nat) := Idx m → Ty n

def Subst.app (f : Subst m n) : Ty m → Ty n
  | .var x => f x
  | .arrow s t => .arrow (Subst.app f s) (Subst.app f t)

def thin : {n : Nat} → Idx (n + 1) → Idx n → Idx (n + 1)
  | _, .zero, y => .succ y
  | _, .succ _, .zero => .zero
  | _ + 1, .succ x, .succ y => .succ (thin x y)

def thick : {n : Nat} → Idx (n + 1) → Idx (n + 1) → Option (Idx n)
  | _, .zero, .zero => none
  | _, .zero, .succ y => some y
  | _ + 1, .succ _, .zero => some .zero
  | _ + 1, .succ x, .succ y => .succ <$> thick x y

def occurs : Idx (n + 1) → Ty (n + 1) → Option (Ty n)
  | x, .var y => .var <$> thick x y
  | x, .arrow s t => .arrow <$> occurs x s <*> occurs x t

def replace (t : Ty n) (x : Idx (n + 1)) (y : Idx (n + 1)) : Ty n :=
  match thick x y with
  | .none => t
  | .some y' => .var y'

notation "[" x "↦" t "]" => replace t x

def flexFlex : {m : Nat} → Idx m → Idx m → Sigma (AList m)
  | m + 1, x, y =>
      match thick x y with
      | .none => ⟨m + 1, .nil⟩
      | .some y' => ⟨m, .snoc .nil x (.var y')⟩

def flexRigid : {m : Nat} → Idx m → Ty m → Option (Sigma (AList m))
  | m + 1, x, t =>
      match occurs x t with
      | .none => none
      | .some t' => some ⟨m, .snoc .nil x t'⟩

def aunify {m : Nat} : Ty m → Ty m → Sigma (AList m) → Option (Sigma (AList m))
  | .arrow s₁ s₂, .arrow t₁ t₂, acc => aunify s₁ t₁ acc >>= aunify s₂ t₂
  | .var x, .var y, ⟨_, .nil⟩ => some (flexFlex x y)
  | .var x, t, ⟨_, .nil⟩ => flexRigid x t
  | s, .var x, ⟨_, .nil⟩ => flexRigid x s
  | s, t, ⟨n, .snoc σ z r⟩ =>
      match aunify (Subst.app [z ↦ r] s) (Subst.app [z ↦ r] t) ⟨n, σ⟩ with
      | .none => none
      | .some ⟨n', σ'⟩ => some ⟨n', .snoc σ' z r⟩
termination_by s => (m, sizeOf s)

def unify (s : Ty m) (t : Ty m) : Option (Sigma (AList m)) :=
  aunify s t ⟨m, .nil⟩
end AlgorithmW
