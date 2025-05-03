import Plfl.AlgorithmW.Syntax

namespace AlgorithmW
def thin : {n : Nat} → Idx (n + 1) → Idx n → Idx (n + 1)
  | _, .zero, y => .succ y
  | _, .succ _, .zero => .zero
  | _ + 1, .succ x, .succ y => .succ (thin x y)

def thick : {n : Nat} → Idx (n + 1) → Idx (n + 1) → Option (Idx n)
  | _, .zero, .zero => none
  | _, .zero, .succ y => some y
  | _ + 1, .succ _, .zero => some .zero
  | _ + 1, .succ x, .succ y => .succ <$> thick x y

theorem thick_none_eq : {n : Nat} → (x y : Idx (n + 1)) →  thick x y = none → x = y
  | _, .zero, .zero, _ => rfl
  | _, .zero, .succ y, h => by simp [thick] at h
  | _+ 1, .succ _, .zero, h => by simp [thick] at h
  | _+ 1, .succ x, .succ y, h => by
      simp [thick] at h
      simp
      apply thick_none_eq x y h

theorem thick_same_none : {n : Nat} → (x : Idx (n + 1)) → thick x x = none
  | _, .zero => by simp [thick]
  | _ + 1, .succ x => by simp [thick]; apply thick_same_none

def occurs : Idx (n + 1) → Ty (n + 1) → Option (Ty n)
  | x, .var y => .var <$> thick x y
  | x, .arrow s t => .arrow <$> occurs x s <*> occurs x t

def replace (x : Idx (n + 1)) (t : Ty n) (y : Idx (n + 1)) : Ty n :=
  match thick x y with
  | .none => t
  | .some y' => .var y'

notation "[" x "↦" t "]" => replace x t

def Ty.subst : AList m n → Ty m → Ty n
  | .nil, .var x => .var x
  | .snoc σ x t, .var y => Ty.subst σ (replace x t y)
  | σ, .arrow s t => .arrow (Ty.subst σ s) (Ty.subst σ t)

theorem Ty.subst_nil  : Ty.subst .nil t = t := by
  induction t with
  | var x => simp [Ty.subst]
  | arrow s t ih₁ ih₂ =>
      simp [Ty.subst] at ih₁ ih₂
      simp [Ty.subst, ih₁, ih₂]

theorem thm : occurs x t = Ty.subst (AList.nil.snoc x t') t := by
  
  sorry
end AlgorithmW
