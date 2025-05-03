import Plfl.AlgorithmW.Rename

namespace AlgorithmW
abbrev Subst (m n : Nat) := Idx m → Ty n

def Subst.app (f : Subst m n) : Ty m → Ty n
  | .var x => f x
  | .arrow s t => .arrow (Subst.app f s) (Subst.app f t)

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

def flexFlex2 : {m : Nat} →  (x y : Fin m) → Σ n, Σ σ : AList m n, Decidable ((Ty.var x).subst σ = (Ty.var y).subst σ)
  | m + 1, x, y =>
      match h1 : thick x y with
      | .none =>
          let eq := congrArg (Ty.subst .nil ∘ .var) (thick_none_eq x y h1)
          ⟨m + 1, .nil, isTrue eq⟩
      | .some y' =>
          let eq : (Ty.var x).subst (.snoc .nil x (.var y')) = (Ty.var y).subst (.snoc .nil x (.var y')) :=
            sorry -- congrArg (Ty.subst (.snoc .nil x (.var y')) ∘ .var) sorry
          have h : (Ty.var x).subst (.snoc .nil x (.var y')) = (Ty.var y).subst (.snoc .nil x (.var y')) := by
            simp [Ty.subst, replace, thick_same_none x]
            cases h : thick x y with
            | none => simp [Ty.subst]
            | some v =>
                simp [Ty.subst]
                have h' : some y' = some v := by rw [← h, ← h1]
                cases h'
                rfl
          ⟨m, .snoc .nil x (.var y'), isTrue eq⟩

def flexRigid2 : {m : Nat} → (x : Fin m) → (t : Ty m) → Option (Σ n, Σ σ : AList m n, Decidable ((Ty.var x).subst σ = t.subst σ))
  | m + 1, x, t =>
      match h : occurs x t with
      | .none => none
      | .some t' =>
          have h' : (Ty.var x).subst (AList.nil.snoc x t') = t.subst (AList.nil.snoc x t') := by
            simp [Ty.subst]
            rw [thick_none_eq x x (thick_same_none x)]
            simp [replace, thick_same_none x, Ty.subst_nil]
            cases t with
            | var y =>
                simp [Ty.subst, replace]
                simp [occurs] at h
                have ⟨a, h1, h2⟩ := h
                simp [h1, ← h2, Ty.subst_nil]
            | arrow a b =>
                simp [Ty.subst, replace]
                simp [occurs, Seq.seq, Option.map] at h
                sorry
          some ⟨m, .snoc .nil x t', isTrue h'⟩

def aunify2 : (s : Ty m) → (t : Ty m) → (Σ n, AList m n) → Option (Σ n, Σ σ : AList m n, Decidable (s.subst σ = t.subst σ))
  | .arrow s₁ s₂, .arrow t₁ t₂, acc => do
      -- aunify2 s₂ t₂ acc
      sorry --  >>= aunify2 s₂ t₂
  | _, _, _ => sorry

def unify2 {m : Nat} : (s t : Ty m) → Option (Σ n, Σ σ : AList m n, Decidable (s.subst σ = t.subst σ))
  | _, _ => sorry
end AlgorithmW
