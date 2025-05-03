import Plfl.AlgorithmW.Unify

namespace AlgorithmW
inductive Ctx : Nat → Nat → Type
  | nil  : Ctx n 0
  | cons : Ty m → Ctx m n → Ctx m (n + 1)

infix:50 " :: " => Ctx.cons

def Ctx.map : (Ty m → Ty m') → Ctx m n → Ctx m' n
  | _, .nil => nil
  | f, .cons x xs => cons (f x) (Ctx.map f xs)

def Ctx.lift (i : Nat) (Γ : Ctx m n) : Ctx (m + i) n :=
  Γ.map (Ty.lift i)

theorem Ctx.lift_zero : Ctx.lift 0 Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons x xs ih =>
      simp [Ctx.lift, Ctx.map]
      apply And.intro
      . exact Ty.lift_zero
      . simp [Ctx.lift] at ih; exact ih

def Ctx.lift' (h : m < m') (Γ : Ctx m n) : Ctx m' n :=
  Γ.map (Ty.lift' h)

def Ctx.subst : AList m m' → Ctx m n → Ctx m' n
  | σ, .nil => .nil
  | σ, .cons t Γ => Ctx.cons (Ty.subst σ t) (Ctx.subst σ Γ)

theorem Ctx.subst_nil : Ctx.subst .nil Γ = Γ := by
  cases Γ with
  | nil => rfl
  | cons t Γ =>
      simp [Ctx.subst]
      apply And.intro
      . apply Ty.subst_nil
      . apply Ctx.subst_nil

def Ctx.lookup : Idx n → Ctx m n → Ty m
  | .zero, .cons t _ => t
  | .succ j, .cons _ Γ => lookup j Γ

infix:40 " ∈ " => Ctx.lookup

def Ctx.extend (Γ : Ctx m n) (t : Ty (m + 1)) : Ctx (m + 1) (n + 1) :=
  Ctx.cons t (Γ.lift 1)

/- def infer (Γ : Ctx m n) (e : Tm n) : Option (Σ m', (AList (m + e.size) m') × Ty m') :=
  match e with
  | .var x => .some ⟨m, .nil,  Γ.lookup x⟩
  | .lam e' =>
      let α := Ty.var (Fin.fromNat m)
      match infer (Γ.extend α) e' with
      | .none => none
      | .some ⟨m', σ, t⟩ =>
          let s := Ty.subst σ (Ty.lift (e'.size) α)
          let σ' := Nat.add_assoc _ _ _ ▸ σ
          .some ⟨m', σ', s ⇒ t⟩
  | .app e₁ e₂ => do
      let ⟨_, σ₁, t₁⟩ ← infer Γ e₁
      let ⟨m₂, σ₂, t₂⟩ ← infer ((Γ.lift e₁.size).subst σ₁) e₂
      let ⟨m₃, σ₃⟩ ← unify (((t₁.lift e₂.size).subst σ₂).lift 1) (t₂.lift 1 ⇒ .var (Fin.fromNat m₂))
      let σ₃₂₁ : AList (m + (e₁.size + (e₂.size + 1))) m₃ :=
        Nat.add_assoc m _ _ ▸ σ₃ <++ (σ₂.lift 1 <++ σ₁.lift (e₂.size + 1))
      .some ⟨m₃, σ₃₂₁, Ty.subst σ₃ (.var (Fin.fromNat m₂))⟩ -/

inductive TypedTm : (Γ : Ctx m n) → Ty m → Type
  | var : (x : Idx n) → TypedTm Γ (x ∈ Γ)
  | lam : (s : Ty m) → {t : Ty m} → TypedTm (s :: Γ) t → TypedTm Γ (s ⇒ t)
  | app : TypedTm Γ (s ⇒ t) → TypedTm Γ s → TypedTm Γ t

mutual
def infer (Γ : Ctx m n) (e : Tm n) : Option (Σ m' σ, Σ t : Ty m', TypedTm ((Γ.lift e.size).subst σ) t) :=
  match e with
  | .var x => .some ⟨m, .nil, Γ.lookup x, Ctx.subst_nil ▸ (Ctx.lift_zero ▸ .var x)⟩
  | .lam e' => do
      let α := Ty.var (Fin.fromNat m)
      let ⟨m', σ, t, w⟩ ← infer (α :: Γ.lift 1) e'
      let s := Ty.subst σ (Ty.lift (e'.size) α)
      let σ' := Nat.add_assoc _ _ _ ▸ σ
      let w' : TypedTm (s :: (Γ.lift e'.lam.size).subst σ') t := by
        have w' : TypedTm (s :: ((Γ.lift 1).lift e'.size).subst σ) t := w
        simp [Tm.size]
        have h1 : Γ.lift (1 + e'.size) = Nat.add_assoc _ _ _ ▸ (Γ.lift 1).lift e'.size := by

          sorry
        have h2 : (Γ.lift (1 + e'.size)).subst σ' = ((Γ.lift 1).lift e'.size).subst σ := by
          sorry
        rw [h2]
        apply w'
      .some ⟨m', σ', s ⇒ t, .lam s w'⟩
  | .app e₁ e₂ => do
      let ⟨m₁, σ₁, t₁, w₁⟩ ← infer Γ e₁
      let ⟨m₂, σ₂, t₂, w₂⟩ ← infer ((Γ.lift e₁.size).subst σ₁) e₂
      let β := Ty.var (Fin.fromNat m₂)
      let ⟨m₃, σ₃, eq⟩ ← unify2 (((t₁.lift e₂.size).subst σ₂).lift 1) (t₂.lift 1 ⇒ β)
      let σ₃₂₁ : AList (m + (e₁.size + (e₂.size + 1))) m₃ :=
        Nat.add_assoc m _ _ ▸ σ₃ <++ (σ₂.lift 1 <++ σ₁.lift (e₂.size + 1))
      let w₁' : TypedTm ((Γ.lift ((e₁.app e₂).size)).subst σ₃₂₁) (Ty.subst σ₃ (t₂.lift 1 ⇒ β)) := by
        sorry
      let w₂' : TypedTm ((Γ.lift ((e₁.app e₂).size)).subst σ₃₂₁) (Ty.subst σ₃ (t₂.lift 1)) :=
        sorry
      let w₁₂ : TypedTm ((Γ.lift ((e₁.app e₂).size)).subst σ₃₂₁) (β.subst σ₃) := by
        simp [Ty.subst] at w₁' w₂'
        exact TypedTm.app w₁' w₂'
      .some ⟨m₃, σ₃₂₁, Ty.subst σ₃ (.var (Fin.fromNat m₂)), w₁₂⟩
end
end AlgorithmW
