import Plfl.AlgorithmW.Syntax
import Plfl.AlgorithmW.Unify

namespace AlgorithmW
inductive Ctx : Nat → Nat → Type
  | nil  : Ctx n 0
  | cons : Ty m → Ctx m n → Ctx m (n + 1)

def Ctx.map : (Ty m → Ty m') → Ctx m n → Ctx m' n
  | _, .nil => nil
  | f, .cons x xs => cons (f x) (Ctx.map f xs)

def Ctx.lift (i : Nat) (Γ : Ctx m n) : Ctx (m + i) n :=
  Γ.map (Ty.lift i)

def Ty.subst : AList m n → Ty m → Ty n
  | .nil, .var x => .var x
  | .snoc σ x t, .var y => Ty.subst σ (replace t x y)
  | σ, .arrow s t => .arrow (Ty.subst σ s) (Ty.subst σ t)

def Ctx.subst : AList m m' → Ctx m n → Ctx m' n
  | σ, .nil => .nil
  | σ, .cons t Γ => Ctx.cons (Ty.subst σ t) (Ctx.subst σ Γ)

def Ctx.lookup : Idx n → Ctx m n → Ty m
  | .zero, .cons t _ => t
  | .succ j, .cons _ Γ => lookup j Γ

def Ctx.extend (Γ : Ctx m n) (t : Ty (m + 1)) : Ctx (m + 1) (n + 1) :=
  Ctx.cons t (Γ.lift 1)

def infer (Γ : Ctx m n) (e : Tm n) : Option (Σ m', (AList (m + e.size) m') × Ty m') :=
  match e with
  | .var x => .some ⟨m, (.nil,  Γ.lookup x)⟩
  | .lam e' =>
    let α := Ty.var (Fin.fromNat m)
    match infer (Γ.extend α) e' with
    | .none => none
    | .some ⟨m', ⟨σ, t⟩⟩ =>
        let s := Ty.subst σ (Ty.lift (e'.size) α)
        let σ' := Nat.add_assoc _ _ _ ▸ σ
        .some ⟨m', ⟨σ', s ⇒ t⟩⟩
  | .app e₁ e₂ => do
      let ⟨_, (σ₁, t₁)⟩ ← infer Γ e₁
      let ⟨m₂, (σ₂, t₂)⟩ ← infer ((Γ.lift e₁.size).subst σ₁) e₂
      let ⟨m₃, σ₃⟩ ← unify (((t₁.lift e₂.size).subst σ₂).lift 1) (t₂.lift 1 ⇒ .var (Fin.fromNat m₂))
      let σ₃₂₁ : AList (m + (e₁.size + (e₂.size + 1))) m₃ :=
        Nat.add_assoc m _ _ ▸ σ₃ <++ (σ₂.lift 1 <++ σ₁.lift (e₂.size + 1))
      .some ⟨m₃, σ₃₂₁, Ty.subst σ₃ (.var (Fin.fromNat m₂))⟩
end AlgorithmW
