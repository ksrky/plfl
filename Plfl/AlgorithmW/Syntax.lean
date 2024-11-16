namespace AlgorithmW
inductive Fin : Nat → Type
  | zero : {n : Nat} → Fin (n + 1)
  | succ : {n : Nat} → Fin n → Fin (n + 1)
  deriving DecidableEq

def Fin.toNat : Fin n → Nat
  | .zero => 0
  | .succ i => .succ (Fin.toNat i)

def Fin.fromNat : (n : Nat) → Fin (n + 1)
  | 0 => .zero
  | .succ n => Fin.succ <| fromNat n

def Fin.addNat (i : Fin n) : (j : Nat) → Fin (n + j)
  | 0 => i
  | .succ j => Fin.succ (addNat i j)

abbrev Idx := Fin

abbrev Name := String

structure Bind (α : Type) where
  var : Name
  val : α

inductive Tm : Nat → Type
| var : Idx n → Tm n
| lam : Tm (n + 1) → Tm n
| app : Tm n → Tm n → Tm n

@[simp]
def Tm.size : Tm n → Nat
  | .var _ => 0
  | .lam e => 1 + Tm.size e
  | .app e₁ e₂ => Tm.size e₁ + Tm.size e₂ + 1

abbrev Mvar := Fin

inductive Ty : Nat → Type
| var   : Idx n → Ty n
| arrow : Ty n → Ty n → Ty n

infixr:60 " ⇒ " => Ty.arrow

def Ty.lift (i : Nat) : Ty n → Ty (n + i)
  | .var x => .var (x.addNat i)
  | .arrow s t => .arrow (Ty.lift i s) (Ty.lift i t)

inductive AList : Nat → Nat → Type
  | nil  : AList n n
  | snoc : AList m n → Idx (m + 1) → Ty m → AList (m + 1) n

def AList.append : AList m n → AList l m → AList l n
  | ρ, .nil => ρ
  | ρ, .snoc σ t x => snoc (append ρ σ) t x

infix:80 " <++ " => AList.append

def AList.lift (i : Nat) (l : AList m n) : AList (m + i) (n + i) :=
  match l with
  | .nil => nil
  | AList.snoc l x t =>
    let x' := Nat.add_right_comm _ _ _ ▸ x.addNat i
    Nat.add_right_comm _ _ _ ▸ snoc (l.lift i) x' (t.lift i)
end AlgorithmW
