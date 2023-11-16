import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/- Variables -/
def Var : Type := Nat
instance : DecidableEq Var := Nat.decEq

/- Symbols -/
def Symbol : Type := String
instance : DecidableEq Symbol := String.decEq

/- Arrow symbol -/
def arrow : Symbol := "->"

/- Types -/
inductive Ty : Type
  | var : Var → Ty
  | con : Symbol → Ty
  | arr : Ty → Ty → Ty

/- Substitution -/
def subs (x : Var) (t t' : Ty) : Ty :=
  match t' with
  | Ty.var v => if x = v then t else t'
  | Ty.con _ => t'
  | Ty.arr t1 t2 => Ty.arr (subs x t t1) (subs x t t2)

def subs_constraint (x : Var) (t : Ty) : Ty × Ty -> Ty × Ty
  | (t1, t2) => (subs x t t1, subs x t t2)

/- Getting type variables from type -/
def tyvars : Ty → List Var
  | Ty.var x => [x]
  | Ty.con _ => []
  | Ty.arr t1 t2 => tyvars t1 ++ tyvars t2

def tyvars_constraint : Ty × Ty -> List Var
  | (t1, t2) => tyvars t1 ++ tyvars t2

theorem notin_subs {x : Var} {t : Ty} (t' : Ty) (x_notin_t : x ∉ tyvars t) :
  x ∉ tyvars (subs x t t') := by
    induction t' with
    | var y =>
        simp [subs]
        split
        exact x_notin_t
        simp [tyvars]
        trivial
    | con _ => simp [subs, tyvars]
    | arr t1 t2 ih1 ih2 =>
        simp [subs, tyvars]
        intro h
        cases h with
        | inl h => contradiction
        | inr h => contradiction


/- Getting symbols from type -/
def symbols : Ty → List Symbol
  | Ty.var _ => []
  | Ty.con s => [s]
  | Ty.arr t1 t2 => symbols t1 ++ [arrow] ++ symbols t2

def symbols_constraint : Ty × Ty -> List Symbol := fun
  | (t1, t2) => symbols t1 ++ symbols t2

/- Occurs check -/
def occurs (x : Var) : Ty -> Bool
  | Ty.var y => x = y
  | Ty.con _ => false
  | Ty.arr t1 t2 => occurs x t1 || occurs x t2

theorem not_occurs {x : Var} {t : Ty} (h : occurs x t = false) :
  x ∉ tyvars t := by
    induction t with
    | var y =>
        simp [tyvars]
        intro h1
        cases h1 with
        | refl  => simp [occurs] at h
    | con _ => simp [tyvars]
    | arr t1 t2 ih1 ih2 =>
        simp [tyvars]
        intro h1
        cases h1 with
        | inl h1 =>
            simp [occurs] at h
            have _ := ih1 h.left
            contradiction
        | inr h1 =>
            simp [occurs] at h
            have _ := ih2 h.right
            contradiction

theorem notin_subs_applied {x : Var} {t : Ty} {l : List (Ty × Ty)} (x_notin_t : x ∉ tyvars t) :
  x ∉ (l.map (tyvars_constraint ∘ subs_constraint x t)).join := by
    induction l with
    | nil => simp
    | cons hd tl _ =>
      simp
      intro h
      cases h with
      | inl h =>
        simp [tyvars_constraint, subs_constraint] at h
        cases h with
        | inl h => simp [notin_subs hd.1 x_notin_t] at h
        | inr h => simp [notin_subs hd.2 x_notin_t] at h
      | inr h =>
          have ⟨l, h⟩ := h
          have ⟨h, x_in_l⟩ := h
          have ⟨a, ⟨b, h⟩⟩ := h
          have h := h.right
          simp [h.symm] at x_in_l
          simp [tyvars_constraint, subs_constraint] at x_in_l
          cases x_in_l with
          | inl h1 => simp [notin_subs a x_notin_t] at h1
          | inr h1 => simp [notin_subs b x_notin_t] at h1

def unify_measure (l : List (Ty × Ty)) : Nat × Nat :=
  ((l.map tyvars_constraint).join.eraseDup.length, (l.map symbols_constraint).join.eraseDup.length)

mutual
  def unify (l : List (Ty × Ty)) : Option (List (Var × Ty)) :=
    match l with
    | [] => some []
    | (Ty.var x, t) :: l' => if h : occurs x t
      then none
      else Option.map (fun l => (x, t) :: l) (unify (l'.map (subs_constraint x t)))
    | (t, Ty.var x) :: l' => unify ((Ty.var x, t) :: l')
    | (Ty.con s, Ty.con s') :: l' => if s = s' then unify l' else none
    | (Ty.arr t1 t2, Ty.arr t1' t2') :: l' => unify ((t1, t1') :: (t2, t2') :: l')
    | _ => none
end
termination_by
  unify l => unify_measure l
decreasing_by
  simp_wf
  apply Prod.Lex.left
  simp
  sorry
