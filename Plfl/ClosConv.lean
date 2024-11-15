import Init.Data.List.Basic

mutual
inductive Val : Type
  | num : Int → Val
  | var : String → Val
  | lam : List String → Exp → Val
  | tuple : List Val → Val

inductive Exp : Type
  | letProj {n : Nat} : String → Fin n → Val → Exp → Exp
  | app : Val → List Val → Exp
  | halt : Val → Exp
end

@[simp]
def Exp.letVal (x : String) (v : Val) (e : Exp) : Exp :=
  .app (.lam [x] e) [v]

@[simp]
def Exp.letVals (xvs : List (String × Val)) : Exp →  Exp :=
  xvs.foldr (fun ⟨x, v⟩ => Exp.letVal x v)

mutual
@[simp]
def Val.subst (x : String) (s : Val) : Val → Val
  | .num n => .num n
  | .var y => if x = y then s else Val.var y
  | .lam ys e => .lam ys (if ys.elem x then e else Exp.subst x s e)
  | .tuple vs => .tuple (List.map (fun ⟨a, _⟩ => Val.subst x s a) vs.attach)

@[simp]
def Exp.subst (x : String) (s : Val) : Exp → Exp
  | .letProj y i v t => .letProj y i (Val.subst x s v) (Exp.subst x s t)
  | .app v us => .app (Val.subst x s v) (List.map (fun ⟨a, _⟩ => Val.subst x s a) us.attach)
  | .halt v => .halt (Val.subst x s v)
end

notation:90 "[" x "↦" s "]" v:80 => Val.subst x s v
notation:90 "[" x "↦" s "]" e:80 => Exp.subst x s e

def Exp.msubst (subs : List (String × Val)) : Exp → Exp
  | e => subs.foldl (λ e ⟨x, s⟩ => [x ↦ s] e) e

inductive Step : Exp → Exp → Prop
  | app_abs {xs e vs} : Step (.app (.lam xs e) vs) (e.msubst (List.zip xs vs))
  | letProj_tuple {x vs e} {i : Fin vs.length} : Step (.letProj x i (Val.tuple vs) e) ([x ↦ vs.get i] e)

infix:40 " ——→ " => Step

inductive Steps : Exp → Exp → Prop
  | halt {e v}      : e = .halt v → Steps e e
  | step {e e' e''} : e ——→ e' → Steps e' e'' → Steps e e''

infix:40 " ——→* " => Steps

theorem steps_composite {e e' e''} : e ——→* e' → e' ——→* e'' → e ——→* e'' := by
  intro h1
  intro h2
  induction h1
  case halt _ => exact h2
  case step e1 e1' e1'' h3 _ h5 =>
    have h6 := h5 h2
    exact Steps.step h3 h6

@[simp]
def halts (e : Exp) (v : Val) : Prop := e ——→* .halt v

infix:50 " ⇓ " => halts

infix:50 " ≈ " => Eq

mutual
def Val.freeVars : Val → List String
  | .num _ => []
  | .var x => [x]
  | .lam xs e => e.freeVars.removeAll xs
  | .tuple vs => vs.attach.foldl (fun acc ⟨v, _⟩ => (acc ++ v.freeVars).eraseDups) []
termination_by v => sizeOf v

def Exp.freeVars : Exp → List String
  | .letProj x _ v e => (v.freeVars ++ e.freeVars.erase x).eraseDups
  | .app v vs => (vs.attach.foldl (fun acc ⟨v, _⟩ => (acc ++ v.freeVars).eraseDups) (v.freeVars))
  | .halt v => v.freeVars
termination_by e => sizeOf e
end

theorem enumFrom_dec {i j : Nat} {x : α} {xs : List α} : ⟨j, x⟩ ∈ xs.enumFrom i → j < i + xs.length := by
  intro h
  cases xs
  case nil => simp at h
  case cons hd tl =>
    simp at h
    cases h with
    | inl h => simp [h]
    | inr h =>
        rw [List.length_cons, Nat.add_left_comm, Nat.add_comm]
        apply enumFrom_dec h
termination_by xs.length

mutual
def Val.clos_conv : Val → Val
  | .num n => .num n
  | .var x => .var x
  | .lam xs e =>
      let c := "c"
      let ys := Val.freeVars (.lam xs e)
      let enum_ys := ys.enumFrom 1
      let exp := enum_ys.attach.foldr (fun ⟨⟨i, y⟩, p⟩ => .letProj y (.mk i (enumFrom_dec p)) (.var c)) e.clos_conv
      .tuple (.lam (c :: xs) exp :: (ys.map Val.var))
  | .tuple vs => .tuple (List.map (fun ⟨a, _⟩ => Val.clos_conv a) vs.attach)
termination_by v => sizeOf v

def Exp.clos_conv : Exp → Exp
  | .letProj x i v e => .letProj x i (Val.clos_conv v) (Exp.clos_conv e)
  | .app v vs =>
      let c := "c"
      let f := "f"
      let prf := Nat.zero_lt_succ (vs.length)
      .letVal c v.clos_conv <|
      .letProj f (.mk 0 prf) (Val.var c) <|
      .app (Val.var c) (List.map (fun ⟨a, _⟩ => Val.clos_conv a) vs.attach)
  | .halt v => .halt (Val.clos_conv v)
termination_by e => sizeOf e
end

notation:80 "⟦" v "⟧" => Val.clos_conv v
notation:80 "⟦" e "⟧" => Exp.clos_conv e

def Val.rel (v v' : Val) : Prop := Val.clos_conv v = v'
def Exp.rel (e e' : Exp) : Prop := Exp.clos_conv e = e'

infix:50 " ≳ " => Val.rel
infix:50 " ≳ " => Exp.rel

theorem clos_conv_satisfies_rel {e : Exp} : e ≳ ⟦ e ⟧ := by
  simp [Exp.rel, Exp.clos_conv]

theorem rel_implies_equal {e e' : Exp} : e ≳ e' → ⟦ e ⟧ ≈ e' := by
  intro h
  simp [Exp.rel] at h
  rw [h]

theorem Val.subst_preserves {v : Val} {v' : Val} : [x ↦ v] v' ≳ [x ↦ ⟦v⟧] ⟦v'⟧ := by
  cases v'
  case num n => simp [Val.clos_conv, Val.rel]
  case var y =>
    simp [Val.clos_conv, Val.rel]
    split
    . trivial
    . simp [Val.clos_conv]
  case lam ys e =>
    simp [Val.clos_conv]
    split
    case isTrue h =>
      simp [Val.rel, Val.clos_conv]
      apply And.intro
      . split
        case isTrue => trivial
        case isFalse h1 =>
          simp at h1
          have h2 := h1.right
          contradiction
      . simp [Function.comp_def, List.attach_map_val]
        intro a
        intro h1
        split
        case isTrue h2 =>
          rw [← h2] at h1
          sorry
        trivial
    case isFalse h =>
      simp [Val.rel, Val.clos_conv]
      apply And.intro
      .
        sorry
      . sorry
  case tuple vs => sorry -- simp [Val.clos_conv, Val.rel]

theorem Exp.subst_preserves {e : Exp} {v : Val} : [x ↦ v] e ≳ [x ↦ ⟦v⟧] ⟦e⟧ := by
  cases e
  case halt v' =>
    simp [Exp.clos_conv, Exp.rel]
    exact Val.subst_preserves
  case letProj n x' i v' e' =>
    simp
    simp [Exp.clos_conv, Exp.rel]
    apply And.intro Val.subst_preserves Exp.subst_preserves
  case app v' us =>
    simp
    simp [Exp.clos_conv, Exp.rel]
    apply And.intro
    . sorry
    . exact Val.subst_preserves

theorem simulation {e₁ e₁' e₂ : Exp} : e₁ ≳ e₁' ∧ e₁ ——→ e₂ → ∃ e₂', e₂ ≳ e₂' ∧ e₁' ——→* e₂' := by
  intro h1
  cases h1.right
  case app_abs xs e vs =>
    have h2 := h1.left
    simp [Exp.rel, Exp.clos_conv, Val.clos_conv] at h2
    apply Exists.intro (⟦e.msubst (xs.zip vs)⟧)
    apply And.intro
    . simp [Exp.rel]
    . rw [← h2]
      apply Steps.step .app_abs
      . simp [Exp.msubst]
        apply Steps.step
        . -- apply Step.letProj_tuple (x := "f") (i := ⟨0, _⟩)
          sorry
        . sorry
        sorry
  case letProj_tuple x vs e i =>
    have h2 := h1.left
    simp [Exp.rel, Exp.clos_conv, Val.clos_conv] at h2
    apply Exists.intro (⟦e.subst x (vs.get i)⟧)
    apply And.intro
    . simp [Exp.rel]
    . rw [← h2]
      apply Steps.step
      . simp [List.attach_map_val]
        have h3 : Fin vs.length = Fin (List.map Val.clos_conv vs).length := by
          rw [List.length_map]
        apply Step.letProj_tuple (x := x) (i := i) (vs := List.map Val.clos_conv vs)
        sorry
      . sorry
      . trivial

theorem simulation_terminate {e e' : Exp} {v: Val} : e ≳ e' ∧ e ⇓ v → ∃ v', e' ⇓ v' ∧ ⟦ v ⟧ ≈ v' := by
  intro h1
  have h2 := h1.left
  have h3 := h1.right
  simp at h3
  cases h3
  case halt =>
    apply Exists.intro (⟦ v ⟧)
    cases h2
    simp [Exp.clos_conv]
    apply Steps.halt (v := ⟦ v ⟧)
    trivial
  case step e1 h4 h5 =>
    have ⟨e1', h6⟩ := simulation (And.intro h2 h4)
    have h7 := h6.left
    rw [← halts] at h5
    have ⟨v', h8⟩ := simulation_terminate (And.intro h7 h5)
    apply Exists.intro v'
    apply And.intro
    have h9 := h8.left
    simp at h9
    exact steps_composite h6.right h9
    exact h8.right
termination_by h => sizeOf h.right

theorem completeness {e v} : e ⇓ v → ∃ v', ⟦ e ⟧ ⇓ v' ∧ ⟦ v ⟧ ≈ v' := by
  intro h1
  have h2 := simulation_terminate (e := e) (v := v) (e' := ⟦ e ⟧)
  have h3 := And.intro (clos_conv_satisfies_rel (e := e)) h1
  exact h2 h3

/-
theorem soundness {e v'} : ⟦ e ⟧ ⇓ v' → ∃ v, e ⇓ v ∧ ⟦ v ⟧ ≈ v' := by
  intro h1
  cases e
  case halt v =>
    apply Exists.intro v
    simp [Exp.clos_conv] at h1
    apply And.intro
    exact Steps.halt rfl
    cases h1
    trivial
    trivial
  case letProj n x i v e =>
    cases v
    case tuple vs =>
      simp [Exp.clos_conv] at h1
      cases h1
      case step e' h2 h3 =>
        simp [Val.clos_conv] at h2
        cases h2
        case letProj_tuple i =>
          simp at h3
          rw [← Exp.subst_preserves] at h3
          have ⟨v, h4⟩ := soundness h3
          apply Exists.intro v
          apply And.intro
          simp
          apply Steps.step (e' := [x ↦ vs.attach[↑i].val] e)
          sorry
          exact h4.left
          exact h4.right
    case lam ys e' =>
      simp [Exp.clos_conv] at h1
      cases h1
      sorry
    case num _ => sorry
    case var _ => sorry
  case app _ _ => sorry -/
