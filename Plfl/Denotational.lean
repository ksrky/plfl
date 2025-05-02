inductive Ty : Type
  | star : Ty

notation "*" => Ty.star

inductive Context : Type
  | empty : Context
  | cons  : Context → Ty → Context

notation "∅" => Context.empty
infixl:5 " ; " => Context.cons

inductive Lookup : Context → Ty → Type where
  | here : ∀ {Γ A}, Lookup (Γ ; A) A
  | there : ∀ {Γ A B}, Lookup Γ A → Lookup (Γ ; B) A

infix:4 " ∋ " => Lookup

def Rename (Γ Δ : Context) := ∀ {A : Ty}, (Γ ∋ A) → (Δ ∋ A)

def ext {Γ Δ} (ρ : Rename Γ Δ) {A B} : (Γ ; B ∋ A) → (Δ ; B ∋ A)
  | .here => .here
  | .there x => .there (ρ x)

inductive Typing : Context → Ty → Type
  | var : ∀ {Γ}, (Γ ∋ *) → Typing Γ *
  | lam : ∀ {Γ}, Typing (Γ ; *) * → Typing Γ *
  | app : ∀ {Γ}, Typing Γ * → Typing Γ * → Typing Γ *

infix:4 " ⊢ " => Typing
prefix:6 "$ " => Typing.var
prefix:6 "ƛ " => Typing.lam
infixl:7 " ⬝ " => Typing.app

def rename {Γ Δ} (ρ : Rename Γ Δ) {A} : (Γ ⊢ A) → (Δ ⊢ A)
  | $ x => $ (ρ x)
  | ƛ N => ƛ (rename (ext ρ) N)
  | M ⬝ N => (rename ρ M) ⬝ (rename ρ N)

inductive Value : Type
  | bot   : Value
  | maps  : Value → Value → Value
  | union : Value → Value → Value

notation "⊥" => Value.bot
infix:7 " ↦ " => Value.maps
infix:5 " ⊔ " => Value.union

inductive Subs : Value → Value → Type
  | bot   : ∀ {v}, Subs ⊥ v
  | conjL : ∀ {u v w}, Subs v u → Subs w u → Subs (v ⊔ w) u
  | conjR1 : ∀ {u v w}, Subs u v → Subs u (v ⊔ w)
  | conjR2 : ∀ {u v w}, Subs u w → Subs u (v ⊔ w)
  | trans : ∀ {u v w}, Subs u v → Subs v w → Subs u w
  | maps : ∀ {v w v' w'}, Subs v' v → Subs w w' → Subs (v ↦ w) (v' ↦ w')
  | dist : ∀ {v w w'}, Subs (v ↦ w ⊔ w') (v ↦ w)

infix:5 " ⊑ " => Subs

def Subs.refl : ∀ {v}, v ⊑ v
  | ⊥ => .bot
  | _ ↦ _ => .maps .refl .refl
  | _ ⊔ _ => .conjL (.conjR1 .refl) (.conjR2 .refl)

/-
  **Environments**
-/

def Env (Γ : Context) : Type := (Γ ∋ *) → Value

def Env.empty : Env ∅ := fun _ => ⊥

def Env.cons {Γ} (γ : Env Γ) (v : Value) : Env (Γ ; *)
  | .here => v
  | .there x => γ x

infixl:5 " `; " => Env.cons

def Env.init {Γ} (γ : Env (Γ ; *)) : Env Γ := fun x => γ (.there x)

def Env.last {Γ} (γ : Env (Γ ; *)) : Value := γ .here

def Env.init_last {Γ} {γ : Env (Γ ; *)} : γ = (Env.init γ `; Env.last γ) := by
  funext x
  cases x
  case here => rfl
  case there x => rfl

def Env.Subs {Γ} (γ : Env Γ) (δ : Env Γ) := ∀ (x : Γ ∋ *), γ x ⊑ δ x

def Env.bot {Γ} : Env Γ := fun _ => ⊥

def Env.union {Γ} (γ δ : Env Γ) : Env Γ := fun x => γ x ⊔ δ x

infix:5 " `⊑ " => Env.Subs
notation "`⊥" => Env.bot
infix:5 " `⊔ " => Env.union

def Env.refl {Γ} {γ : Env Γ} : γ `⊑ γ := fun x => Subs.refl (v := γ x)

def Env.conjR1 {Γ} {γ δ : Env Γ} : γ `⊑ (γ `⊔ δ) := fun _ => Subs.conjR1 Subs.refl

def Env.conjR2 {Γ} {γ δ : Env Γ} : δ `⊑ (γ `⊔ δ) := fun _ => Subs.conjR2 Subs.refl

def Env.ext {Γ Δ v} {γ : Env Γ} {δ : Env Δ} (ρ : Rename Γ Δ) (lt : γ `⊑ (δ ∘ ρ)) :
   (γ `; v) `⊑ ((δ `; v) ∘ ext ρ) := fun
  | .here => .refl
  | .there n' => lt n'

inductive Denot : ∀ {Γ}, Env Γ → (Γ ⊢ *) → Value → Type
  | var : ∀ {Γ} {γ : Env Γ} {x : Γ ∋ *}, Denot γ ($ x) (γ x)
  | maps_elim : ∀ {Γ} {γ : Env Γ} {L M : Γ ⊢ *} {v w : Value},
      Denot γ L (v ↦ w) → Denot γ M v → Denot γ (L ⬝ M) (w)
  | maps_intro : ∀ {Γ} {γ : Env Γ} {N : Γ ; * ⊢ *} {v w : Value},
      Denot (γ `; v) N w → Denot γ (ƛ N) (v ↦ w)
  | bot_intro : ∀ {Γ} {γ : Env Γ} {M : Γ ⊢ *}, Denot γ M ⊥
  | union_intro : ∀ {Γ} {γ : Env Γ} {M : Γ ⊢ *} {v w : Value},
      Denot γ M v → (w ⊑ v) → Denot γ M w
  | sub : ∀ {Γ} {γ : Env Γ} {M : Γ ⊢ *} {v w : Value},
      Denot γ M v → (w ⊑ v) → Denot γ M w

notation:3 Γ "⊢" γ "↓" v => Denot Γ γ v

def rename_pres {Γ Δ} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ *} {v : Value} (ρ : Rename Γ Δ) (lt : γ `⊑ (δ ∘ ρ)) :
  (γ ⊢ M ↓ v) → (δ ⊢ (rename ρ M) ↓ v)
    | .var (x := x) => .sub .var (lt x)
    | .maps_elim d d₁ => .maps_elim (rename_pres ρ lt d) (rename_pres ρ lt d₁)
    | .maps_intro d => .maps_intro (rename_pres (ext ρ) (Env.ext ρ lt) d)
    | _ => sorry

def Denotation (Γ : Context) : Type 1 := Env Γ → Value → Type

def Denotation.E {Γ} (M : Γ ⊢ *) : Denotation Γ := fun γ v => γ ⊢ M ↓ v

def Denotation.equiv {Γ} (D₁ D₂ : Denotation Γ) : Prop :=
  (γ : Env Γ) → (v : Value) → D₁ γ v = D₂ γ v

def Denotation.F {Γ} (D : Denotation (Γ ; *)) : Denotation Γ := fun
  | γ, v ↦ w => D (γ `; v) w
  | _, ⊥ => Unit
  | γ, (u ⊔ v) => (F D γ u) × (F D γ v)

def sub_F {Γ} {N : Γ ; * ⊢ *} {γ : Env Γ} {v u : Value} (d : Denotation.F (Denotation.E N) γ v) :
  (u ⊑ v) → Denotation.F (Denotation.E N) γ u := fun
    | .bot => ()
    | .maps lt lt' => Denot.sub sorry lt'
    | _ => sorry
