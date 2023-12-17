def Loc := String deriving Repr, BEq

inductive Aexp : Type :=
  | num : Nat → Aexp
  | var : Loc → Aexp
  | add : Aexp → Aexp → Aexp
  | sub : Aexp → Aexp → Aexp
  | mul : Aexp → Aexp → Aexp
  deriving Repr

prefix:90 "% " => Aexp.num
prefix:90 "` " => Aexp.var
infixl:65 " +ᵃ " => Aexp.add
infixl:65 " -ᵃ " => Aexp.sub
infixl:70 " *ᵃ " => Aexp.mul

#eval %1 +ᵃ %2

inductive Bexp : Type
  | tru : Bexp
  | fls : Bexp
  | eq  : Aexp → Aexp → Bexp
  | le  : Aexp → Aexp → Bexp
  | not : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  | or  : Bexp → Bexp → Bexp

notation "true" => Bexp.tru
notation "false" => Bexp.fls
infix:50 " =ᵇ " => Bexp.eq
infix:50 " ≤ᵇ " => Bexp.le
prefix:85 "¬ᵇ " => Bexp.not
infixr:35 " ∧ᵇ " => Bexp.and
infixr:30 " ∨ᵇ " => Bexp.or

inductive Com : Type
  | skip  : Com
  | asg   : Loc → Aexp → Com
  | seq   : Com → Com → Com
  | ite   : Bexp → Com → Com → Com
  | while : Bexp → Com → Com

notation "skip" => Com.skip
infix:60 " ≔ " => Com.asg
infix:65 " ; " => Com.seq
notation:60 "if" b "then" c₁:60 "else" c₂:60 => Com.ite b c₁ c₂
notation:60 "while" b "do_" c => Com.while b c

def State := Loc → Nat

inductive AEval : Aexp → State → Nat → Prop
  | num {n σ} : AEval (% n) σ n
  | var {x σ} : AEval (` x) σ (σ x)
  | add {a₀ a₁ n₀ n₁ σ} :
      AEval a₀ σ n₀ →
      AEval a₁ σ n₁ →
      AEval (a₀ +ᵃ a₁) σ (n₀ + n₁)
  | sub {a₀ a₁ n₀ n₁ σ} :
      AEval a₀ σ n₀ →
      AEval a₁ σ n₁ →
      AEval (a₀ -ᵃ a₁) σ (n₀ - n₁)
  | mul {a₀ a₁ n₀ n₁ σ} :
      AEval a₀ σ n₀ →
      AEval a₁ σ n₁ →
      AEval (a₀ *ᵃ a₁) σ (n₀ * n₁)

inductive BEval : Bexp → State → Bool → Prop
  | tru {σ} : BEval true σ Bool.true
  | fls {σ} : BEval false σ Bool.false
  | eq {a₀ a₁ n₀ n₁ σ} :
      AEval a₀ σ n₀ →
      AEval a₁ σ n₁ →
      BEval (a₀ =ᵇ a₁) σ (n₀ == n₁)
  | le {a₀ a₁ n₀ n₁ σ} :
      AEval a₀ σ n₀ →
      AEval a₁ σ n₁ →
      BEval (a₀ ≤ᵇ a₁) σ (n₀ <= n₁)
  | not {b b' σ} :
      BEval b σ b' →
      BEval (¬ᵇ b) σ (!b')
  | and {b₀ b₁ t₀ t₁ σ} :
      BEval b₀ σ t₀ →
      BEval b₁ σ t₁ →
      BEval (b₀ ∧ᵇ b₁) σ (t₀ && t₁)
  | or {b₀ b₁ t₀ t₁ σ} :
      BEval b₀ σ t₀ →
      BEval b₁ σ t₁ →
      BEval (b₀ ∨ᵇ b₁) σ (t₀ || t₁)

def ext (σ : State) (m : Nat) (x : Loc) : State :=
  fun y => if y == x then m else σ y

notation:70 σ "[" m "⧸" x "]" => ext σ m x

inductive CEval : Cexp → State → State → Prop
  | skip {σ} : CEval skip σ σ
  | ass {a σ m x} : AEval a σ m → CEval (x ≔ a) σ (σ [m ⧸ x])
  | seq {c₀ c₁ σ σ' σ''} :
      CEval c₀ σ σ'' →
      CEval c₁ σ'' σ' →
      CEval (c₀ ; c₁) σ σ'
  | itetru {b σ c₀ σ'} :
      BEval b σ Bool.true →
      CEval c₀ σ σ' →
      CEval (if b then c₀ else c₁) σ σ'
  | itefls {b σ c₀ σ'} :
      BEval b σ Bool.true →
      CEval c₁ σ σ' →
      CEval (if b then c₀ else c₁) σ σ'
  | whilefls {b σ c} :
      BEval b σ Bool.false →
      CEval (while b do_ c) σ σ
  | whiletru {b σ c} :
      BEval b σ Bool.false →
      CEval (while b do_ c) σ σ
