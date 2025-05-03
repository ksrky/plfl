namespace CategoryTheory

class CategoryStruct : Type (max (u + 1) (v + 1))where
  Obj  : Type u
  Hom  : Obj → Obj → Type v
  id   : Hom X X
  comp : Hom Y Z → Hom X Y → Hom X Z

infixr:60 " ⟶ " => CategoryStruct.Hom
infixr:90 " ⊚ " => CategoryStruct.comp

class Category extends CategoryTheory.CategoryStruct.{v, u} where
  id_comp {f : Hom a b} : comp id f = f
  comp_id {f : Hom a b} : comp f id = f
  assoc {f : Hom a b} {g : Hom b c} {h : Hom c d} : (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f)

structure Epi [C : Category] {X Y : C.Obj} (f : X ⟶ Y) where
  commute {g g' : C.Hom Y Z} : g ⊚ f = g' ⊚ f → g = g'

-- def Parallel [C : Category] (X Y : C.Obj) : Type := X ⟶ Y × X ⟶ Y
--
-- infix:60 " ⇉ " => Parallel
--
-- def Parallel.comp [C : Category] {X Y Z : C.Obj} : Y ⇉ Z → X ⟶ Y → X ⇉ Z :=
--   fun (f, g) h => (f ⊚ h, g ⊚ h)

structure IsCoequalizer [C : Category] {E : C.Obj} {X Y} (f g : X ⟶ Y) (q : Y ⟶ E) where
  commute : q ⊚ f = q ⊚ g
  coequalize {h : Y ⟶ Z} : h ⊚ f = h ⊚ g → E ⟶ Z
  universal {h : Y ⟶ Z} {eq : h ⊚ f = h ⊚ g} : h = coequalize eq ⊚ q
  unique {h : Y ⟶ Z} (u : E ⟶ Z) (eq : h ⊚ f = h ⊚ g) : h = u ⊚ q → u = coequalize eq

structure Coequalizer [C : Category] {X Y} (f g : X ⟶ Y) where
  Q : C.Obj
  q : Y ⟶ Q
  isCoequalizer : IsCoequalizer f g q

structure Sum [C : Category] (X Y : C.Obj) where
  P    : C.Obj
  inj₁ : X ⟶ P
  inj₂ : Y ⟶ P
  case (f : X ⟶ Z) (g : Y ⟶ Z) : P ⟶ Z
  commute₁ {f : X ⟶ Z} {g : Y ⟶ Z} : case f g ⊚ inj₁ = f
  commute₂ {f : X ⟶ Z} {g : Y ⟶ Z} : case f g ⊚ inj₂ = g
  universal {f : X ⟶ Z} {g : Y ⟶ Z} {h : P ⟶  Z} : h ⊚ inj₁ = f → h ⊚ inj₂ = g → case f g = h

  universal_eta {h : P ⟶ Z} : case (h ⊚ inj₁) (h ⊚ inj₂) = h := universal rfl rfl

-- notation:30 "[" f "," g "]" => Sum.case _ f g

def coequalize_sum [C : Category] {X X' Y} {f g : X ⟶ Y} {f' g' : X' ⟶ Y} (coeq : Coequalizer f g) (coeq' : Coequalizer (coeq.q ⊚ f') (coeq.q ⊚ g')) {XX' : Sum X X'}
  : IsCoequalizer (XX'.case f f') (XX'.case g g') (coeq'.q ⊚ coeq.q) :=
  { commute := by
      have h := coeq.isCoequalizer.commute
      have hf := XX'.commute₁ (f := f) (g := f')
      have hg := XX'.commute₁ (f := g) (g := g')
      simp (config := { singlePass := true }) [← hf, ← hg, ← C.assoc] at h
      have h := congrArg (C.comp coeq'.q) h
      simp [← C.assoc] at h
      have h' := coeq'.isCoequalizer.commute
      have hf' := XX'.commute₂ (f := f) (g := f')
      have hg' := XX'.commute₂ (f := g) (g := g')
      simp (config := { singlePass := true }) [← hf', ← hg', ← C.assoc] at h'
      simp [← C.assoc] at h'
      have hh := XX'.universal h h'
      simp [XX'.universal_eta (h := (coeq'.q ⊚ coeq.q) ⊚ XX'.case g g')] at hh
      exact Eq.symm hh
  , coequalize := by
      /- intros Z h eq
      have eq' := congrArg (fun f => f ⊚ XX'.inj₁) eq
      simp [C.assoc] at eq'
      rw [XX'.commute₁, XX'.commute₁] at eq'
      have uq := coeq.isCoequalizer.coequalize eq'
      have u := coeq'.isCoequalizer.coequalize (h := uq)
      apply u -/
      sorry
  , universal := by
      sorry
  , unique := by
      sorry
  }

def coequalizer_right_comp [C : Category] {X' X Y : C.Obj} {f g : X ⟶ Y} {h : X' ⟶ X} (coeq : Coequalizer f g)
  : Epi h → IsCoequalizer (f ⊚ h) (g ⊚ h) coeq.q :=
  fun epi =>
    { commute := by
        have ih := coeq.isCoequalizer.commute
        simp [C.assoc] at ih
        exact ih
    , coequalize := by
        intros _ _ eq
        simp [← C.assoc] at eq
        exact coeq.isCoequalizer.coequalize (epi.commute eq)
    , universal := by
        intros _ _ eq
        simp [← C.assoc] at eq
        exact coeq.isCoequalizer.universal (eq := epi.commute eq)
    , unique := by
        intros _ _ u eq
        simp [← C.assoc] at eq
        exact coeq.isCoequalizer.unique u (epi.commute eq)
    }

end CategoryTheory
