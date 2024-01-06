import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Topology.CompactOpen
import LeanCourse.Project.Pointed
open BigOperators Function Set Filter Topology TopologicalSpace CategoryTheory

noncomputable section

/-
Partial references:
- Allen Hatcher, Algebraic Topology. Chapter 0, Operations on Spaces (from page 8, ignoring cell complexes), Example 0.10 (page 12)
- https://www.math.uni-bielefeld.de/~tcutler/pdf/Elementary%20Homotopy%20Theory%20II%20-%20The%20Pointed%20Category.pdf


Done:
- Defined quotienting a space with respect to a subspace
- Defined the cylinder X × I of a space
- Defined the free suspension of a space
- Defined the suspension of a function
- Defined the based cylinder and the pointed suspension of a pointed space
- Defined the wedge product X ⋁ Y of two pointed spaces X and Y
- Some lemmas to deal with wedge products more easily
- Constructed an embedding X ⋁ Y ↪ X × Y and showed it is an embedding
- Defined the smash product X ⋀ Y of two pointed spaces X and Y
- Started some work on spheres [EXTREMELY BROKEN; NOT IN A DECENT STATE YET]

To do:
- See comment at the end

Things that should be polished:
- Divide the content into sections, e.g. unpointed vs pointed. Specifically, also have the pointed spaces be X and X instead of X and Y
- Deal with the implicit/explicit variable mess in the lemmas. Some are fine, some don't really need to be explicit
-/


section unpointed_spaces

variable {X: Type*} [TopologicalSpace X]
variable {X': Type*} [TopologicalSpace X']
variable (f: X → X')


/--The setoid on X associated to the quotient topological space X/A-/
def quotient_setoid (A: Set X) : Setoid (X) where
  r:= fun x ↦ fun y ↦ (x ∈ A ∧ y ∈ A) ∨ x=y
  iseqv := {
    refl:= by tauto
    symm := by tauto
    trans := by{
      intro x y z hxy hyz
      obtain hxy1|hxy2 := hxy
      · obtain hyz1|hyz2 := hyz
        · tauto
        · rw[← hyz2]
          tauto
      · rw[hxy2]
        assumption
    }
  }


@[simp] theorem quotient_setoid_equiv_iff (A: Set X) (x y : X) : (quotient_setoid A).r x y ↔ ((x ∈ A ∧ y ∈ A) ∨ x = y ) := by {
  exact Iff.rfl
}

@[simp] theorem quotient_setoid_equiv (A: Set X) (s: Setoid X) (h : s = quotient_setoid A) (x y : X) : x ≈ y ↔  ((x ∈ A ∧ y ∈ A) ∨ x = y ) := by {
  have: s.r x y ↔ x ≈ y := by exact Iff.rfl
  rw[← this]
  simp[h]
}

/--define the setoid for taking a quotient in which to two disjoint subspaces A and B are collapsed to one point each-/
def double_quotient_setoid {A B: Set X} (h: Disjoint A B) : Setoid (X) where
  r:= fun x ↦ fun y ↦ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) ∨ x = y
  iseqv := {
    refl:= by tauto
    symm := by tauto
    trans := by{
      intro x y z hxy hyz
      obtain hxy1|hxy2|hxy3 := hxy
      · obtain hyz1|hyz2|hyz3 := hyz
        · tauto
        · have : y ∈ A ∩ B := by {
            constructor
            · exact hxy1.2
            · exact hyz2.1
          }
          rw[Set.disjoint_iff_inter_eq_empty] at h
          rw[h] at this
          contradiction
        · rw[← hyz3]
          tauto
      · obtain hyz1|hyz2|hyz3 := hyz
        · have : y ∈ A ∩ B := by {
            constructor
            · exact hyz1.1
            · exact hxy2.2
          }
          rw[Set.disjoint_iff_inter_eq_empty] at h
          rw[h] at this
          contradiction
        · tauto
        · rw[← hyz3]
          tauto
      · rw[hxy3]
        assumption
    }
  }


lemma double_quotient_setoid_equiv_iff {A B: Set X} (h: Disjoint A B) (x y : X) : (double_quotient_setoid h).r x y ↔ ((x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) ∨ x = y) := Iff.rfl

-- we will need to define functions X/∼  → X/∼
def quotient_double_lift {A B : Type*} (S: Setoid A) (T: Setoid B) (f: A → B) (h: ∀ a₁ a₂ : A, S.r a₁ a₂ → T.r (f a₁) (f a₂)) : Quotient S → Quotient T := by {
  apply Quotient.lift (Quotient.mk T ∘ f)
  intro a₁ a₂ h12
  have : S.r a₁ a₂ := h12
  specialize h a₁ a₂ h12
  rw[Function.comp, Function.comp]
  exact Quotient.eq.mpr h
}

lemma quotient_double_lift_commutes {A B : Type*} {S: Setoid A} {T: Setoid B} (f: A → B) {h: ∀ a₁ a₂ : A, S.r a₁ a₂ → T.r (f a₁) (f a₂)} : (Quotient.mk T) ∘ f = quotient_double_lift S T f h ∘ (Quotient.mk S) := by{
  funext x
  simp[quotient_double_lift]
}
--ARE TOO MANY ARGUMENTS IMPLICIT?
--So far, I haven't used this. I should rephrase quotient-to-quotient maps in terms of this if it's worth it


variable (X X')
--define the (non-based) cylinder of X
--I may want to set I to be [ -1, 1] later to make everything cleaner
notation "I" => (Icc 0 1 : Set ℝ)
def Cylinder := X × I

instance : TopologicalSpace (Cylinder X) := instTopologicalSpaceProd


def cyl_setoid : Setoid (Cylinder X) := by{
  let A : Set (Cylinder X) := {x : Cylinder X | x.2=0 }
  let B : Set (Cylinder X) := {x : Cylinder X | x.2=1}
  have h : Disjoint A B := by{
    rw[Set.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      simp at hx
      simp
      have : (0 : I)=1 := by {
        rw[← hx.1, hx.2]
      }
      norm_num at this
    · intros
      contradiction
  }
  exact double_quotient_setoid h
}

-- define the (free) suspension of X
def Suspension  := Quotient (cyl_setoid X)
instance : TopologicalSpace (Suspension  X) := instTopologicalSpaceQuotient

notation (priority:= high) "S" => Suspension

-- define the (free) suspension of a map
def MapTimesI : Cylinder X → Cylinder X' := fun x ↦ (f (x.1), x.2)

variable {X X'} in
def MapSuspension: Suspension  X → Suspension  X' := by {
  let _hsusX := cyl_setoid X
  let _hsusX' := cyl_setoid X'
  apply Quotient.lift ( (Quotient.mk (cyl_setoid X') )∘ (MapTimesI X X' f) )
  intro a b hab
  have hab2 : (cyl_setoid X).r a b := by exact hab
  have fa : MapTimesI X X' f a = (f (a.1), a.2) := by rfl
  have fb : MapTimesI X X' f b = (f (b.1), b.2) := by rfl

  simp [cyl_setoid, double_quotient_setoid_equiv_iff] at hab2
  simp
  have : (cyl_setoid X').r (MapTimesI X X' f a) (MapTimesI X X' f b) := by {
    simp[cyl_setoid, double_quotient_setoid_equiv_iff]
    simp[fa, fb]
    obtain hc1|hc2|hc3 := hab2
    · left
      assumption
    · right; left
      assumption
    · right; right
      rw[hc3]
  }
  exact this
}

--show that if f is continuous, then so is its suspension
variable{X X' f} in
lemma mapsuspension_cont (hf: Continuous f) : Continuous (MapSuspension f) := by{
  apply Continuous.quotient_lift
  apply Continuous.comp
  · exact continuous_coinduced_rng
  · simp[MapTimesI]
    apply Continuous.prod_map hf continuous_id
}


lemma mapsuspension_id : MapSuspension id = @id (Suspension X) := by{
  let _hsusX := cyl_setoid X
  funext x
  simp[MapSuspension, MapTimesI]
  have : Quotient.mk (cyl_setoid X) ∘ (fun x ↦ x) = Quotient.mk (cyl_setoid X) := by{
    funext
    simp
  }
  simp[this]
  obtain ⟨x₁, hx₁⟩ := Quot.exists_rep x
  rw[← hx₁]
  apply Quotient.lift_mk
}

variable (Y': Type*) [TopologicalSpace Y']
variable (g: X' → Y')

variable {X X'} in
lemma mapsuspension_comp : MapSuspension (g ∘ f) = (MapSuspension g) ∘ (MapSuspension f) := by{
  funext x
  simp
  obtain ⟨x₁, hx₁⟩ := Quot.exists_rep x
  rw[←hx₁]
  simp[MapSuspension, MapTimesI]
  rfl
}

-- Show (free) suspension is a functor

def SuspensionFunctor : CategoryTheory.Functor TopCat TopCat where
  obj:= fun X ↦ TopCat.of (S X)
  map:= fun
    | .mk f continuous_f => .mk (MapSuspension f) (mapsuspension_cont continuous_f)
  map_id := by{
    simp
    intro X
    simp [mapsuspension_id]
    rfl
  }
  map_comp := by{
    simp
    intros
    simp[mapsuspension_comp]
    rfl
  }

--[ TODO ] Define iterated suspensions
--[ TODO ] joins in general???


end unpointed_spaces

section pointed_spaces

--define the pointed cylinder of X
variable (X:Type*) [TopologicalSpace X] [Inhabited X]

def pointedcylinder_setoid : Setoid (Cylinder X) := by{
  exact quotient_setoid ({p : Cylinder X | p.1 = default})
}

/--Pointed cylinder of a pointed topological space-/
def PointedCylinder := Quotient (pointedcylinder_setoid X)

--show PointedCylinder is a pointed topological space with basepoint * × I
instance : TopologicalSpace (PointedCylinder X) := instTopologicalSpaceQuotient

instance : Inhabited (PointedCylinder X) where
  default := Quotient.mk (pointedcylinder_setoid X) ((default : X), 0)


--define the pointed suspension of X
def basedsuspension_setoid : Setoid (Cylinder X) := by{
  let A := {p : Cylinder X | p.1 = default}
  let B := {p : Cylinder X | p.2 = 0}
  let C := {p : Cylinder X | p.2 = 1}
  exact quotient_setoid (A ∪ B ∪ C)
}

def BasedSuspension := Quotient (basedsuspension_setoid X)
instance : TopologicalSpace (BasedSuspension X) := instTopologicalSpaceQuotient

instance : Inhabited (BasedSuspension X) where
  default:= Quotient.mk (basedsuspension_setoid X) ((default:X), 0)

notation (priority:= high) "Σ₀" => BasedSuspension

--[ TODO ] Define the based suspension functor and show it is a functor
--[ TODO ] Define iterated suspensions

-- define the wedge product X ⋁ Y of two pointed spaces X and Y
variable (Y:Type*) [TopologicalSpace Y] [Inhabited Y]
instance: TopologicalSpace (X ⊕ Y) := by infer_instance

def wedge_setoid : Setoid (X ⊕ Y) := by{
  let A: Set (X ⊕ Y) := { p : X ⊕ Y | p = Sum.inl (default:X) ∨ p = Sum.inr (default:Y)}
  exact quotient_setoid A
}


def Wedge := Quotient (wedge_setoid X Y)
instance: TopologicalSpace (Wedge X Y) := by exact instTopologicalSpaceQuotient
instance: Inhabited (Wedge X Y) where
  default:= Quotient.mk (wedge_setoid X Y) (Sum.inl (default:X))

infix:50 " ⋁ " => Wedge

-- easy lemma for later
lemma wedge_defaults_equiv: Quotient.mk (wedge_setoid X Y) (Sum.inl default) = Quotient.mk (wedge_setoid X Y) (Sum.inr default) := by{
  let _hwedge := wedge_setoid X Y
  refine Quotient.eq.mpr ?_
  have : (wedge_setoid X Y).r (Sum.inl default) (Sum.inr default) := by simp
  exact this
}

--[ TODO ] define arbitrarily large wedge products


-- Show that there is a homeomorphism X ⋁ Y ≃ Y ⋁ X

lemma continuous_sum_swap: Continuous (@Sum.swap X Y) := by{ --this looks like it should be a lemma from the library but I couldn't find it
  refine continuous_sum_dom.mpr ?_
  constructor
  · have : (@Sum.swap X Y) ∘ (@Sum.inl X Y) = @Sum.inr Y X := rfl
    rw[this]
    exact continuous_inr
  · have : (@Sum.swap X Y) ∘ (@Sum.inr X Y) = @Sum.inl Y X := rfl
    rw[this]
    exact continuous_inl
}


def sum_commutes: X ⊕ Y ≃ₜ Y ⊕ X where
  toFun:= @Sum.swap X Y
  continuous_toFun := continuous_sum_swap X Y
  invFun:= @Sum.swap Y X
  continuous_invFun := continuous_sum_swap Y X
  left_inv:= by simp
  right_inv:= by simp


--TO REWRITE using subsequent standard way to map from wedge
def wedge_swap: X ⋁ Y → Y ⋁ X := by{
  let _hwedge := wedge_setoid X Y
  let _hwedge' := wedge_setoid Y X
  apply Quotient.lift ( (Quotient.mk (wedge_setoid Y X)  ) ∘ (@Sum.swap X Y))
  intro a b hab
  -- I still have to take this extra step I don't want to take
  have hab2: Setoid.r a b := by exact hab
  simp [quotient_setoid_equiv_iff] at hab2
  obtain hc1|hc2 := hab2
  · induction a
    case inl xa => {
      induction b
      case inl xb => {
        simp at hc1
        simp[hc1]
      }
      case inr yb => {
        simp at hc1
        simp[hc1]
        have : Setoid.r (@Sum.inr Y X default) (Sum.inl default) := by simp
        exact this
      }
    }
    case inr ya => {
      induction b
      case inl xb => {
        simp at hc1
        simp [hc1]
        have : Setoid.r (@Sum.inl Y X default) (Sum.inr default) := by simp[quotient_setoid_equiv_iff]
        exact this
      }
      case inr yb => {
        simp at hc1
        simp[hc1]
      }
    }
  · rw[hc2]
}

lemma continuous_wedge_swap : Continuous (wedge_swap X Y) := by{
  apply Continuous.quotient_lift
  apply Continuous.comp
  · exact continuous_coinduced_rng
  · exact continuous_sum_swap X Y
}


lemma wedge_swap_inl (y:X) : (wedge_swap X Y) (Quotient.mk _ (Sum.inl y) ) = Quotient.mk _ (@Sum.inr Y X y) := by{
  simp[wedge_swap]
  apply Quot.lift_mk
  exact fun a₁ a₂ a ↦ a
}


lemma wedge_swap_inr (z:Y) : (wedge_swap X Y) (Quotient.mk _ (Sum.inr z) ) = Quotient.mk _ (@Sum.inl Y X z) := by{
  simp[wedge_swap]
  apply Quot.lift_mk
  exact fun a₁ a₂ a ↦ a
}


def wedge_commutes: X ⋁ Y ≃ₜ Y ⋁ X where
  toFun:= wedge_swap X Y
  continuous_toFun := continuous_wedge_swap X Y
  invFun:= wedge_swap Y X
  continuous_invFun := continuous_wedge_swap Y X
  left_inv:= by {
    let _hwedge := wedge_setoid X Y
    let _hwedge' := wedge_setoid Y X
    simp[LeftInverse]
    intro p
    obtain ⟨p', hp'⟩ := Quotient.exists_rep p
    rw[← hp']
    induction p'
    case inl y => {
      rw[wedge_swap_inl X Y y]
      rw[wedge_swap_inr]
    }
    case inr z => {
      rw[wedge_swap_inr, wedge_swap_inl]
    }
  }
  right_inv:= by {
    simp[Function.RightInverse, LeftInverse]
    intro p
    obtain ⟨p', hp'⟩ := Quotient.exists_rep p
    rw[← hp']
    induction p'
    case inl y => {
      rw[wedge_swap_inl, wedge_swap_inr]
    }
    case inr z => {
      rw[wedge_swap_inr, wedge_swap_inl]
    }
  }



--"The wedge product is the coproduct in pointed topological spaces"
variable {X Y} in
def wedge_induced {Z: Type*} [TopologicalSpace Z] [Inhabited Z] {f: X → Z} {g: Y → Z} (hf: f default = default) (hg: g default = default) : X ⋁ Y → Z := by {
  let _ := wedge_setoid X Y
  let sum_map : X ⊕ Y → Z := fun
    | .inl x => f x
    | .inr y => g y
  apply Quotient.lift sum_map
  intro a b hab
  have : (wedge_setoid X Y).r a b := hab
  simp[wedge_setoid, quotient_setoid_equiv_iff] at this
  induction a
  case inl xa => {
    induction b
    case inl xb => {
      simp at this
      obtain hc1|hc2:= this
      · simp[hc1]
      · simp[hc2]
    }
    case inr yb => {
      simp at this
      simp[this, hf, hg]
    }
  }
  case inr ya => {
    induction b
    case inl xb => {
      simp at this
      simp[this, hf, hg]
    }
    case inr yb => {
      simp at this
      obtain hc1|hc2:= this
      · simp[hc1]
      · simp[hc2]
    }
  }
}


variable {X Y} in
lemma continuous_wedge_induced {Z: Type*} [TopologicalSpace Z] [Inhabited Z] {f: X → Z} {g: Y → Z} {hf: f default = default} {hg: g default = default} (hf2: Continuous f) (hg2: Continuous g) : Continuous (wedge_induced hf hg) := by{
  apply Continuous.quotient_lift
  simp [continuous_sum_dom]
  constructor
  · exact hf2
  · exact hg2
}

variable {X Y} in
lemma pointed_wedge_induced {Z: Type*} [TopologicalSpace Z] [Inhabited Z] {f: X → Z} {g: Y → Z} {hf: f default = default} {hg: g default = default} : wedge_induced hf hg default = default := by{
  let _ := wedge_setoid X Y
  have : (default : X ⋁ Y) = Quotient.mk (wedge_setoid X Y) (Sum.inl (default:X)) := rfl
  rw[this]
  simp[wedge_induced, Quotient.lift_mk]
  exact hf
}


def wedge_inl : X → X ⋁ Y := (Quotient.mk (wedge_setoid X Y)) ∘ Sum.inl
def wedge_inr : Y → X ⋁ Y := (Quotient.mk (wedge_setoid X Y)) ∘ Sum.inr

lemma continuous_wedge_inl : Continuous (wedge_inl X Y) := by{
  apply Continuous.comp
  · exact continuous_coinduced_rng
  · exact continuous_inl
}

lemma continuous_wedge_inr : Continuous (wedge_inr X Y) := by{
  apply Continuous.comp
  · exact continuous_coinduced_rng
  · exact continuous_inr
}

lemma pointed_wedge_inl: wedge_inl X Y default = default := by{
  simp[wedge_inl]
  rfl
}

lemma pointed_wedge_inr: wedge_inr X Y default = default := by{
  simp[wedge_inr]
  rw[← wedge_defaults_equiv]
  rfl
}


--Show that X ≃ₜ⋆ Z implies X ⋁ Y ≃ₜ⋆  Z ⋁ Y
def homeo_wedge_swap {Z: Type*} [TopologicalSpace Z] [Inhabited Z] (f: X ≃ₜ⋆ Z) : X ⋁ Y ≃ₜ⋆ Z ⋁ Y  where
  toFun:= by{
    apply @wedge_induced X _ Y _ (Z ⋁ Y) _ _ ((wedge_inl Z Y) ∘ f.toFun) (wedge_inr Z Y) ?_ ?_
    · rw[Function.comp, f.pointed_toFun]
      rfl
    · simp[wedge_inr]
      rw[← wedge_defaults_equiv]
      rfl
  }
  continuous_toFun := by{
    dsimp
    apply continuous_wedge_induced
    · apply Continuous.comp
      · exact continuous_wedge_inl Z Y
      · exact f.continuous_toFun
    · exact continuous_wedge_inr Z Y
  }

  invFun:= by{
    apply @wedge_induced Z _ Y _ (X ⋁ Y) _ _ ((wedge_inl X Y) ∘ f.invFun) (wedge_inr X Y) ?_ ?_
    · rw[Function.comp, f.pointed_invFun]
      rfl
    · simp[wedge_inr]
      rw[← wedge_defaults_equiv]
      rfl
  }

  continuous_invFun := by {
    dsimp
    apply continuous_wedge_induced
    · apply Continuous.comp
      · exact continuous_wedge_inl X Y
      · exact f.continuous_invFun
    · exact continuous_wedge_inr X Y
  }

  left_inv:= by {
    let _ := wedge_setoid X Y
    let _ := wedge_setoid Z Y
    simp[LeftInverse]
    intro x
    simp[wedge_induced]
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw[← hx']
    induction x'
    case inl y => {
      simp[wedge_inl, Quotient.lift_mk]
    }
    case inr z => {
      simp[wedge_inr, Quotient.lift_mk]
    }
  }
  right_inv:= by {
    dsimp
    let _ := wedge_setoid X Y
    let _ := wedge_setoid Z Y
    simp[Function.RightInverse, LeftInverse]
    intro x
    simp[wedge_induced]
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw[← hx']
    induction x'
    case inl y => {
      simp[wedge_inl, Quotient.lift_mk]
    }
    case inr z => {
      simp[wedge_inr, Quotient.lift_mk]
    }
  }

  pointed_toFun := by{
    let _ := wedge_setoid X Y
    dsimp
    simp[wedge_induced]
    have : (default: X ⋁ Y) = Quotient.mk (wedge_setoid X Y) (Sum.inl (default:X)) := rfl
    rw[this]
    simp[Quotient.lift_mk]
    have hf:= f.pointed_toFun
    dsimp at hf
    rw[hf]
    exact pointed_wedge_inl Z Y
  }



-- Show that there is an embedding of the wedge product inside the topological product X × Y
-- THIS CAN PROBABLY BE REWRITTEN USING THE COPRODUCT PROPERTY ABOVE
def coprod_prod_map : X ⊕ Y → X × Y := fun
  | .inl x => (x, (default:Y))
  | .inr y => ((default:X), y)

lemma coprod_prod_map_cont: Continuous (coprod_prod_map X Y) := by {
  simp[coprod_prod_map, continuous_sum_dom]
  constructor
  · constructor
    · apply continuous_id
    · apply continuous_const
  · constructor
    · apply continuous_const
    · apply continuous_id
}


def wedge_embedding : X ⋁ Y → X × Y := by {
  apply Quotient.lift (coprod_prod_map X Y)
  intro a b hab
  have hab2 : (wedge_setoid X Y).r a b := hab

  induction a
  case inl xa => {
    induction b
    case inl xb => {
      simp[coprod_prod_map]
      simp[quotient_setoid_equiv_iff] at hab2
      obtain hc1|hc2 := hab2
      · calc
        xa = default := hc1.1
        _ = xb := by{symm; exact hc1.2}
      · assumption
    }
    case inr yb => {
      simp[coprod_prod_map]
      simp[quotient_setoid_equiv_iff] at hab2
      tauto
    }
  }
  case inr ya => {
    induction b
    case inl xb => {
      simp[coprod_prod_map]
      simp[quotient_setoid_equiv_iff] at hab2
      tauto
    }
    case inr yb => {
      simp[coprod_prod_map]
      simp[quotient_setoid_equiv_iff] at hab2
      obtain hc1|hc2 := hab2
      · calc
        ya = default := hc1.1
        _ = yb := by{symm; exact hc1.2}
      · assumption
    }
  }
}

-- prove this is an embedding
lemma wedge_embedding_cont: Continuous (wedge_embedding X Y) := by{
  apply Continuous.quotient_lift
  exact coprod_prod_map_cont X Y
}


lemma wedge_embedding_inducing: Inducing (wedge_embedding X Y) := by{
  let _ := wedge_setoid X Y
  rw[inducing_iff]
  refine TopologicalSpace.ext_iff.mpr ?left.a
  intro A
  constructor
  · intro hA
    apply isOpen_induced_iff.mpr
    let A' := (Quotient.mk (wedge_setoid X Y))⁻¹' A
    let B := Sum.inl⁻¹' A'
    let C := Sum.inr⁻¹' A'
    have hApre: IsOpen B ∧ IsOpen C := hA
    by_cases hcase: default ∈ A
    · use B ×ˢ C
      constructor
      · exact IsOpen.prod hApre.1 hApre.2
      · ext p
        constructor
        · intro hp
          rw[Set.mem_preimage] at hp
          obtain ⟨p', hp'⟩ := Quotient.exists_rep p
          rw[← hp'] at hp
          induction p'
          case inl x => {
            simp[wedge_embedding, coprod_prod_map] at hp
            rw[← hp']
            exact hp.1
          }
          case inr y => {
            simp[wedge_embedding, coprod_prod_map] at hp
            rw[← hp']
            exact hp.2
          }
        · intro hp
          rw[Set.mem_preimage]
          obtain ⟨p', hp'⟩ := Quotient.exists_rep p
          rw[← hp']
          induction p'
          case inl x => {
            simp[wedge_embedding, coprod_prod_map]
            constructor
            · exact mem_of_eq_of_mem hp' hp
            · rw[← wedge_defaults_equiv]
              exact hcase
          }
          case inr y => {
            simp[wedge_embedding, coprod_prod_map]
            constructor
            · exact hcase
            · exact mem_of_eq_of_mem hp' hp
          }
    · use B ×ˢ univ ∪ univ ×ˢ C
      constructor
      · apply IsOpen.union
        · exact IsOpen.prod hApre.1 isOpen_univ
        · exact IsOpen.prod isOpen_univ hApre.2
      · ext p
        constructor
        · intro hp
          rw[Set.mem_preimage] at hp
          obtain ⟨p', hp'⟩ := Quotient.exists_rep p
          rw[← hp'] at hp
          induction p'
          case inl x => {
            simp[wedge_embedding, coprod_prod_map] at hp
            obtain hp1|hp2 := hp
            · exact mem_of_eq_of_mem (id hp'.symm) hp1
            · have : default ∈ A := by {
                rw[← wedge_defaults_equiv] at hp2
                exact hp2
                }
              contradiction
          }
          case inr y => {
            simp[wedge_embedding, coprod_prod_map] at hp
            obtain hp1|hp2 := hp
            · have : default ∈ A := by exact hp1
              contradiction
            · exact mem_of_eq_of_mem (id hp'.symm) hp2
          }
        · intro hp
          rw[Set.mem_preimage]
          obtain ⟨p', hp'⟩ := Quotient.exists_rep p
          rw[← hp']
          induction p'
          case inl x => {
            simp[wedge_embedding, coprod_prod_map]
            left
            exact mem_of_eq_of_mem hp' hp
          }
          case inr y => {
            simp[wedge_embedding, coprod_prod_map]
            right
            exact mem_of_eq_of_mem hp' hp
          }
  · have hcont : Continuous (wedge_embedding X Y) := wedge_embedding_cont X Y
    intro hA
    rw[isOpen_induced_iff] at hA
    obtain ⟨B, hB1, hB2⟩ := hA
    have that := IsOpen.preimage hcont hB1
    rw[hB2] at that
    assumption
}

lemma wedge_embedding_pointed: wedge_embedding X Y default = default := by{
  let _:= wedge_setoid X Y
  simp[wedge_embedding]
  have: (default: X ⋁ Y) = Quotient.mk (wedge_setoid X Y) (Sum.inl (default:X)) := rfl
  rw[this]
  simp[Quotient.lift_mk, coprod_prod_map]
  rfl
}


theorem wedge_embeds_into_product: Embedding (wedge_embedding X Y) := by{
  let _hwedge := wedge_setoid X Y
  rw[embedding_iff]
  constructor
  --induced topology
  · exact wedge_embedding_inducing X Y

  --injectivity
  · intro a b hab
    rw[wedge_embedding] at hab
    obtain ⟨a', ha'⟩ := Quotient.exists_rep a
    obtain ⟨b', hb'⟩:= Quotient.exists_rep b
    rw[← ha', ← hb'] at hab
    have hab' : (coprod_prod_map X Y) a' = (coprod_prod_map X Y) b' := hab
    rw[← ha', ← hb']
    induction a'
    case inl xa => {
      induction b'
      case inl xb =>{
        simp[coprod_prod_map] at hab'
        rw[hab']
      }
      case inr yb =>{
        simp[coprod_prod_map] at hab'
        have : (wedge_setoid X Y).r (Sum.inl xa) (Sum.inr yb) := by {
          simp[quotient_setoid_equiv_iff]
          tauto
        }
        rw [Quotient.eq]
        exact this
      }
    }
    case inr ya => {
      induction b'
      case inl xb =>{
        simp[coprod_prod_map] at hab'
        rw[Quotient.eq]
        have: (wedge_setoid X Y).r (Sum.inr ya) (Sum.inl xb) := by {
          simp[quotient_setoid_equiv_iff]
          tauto
        }
        exact this
      }
      case inr yb =>{
        simp[coprod_prod_map] at hab'
        rw[hab']
      }
    }
}

--if something is in the image of the wedge embedding, then at least one of its coordinates is default
lemma wedge_embedding_ran {p: X × Y} (h: p ∈ range (wedge_embedding X Y)) : p.1=default ∨ p.2=default := by{
  let _:= wedge_setoid X Y
  simp at h
  obtain ⟨t, ht⟩:= h
  obtain ⟨t', ht'⟩:= Quotient.exists_rep t
  induction t'
  case inl x => {
    right
    rw[← ht'] at ht
    have : p = (x, default) := by {
      rw[← ht]
      simp[wedge_embedding, coprod_prod_map]
    }
    simp[this]
  }
  case inr y => {
    left
    rw[← ht'] at ht
    have : p = (default, y) := by{
      rw[← ht]
      simp[wedge_embedding, coprod_prod_map]
    }
    simp[this]
  }
}

lemma wedge_embedding_inl (x:X) : wedge_embedding X Y (wedge_inl X Y x) = (x, default) := by{
  let _:= wedge_setoid X Y
  simp[wedge_embedding, wedge_inl, coprod_prod_map]
}

lemma wedge_embedding_inr (y:Y) : wedge_embedding X Y (wedge_inr X Y y) = (default, y) := by{
  let _:= wedge_setoid X Y
  simp[wedge_embedding, wedge_inr, coprod_prod_map]
}

-- define smash products
def smashsetoid : Setoid (X × Y) := by{
  let A : Set (X × Y) := wedge_embedding X Y '' univ
  exact quotient_setoid A
}

def Smash := Quotient (smashsetoid X Y)

/-NOTE: None of the smash definition requires topological spaces, and Lean recognizes this:
it correctly identifies the smash products of any two inhabited types
Ideally, this construction should simply be part of the category of pointed types.
So there should be something like Pointed.smash that takes two pointed types (as in Mathlib/CategoryTheory/Category/Pointed)
and gives back their smash products.
This way, I can define the currying and uncurrying functions at the level of pointed sets
then do what I want to do for (locally compact when needed) topological spaces
-/

instance: TopologicalSpace (Smash X Y) := by exact instTopologicalSpaceQuotient
instance: Inhabited (Smash X Y) where
  default:= Quotient.mk (smashsetoid X Y) (default, default)

infix:50 " ⋀  " => Smash

variable {X Y} in
def smash_elt (y:X) (z:Y) : X ⋀ Y := Quotient.mk (smashsetoid X Y) (y,z)

infix:50 " ∧' " => smash_elt


variable {X Y} in
lemma smash_elt_eq_iff (x x' :X) (y y':Y) : (smash_elt x y = smash_elt x' y') ↔ ( (x=default ∨ y=default) ∧ (x'=default ∨ y'=default) )∨ ( (x,y) = (x', y') ) := by{
  let _:= smashsetoid X Y
  let _:= wedge_setoid X Y
  simp[smash_elt]
  constructor
  · intro h
    have : (smashsetoid X Y).r (x,y) (x', y') := by exact Quotient.eq'.mp h
    simp[quotient_setoid_equiv_iff] at this
    obtain hc1|hc2 := this
    · left
      obtain ⟨h1, h2⟩:= hc1
      have h1':= wedge_embedding_ran X Y h1
      have h2':= wedge_embedding_ran X Y h2
      tauto
    · rw[hc2.1, hc2.2]
      tauto
  · intro h
    have : (smashsetoid X Y).r (x,y) (x', y') := by {
      obtain hc1|hc2:= h
      · simp[quotient_setoid_equiv_iff]
        left
        constructor
        · obtain hd1|hd2:= hc1.1
          · rw[hd1]
            use wedge_inr X Y y
            simp [wedge_embedding, wedge_inr, coprod_prod_map]
          · rw[hd2]
            use wedge_inl X Y x
            simp [wedge_embedding, wedge_inl, coprod_prod_map]
        · obtain hd1|hd2:= hc1.2
          · rw[hd1]
            use wedge_inr X Y y'
            simp [wedge_embedding, wedge_inr, coprod_prod_map]
          · rw[hd2]
            use wedge_inl X Y x'
            simp [wedge_embedding, wedge_inl, coprod_prod_map]
      · rw[hc2.1, hc2.2]
        exact Quotient.eq'.mp rfl
    }
    exact Quotient.eq.mpr this
}

@[simp] theorem smash_defaults_left (x:X) : (x ∧' (default:Y)) = default := by{
  have : (default: X ⋀ Y) = (default ∧' default) := rfl
  rw[this]
  simp[smash_elt_eq_iff]
}

@[simp] theorem smash_defaults_right (y:Y) : ((default:X) ∧' y) = default := by{
  have : (default: X ⋀ Y) = (default ∧' default) := rfl
  rw[this]
  rw[smash_elt_eq_iff]
  left
  simp
}

namespace Pointed

-- Pointed is the thing I should extend to the category of pointed topological spaces
-- I'm starting to define some constructions for pointed sets

variable (α β: Pointed)

instance : Inhabited α.X where
  default:= α.point

def smash : Pointed := ⟨α ⋀ β, (default: α ⋀ β)⟩

variable {α β}
variable {γ: Pointed}

def smash_curry' (f: α ⋀ β → γ) : (α → (β → γ)) := fun a ↦ (fun b ↦ f (a ∧' b))

def smash_curry (f: Pointed.Hom (Pointed.smash α β) γ) : Pointed.Hom α (⟨Pointed.Hom β γ, ⟨fun _ ↦ γ.point, by simp ⟩  ⟩) := sorry

/- etc etc
This should be done at some point -/

end Pointed





--show that there is a pointed isomorphism X ⋀ Y ≃ₜ Y ⋀ X
/- The way I'm doing this might be problematic if this construction is of pointed types.
I should define an equivalence that works for all pointed types
then extend the equivalence to a homeomorphism for topological spaces
I think this just requires some rearranging and can be done easily
-/

def prod_swap : X × Y → Y × X := fun (y,z) ↦ (z,y)

lemma prod_swap_cont: Continuous (prod_swap X Y) := by {
  simp[prod_swap]
  constructor
  · continuity
  · continuity
}

lemma prod_swap_wedge: (prod_swap X Y) ∘ (wedge_embedding X Y) = (wedge_embedding Y X) ∘ (wedge_swap X Y) := by{
  let _:= wedge_setoid X Y
  let _:= wedge_setoid Y X
  ext v
  · obtain ⟨p, hp⟩ := Quotient.exists_rep v
    rw[← hp]
    induction p
    case inl x => {
      simp[prod_swap, wedge_embedding, wedge_swap, Quotient.lift_mk, coprod_prod_map]
    }
    case inr y => {
      simp[prod_swap, wedge_embedding, wedge_swap, Quotient.lift_mk, coprod_prod_map]
    }
  --this is just a copy of the proof of the first goal
  · obtain ⟨p, hp⟩ := Quotient.exists_rep v
    rw[← hp]
    induction p
    case inl x => {
      simp[prod_swap, wedge_embedding, wedge_swap, Quotient.lift_mk, coprod_prod_map]
    }
    case inr y => {
      simp[prod_swap, wedge_embedding, wedge_swap, Quotient.lift_mk, coprod_prod_map]
    }
}

def smash_swap : X ⋀ Y → Y ⋀ X := by{
  let _:= smashsetoid X Y
  let _:= smashsetoid Y X
  apply Quotient.lift ( (Quotient.mk (smashsetoid Y X) )∘ (prod_swap X Y))
  intro a b hab
  simp[smashsetoid, prod_swap, smash_elt_eq_iff]
  have hab': Setoid.r a b := hab
  simp[quotient_setoid_equiv_iff] at hab'
  have : Setoid.r (a.2, a.1) (b.2, b.1) := by{
    rw [quotient_setoid_equiv_iff]
    obtain hc1|hc2 := hab'
    · left
      obtain ⟨h1, h2⟩ := hc1
      obtain ⟨c, hc⟩ := h1
      obtain ⟨d, hd⟩ := h2
      simp
      constructor
      · use wedge_swap _ _ c
        have : wedge_embedding Y X (wedge_swap X Y c) = ((wedge_embedding Y X) ∘ (wedge_swap X Y)) c := rfl
        rw [this, ← prod_swap_wedge X Y, Function.comp, hc]
        simp[prod_swap]
      · use wedge_swap _ _ d
        have : wedge_embedding Y X (wedge_swap X Y d) = ((wedge_embedding Y X) ∘  (wedge_swap X Y)) d := rfl
        rw [this, ← prod_swap_wedge X Y, Function.comp, hd]
        simp[prod_swap]
    · right
      rw[hc2]
  }
  exact Quotient.eq.mpr this
}

lemma continuous_smash_swap: Continuous (smash_swap X Y) := by{
  apply Continuous.quotient_lift
  apply Continuous.comp
  · apply continuous_quot_mk
  · exact prod_swap_cont X Y
}

variable{X Y} in
@[simp] lemma swap_pair (x:X) (y:Y) : smash_swap X Y (x ∧' y) = (y ∧' x) := by {
  let _:= smashsetoid X Y
  let _:= smashsetoid Y X
  simp[smash_swap, smash_elt, Quotient.lift_mk, prod_swap]
}

lemma pointed_smash_swap: (smash_swap X Y) default = default := by{
  have h1 : (default : X ⋀ Y)  = (default ∧' default) := rfl
  have h2 : (default : Y ⋀ X)  = (default ∧' default) := rfl
  rw[h1, h2, swap_pair]
}


variable {X Y} in
lemma swap_swap (p: X ⋀ Y) : smash_swap Y X (smash_swap X Y p) = p := by{
  obtain ⟨v, hv⟩:= Quotient.exists_rep p
  have : p = ((v.1) ∧' (v.2)) := by {
    simp[hv, smash_elt]
  }
  rw[this]
  simp[swap_pair]
}

def homeo_smash_swap: X ⋀ Y ≃ₜ⋆ Y ⋀ X where
  toFun := smash_swap X Y
  continuous_toFun := continuous_smash_swap X Y
  invFun := smash_swap Y X
  continuous_invFun := continuous_smash_swap Y X

  left_inv := by{
    rw[LeftInverse]
    intro p
    exact swap_swap p
  }
  right_inv := by{
    rw[Function.RightInverse, LeftInverse]
    intro p
    exact swap_swap p
  }

  pointed_toFun := pointed_smash_swap X Y



--Show that X ≃ₜ⋆  Z → X ⋀ Y ≃ₜ⋆  Z ⋀ Y
variable (Z:Type*) [TopologicalSpace Z] [Inhabited Z]
variable (W':Type*) [TopologicalSpace W'] [Inhabited W']

section smashmaps
variable {X Y Z W'}


def prod_maps (f: X → Z) (g: Y → W') : X × Y → Z × W' := fun (y, z) ↦ (f y, g z)

variable {f: X → Z}
variable {g: Y → W'}
variable (hf: f default = default)
variable (hg: g default = default)


def smash_maps : X ⋀ Y → Z ⋀ W' := by {
  let _:= smashsetoid X Y
  let _:= smashsetoid Z W'
  apply Quotient.lift ( (Quotient.mk (smashsetoid Z W') )∘ (prod_maps f g))
  intro a b hab
  simp[prod_maps]
  have: Setoid.r a b := hab
  simp[quotient_setoid_equiv_iff] at this
  obtain hc1| hc2 := this
  · obtain ⟨ha, hb⟩:= hc1
    have ha' : a.1 = default ∨ a.2 = default := wedge_embedding_ran X Y ha
    have hb' : b.1 = default ∨ b.2 = default := wedge_embedding_ran X Y hb
    have : Setoid.r (f a.1, g a.2) (f b.1, g b.2) := by{
      simp[quotient_setoid_equiv_iff]
      left
      constructor
      · obtain hal|har := ha'
        · use wedge_inr Z W' (g a.2)
          rw[hal, hf]
          apply wedge_embedding_inr
        · use wedge_inl Z W' (f a.1)
          rw[har, hg]
          apply wedge_embedding_inl
      · obtain hbl|hbr := hb'
        · use wedge_inr Z W' (g b.2)
          rw[hbl, hf]
          apply wedge_embedding_inr
        · use wedge_inl Z W' (f b.1)
          rw[hbr, hg]
          apply wedge_embedding_inl
    }
    exact this
  · simp[hc2]
    exact Quotient.eq.mp rfl
}


lemma continuous_smash_maps (hf': Continuous f) (hg': Continuous g) : Continuous (smash_maps hf hg) := by {
  simp [smash_maps]
  apply Continuous.quotient_lift
  apply Continuous.comp
  · apply continuous_quot_mk
  · simp[prod_maps]
    constructor
    · exact Continuous.fst' hf'
    · exact Continuous.snd' hg'
}


lemma pointed_smash_maps: (smash_maps hf hg) default = default := by{
  let _:= smashsetoid X Y
  let _:= smashsetoid Z W'
  simp[smash_maps]
  have : (default: X ⋀ Y) = Quotient.mk (smashsetoid X Y) (default, default) := rfl
  rw[this, Quotient.lift_mk]
  simp[prod_maps, hf, hg]
  symm
  rfl
}


lemma smash_maps_comp {W₁ W₂: Type*} [TopologicalSpace W₁] [Inhabited W₁] [TopologicalSpace W₂] [Inhabited W₂] {f': Z → W₁} {g': W' → W₂} (hf': f' default = default) (hg': g' default = default) (p: X ⋀ Y) : smash_maps hf' hg' (smash_maps hf hg p) = @smash_maps _ _ _ _ _ _ _ _ (f' ∘ f) (g' ∘g) (by simp[hf, hf']) (by simp[hg, hg']) p := by{
  let _:= smashsetoid X Y
  let _:= smashsetoid Z W'
  let _:= smashsetoid W₁ W₂
  simp[smash_maps]
  obtain ⟨p', hp'⟩:= Quotient.exists_rep p
  rw[←hp']
  simp[Quotient.lift_mk]
  simp[prod_maps]
}

end smashmaps

variable (k: X ≃ₜ⋆ Z)

variable{X Z} in
def wedge_compare : X ⋀ Y → Z ⋀ Y := by {
  apply @smash_maps _ _ _ _ _ _ _ _ k.toFun id
  · exact k.pointed_toFun
  · simp
}

variable{X Z} in
lemma continuous_wedge_compare : Continuous (wedge_compare Y k) := by{
  rw[wedge_compare]
  apply continuous_smash_maps
  · exact k.continuous_toFun
  · exact continuous_id
}

variable{X Z} in
lemma pointed_wedge_compare : (wedge_compare Y k) default = default := by {
  simp[wedge_compare]
  apply pointed_smash_maps
}

variable{X Z} in
/--The pointed homeomorphism from X ⋀ Y to Z ⋀ Y obtained via a pointed homeomorphism from X to Z-/
def homeo_wedge_compare : X ⋀ Y ≃ₜ⋆ Z ⋀ Y where
  toFun := wedge_compare Y k
  continuous_toFun := continuous_wedge_compare Y k
  invFun := wedge_compare Y (PointedHomeo.symm k)
  continuous_invFun := continuous_wedge_compare Y (PointedHomeo.symm k)

  left_inv := by{
    let _:=smashsetoid X Y
    let _:= smashsetoid Z Y
    simp[LeftInverse]
    intro p
    simp[wedge_compare]
    simp [smash_maps_comp, PointedHomeo.symm, smash_maps]
    obtain ⟨p', hp'⟩:= Quotient.exists_rep p
    rw[← hp']
    simp[Quotient.lift_mk, prod_maps]
  }
  right_inv := by{
    let _:=smashsetoid X Y
    let _:= smashsetoid Z Y
    simp[Function.RightInverse, LeftInverse]
    intro p
    simp[wedge_compare]
    simp [smash_maps_comp, PointedHomeo.symm, smash_maps]
    obtain ⟨p', hp'⟩:= Quotient.exists_rep p
    rw[← hp']
    simp[Quotient.lift_mk, prod_maps]
  }

  pointed_toFun := pointed_wedge_compare Y k

#check homeo_wedge_compare Y k

#check PointedHomeo.trans

variable{X Z} in
/--The pointed homeomorphism from Y ⋀ X to Y ⋀ Z obtained via a pointed homeomorphism from X to Z-/
def homeo_wedge_compare': Y ⋀ X ≃ₜ⋆ Y ⋀ Z := PointedHomeo.trans (PointedHomeo.trans (homeo_smash_swap Y X) (homeo_wedge_compare Y k)) (homeo_smash_swap Z Y)

--define the spheres Sⁿ

variable (n:ℕ)
notation "𝕊" n => Metric.sphere (0:EuclideanSpace ℝ (Fin (n+1) )) 1
noncomputable instance: TopologicalSpace (EuclideanSpace ℝ (Fin (n+1) )) := by exact UniformSpace.toTopologicalSpace
instance: TopologicalSpace (𝕊 n) := instTopologicalSpaceSubtype


#check EuclideanSpace.single (1 : Fin 4) (2: ℝ)

instance: Inhabited (𝕊 n) where
  default := ⟨EuclideanSpace.single (0: Fin 3) (1:ℝ) , by simp⟩ --3??? This should be n+1 I think, but it fails



--[ TODO ] show that S¹≃ₜ I/∼
notation "circle" => 𝕊 1


def ciao2: EuclideanSpace ℝ (Fin 2) := fun n ↦ n
#check Finset.sum_fin_eq_sum_range

#check Real.cos_eq_cos_iff

def wrap : I → circle := fun t ↦ ⟨ fun i ↦ i * Real.sin (2*Real.pi*t) + (1-i) * Real.cos (2 * Real.pi * t), by {simp[EuclideanSpace.norm_eq, Finset.sum_range_succ, Finset.sum_fin_eq_sum_range]} ⟩


example (a b c : ℝ) (h: a ≠ 0) (k: a * b = a * c) : b = c := by {
  rw[mul_right_inj'] at k
  assumption
  assumption
}


lemma wrap_eq_iff (a b : I): wrap a = wrap b ↔ (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∨ a = b := by{
  constructor
  · intro h
    have : (wrap a).val 1 = (wrap b).val 1 := by exact congrFun (congrArg Subtype.val h) 1
    have h1 : Real.sin (2*Real.pi * a) = Real.sin (2*Real.pi * b) := by{
      simp[wrap] at this
      assumption
    }
    rw[Real.sin_eq_sin_iff] at h1
    obtain ⟨k, hk⟩:= h1

    have : (wrap a).val 0 = (wrap b).val 0 := by exact congrFun (congrArg Subtype.val h) 0
    have h2 : Real.cos (2*Real.pi * a) = Real.cos (2*Real.pi * b) := by{
      simp[wrap] at this
      assumption
    }
    --rw[Real.cos_eq_cos_iff] at h2
    --obtain ⟨k', hk'⟩:= h2

    obtain hc1|hc2 := hk
    · ring at hc1
      rw[mul_assoc, mul_assoc, mul_assoc,  ← mul_add Real.pi] at hc1
      simp [Real.pi_ne_zero, mul_right_inj' ] at hc1
      rw[← add_mul, mul_left_inj'] at hc1
      have : k=0 ∨ k=1 ∨ k =-1 := by{
        sorry
      }
      obtain hd1|hd2|hd3 := this
      · rw[hd1] at hc1
        simp at hc1
        right
        ext
        simp[hc1]
      · left
        constructor
        · sorry
        · sorry
      · left
        constructor
        · sorry
        · sorry
      · norm_num
    · rw[hc2, Real.cos_sub] at h2
      have hsin: Real.sin (2 * Real.pi * a) = 0 := by sorry
      have hcos: Real.cos ((2*k + 1) * Real.pi) = -1 := by sorry
      rw[hsin, hcos] at h2
      simp[Real.cos_eq_zero_iff] at h2
      obtain ⟨k', hk'⟩ := h2
      have : k' = 0 ∨ k' = 1 := by {
        sorry
      }
      obtain hd1|hd2 := this
      · rw[hd1] at hk'
        simp at hk'
        sorry



      rw[mul_assoc, mul_comm, mul_comm (2*(k:ℝ) +1) Real.pi, mul_assoc 2, mul_comm 2 (Real.pi * (a:ℝ) ), mul_assoc Real.pi a, ← mul_sub Real.pi, mul_assoc ] at hc2
      simp [Real.pi_ne_zero, mul_left_inj'] at hc2


  · intro h
    obtain hc1|hc2 := h
    · have: wrap 0 = wrap 1 := by simp[wrap]
      obtain ⟨hx, hy⟩ := hc1
      obtain hd1|hd2 := hx
      · obtain he1|he2 := hy
        · rw[hd1, he1]
        · rw[hd1, he2, this]
      · obtain he1|he2 := hy
        · rw[hd2, he1, this]
        · rw[hd2, he2]
    · rw[hc2]
}

lemma continuous_wrap: Continuous wrap := by {
  simp[wrap]
  refine Continuous.subtype_mk ?h fun x ↦ wrap.proof_2 x



  have: ∀ i : Fin (1+1), Continuous fun t ↦ ↑↑i * Real.sin (2 * Real.pi * ↑t) + (1 - ↑↑i) * Real.cos (2 * Real.pi * ↑t) := by {
    intro i
    continuity
  }


  sorry --shouldn't this be a lemma from the library? by discreteness of Fin n
}


def I_quotient: Setoid (I) := quotient_setoid ({x: I | x = 0 ∨ x = 1})

def J := Quotient I_quotient
instance: TopologicalSpace J := instTopologicalSpaceQuotient
instance: Inhabited J where
  default:= Quotient.mk I_quotient 0


def wrap_quot: J → circle := by{
  apply Quotient.lift wrap
  intro x y hxy
  rw[wrap_eq_iff]
  have: (I_quotient).r x y := hxy
  simp[quotient_setoid_equiv_iff] at this
  exact this
}



lemma continuous_wrap_quot : Continuous wrap_quot := by {
  apply Continuous.quotient_lift
  exact continuous_wrap
}

lemma injective_wrap_quot : Injective wrap_quot := by{
  let _:= I_quotient
  rw[Injective]
  intro s t hst
  simp[wrap_quot] at hst
  obtain ⟨i, hi⟩ := Quotient.exists_rep s
  obtain ⟨j, hj⟩ := Quotient.exists_rep t
  rw[← hi, ← hj, Quotient.lift_mk, Quotient.lift_mk] at hst
  have h' : (I_quotient).r i j := by {
    simp[quotient_setoid_equiv_iff]
    rw[← wrap_eq_iff]
    assumption
  }
  rw[← hi, ← hj]
  rw [Quotient.eq]
  exact h'
}

lemma surjective_wrap_quot : Surjective wrap_quot := by {
  simp[wrap_quot]
  rw [Quot.surjective_lift]
  simp[wrap, Surjective]
  intro x hx
  by_cases h: x 1 ≥ 0
  · use (Real.arccos (x 0)) / (2*Real.pi)
    constructor
    · sorry
    · rw[mul_comm]
      ring
      rw[mul_assoc]
      have: Real.pi * (Real.pi)⁻¹ = 1 := by sorry
      rw[this]
      ring
      have h1 : -1 ≤ x 0 := by sorry
      have h2 : x 0 ≤ 1  := by sorry
      rw[Real.cos_arccos h1 h2]
      rw[Real.sin_arccos]

      have h3: x 1 = Real.sqrt (1 - (x 0)^2) := by sorry
      sorry

  · use (2 * Real.pi - Real.arccos (x 0)) /(2*Real.pi)
    constructor
    · sorry
    · sorry
}


def wrap_quot_equiv: J ≃ circle := by{
  apply Equiv.ofBijective wrap_quot
  rw[Bijective]
  constructor
  · exact injective_wrap_quot
  · exact surjective_wrap_quot
}

lemma continuous_wrap_quot_equiv : Continuous wrap_quot_equiv := continuous_wrap_quot

instance: CompactSpace J := Quotient.compactSpace

def wrap_quot_homeo: J ≃ₜ circle := by{
  apply Continuous.homeoOfEquivCompactToT2 continuous_wrap_quot_equiv
}


lemma pointed_wrap_quot : wrap_quot_equiv default = default := by{
  let _:= I_quotient
  simp[wrap_quot_equiv, wrap_quot]
  have : (default : J) = Quotient.mk I_quotient 0 := rfl
  rw[this]
  rw[Quotient.lift_mk]
  simp[wrap, default, EuclideanSpace.single]
  funext t
  simp
  split_ifs with h
  · rw[h]
    norm_num
  · have : t=1 := by {
    have htlt : t.val < 1 + 1 := t.isLt
    have : t.val < 2 := by exact htlt
    have ht : t.val = 0 ∨ t.val = 1 := by{
      refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
      exact Nat.lt_succ.mp this
    }
    ext
    have : t.val ≠ 0 := by {
      by_contra hcontr
      have : 0= (@OfNat.ofNat (Fin (1 + 1)) 0 Zero.toOfNat0).val := rfl
      rw[this] at hcontr
      have := Fin.eq_of_val_eq hcontr
      exact h this
    }
    tauto
  }
    rw[this]
    norm_num
}

def wrap_quot_pointed_homeo: J ≃ₜ⋆ circle where
  toHomeomorph:= wrap_quot_homeo
  pointed_toFun := pointed_wrap_quot

#check EuclideanSpace.single


/-- A pointed homeomorphism between X ⋀ 𝕊¹ and X ⋀ [0,1]/∼, where the equivalence relation quotients out the extremes. -/
def smash_circle_J_pointed_homeo : X ⋀ (𝕊 1) ≃ₜ⋆ X ⋀ J := PointedHomeo.symm (homeo_wedge_compare' X (wrap_quot_pointed_homeo))


-- Now I can show that X ⋀ J ≃ₜ Σ₀ X

def prod_to_wedge : (X × I) → (X ⋀ J) := fun (y, t) ↦ smash_elt y (Quotient.mk I_quotient t)

lemma continuous_prod_to_wedge: Continuous (prod_to_wedge X) := by sorry

def sus_to_wedge : Σ₀ X → (X ⋀ J) := by{
  let _:= basedsuspension_setoid X
  apply Quotient.lift (prod_to_wedge X)
  intro a b hab
  have : (basedsuspension_setoid X).r a b := hab
  simp[quotient_setoid_equiv_iff] at this
  simp[prod_to_wedge, smash_elt_eq_iff]

  obtain hc1|hc2 := this
  · obtain ⟨ha, hb⟩:= hc1
    obtain hd1|hd2 := ha
    · sorry
    · sorry
  · rw[hc2]
    sorry
}

lemma continuous_sus_to_wedge : Continuous (sus_to_wedge X) := by{
  apply Continuous.quotient_lift
  exact continuous_prod_to_wedge X
}

-- Pointed etc


--Finally, compose to get
--[ TODO ] show X ⋀ S¹ ≃ₜ⋆  Σ₀ X




--[ TODO ] adjunction Top_* (X ⋀ Y, Z) ≃ Top_* (X, Top_* (Y,Z)) for Y locally compact
section adjunction
/-
Ideally, this should be a categorical statement: the functor Hom(Y,-) is right adjoint to -⋀ Y
in pointed topological spaces. I haven't framed pointed spaces as a category, see eg
    mathlib4/Mathlib/CategoryTheory/Category/Pointed.lean
for general pointed types.
I think the bulk of the proof is what I'm doing now and it can all be polished up at a later stage
-/

/-The unpointed version of the map we want is already in Mathlib as ContinuousMap.curry
  This is why ours will be called PointedMap.curry -/

variable [LocallyCompactSpace Y]
instance : TopologicalSpace C⋆(Y,Z) := PointedMap.compactOpen Y Z
instance : Inhabited C⋆(Y,Z) where
  default := PointedMap.trivial Y Z


namespace PointedMap
variable {X Y Z}
/- Much of the following (up to end PointedMap) is adapted from mathlib4/Mathlib/Topology/CompactOpen.lean by Reid Barton, starting on line 364 -/

/-- Auxiliary definition, see `PointedMap.curry`. -/
def curry' (f : C⋆(X ⋀ Y, Z)) (y : X) : C⋆(Y, Z) where
  toFun := Function.curry (f ∘ Quotient.mk (smashsetoid X Y)) y
  continuous_toFun := by {
    apply Continuous.comp
    · apply Continuous.comp
      · exact map_continuous f
      · exact continuous_quot_mk
    · exact Continuous.Prod.mk y
  }
  pointed_toFun := by{
    simp
    have : Quotient.mk (smashsetoid X Y) (y, default) = ( y ∧' default) := rfl
    simp[this]
  }

  /-- If a map `X ⋀ Y → Z` is continuous, then its curried form `X → C⋆(Y, Z)` is continuous. -/
theorem continuous_curry' (f : C⋆(X ⋀ Y, Z)) : Continuous (curry' f) := by{
  --apply Continuous.comp
  sorry
}



--Continuous.comp (continuous_comp f) continuous_coev

  /-- If a map `X ⋀ Y → Z` is pointed, then its curried form `X → C⋆(Y, Z)` is pointed. -/
theorem pointed_curry' (f : C⋆(X ⋀ Y, Z)) : (curry' f) default = default := by{
  simp[curry', Function.curry]
  ext z
  simp[default, PointedMap.trivial]
  -- Don't I have a simp lemma that simplifies this further??? Shouldn't this be just simp now?
  sorry
}

/-- The curried form of a pointed continuous map `X ⋀ Y → Z` as a pointed continuous map `X → C⋆(Y, Z)`.
    If `Y` is locally compact, this is a bijection and carries an adjunction of functors `- ⋀ Y  ⊣ C⋆(Y, -)` . -/
def curry (f : C⋆(X ⋀ Y, Z)) : C⋆(X, C⋆(Y, Z)) where
  continuous_toFun:= continuous_curry' f
  pointed_toFun:= pointed_curry' f

@[simp]
theorem curry_apply (f : C⋆(X ⋀ Y, Z)) (y : X) (z : Y) : f.curry y z = f (y ∧'z) :=
  rfl


def toFun_toFun (f:C⋆(X, C⋆(Y, Z))) : X → (Y → Z) := fun y ↦ (fun z ↦ (f y) z)

-- I think much of this can happen at the level of pointed types with no mention of the topology. Should I do it there and extend?
/-- The uncurrying of a pointed function X → (Y → Z)  to a function X ⋀ Y → Z. This is not the same as Function.uncurry, which maps to X × Y → Z -/
def uncurry' (f:C⋆(X, C⋆(Y, Z))) : X ⋀ Y → Z := by {
  let _:= smashsetoid X Y
  apply Quotient.lift (Function.uncurry f.toFun_toFun)
  -- from now on, semi-identical proofs of this kind have occured many times, perhaps it should be automated a bit
  intro a b hab
  have hab' : Setoid.r a b := hab
  simp[quotient_setoid_equiv_iff] at hab'
  obtain hc1|hc2 := hab'
  · simp[Function.uncurry, toFun_toFun]
    obtain ⟨h1, h2⟩:= hc1
    have h1' := wedge_embedding_ran _ _ h1
    have h2' := wedge_embedding_ran _ _ h2
    have h1'' : (f.toContinuousMap a.1).toContinuousMap a.2 = default := by{
      obtain hl|hr := h1'
      · simp[hl]
        -- I feel like the simps for pointed maps are too weak against their extension from continuous maps!
        --simp[f.pointed_toFun]
        sorry
      · simp[hr, (f a.1).pointed_toFun]
        sorry
    }
    have h2'' : (f.toContinuousMap b.1).toContinuousMap b.2 = default := by{
      -- copy proof for h1''
      sorry
    }
    rw[h1'', h2'']
  · rw[hc2]
}




/-- The uncurried form of a continuous map `X → C⋆(Y, Z)` for `Y` locally compact is a continuous map `X ⋀ Y → Z`. -/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace Y] (f:C⋆(X, C⋆(Y, Z))) : Continuous (f.uncurry') := by{
  simp[uncurry']
  apply Continuous.quotient_lift
  simp[toFun_toFun]
  apply ContinuousMap.continuous_uncurry_of_continuous  --why is it failing so badly???


  -- Again, if simp was powerful enough, this should be simpler to deal with
  --apply ContinuousMap.continuous_uncurry_of_continuous (ContinuousMap.uncurry f.toFun_toFun)
  -- gets stuck into bad coercions


}

#check ContinuousMap.continuous_uncurry_of_continuous


/- ORIGINAL FILE FOR Continuous.curry: NOT MY CODE!!!


PLEASE COPY AGAIN BEFORE USING -- I FOUND AND REPLACED Y->X AND Z->Y AND NOW THIS IS SUPER MESSED UP

-- my maps here will have to be forced to be pointed by assumption but it's fine I guess
/-- To show continuity of a map `X → C(Y, Z)`, it suffices to show that its uncurried form
    `X × X → Y` is continuous. -/
theorem continuous_of_continuous_uncurry (f : X → C(X, Y))
    (h : Continuous (Function.uncurry fun x y => f x y)) : Continuous f :=
  continuous_curry' ⟨_, h⟩



/-- The currying process is a continuous map between function spaces. -/
theorem continuous_curry [LocallyCompactSpace (X × X)] :
    Continuous (curry : C(X × X, Y) → C(X, C(X, Y))) := by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).symm.comp_continuous_iff']
  exact continuous_eval


/-- The uncurried form of a continuous map `X → C(X, Y)` is a continuous map `X × X → Y`. -/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace X] (f : C(X, C(X, Y))) :
    Continuous (Function.uncurry fun x y => f x y) :=
  continuous_eval.comp <| f.continuous.prod_map continuous_id


/-- The uncurried form of a continuous map `X → C(X, Y)` as a continuous map `X × X → Y` (if `X` is
    locally compact). If `X` is also locally compact, then this is a homeomorphism between the two
    function spaces, see `Homeomorph.curry`. -/
@[simps]
def uncurry [LocallyCompactSpace X] (f : C(X, C(X, Y))) : C(X × X, Y) :=
  ⟨_, continuous_uncurry_of_continuous f⟩


/-- The uncurrying process is a continuous map between function spaces. -/
theorem continuous_uncurry [LocallyCompactSpace X] [LocallyCompactSpace X] :
    Continuous (uncurry : C(X, C(X, Y)) → C(X × X, Y)) := by
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).comp_continuous_iff']
  apply continuous_eval.comp (continuous_eval.prod_map continuous_id)

-/







-- Currying is an equivalence

theorem injective_curry: Injective (curry : C⋆(X ⋀ Y, Z) → C⋆(X, C⋆(Y, Z))) := by{
  simp[Injective]
  intro f g hfg
  ext x'
  let ⟨x, hx⟩ := Quotient.exists_rep x'
  have : x = (x.1, x.2) := rfl
  have : x'= ((x.1) ∧' (x.2)) := by {rw[← hx, this]; rfl}
  rw[this]
  have hfg' : curry f x.1 x.2 = curry g x.1 x.2 := congrFun (congrArg FunLike.coe (congrFun (congrArg FunLike.coe hfg) x.1)) x.2
  simp at hfg'
  assumption
}

theorem surjective_curry: Surjective (curry : C⋆(X ⋀ Y, Z) → C⋆(X, C⋆(Y, Z))) := by{
  simp[Surjective]
  intro F
  sorry
}


def equiv_curry: C⋆(X ⋀ Y, Z) ≃ C⋆(X, C⋆(Y, Z)) := by{
  apply Equiv.ofBijective (curry)
  constructor
  · exact injective_curry
  · exact surjective_curry
}



-- [ TODO ] Naturality

end PointedMap



end adjunction

-- [ TODO? ] Do Proposition 1.3 in Cutler's pdf



-- [TODO] Prove that the free suspension of 𝕊ⁿ is homeomorphic to 𝕊^{n+1}

lemma target_in_sphere (y : 𝕊 n) (t: I) : @norm (EuclideanSpace ℝ (Fin (n + 1))) SeminormedAddGroup.toNorm (Fin.snoc (fun i ↦ Real.sqrt (1 - (↑t+1)/2 * (↑t+1)/2) * (y.1 i) ) ((↑t +1)/2))  = 1 := by{
  simp[Fin.snoc, EuclideanSpace.norm_eq, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  sorry
  -- I remember this working earlier (???)
}


def cyl_to_sphere: (𝕊 n) × I  → (𝕊 (n+1)) :=
  fun (⟨x, p⟩, t) ↦ ⟨Fin.snoc ( fun i ↦ Real.sqrt (1-((↑t +1)/2)*((↑t +1)/2)) * (x i) ) ((↑t +1)/2) ,  by{simp; /-exact target_in_sphere n (⟨x, p⟩) t}-/ sorry} ⟩


def sus_to_sphere: S (𝕊 n) → 𝕊 (n+1) := by{
  apply Quotient.lift (cyl_to_sphere n)
  intro a b hab
  ext i
  simp[cyl_to_sphere, Fin.snoc]
  sorry
}


theorem injective_sus_to_sphere : Injective (sus_to_sphere n) := by{
  sorry
}

theorem surjective_sus_to_sphere : Surjective (sus_to_sphere n) := by{
  sorry
}

def sus_to_sphere_equiv : S (𝕊 n) ≃ (𝕊 (n+1)) := by{
  apply Equiv.ofBijective (sus_to_sphere n)
  rw[Bijective]
  constructor
  · exact injective_sus_to_sphere n
  · exact surjective_sus_to_sphere n
}

theorem continuous_sus_to_sphere : Continuous (sus_to_sphere_equiv n) := by{
  sorry
}


instance : CompactSpace (Cylinder (𝕊 n)) := instCompactSpaceProdInstTopologicalSpaceProd
instance : CompactSpace (S (𝕊 n)) := Quotient.compactSpace


def sus_to_sphere_homeo: S (𝕊 n)  ≃ₜ (𝕊 (n+1))  := by{
  apply Continuous.homeoOfEquivCompactToT2 (continuous_sus_to_sphere n)
}

-- add pointed



/- Ideal, partial todo list:
-- suspension as smashing with S^1 [Done]
-- suspension of S^n is S^{n+1} [very roughly sketched above]
-- free and reduced suspension are homotopy equivalent [I THINK THIS ONLY HOLDS FOR CW COMPLEXES SO NO]
-- adjunction with loop (depending on difficulty, either the smash version or just the suspension version) [Doing the general version] [TODO compose the correct maps to get the special case]
-- time permitting, more related and basic topological things that are missing [I don't think time permits]

Some things about the mapping cone seem to be in Mathlib in abstract nonsense form (I should check more carefully), maxbe define mapping cones and show they fit the nonsense?
-/


/-
Possible references to add:
https://ncatlab.org/nlab/show/smash+product
-/

--#lint
end pointed_spaces

end
