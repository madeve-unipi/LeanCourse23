import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
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
- Defined the wedge product Y ⋁ Z of two pointed spaces Y and Z
- Some lemmas to deal with wedge products more easily
- Constructed an embedding Y ⋁ Z ↪ Y × Z and showed it is an embedding
- Defined the smash product Y ⋀ Z of two pointed spaces Y and Z
- Started some work on spheres [EXTREMELY BROKEN; NOT IN A DECENT STATE YET]

To do:
- See comment at the end

Things that should be polished:
- Divide the content into sections, e.g. unpointed vs pointed. Specifically, also have the pointed spaces be X and Y instead of Y and Z
- Deal with the implicit/explicit variable mess in the lemmas. Some are fine, some don't really need to be explicit
-/


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

lemma quotient_setoid_equiv_iff (A: Set X) (x y : X) : (quotient_setoid A).r x y ↔ ((x ∈ A ∧ y ∈ A) ∨ x = y ) := by {
  exact Iff.rfl
}

--define the setoid for taking a quotient in which to two disjoint subspaces A and B are collapsed to one point each
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

-- we will need to define functions X/∼  → Y/∼
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




--define the pointed cylinder of Y
variable (Y:Type*) [TopologicalSpace Y] [Inhabited Y]

def pointedcylinder_setoid : Setoid (Cylinder Y) := by{
  exact quotient_setoid ({x : Cylinder Y | x.1 = default})
}

/--Pointed cylinder of a pointed topological space-/
def PointedCylinder := Quotient (pointedcylinder_setoid Y)

--show PointedCylinder is a pointed topological space with basepoint * × I
instance : TopologicalSpace (PointedCylinder Y) := instTopologicalSpaceQuotient

instance : Inhabited (PointedCylinder Y) where
  default := Quotient.mk (pointedcylinder_setoid Y) ((default : Y), 0)


--define the pointed suspension of Y
def basedsuspension_setoid : Setoid (Cylinder Y) := by{
  let A := {x : Cylinder Y | x.1 = default}
  let B := {x : Cylinder Y | x.2 = 0}
  let C := {x : Cylinder Y | x.2 = 1}
  exact quotient_setoid (A ∪ B ∪ C)
}

def BasedSuspension := Quotient (basedsuspension_setoid Y)
instance : TopologicalSpace (BasedSuspension Y) := instTopologicalSpaceQuotient

instance : Inhabited (BasedSuspension Y) where
  default:= Quotient.mk (basedsuspension_setoid Y) ((default:Y), 0)

notation (priority:= high) "Σ₀" => BasedSuspension

--[ TODO ] Define the based suspension functor and show it is a functor
--[ TODO ] Define iterated suspensions

-- define the wedge product Y ⋁ Z of two pointed spaces Y and Z


variable (Z:Type*) [TopologicalSpace Z] [Inhabited Z]
instance: TopologicalSpace (Y ⊕ Z) := by infer_instance

def wedge_setoid : Setoid (Y ⊕ Z) := by{
  let A: Set (Y ⊕ Z) := { x : Y ⊕ Z | x = Sum.inl (default:Y) ∨ x = Sum.inr (default:Z)}
  exact quotient_setoid A
}


def Wedge := Quotient (wedge_setoid Y Z)
instance: TopologicalSpace (Wedge Y Z) := by exact instTopologicalSpaceQuotient
instance: Inhabited (Wedge Y Z) where
  default:= Quotient.mk (wedge_setoid Y Z) (Sum.inl (default:Y))

infix:50 " ⋁ " => Wedge

-- easy lemma for later
lemma wedge_defaults_equiv: Quotient.mk (wedge_setoid Y Z) (Sum.inl default) = Quotient.mk (wedge_setoid Y Z) (Sum.inr default) := by{
  let _hwedge := wedge_setoid Y Z
  refine Quotient.eq.mpr ?_
  have : (wedge_setoid Y Z).r (Sum.inl default) (Sum.inr default) := by{
    simp[quotient_setoid_equiv_iff]
  }
  exact this
}

--[ TODO ] define arbitrarily large wedge products


-- Show that there is a homeomorphism X ⋁ Y ≃ Y ⋁ X

lemma continuous_sum_swap: Continuous (@Sum.swap Y Z) := by{ --this looks like it should be a lemma from the library but I couldn't find it
  refine continuous_sum_dom.mpr ?_
  constructor
  · have : (@Sum.swap Y Z) ∘ (@Sum.inl Y Z) = @Sum.inr Z Y := rfl
    rw[this]
    exact continuous_inr
  · have : (@Sum.swap Y Z) ∘ (@Sum.inr Y Z) = @Sum.inl Z Y := rfl
    rw[this]
    exact continuous_inl
}


def sum_commutes: Y ⊕ Z ≃ₜ Z ⊕ Y where
  toFun:= @Sum.swap Y Z
  continuous_toFun := continuous_sum_swap Y Z
  invFun:= @Sum.swap Z Y
  continuous_invFun := continuous_sum_swap Z Y
  left_inv:= by simp
  right_inv:= by simp


--TO REWRITE using subsequent standard way to map from wedge
def wedge_swap: Y ⋁ Z → Z ⋁ Y := by{
  let _hwedge := wedge_setoid Y Z
  let _hwedge' := wedge_setoid Z Y
  apply Quotient.lift ( (Quotient.mk (wedge_setoid Z Y)  ) ∘ (@Sum.swap Y Z))
  intro a b hab
  have hab2: Setoid.r a b := by exact hab
  simp [quotient_setoid_equiv_iff] at hab2
  obtain hc1|hc2 := hab2
  · induction a
    case inl ya => {
      induction b
      case inl yb => {
        simp at hc1
        simp[hc1]
      }
      case inr zb => {
        simp at hc1
        simp[hc1]
        have : Setoid.r (@Sum.inr Z Y default) (Sum.inl default) := by{
          simp[quotient_setoid_equiv_iff]
        }
        exact this
      }
    }
    case inr za => {
      induction b
      case inl yb => {
        simp at hc1
        simp [hc1]
        have : Setoid.r (@Sum.inl Z Y default) (Sum.inr default) := by simp[quotient_setoid_equiv_iff]
        exact this
      }
      case inr zb => {
        simp at hc1
        simp[hc1]
      }
    }
  · rw[hc2]
}

lemma continuous_wedge_swap : Continuous (wedge_swap Y Z) := by{
  apply Continuous.quotient_lift
  apply Continuous.comp
  · exact continuous_coinduced_rng
  · exact continuous_sum_swap Y Z
}


lemma wedge_swap_inl (y:Y) : (wedge_swap Y Z) (Quotient.mk _ (Sum.inl y) ) = Quotient.mk _ (@Sum.inr Z Y y) := by{
  simp[wedge_swap]
  apply Quot.lift_mk
  exact fun a₁ a₂ a ↦ a
}


lemma wedge_swap_inr (z:Z) : (wedge_swap Y Z) (Quotient.mk _ (Sum.inr z) ) = Quotient.mk _ (@Sum.inl Z Y z) := by{
  simp[wedge_swap]
  apply Quot.lift_mk
  exact fun a₁ a₂ a ↦ a
}


def wedge_commutes: Y ⋁ Z ≃ₜ Z ⋁ Y where
  toFun:= wedge_swap Y Z
  continuous_toFun := continuous_wedge_swap Y Z
  invFun:= wedge_swap Z Y
  continuous_invFun := continuous_wedge_swap Z Y
  left_inv:= by {
    let _hwedge := wedge_setoid Y Z
    let _hwedge' := wedge_setoid Z Y
    simp[LeftInverse]
    intro x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw[← hx']
    induction x'
    case inl y => {
      rw[wedge_swap_inl Y Z y]
      rw[wedge_swap_inr]
    }
    case inr z => {
      rw[wedge_swap_inr, wedge_swap_inl]
    }
  }
  right_inv:= by {
    simp[Function.RightInverse, LeftInverse]
    intro x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw[← hx']
    induction x'
    case inl y => {
      rw[wedge_swap_inl, wedge_swap_inr]
    }
    case inr z => {
      rw[wedge_swap_inr, wedge_swap_inl]
    }
  }



--"The wedge product is the coproduct in pointed topological spaces"
variable {Y Z} in
def wedge_induced {W: Type*} [TopologicalSpace W] [Inhabited W] {f: Y → W} {g: Z → W} (hf: f default = default) (hg: g default = default) : Y ⋁ Z → W := by {
  let _ := wedge_setoid Y Z
  let sum_map : Y ⊕ Z → W := fun
    | .inl y => f y
    | .inr z => g z
  apply Quotient.lift sum_map
  intro a b hab
  have : (wedge_setoid Y Z).r a b := hab
  simp[wedge_setoid, quotient_setoid_equiv_iff] at this
  induction a
  case inl ya => {
    induction b
    case inl yb => {
      simp at this
      obtain hc1|hc2:= this
      · simp[hc1]
      · simp[hc2]
    }
    case inr zb => {
      simp at this
      simp[this, hf, hg]
    }
  }
  case inr za => {
    induction b
    case inl yb => {
      simp at this
      simp[this, hf, hg]
    }
    case inr zb => {
      simp at this
      obtain hc1|hc2:= this
      · simp[hc1]
      · simp[hc2]
    }
  }
}


variable {Y Z} in
lemma continuous_wedge_induced {W: Type*} [TopologicalSpace W] [Inhabited W] {f: Y → W} {g: Z → W} {hf: f default = default} {hg: g default = default} (hf2: Continuous f) (hg2: Continuous g) : Continuous (wedge_induced hf hg) := by{
  apply Continuous.quotient_lift
  simp [continuous_sum_dom]
  constructor
  · exact hf2
  · exact hg2
}

variable {Y Z} in
lemma pointed_wedge_induced {W: Type*} [TopologicalSpace W] [Inhabited W] {f: Y → W} {g: Z → W} {hf: f default = default} {hg: g default = default} : wedge_induced hf hg default = default := by{
  let _ := wedge_setoid Y Z
  have : (default : Y ⋁ Z) = Quotient.mk (wedge_setoid Y Z) (Sum.inl (default:Y)) := rfl
  rw[this]
  simp[wedge_induced, Quotient.lift_mk]
  exact hf
}


def wedge_inl : Y → Y ⋁ Z := (Quotient.mk (wedge_setoid Y Z)) ∘ Sum.inl
def wedge_inr : Z → Y ⋁ Z := (Quotient.mk (wedge_setoid Y Z)) ∘ Sum.inr

lemma continuous_wedge_inl : Continuous (wedge_inl Y Z) := by{
  apply Continuous.comp
  · exact continuous_coinduced_rng
  · exact continuous_inl
}

lemma continuous_wedge_inr : Continuous (wedge_inr Y Z) := by{
  apply Continuous.comp
  · exact continuous_coinduced_rng
  · exact continuous_inr
}

lemma pointed_wedge_inl: wedge_inl Y Z default = default := by{
  simp[wedge_inl]
  rfl
}

lemma pointed_wedge_inr: wedge_inr Y Z default = default := by{
  simp[wedge_inr]
  rw[← wedge_defaults_equiv]
  rfl
}


--Show that Y ≃ₜ⋆  W implies Y ⋁ Z ≃ₜ⋆  W ⋁ Z
def homeo_wedge_swap {W: Type*} [TopologicalSpace W] [Inhabited W] (f: Y ≃ₜ⋆ W) : Y ⋁ Z ≃ₜ⋆ W ⋁ Z  where
  toFun:= by{
    apply @wedge_induced Y _ Z _ (W ⋁ Z) _ _ ((wedge_inl W Z) ∘ f.toFun) (wedge_inr W Z) ?_ ?_
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
      · exact continuous_wedge_inl W Z
      · exact f.continuous_toFun
    · exact continuous_wedge_inr W Z
  }

  invFun:= by{
    apply @wedge_induced W _ Z _ (Y ⋁ Z) _ _ ((wedge_inl Y Z) ∘ f.invFun) (wedge_inr Y Z) ?_ ?_
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
      · exact continuous_wedge_inl Y Z
      · exact f.continuous_invFun
    · exact continuous_wedge_inr Y Z
  }

  left_inv:= by {
    let _ := wedge_setoid Y Z
    let _ := wedge_setoid W Z
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
    let _ := wedge_setoid Y Z
    let _ := wedge_setoid W Z
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
    let _ := wedge_setoid Y Z
    dsimp
    simp[wedge_induced]
    have : (default: Y ⋁ Z) = Quotient.mk (wedge_setoid Y Z) (Sum.inl (default:Y)) := rfl
    rw[this]
    simp[Quotient.lift_mk]
    have hf:= f.pointed_toFun
    dsimp at hf
    rw[hf]
    exact pointed_wedge_inl W Z
  }



-- Show that there is an embedding of the wedge product inside the topological product X × Y
-- THIS CAN PROBABLY BE REWRITTEN USING THE COPRODUCT PROPERTY ABOVE
def coprod_prod_map : Y ⊕ Z → Y × Z := fun
  | .inl y => (y, (default:Z))
  | .inr z => ((default:Y), z)

lemma coprod_prod_map_cont: Continuous (coprod_prod_map Y Z) := by {
  simp[coprod_prod_map, continuous_sum_dom]
  constructor
  · constructor
    · apply continuous_id
    · apply continuous_const
  · constructor
    · apply continuous_const
    · apply continuous_id
}


def wedge_embedding : Y ⋁ Z → Y × Z := by {
  apply Quotient.lift (coprod_prod_map Y Z)
  intro a b hab
  have hab2 : (wedge_setoid Y Z).r a b := hab

  induction a
  case inl ya => {
    induction b
    case inl yb => {
      simp[coprod_prod_map]
      simp[quotient_setoid_equiv_iff] at hab2
      obtain hc1|hc2 := hab2
      · calc
        ya = default := hc1.1
        _ = yb := by{symm; exact hc1.2}
      · assumption
    }
    case inr zb => {
      simp[coprod_prod_map]
      simp[quotient_setoid_equiv_iff] at hab2
      tauto
    }
  }
  case inr za => {
    induction b
    case inl yb => {
      simp[coprod_prod_map]
      simp[quotient_setoid_equiv_iff] at hab2
      tauto
    }
    case inr zb => {
      simp[coprod_prod_map]
      simp[quotient_setoid_equiv_iff] at hab2
      obtain hc1|hc2 := hab2
      · calc
        za = default := hc1.1
        _ = zb := by{symm; exact hc1.2}
      · assumption
    }
  }
}

-- prove this is an embedding
lemma wedge_embedding_cont: Continuous (wedge_embedding Y Z) := by{
  apply Continuous.quotient_lift
  exact coprod_prod_map_cont Y Z
}


lemma wedge_embedding_inducing: Inducing (wedge_embedding Y Z) := by{
  let _ := wedge_setoid Y Z
  rw[inducing_iff]
  refine TopologicalSpace.ext_iff.mpr ?left.a
  intro A
  constructor
  · intro hA
    apply isOpen_induced_iff.mpr
    let A' := (Quotient.mk (wedge_setoid Y Z))⁻¹' A
    let B := Sum.inl⁻¹' A'
    let C := Sum.inr⁻¹' A'
    have hApre: IsOpen B ∧ IsOpen C := hA
    by_cases hcase: default ∈ A
    · use B ×ˢ C
      constructor
      · exact IsOpen.prod hApre.1 hApre.2
      · ext x
        constructor
        · intro hx
          rw[Set.mem_preimage] at hx
          obtain ⟨x', hx'⟩ := Quotient.exists_rep x
          rw[← hx'] at hx
          induction x'
          case inl y => {
            simp[wedge_embedding, coprod_prod_map] at hx
            rw[← hx']
            exact hx.1
          }
          case inr z => {
            simp[wedge_embedding, coprod_prod_map] at hx
            rw[← hx']
            exact hx.2
          }
        · intro hx
          rw[Set.mem_preimage]
          obtain ⟨x', hx'⟩ := Quotient.exists_rep x
          rw[← hx']
          induction x'
          case inl y => {
            simp[wedge_embedding, coprod_prod_map]
            constructor
            · exact mem_of_eq_of_mem hx' hx
            · rw[← wedge_defaults_equiv]
              exact hcase
          }
          case inr z => {
            simp[wedge_embedding, coprod_prod_map]
            constructor
            · exact hcase
            · exact mem_of_eq_of_mem hx' hx
          }
    · use B ×ˢ univ ∪ univ ×ˢ C
      constructor
      · apply IsOpen.union
        · exact IsOpen.prod hApre.1 isOpen_univ
        · exact IsOpen.prod isOpen_univ hApre.2
      · ext x
        constructor
        · intro hx
          rw[Set.mem_preimage] at hx
          obtain ⟨x', hx'⟩ := Quotient.exists_rep x
          rw[← hx'] at hx
          induction x'
          case inl y => {
            simp[wedge_embedding, coprod_prod_map] at hx
            obtain hx1|hx2 := hx
            · exact mem_of_eq_of_mem (id hx'.symm) hx1
            · have : default ∈ A := by {
                rw[← wedge_defaults_equiv] at hx2
                exact hx2
                }
              contradiction
          }
          case inr z => {
            simp[wedge_embedding, coprod_prod_map] at hx
            obtain hx1|hx2 := hx
            · have : default ∈ A := by exact hx1
              contradiction
            · exact mem_of_eq_of_mem (id hx'.symm) hx2
          }
        · intro hx
          rw[Set.mem_preimage]
          obtain ⟨x', hx'⟩ := Quotient.exists_rep x
          rw[← hx']
          induction x'
          case inl y => {
            simp[wedge_embedding, coprod_prod_map]
            left
            exact mem_of_eq_of_mem hx' hx
          }
          case inr z => {
            simp[wedge_embedding, coprod_prod_map]
            right
            exact mem_of_eq_of_mem hx' hx
          }
  · have hcont : Continuous (wedge_embedding Y Z) := wedge_embedding_cont Y Z
    intro hA
    rw[isOpen_induced_iff] at hA
    obtain ⟨B, hB1, hB2⟩ := hA
    have that := IsOpen.preimage hcont hB1
    rw[hB2] at that
    assumption
}

lemma wedge_embedding_pointed: wedge_embedding Y Z default = default := by{
  let _:= wedge_setoid Y Z
  simp[wedge_embedding]
  have: (default: Y ⋁ Z) = Quotient.mk (wedge_setoid Y Z) (Sum.inl (default:Y)) := rfl
  rw[this]
  simp[Quotient.lift_mk, coprod_prod_map]
  rfl
}


theorem wedge_embeds_into_product: Embedding (wedge_embedding Y Z) := by{
  let _hwedge := wedge_setoid Y Z
  rw[embedding_iff]
  constructor
  --induced topology
  · exact wedge_embedding_inducing Y Z

  --injectivity
  · intro a b hab
    rw[wedge_embedding] at hab
    obtain ⟨a', ha'⟩ := Quotient.exists_rep a
    obtain ⟨b', hb'⟩:= Quotient.exists_rep b
    rw[← ha', ← hb'] at hab
    have hab' : (coprod_prod_map Y Z) a' = (coprod_prod_map Y Z) b' := hab
    rw[← ha', ← hb']
    induction a'
    case inl ya => {
      induction b'
      case inl yb =>{
        simp[coprod_prod_map] at hab'
        rw[hab']
      }
      case inr zb =>{
        simp[coprod_prod_map] at hab'
        have : (wedge_setoid Y Z).r (Sum.inl ya) (Sum.inr zb) := by {
          simp[quotient_setoid_equiv_iff]
          tauto
        }
        rw [Quotient.eq]
        exact this
      }
    }
    case inr za => {
      induction b'
      case inl yb =>{
        simp[coprod_prod_map] at hab'
        rw[Quotient.eq]
        have: (wedge_setoid Y Z).r (Sum.inr za) (Sum.inl yb) := by {
          simp[quotient_setoid_equiv_iff]
          tauto
        }
        exact this
      }
      case inr zb =>{
        simp[coprod_prod_map] at hab'
        rw[hab']
      }
    }
}

--if something is in the image of the wedge embedding, then at least one of its coordinates is default
lemma wedge_embedding_ran {x: Y × Z} (h: x ∈ range (wedge_embedding Y Z)) : x.1=default ∨ x.2=default := by{
  let _:= wedge_setoid Y Z
  simp at h
  obtain ⟨t, ht⟩:= h
  obtain ⟨t', ht'⟩:= Quotient.exists_rep t
  induction t'
  case inl y => {
    right
    rw[← ht'] at ht
    have : x = (y, default) := by {
      rw[← ht]
      simp[wedge_embedding, coprod_prod_map]
    }
    simp[this]
  }
  case inr z => {
    left
    rw[← ht'] at ht
    have : x = (default, z) := by{
      rw[← ht]
      simp[wedge_embedding, coprod_prod_map]
    }
    simp[this]
  }
}

lemma wedge_embedding_inl (y:Y) : wedge_embedding Y Z (wedge_inl Y Z y) = (y, default) := by{
  let _:= wedge_setoid Y Z
  simp[wedge_embedding, wedge_inl, coprod_prod_map]
}

lemma wedge_embedding_inr (z:Z) : wedge_embedding Y Z (wedge_inr Y Z z) = (default, z) := by{
  let _:= wedge_setoid Y Z
  simp[wedge_embedding, wedge_inr, coprod_prod_map]
}

-- define smash products
def smashsetoid : Setoid (Y × Z) := by{
  let A : Set (Y × Z) := wedge_embedding Y Z '' univ
  exact quotient_setoid A
}

def Smash := Quotient (smashsetoid Y Z)
instance: TopologicalSpace (Smash Y Z) := by exact instTopologicalSpaceQuotient
instance: Inhabited (Smash Y Z) where
  default:= Quotient.mk (smashsetoid Y Z) (default, default)

infix:50 " ⋀  " => Smash

variable {Y Z} in
def smash_elt (y:Y) (z:Z) : Y ⋀ Z := Quotient.mk (smashsetoid Y Z) (y,z)

infix:50 " ∧' " => smash_elt


variable {Y Z} in
lemma smash_elt_eq_iff (y y' :Y) (z z':Z) : (smash_elt y z = smash_elt y' z') ↔ ( (y=default ∨ z=default) ∧ (y'=default ∨ z'=default) )∨ ( (y,z) = (y', z') ) := by{
  let _:= smashsetoid Y Z
  let _:= wedge_setoid Y Z
  simp[smash_elt]
  constructor
  · intro h
    have : (smashsetoid Y Z).r (y,z) (y', z') := by exact Quotient.eq'.mp h
    simp[quotient_setoid_equiv_iff] at this
    obtain hc1|hc2 := this
    · left
      obtain ⟨h1, h2⟩:= hc1
      have h1':= wedge_embedding_ran Y Z h1
      have h2':= wedge_embedding_ran Y Z h2
      tauto
    · rw[hc2.1, hc2.2]
      tauto
  · intro h
    have : (smashsetoid Y Z).r (y,z) (y', z') := by {
      obtain hc1|hc2:= h
      · simp[quotient_setoid_equiv_iff]
        left
        constructor
        · obtain hd1|hd2:= hc1.1
          · rw[hd1]
            use wedge_inr Y Z z
            simp [wedge_embedding, wedge_inr, coprod_prod_map]
          · rw[hd2]
            use wedge_inl Y Z y
            simp [wedge_embedding, wedge_inl, coprod_prod_map]
        · obtain hd1|hd2:= hc1.2
          · rw[hd1]
            use wedge_inr Y Z z'
            simp [wedge_embedding, wedge_inr, coprod_prod_map]
          · rw[hd2]
            use wedge_inl Y Z y'
            simp [wedge_embedding, wedge_inl, coprod_prod_map]
      · rw[hc2.1, hc2.2]
        exact Quotient.eq'.mp rfl
    }
    exact Quotient.eq.mpr this
}

@[simp] theorem smash_defaults_left (y:Y) : (y ∧' (default:Z)) = default := by{
  have : (default: Y ⋀ Z) = (default ∧' default) := rfl
  rw[this]
  simp[smash_elt_eq_iff]
}

@[simp] theorem smash_defaults_right (z:Z) : ((default:Y) ∧' z) = default := by{
  have : (default: Y ⋀ Z) = (default ∧' default) := rfl
  rw[this]
  rw[smash_elt_eq_iff]
  left
  simp
}

--show that there is a pointed isomorphism Y ⋀ Z ≃ₜ Z ⋀ Y

def prod_swap : Y × Z → Z × Y := fun (y,z) ↦ (z,y)

lemma prod_swap_cont: Continuous (prod_swap Y Z) := by {
  simp[prod_swap]
  constructor
  · continuity
  · continuity
}

lemma prod_swap_wedge: (prod_swap Y Z) ∘ (wedge_embedding Y Z) = (wedge_embedding Z Y) ∘ (wedge_swap Y Z) := by{
  let _:= wedge_setoid Y Z
  let _:= wedge_setoid Z Y
  ext v
  · obtain ⟨x, hx⟩ := Quotient.exists_rep v
    rw[← hx]
    induction x
    case inl y => {
      simp[prod_swap, wedge_embedding, wedge_swap, Quotient.lift_mk, coprod_prod_map]
    }
    case inr z => {
      simp[prod_swap, wedge_embedding, wedge_swap, Quotient.lift_mk, coprod_prod_map]
    }
  --this is just a copy of the proof of the first goal
  · obtain ⟨x, hx⟩ := Quotient.exists_rep v
    rw[← hx]
    induction x
    case inl y => {
      simp[prod_swap, wedge_embedding, wedge_swap, Quotient.lift_mk, coprod_prod_map]
    }
    case inr z => {
      simp[prod_swap, wedge_embedding, wedge_swap, Quotient.lift_mk, coprod_prod_map]
    }
}

def smash_swap : Y ⋀ Z → Z ⋀ Y := by{
  let _:= smashsetoid Y Z
  let _:= smashsetoid Z Y
  apply Quotient.lift ( (Quotient.mk (smashsetoid Z Y) )∘ (prod_swap Y Z))
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
        have : wedge_embedding Z Y (wedge_swap Y Z c) = ((wedge_embedding Z Y) ∘ (wedge_swap Y Z)) c := rfl
        rw [this, ← prod_swap_wedge Y Z, Function.comp, hc]
        simp[prod_swap]
      · use wedge_swap _ _ d
        have : wedge_embedding Z Y (wedge_swap Y Z d) = ((wedge_embedding Z Y) ∘  (wedge_swap Y Z)) d := rfl
        rw [this, ← prod_swap_wedge Y Z, Function.comp, hd]
        simp[prod_swap]
    · right
      rw[hc2]
  }
  exact Quotient.eq.mpr this
}

lemma continuous_smash_swap: Continuous (smash_swap Y Z) := by{
  apply Continuous.quotient_lift
  apply Continuous.comp
  · apply continuous_quot_mk
  · exact prod_swap_cont Y Z
}

variable{Y Z} in
lemma swap_pair (y:Y) (z:Z) : smash_swap Y Z (y ∧' z) = (z ∧' y) := by {
  let _:= smashsetoid Y Z
  let _:= smashsetoid Z Y
  simp[smash_swap, smash_elt, Quotient.lift_mk, prod_swap]
}

lemma pointed_smash_swap: (smash_swap Y Z) default = default := by{
  have h1 : (default : Y ⋀ Z)  = (default ∧' default) := rfl
  have h2 : (default : Z ⋀ Y)  = (default ∧' default) := rfl
  rw[h1, h2, swap_pair]
}


variable {Y Z} in
lemma swap_swap (x: Y ⋀ Z) : smash_swap Z Y (smash_swap Y Z x) = x := by{
  obtain ⟨v, hv⟩:= Quotient.exists_rep x
  have : x = ((v.1) ∧' (v.2)) := by {
    simp[hv, smash_elt]
  }
  rw[this]
  simp[swap_pair]
}

def homeo_smash_swap: Y ⋀ Z ≃ₜ⋆ Z ⋀ Y where
  toFun := smash_swap Y Z
  continuous_toFun := continuous_smash_swap Y Z
  invFun := smash_swap Z Y
  continuous_invFun := continuous_smash_swap Z Y

  left_inv := by{
    rw[LeftInverse]
    intro x
    exact swap_swap x
  }
  right_inv := by{
    rw[Function.RightInverse, LeftInverse]
    intro x
    exact swap_swap x
  }

  pointed_toFun := pointed_smash_swap Y Z



--Show that Y ≃ₜ⋆  W → Y ⋀ Z ≃ₜ⋆  W ⋀ Z
variable (W:Type*) [TopologicalSpace W] [Inhabited W]
variable (W':Type*) [TopologicalSpace W'] [Inhabited W']

section smashmaps
variable {Y Z W W'}


def prod_maps (f: Y → W) (g: Z → W') : Y × Z → W × W' := fun (y, z) ↦ (f y, g z)

variable {f: Y → W}
variable {g: Z → W'}
variable (hf: f default = default)
variable (hg: g default = default)


def smash_maps : Y ⋀ Z → W ⋀ W' := by {
  let _:= smashsetoid Y Z
  let _:= smashsetoid W W'
  apply Quotient.lift ( (Quotient.mk (smashsetoid W W') )∘ (prod_maps f g))
  intro a b hab
  simp[prod_maps]
  have: Setoid.r a b := hab
  simp[quotient_setoid_equiv_iff] at this
  obtain hc1| hc2 := this
  · obtain ⟨ha, hb⟩:= hc1
    have ha' : a.1 = default ∨ a.2 = default := wedge_embedding_ran Y Z ha
    have hb' : b.1 = default ∨ b.2 = default := wedge_embedding_ran Y Z hb
    have : Setoid.r (f a.1, g a.2) (f b.1, g b.2) := by{
      simp[quotient_setoid_equiv_iff]
      left
      constructor
      · obtain hal|har := ha'
        · use wedge_inr W W' (g a.2)
          rw[hal, hf]
          apply wedge_embedding_inr
        · use wedge_inl W W' (f a.1)
          rw[har, hg]
          apply wedge_embedding_inl
      · obtain hbl|hbr := hb'
        · use wedge_inr W W' (g b.2)
          rw[hbl, hf]
          apply wedge_embedding_inr
        · use wedge_inl W W' (f b.1)
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
  let _:= smashsetoid Y Z
  let _:= smashsetoid W W'
  simp[smash_maps]
  have : (default: Y ⋀ Z) = Quotient.mk (smashsetoid Y Z) (default, default) := rfl
  rw[this, Quotient.lift_mk]
  simp[prod_maps, hf, hg]
  symm
  rfl
}


lemma smash_maps_comp {W₁ W₂: Type*} [TopologicalSpace W₁] [Inhabited W₁] [TopologicalSpace W₂] [Inhabited W₂] {f': W → W₁} {g': W' → W₂} (hf': f' default = default) (hg': g' default = default) (x: Y ⋀ Z) : smash_maps hf' hg' (smash_maps hf hg x) = @smash_maps _ _ _ _ _ _ _ _ (f' ∘ f) (g' ∘g) (by simp[hf, hf']) (by simp[hg, hg']) x := by{
  let _:= smashsetoid Y Z
  let _:= smashsetoid W W'
  let _:= smashsetoid W₁ W₂
  simp[smash_maps]
  obtain ⟨x', hx'⟩:= Quotient.exists_rep x
  rw[←hx']
  simp[Quotient.lift_mk]
  simp[prod_maps]
}

end smashmaps

variable (k: Y ≃ₜ⋆ W)

variable{Y W} in
def wedge_compare : Y ⋀ Z → W ⋀ Z := by {
  apply @smash_maps _ _ _ _ _ _ _ _ k.toFun id
  · exact k.pointed_toFun
  · simp
}

variable{Y W} in
lemma continuous_wedge_compare : Continuous (wedge_compare Z k) := by{
  rw[wedge_compare]
  apply continuous_smash_maps
  · exact k.continuous_toFun
  · exact continuous_id
}

variable{Y W} in
lemma pointed_wedge_compare : (wedge_compare Z k) default = default := by {
  simp[wedge_compare]
  apply pointed_smash_maps
}


def homeo_wedge_compare : Y ⋀ Z ≃ₜ⋆ W ⋀ Z where
  toFun := wedge_compare Z k
  continuous_toFun := continuous_wedge_compare Z k
  invFun := wedge_compare Z (PointedHomeo.symm k)
  continuous_invFun := continuous_wedge_compare Z (PointedHomeo.symm k)

  left_inv := by{
    let _:=smashsetoid Y Z
    let _:= smashsetoid W Z
    simp[LeftInverse]
    intro x
    simp[wedge_compare]
    simp [smash_maps_comp, PointedHomeo.symm, smash_maps]
    obtain ⟨x', hx'⟩:= Quotient.exists_rep x
    rw[← hx']
    simp[Quotient.lift_mk, prod_maps]
  }
  right_inv := by{
    let _:=smashsetoid Y Z
    let _:= smashsetoid W Z
    simp[Function.RightInverse, LeftInverse]
    intro x
    simp[wedge_compare]
    simp [smash_maps_comp, PointedHomeo.symm, smash_maps]
    obtain ⟨x', hx'⟩:= Quotient.exists_rep x
    rw[← hx']
    simp[Quotient.lift_mk, prod_maps]
  }

  pointed_toFun := pointed_wedge_compare Z k



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

  sorry --shouldn't this be a lemma from the library?
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

  simp[wrap, default]
  --shouldn't this now be rfl?
  sorry
}

#check EuclideanSpace.single

-- Now, this will allow me to say that by a previous lemma Y ⋀ S¹ ≃ₜ Y ⋀ J
lemma smash_circle_J_equiv : Y ⋀ (𝕊 1) ≃ₜ Y ⋀ J := by sorry


lemma pointed_smash_circle_J_equiv : smash_circle_J_equiv Y default = default := by sorry


-- Now I can show that Y ⋀ J ≃ₜ Σ₀ Y

def prod_to_wedge : (Y × I) → (Y ⋀ J) := fun (y, t) ↦ smash_elt y (Quotient.mk I_quotient t)

lemma continuous_prod_to_wedge: Continuous (prod_to_wedge Y) := by sorry

def sus_to_wedge : Σ₀ Y → (Y ⋀ J) := by{
  let _:= basedsuspension_setoid Y
  apply Quotient.lift (prod_to_wedge Y)
  intro a b hab
  have : (basedsuspension_setoid Y).r a b := hab
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

lemma continuous_sus_to_wedge : Continuous (sus_to_wedge Y) := by{
  apply Continuous.quotient_lift
  exact continuous_prod_to_wedge Y
}

-- Pointed etc


--Finally, compose to get
--[ TODO ] show Y ⋀ S¹ ≃ₜ⋆  Σ₀ Y (Hatcher page 12)




--[ TODO ] adjunction Top_* (Y ⋀ Z, W) ≃ Top_* (Y, Top_* (Z,W)) for Z locally compact
section adjunction
/-
Ideally, this should be a categorical statement: the functor Hom(Z,-) is right adjoint to -⋀ Z
in pointed topological spaces. I haven't framed pointed spaces as a category, see eg
    mathlib4/Mathlib/CategoryTheory/Category/Pointed.lean
for general pointed types.
I think the bulk of the proof is what I'm doing now and it can all be polished up at a later stage
-/

/-The unpointed version of the map we want is already in Mathlib as ContinuousMap.curry
  This is why ours will be called PointedMap.curry -/

variable [LocallyCompactSpace Z]
instance : TopologicalSpace C⋆(Z,W) := PointedMap.compactOpen Z W
instance : Inhabited C⋆(Z,W) where
  default := PointedMap.trivial Z W


namespace PointedMap
variable {Y Z W}
/- Much of the following (up to end PointedMap) is adapted from mathlib4/Mathlib/Topology/CompactOpen.lean by Reid Barton, starting on line 364 -/

/-- Auxiliary definition, see `PointedMap.curry`. -/
def curry' (f : C⋆(Y ⋀ Z, W)) (y : Y) : C⋆(Z, W) where
  toFun := Function.curry (f ∘ Quotient.mk (smashsetoid Y Z)) y
  continuous_toFun := by {
    apply Continuous.comp
    · apply Continuous.comp
      · exact map_continuous f
      · exact continuous_quot_mk
    · exact Continuous.Prod.mk y
  }
  pointed_toFun := by{
    simp
    have : Quotient.mk (smashsetoid Y Z) (y, default) = ( y ∧' default) := rfl
    simp[this]
  }

  /-- If a map `X ⋀ Y → Z` is continuous, then its curried form `X → C⋆(Y, Z)` is continuous. -/
theorem continuous_curry' (f : C⋆(Y ⋀ Z, W)) : Continuous (curry' f) := by{
  --apply Continuous.comp
  sorry
}



--Continuous.comp (continuous_comp f) continuous_coev

theorem pointed_curry' (f : C⋆(Y ⋀ Z, W)) : (curry' f) default = default := by{
  simp[curry']
  ext z
  -- Don't I have a simp lemma that simplifies this further??? Shouldn't this be just simp now?
  sorry
}

-- [TO FIX] Variables are a mess now. Documentation strings have the correct one, and code lines have one shifted. Exercise caution.

/-- The curried form of a pointed continuous map `X ⋀ Y → Z` as a pointed continuous map `X → C⋆(Y, Z)`.
    If `Y` is locally compact, this is a bijection and carries an adjunction of functors `- ⋀ Y  ⊣ C⋆(Y, -)` . -/
def curry (f : C⋆(Y ⋀ Z, W)) : C⋆(Y, C⋆(Z, W)) where
  continuous_toFun:= continuous_curry' f
  pointed_toFun:= pointed_curry' f

@[simp]
theorem curry_apply (f : C⋆(Y ⋀ Z, W)) (y : Y) (z : Z) : f.curry y z = f (y ∧'z) :=
  rfl



/- ORIGINAL FILE FOR Continuous.curry: NOT MY CODE!!!


/-- To show continuity of a map `X → C(Y, Z)`, it suffices to show that its uncurried form
    `X × Y → Z` is continuous. -/
theorem continuous_of_continuous_uncurry (f : X → C(Y, Z))
    (h : Continuous (Function.uncurry fun x y => f x y)) : Continuous f :=
  continuous_curry' ⟨_, h⟩





/-- The currying process is a continuous map between function spaces. -/
theorem continuous_curry [LocallyCompactSpace (X × Y)] :
    Continuous (curry : C(X × Y, Z) → C(X, C(Y, Z))) := by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).symm.comp_continuous_iff']
  exact continuous_eval


/-- The uncurried form of a continuous map `X → C(Y, Z)` is a continuous map `X × Y → Z`. -/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) :
    Continuous (Function.uncurry fun x y => f x y) :=
  continuous_eval.comp <| f.continuous.prod_map continuous_id


/-- The uncurried form of a continuous map `X → C(Y, Z)` as a continuous map `X × Y → Z` (if `Y` is
    locally compact). If `X` is also locally compact, then this is a homeomorphism between the two
    function spaces, see `Homeomorph.curry`. -/
@[simps]
def uncurry [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : C(X × Y, Z) :=
  ⟨_, continuous_uncurry_of_continuous f⟩


/-- The uncurrying process is a continuous map between function spaces. -/
theorem continuous_uncurry [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    Continuous (uncurry : C(X, C(Y, Z)) → C(X × Y, Z)) := by
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).comp_continuous_iff']
  apply continuous_eval.comp (continuous_eval.prod_map continuous_id)

-/









-- [ TODO ] Currying is an equivalence


-- [ TODO ] Naturality

end PointedMap

end adjunction

-- [ TODO? ] Do Proposition 1.3 in Cutler's pdf



--prove that the free suspension of 𝕊ⁿ is homeomorphic to 𝕊^{n+1}

lemma target_in_sphere (y : 𝕊 n) (t: I) : @norm (EuclideanSpace ℝ (Fin (n + 1))) SeminormedAddGroup.toNorm (Fin.snoc (fun i ↦ Real.sqrt (1 - (↑t+1)/2 * (↑t+1)/2) * (y.1 i) ) ((↑t +1)/2))  = 1 := by{
  simp[Fin.snoc, EuclideanSpace.norm_eq, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  sorry
}


def cyl_to_sphere: (𝕊 n) × I  → (𝕊 (n+1)) :=
  fun (⟨x, p⟩, t) ↦ ⟨Fin.snoc ( fun i ↦ Real.sqrt (1-((↑t +1)/2)*((↑t +1)/2)) * (x i) ) ((↑t +1)/2) ,  by{simp; exact target_in_sphere n (⟨x, p⟩) t} ⟩


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

Some things about the mapping cone seem to be in Mathlib in abstract nonsense form (I should check more carefully), maybe define mapping cones and show they fit the nonsense?
-/


/-
Possible references to add:
https://ncatlab.org/nlab/show/smash+product
-/

--#lint

end
