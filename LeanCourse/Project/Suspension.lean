import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
open BigOperators Function Set Filter Topology TopologicalSpace CategoryTheory

noncomputable section

/-
Partial references:
Allen Hatcher, Algebraic Topology. Chapter 0, Operations on Spaces (from page 8, ignoring cell complexes), Example 0.10 (page 12)



Done:
- Defined quotienting a space with respect to a subspace
- Defined the cylinder X × I of a space
- Defined the free suspension of a space
- Defined the suspension of a function
- Defined the based cylinder and the pointed suspension of a pointed space
- Defined the wedge product Y ⋁ Z of two pointed spaces Y and Z
- Constructed an embedding Y ⋁ Z ↪ Y × Z and showed it is an embedding
- Defined the smash product Y ⋀ Z of two pointed spaces Y and Z
- Started some work on spheres [EXTREMELY BROKEN; NOT IN A DECENT STATE YET]
-/


variable (X: Type*) [TopologicalSpace X]
variable (X': Type*) [TopologicalSpace X']
variable (f: X → X')


--define the setoid to construct the quotient space X/A
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

lemma quotient_setoid_equiv_iff (A: Set X) (x y : X) : (quotient_setoid X A).r x y ↔ ((x ∈ A ∧ y ∈ A) ∨ x = y ) := by {
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

lemma double_quotient_setoid_equiv_iff {A B: Set X} (h: Disjoint A B) (x y : X) : (double_quotient_setoid X h).r x y ↔ ((x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) ∨ x = y) := Iff.rfl


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
  exact double_quotient_setoid (Cylinder X) h
}

-- define the (free) suspension of X
def Suspension  := Quotient (cyl_setoid X)
instance : TopologicalSpace (Suspension  X) := instTopologicalSpaceQuotient

notation (priority:= high) "S" => Suspension

-- define the (free) suspension of a map
def MapTimesI : Cylinder X → Cylinder X' := fun x ↦ (f (x.1), x.2)


def MapSuspension {X: Type*} {X': Type*} [TopologicalSpace X] [TopologicalSpace X'] (f:X → X') : Suspension  X → Suspension  X' := by {
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
lemma mapsuspension_cont {f: X → X'} (hf: Continuous f) : Continuous (MapSuspension f) := by{
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
    | .mk f continuous_f => .mk (MapSuspension f) (mapsuspension_cont _ _ continuous_f)
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
  exact quotient_setoid (Cylinder Y) ({x : Cylinder Y | x.1 = default})
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
  exact quotient_setoid (Cylinder Y) (A ∪ B ∪ C)
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
  exact quotient_setoid (Y ⊕ Z) A
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
--[ TODO ] show that there is a natural homeomorphism X ⋁ Y ≃ Y ⋁ X
--[ TODO ] show that X ≃ X'→ X ⋁ Y ≃ X' ⋁ Y


-- show that there is an embedding of the wedge product inside the topological product X × Y
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


-- define smash products
def smashsetoid : Setoid (Y × Z) := by{
  let A : Set (Y × Z) := wedge_embedding Y Z '' univ
  exact quotient_setoid (Y × Z) A
}

def Smash := Quotient (smashsetoid Y Z)
instance: TopologicalSpace (Smash Y Z) := by exact instTopologicalSpaceQuotient
instance: Inhabited (Smash Y Z) where
  default:= Quotient.mk (smashsetoid Y Z) (default, default)

infix:50 " ⋀  " => Smash

--[ TODO ] show that there is a natural isomorphism X ⋀ Y ≃ Y ⋀ X
--[ TODO ] show that X ≃ X'→ X ⋀ Y ≃ X' ⋀ Y
--[ TODO ] show X ⋀ S¹ ≃ Σ₀ X (Hatcher page 12)

--define the spheres Sⁿ

variable (n:ℕ)
notation "𝕊" n => Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1
noncomputable instance: TopologicalSpace (EuclideanSpace ℝ (Fin n)) := by exact UniformSpace.toTopologicalSpace
instance: TopologicalSpace (𝕊 n) := instTopologicalSpaceSubtype

--prove that the free suspension of 𝕊ⁿ is homeomorphic to 𝕊^{n+1}

lemma target_in_sphere (y : 𝕊 n) (t: I) : @norm (EuclideanSpace ℝ (Fin (n + 1))) SeminormedAddGroup.toNorm (Fin.snoc (fun i ↦ Real.sqrt (1 - (↑t+1)/2) * (↑t+1)/2 * y.1 i) ((↑t +1)/2))  = 1 := by{
  simp[Fin.snoc, EuclideanSpace.norm_eq]
  sorry
}


def cyl_to_sphere: (𝕊 n) × I  → (𝕊 (n+1)) :=
  fun (⟨x, p⟩, t) ↦ ⟨Fin.snoc ( fun i ↦ Real.sqrt (1-((↑t +1)/2)*((↑t +1)/2)) * (x i) ) (↑t +1)/2 ,  by{simp; exact target_in_sphere n (⟨x, p⟩) t} ⟩


def sus_to_sphere: S (𝕊 n) → 𝕊 (n+1) := by{
  apply Quotient.lift (cyl_to_sphere n)
  intro a b hab
  sorry
}


theorem injective_sus_to_sphere : Injective (sus_to_sphere n) := by{
  sorry
}

theorem surjective_sus_to_sphere : Surjective (sus_to_sphere n) := by{
  sorry
}

def sus_to_sphere_equiv : S (𝕊 n) ≃ (𝕊 (n+1)) := by{
  sorry
}

theorem continuous_sus_to_sphere : Continuous (sus_to_sphere_equiv n) := by{
  sorry
}


instance : CompactSpace (Cylinder (𝕊 n)) := instCompactSpaceProdInstTopologicalSpaceProd
instance : CompactSpace (S (𝕊 n)) := Quotient.compactSpace


def sus_to_sphere_homeo: S (𝕊 n)  ≃ₜ (𝕊 (n+1))  := by{
  apply Continuous.homeoOfEquivCompactToT2 (continuous_sus_to_sphere n)
}

-- add inhabited part; this is a pointed homeomorphism


/- Ideal, partial todo list:
-- suspension as smashing with S^1
-- suspension of S^n is S^{n+1}
-- free and reduced suspension are homotopy equivalent (is this even true for all spaces though?)
-- adjunction with loop (depending on difficulty, either the smash version or just the suspension version)
-- time permitting, more related and basic topological things that are missing

Some things about the mapping cone seem to be in Mathlib in abstract nonsense form (I should check more carefully), maybe define mapping cones and show they fit the nonsense?
-/

--#lint

end
