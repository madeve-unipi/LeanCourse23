import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
open BigOperators Function Set Filter Topology TopologicalSpace

/-
Partial references:
Allen Hatcher, Algebraic Topology. Chapter 0, Operations on Spaces (from page 8, ignoring cell complexes), Example 0.10 (page 12)



Done:
- Defined quotienting a space with respect to a subspace
- Defined the cylinder X × I of a space
- Defined the free suspension of a space
- Defined the suspension of a function [IN PROGRESS]
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

lemma double_quotient_setoid_equiv_iff (A B: Set X) (h: Disjoint A B) (x y : X) : (double_quotient_setoid X h).r x y ↔ ((x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) ∨ x = y) := Iff.rfl


--define the (non-based) cylinder of X
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
instance : TopologicalSpace (Suspension X) := instTopologicalSpaceQuotient

notation (priority:= high) "S" => Suspension

-- define the (free) suspension of a map
def MapTimesI : Cylinder X → Cylinder X' := fun (x,t) ↦ (f x, t)

def MapSuspension : Suspension X → Suspension X' := by {
  apply Quotient.lift ( (Quotient.mk (cyl_setoid X') )∘ (MapTimesI X X' f) )
  intro a b hab
  simp[cyl_setoid, MapTimesI, double_quotient_setoid_equiv_iff]
  sorry
}

--[ TODO ] show that if f is continuous, then so is its suspension
--[ TODO ] show (free) suspension is a functor

--[ TODO ] joins in general???

--define the pointed cylinder of Y
variable (Y:Type*) [TopologicalSpace Y] [Inhabited Y]

def pointedcylinder_setoid : Setoid (Cylinder Y) := by{
  exact quotient_setoid (Cylinder Y) ({x : Cylinder Y | x.1 = default})
}

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

--[ TODO ] Define the pointed suspension functor and show it is a functor

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
  let hwedge := wedge_setoid Y Z
  refine Quotient.eq.mpr ?_
  have : (wedge_setoid Y Z).r (Sum.inl default) (Sum.inr default) := by{
    simp[quotient_setoid_equiv_iff]
  }
  exact this
}

--[ TODO ] define arbitrarily large wedge products
--[ TODO ] show that there is a natural isomorphism X ⋁ Y ≃ Y ⋁ X


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
  --this is listed as an unused variable, but it fails to synthesize instances if I remove it
  let hwedge := wedge_setoid Y Z
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
  let hwedge := wedge_setoid Y Z
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

--[ TODO ] show X ⋀ S¹ ≃ Σ₀ X (Hatcher page 12)

--define the spheres Sⁿ

variable (n:ℕ)
notation "𝕊" n => Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1

instance: TopologicalSpace (EuclideanSpace ℝ (Fin n)) := by exact UniformSpace.toTopologicalSpace

--???
instance: TopologicalSpace (𝕊 n) := instTopologicalSpaceSubtype

--prove that the free suspension of 𝕊ⁿ is homeomorphic to 𝕊^{n+1}

def test_function : Fin 4 → ℝ := fun i ↦ i
#eval test_function 3
--lol


def suspension_to_sphere: (𝕊 n) × (Icc (-1) 1) → (𝕊 (n+1)) := fun (⟨x, p⟩, t) ↦ ⟨(fun i ↦ Real.sqrt (1-t*t) * (x i) ), by{simp; ring}⟩



theorem sphere_suspension: S (𝕊 n) ≃ₜ (𝕊 (n+1)) := by{
  sorry
}



--define the 1-sphere, with basepoint the point (1,0)
def sphere := {x : ℝ × ℝ | x.1^2 + x.2^2 = 1 }

example: (1,0) ∈ sphere := by{
  simp[sphere]
}

instance: TopologicalSpace (sphere) := instTopologicalSpaceSubtype
instance: Inhabited (sphere) where
  default:= ⟨(1,0), by simp[sphere]⟩

def complex_sphere := {z : ℂ | Complex.normSq z =1 }

example: 1 ∈ complex_sphere := by{
  simp[complex_sphere]
}

instance: TopologicalSpace (complex_sphere):= instTopologicalSpaceSubtype
instance: Inhabited (complex_sphere) where
  default:= ⟨1, by simp[complex_sphere]⟩

def sphere_compare : sphere → complex_sphere := fun ⟨(x,y), p⟩ ↦ ⟨x + y * Complex.I, by {simp[complex_sphere]; rw[Complex.normSq_add_mul_I]; simp[sphere] at p; assumption
}⟩

def sphere_compare_inv : complex_sphere → sphere := fun ⟨z, p⟩ ↦ ⟨(z.re, z.im), by {simp[sphere]; simp[complex_sphere, Complex.normSq_apply] at p; rw[←p]; ring}⟩

--Lean's distance on ℝ² is the supremum distance, not the Euclidean one.
--This is no big deal since they are topologically equivalent
lemma plane_distance (x y : ℝ × ℝ): dist x y = max (|x.1-y.1|) (|x.2-y.2|) := rfl

lemma some_inequality {x y z: ℝ} (h1: x^2 + y^2 < z^2) (h2: z > 0) : |x|< z ∧ |y|<z := by {
  by_contra hcontr
  push_neg at hcontr
  by_cases h: |x|<z
  · specialize hcontr h
    have : z^2 ≤ y^2 := by {
      refine (Real.le_sqrt' h2).mp ?_
      rw [Real.sqrt_sq_eq_abs]
      assumption
    }
    have that : z^2 < z^2 := by {
      calc
      z^2 ≤ y^2 := this
      _ ≤ x^2 + y^2 := by{
        refine tsub_le_iff_right.mp ?_
        ring
        exact sq_nonneg x
      }
      _ < z^2 := h1
    }
    exact LT.lt.false that
  · simp at h
    have : z^2 ≤ x^2 := by {
      refine (Real.le_sqrt' h2).mp ?_
      rw [Real.sqrt_sq_eq_abs]
      assumption
    }
    have that: z^2 < z^2 := by {
      calc
      z^2 ≤ x^2 := this
      _ ≤ x^2 + y^2 := by {
        refine tsub_le_iff_left.mp ?_
        ring
        exact sq_nonneg y
      }
      _ < z^2 := h1
    }
    exact LT.lt.false that
}

lemma sphere_compare_cont : Continuous sphere_compare := by{
  refine Metric.continuous_iff.mpr ?_
  intro z₀ ε hε
  use (Real.sqrt 2)*ε
  constructor
  · simp; assumption
  · intro z hz
    simp [dist, Complex.dist_eq_re_im, sphere_compare]
    rw[plane_distance] at hz

}

lemma sphere_compare_inv_cont: Continuous sphere_compare_inv := by {
  refine Metric.continuous_iff.mpr ?_
  intro z₀ ε hε
  --the minimal choice is something like ε/sqrt2
  use ε
  constructor
  · assumption
  · intro z hz
    simp[sphere_compare_inv, dist]
    simp [dist, Complex.dist_eq_re_im] at hz
    rw[plane_distance]
    simp
    have hz': ((z:ℂ).re - (z₀:ℂ).re)^2 + ((z:ℂ).im - (z₀:ℂ).im)^2 < ε^2 := (Real.sqrt_lt' hε).mp hz
    exact some_inequality hz' hε
}

instance: Homeomorph sphere complex_sphere where
  toFun := sphere_compare
  invFun := sphere_compare_inv
  left_inv := by{
    intro x
    simp[sphere_compare, sphere_compare_inv]
  }
  right_inv := by{
    intro x
    simp[sphere_compare, sphere_compare_inv]
  }
  continuous_toFun := sphere_compare_cont
  continuous_invFun := sphere_compare_inv_cont

-- add inhabited part; this is a pointed homeomorphism

/- Ideal, partial todo list:
-- suspension as smashing with S^1
-- suspension of S^n is S^{n+1}
-- adjunction with loop (depending on difficulty, either the smash version or just the suspension version)
-- time permitting, more related and basic topological things that are missing

Some things about the mapping cone seem to be in Mathlib in abstract nonsense form (I should check more carefully), maybe define mapping cones and show they fit the nonsense?
-/

--#lint
