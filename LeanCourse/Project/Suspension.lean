import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
open BigOperators Function Set Filter Topology TopologicalSpace

/-
Done:
- Defined quotienting a space with respect to a subspace
- Defined the cylinder X × I of a space
- Defined the free suspension of a space
- Defined the based cylinder and the pointed suspension of a pointed space
- Defined the wedge product Y ⋁ Z of two pointed spaces Y and Z
- Constructed an embedding Y ⋁ Z ↪ Y × Z and showed it is an embedding
- Defined the smash product Y ⋀ Z of two pointed spaces Y and Z
- Started some work on spheres [EXTREMELY BROKEN; NOT IN A DECENT STATE YET]
-/


variable (X: Type*) [TopologicalSpace X]

def quotient_setoid (X': Set X) : Setoid (X) where
  r:= fun x ↦ fun y ↦ (x ∈ X' ∧ y ∈ X') ∨ x=y
  iseqv := {
    refl:= by tauto
    symm := by{
      intros
      tauto
    }
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

lemma quotient_setoid_equiv_iff (X': Set X) (x y : X) : (quotient_setoid X X').r x y ↔ ((x ∈ X' ∧ y ∈ X') ∨ x = y ) := by {
  exact Iff.rfl
}


--define the (non-based) cylinder of X
def Cylinder := X × Icc 0 1

instance : TopologicalSpace (Cylinder X) := instTopologicalSpaceProd


def cyl_setoid : Setoid (Cylinder X) where
  r:= fun x ↦ fun y ↦ ((x.2=y.2 ∧ (x.2=0 ∨ x.2 = 1)) ∨ (x.1=y.1 ∧ x.2=y.2))
  iseqv := {
    refl := by {
      intro x
      simp
    }
    symm := by{
      intro x y hxy
      obtain hc1|hc2 := hxy
      · left
        constructor
        · tauto
        · rw[← hc1.1]
          tauto
      · right
        tauto
    }
    trans := by{
      intro x y z hxy hyz
      obtain hyz1|hyz2 := hyz
      · obtain hxy1|hxy2 := hxy
        · left
          constructor
          · rw[hxy1.1]
            tauto
          · tauto
        · left
          constructor
          · rw[←hyz1.1 ]
            tauto
          · rw[hxy2.2]
            tauto
      · obtain hxy1|hxy2 := hxy
        · left
          constructor
          · rw[hxy1.1]
            tauto
          · tauto

        · right
          simp[hxy2]
          tauto
    }
  }

-- define the (free) suspension of X
def Suspension  := Quotient (cyl_setoid X)
instance : TopologicalSpace (Suspension X) := instTopologicalSpaceQuotient

notation (priority:= high) "S" => Suspension
#check S X

variable (Y:Type*) [TopologicalSpace Y] [Inhabited Y]

def pointedcyl : Setoid (Cylinder Y) where
  r:= fun x ↦ fun y ↦ (x.1=default ∧ y.1=default) ∨ (x = y)
  iseqv := {
    refl:= by{
      intros
      simp
    }
    symm := by{
      intros
      tauto
    }
    trans := by{
      intro x y z hxy hyz
      obtain hc1|hc2 := hyz
      · obtain hb1|hb2 := hxy
        · tauto
        · left
          rw[hb2]
          tauto
      · rw[←hc2]
        tauto
    }
  }

--define the pointed cylinder of Y
def PointedCylinder := Quotient (pointedcyl Y)

--show PointedCylinder is a pointed topological space with basepoint * × I
instance : TopologicalSpace (PointedCylinder Y) := instTopologicalSpaceQuotient

instance : Inhabited (PointedCylinder Y) where
  default := Quotient.mk (pointedcyl Y) ((default : Y), 0)

--construct pointed suspension
def pointedsus : Setoid (Cylinder Y) where
  r:= fun x ↦ fun y ↦ ((x.1 = default ∨ x.2=0 ∨ x.2=1)  ∧  (y.1 = default ∨ y.2 = 0 ∨ y.2 =1)) ∨ x=y
  iseqv:= {
    refl := by{
      intros
      simp
    }
    symm := by{
      intros
      tauto
    }
    trans := by{
      intro x y z hxy hyz
      obtain hc1|hc2 := hyz
      · obtain hb1|hb2 := hxy
        · left
          tauto
        · rw[hb2]
          tauto
      · rw[← hc2]
        exact hxy
    }
  }

def BasedSuspension := Quotient (pointedsus Y)
instance : TopologicalSpace (BasedSuspension Y) := instTopologicalSpaceQuotient

instance : Inhabited (BasedSuspension Y) where
  default:= Quotient.mk (pointedsus Y) ((default:Y), 0)

notation (priority:= high) "Σ₀" => BasedSuspension
#check Σ₀ Y


-- define wedge products
variable (Z:Type*) [TopologicalSpace Z] [Inhabited Z]
--#check Sum.inl (default:Y)
instance: TopologicalSpace (Y ⊕ Z) := by infer_instance

def wedgesetoid' : Setoid (Y ⊕ Z) := by{
  let A: Set (Y ⊕ Z) := { x : Y ⊕ Z | x = Sum.inl (default:Y) ∨ x = Sum.inr (default:Z)}
  exact quotient_setoid (Y ⊕ Z) A
}

/-
def wedgerel : (Y ⊕ Z) → (Y ⊕ Z) → Prop := fun
  | .inl val => fun
    | .inl y => y=val
    | .inr z => val=(default:Y) ∧ z=(default:Z)

  | .inr val => fun
    | .inl y => y=(default:Y) ∧ val=(default:Z)
    | .inr z => z=val

def wedgesetoid : Setoid (Y ⊕ Z)  where
  r:= wedgerel Y Z
  iseqv := {
    refl := by {
      intro elt
      induction elt
      case inl y => rfl
      case inr z => rfl
    }

    symm := by{
      intro x1 x2 h
      induction x2
      case inl y2 => {
        induction x1
        case inl y1 => {
          simp[wedgerel] at h
          rw[h]
          rfl
        }
        case inr z1 => {
          simp[wedgerel] at h
          simp [wedgerel]
          assumption
        }
      }
      case inr x2 => {
        induction x1
        case inl y1 => {
          simp[wedgerel] at h
          simp [wedgerel]
          assumption
        }
        case inr z1 => {
          simp [wedgerel] at h
          simp [wedgerel]
          symm
          assumption
        }
      }
    }

    trans := by{
      intro a b c hab hbc
      induction a
      case inl y1 => {
        induction b
        case inl y2 => {
          simp[wedgerel] at hab
          rw[← hab]
          assumption
        }
        case inr z2 => {
          induction c
          case inl y3 => {
            simp [wedgerel]
            simp [wedgerel] at hbc
            simp [wedgerel] at hab
            rw[hbc.1, hab.1]
          }
          case inr z3 => {
            simp [wedgerel]
            simp [wedgerel] at hbc
            simp [wedgerel] at hab
            rw[← hbc] at hab
            assumption
          }
        }
      }
      case inr z1 => {
        induction b
        case inl y2 => {
          induction c
          case inl y3 => {
            simp [wedgerel]
            simp [wedgerel] at hab
            simp [wedgerel] at hbc
            rw[hbc]
            assumption
          }
          case inr z3 => {
            simp [wedgerel]
            simp [wedgerel] at hab
            simp [wedgerel] at hbc
            rw[hbc.2, hab.2]
          }
        }
        case inr z2 => {
          induction c
          case inl y3 => {
            simp [wedgerel]
            simp [wedgerel] at hab
            simp [wedgerel] at hbc
            rw[hab] at hbc
            assumption
          }
          case inr z3 => {
            simp [wedgerel]
            simp [wedgerel] at hab
            simp [wedgerel] at hbc
            rw[hab] at hbc
            assumption
          }
        }
      }
    }
  }
-/

def Wedge := Quotient (wedgesetoid' Y Z)
instance: TopologicalSpace (Wedge Y Z) := by exact instTopologicalSpaceQuotient
instance: Inhabited (Wedge Y Z) where
  default:= Quotient.mk (wedgesetoid' Y Z) (Sum.inl (default:Y))

infix:50 " ⋁ " => Wedge

-- easy lemma for later
lemma wedge_defaults_equiv: Quotient.mk (wedgesetoid' Y Z) (Sum.inl default) = Quotient.mk (wedgesetoid' Y Z) (Sum.inr default) := by{
  let hwedge := wedgesetoid' Y Z
  refine Quotient.eq.mpr ?_
  have : (wedgesetoid' Y Z).r (Sum.inl default) (Sum.inr default) := by{
    simp[quotient_setoid_equiv_iff]
  }
  exact this
}

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

/-
#check Quotient.lift
#check Setoid.eq_iff_rel_eq

instance: Setoid (Y ⊕ Z) := wedgesetoid' Y Z
example (x y: Y ⊕ Z) : x ≈ y ↔ Quotient.mk (wedgesetoid' Y Z) x = Quotient.mk (wedgesetoid' Y Z) y := by {
  simp
}
-/


def wedge_embedding : Y ⋁ Z → Y × Z := by {
  --let hwedge := wedgesetoid' Y Z
  apply Quotient.lift (coprod_prod_map Y Z)
  intro a b hab
  /-have hab' : Quotient.mk (wedgesetoid' Y Z) a = Quotient.mk (wedgesetoid' Y Z) b := by{
    exact Quotient.eq.mpr hab
  }-/
  have hab2 : (wedgesetoid' Y Z).r a b := hab

  induction a
  case inl ya => {
    induction b
    case inl yb => {
      simp[coprod_prod_map]
      --simp[Wedge, Quotient, wedgesetoid', quotient_setoid, quotient_setoid_equiv_iff] at hab'
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
  let hwedge := wedgesetoid' Y Z
  rw[inducing_iff]
  refine TopologicalSpace.ext_iff.mpr ?left.a
  intro A
  constructor
  · intro hA
    apply isOpen_induced_iff.mpr
    let A' := (Quotient.mk (wedgesetoid' Y Z))⁻¹' A
    --have hA' : IsOpen A':= hA
    let B := Sum.inl⁻¹' A'
    let C := Sum.inr⁻¹' A'
    have hApre: IsOpen B ∧ IsOpen C := hA
    --use (B ×ˢ univ) ∪ (univ ×ˢ C)
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
  let hwedge := wedgesetoid' Y Z
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
        have : (wedgesetoid' Y Z).r (Sum.inl ya) (Sum.inr zb) := by {
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
        have: (wedgesetoid' Y Z).r (Sum.inr za) (Sum.inl yb) := by {
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



--define the spheres Sⁿ

variable (n:ℕ)
notation "𝕊" n => Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1

instance: TopologicalSpace (EuclideanSpace ℝ (Fin n)) := by exact UniformSpace.toTopologicalSpace

--???
instance: TopologicalSpace (𝕊 n) := instTopologicalSpaceSubtype

--prove that the free suspension of 𝕊ⁿ is homeomorphic to 𝕊^{n+1}

def suspension_to_sphere: S (𝕊 n) → (𝕊 (n+1)) := fun



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
-/

--#lint
