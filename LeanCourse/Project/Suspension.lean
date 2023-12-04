import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
open BigOperators Function Set Filter Topology TopologicalSpace

variable (X: Type*) [TopologicalSpace X]

lemma quotient_setoid (X': Set X) : Setoid (X) where
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
  --why not rfl???
  sorry
}


--define the (non-based) cylinder of X
def Cylinder := X × Icc 0 1

instance : TopologicalSpace (Cylinder X) := instTopologicalSpaceProd


lemma cyl_setoid : Setoid (Cylinder X) where
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

lemma pointedcyl : Setoid (Cylinder Y) where
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

#check (default : Y)

--define the pointed cylinder of Y
def PointedCylinder := Quotient (pointedcyl Y)

--show PointedCylinder is a pointed topological space with basepoint * × I
instance : TopologicalSpace (PointedCylinder Y) := instTopologicalSpaceQuotient

instance : Inhabited (PointedCylinder Y) where
  default := Quotient.mk (pointedcyl Y) ((default : Y), 0)

--construct pointed suspension
lemma pointedsus : Setoid (Cylinder Y) where
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

lemma wedgesetoid' : Setoid (Y ⊕ Z) := by{
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

lemma wedgesetoid : Setoid (Y ⊕ Z)  where
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

-- show that there is an embedding of the wedge product inside the topological product X × Y
def coprod_prod_map : Y ⊕ Z → Y × Z := fun
  | .inl y => (y, (default:Z))
  | .inr z => ((default:Y), z)


def wedge_embedding : Y ⋁ Z → Y × Z := by {
  apply Quotient.lift (coprod_prod_map Y Z)
  intro a b hab
  induction a
  case inl ya => {
    induction b
    case inl yb => {
      simp[coprod_prod_map]
      sorry
    }
    case inr zb => {
      simp[coprod_prod_map]
      sorry
    }
  }
  case inr z => sorry

}

-- prove this is an embedding

-- define smash products

/- Ideal, partial todo list:
-- suspension as smashing with S^1
-- suspension of S^n is S^{n+1}
-- adjunction with loop (depending on difficulty, either the smash version or just the suspension version)
-- time permitting, more related and basic topological things that are missing
-/
