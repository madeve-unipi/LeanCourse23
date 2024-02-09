import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Maps
import LeanCourse.Project.PointedTopSpaces
import LeanCourse.Project.Quotients

open BigOperators Function Set Filter Topology TopologicalSpace CategoryTheory

noncomputable section

/-
This file defines the free suspension of a topological space and the based suspension of a
pointed topological space, together with their respective functors.
-/




namespace Homeomorph
/-The theorem Homeomorph.homeomorphOfContinuousOpen is already in mathlib
For some reason, I couldn't find the corresponding one for continuous closed bijections
There's no particular reason this is here, I just thought I would need this but ended up never using it.
This proof is copied from Homeomorph.homeomorphOfContinuousOpen in Mathlib.Topology.Homeomorph by swapping open and closed.
-/


/-- If a bijective map `e : X ≃ Y` is continuous and closed, then it is a homeomorphism. -/
def homeomorphOfContinuousClosed {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ Y) (h₁ : Continuous ↑e) (h₂ : IsClosedMap ↑e) : X ≃ₜ Y where
continuous_toFun := h₁
continuous_invFun := by
  rw [continuous_iff_isClosed]
  intro s hs
  convert ← h₂ s hs using 1
  apply e.image_eq_preimage

toEquiv := e

end Homeomorph


section unpointed_spaces

variable (X: Type) [TopologicalSpace X]
variable (X': Type) [TopologicalSpace X']
variable (f: X → X')

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
  exact double_quotient_setoid h
}

/--The free suspension of a topological space.-/
def Suspension  := Quotient (cyl_setoid X)
instance : TopologicalSpace (Suspension  X) := instTopologicalSpaceQuotient

notation (priority:= high) "S" => Suspension


def MapTimesI : Cylinder X → Cylinder X' := fun x ↦ (f (x.1), x.2)

variable {X X'} in
/--The free suspension of a continuous map between topological spaces.-/
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

variable (Y': Type) [TopologicalSpace Y']
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

/--The suspension endofunctor in the category of topological spaces.-/
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

end unpointed_spaces

section pointed_spaces

universe u
--define the pointed cylinder of X
variable (X:Type) [TopologicalSpace X] [Inhabited X]

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

/--The based suspension of a pointed topological space.-/
def BasedSuspension := Quotient (basedsuspension_setoid X)
instance : TopologicalSpace (BasedSuspension X) := instTopologicalSpaceQuotient

instance : Inhabited (BasedSuspension X) where
  default:= Quotient.mk (basedsuspension_setoid X) ((default:X), 0)


notation (priority:= high) "Σ₀" => BasedSuspension


variable (Y:Type) [PointedTopSpace Y]
variable (f: X →ₜ⋆ Y)

variable {X Y} in
def BasedMapSuspensionFun: Σ₀ X → Σ₀ Y := by {
  let _hsusX := basedsuspension_setoid X
  let _hsusX' := basedsuspension_setoid Y
  apply Quotient.lift ( (Quotient.mk (basedsuspension_setoid Y) )∘ (MapTimesI X Y f) )
  intro a b hab
  have hab2 : (basedsuspension_setoid X).r a b := by exact hab
  have fa : MapTimesI X Y f a = (f (a.1), a.2) := by rfl
  have fb : MapTimesI X Y f b = (f (b.1), b.2) := by rfl

  simp [basedsuspension_setoid, quotient_setoid_equiv_iff] at hab2
  simp
  have : (basedsuspension_setoid Y).r (MapTimesI X Y f a) (MapTimesI X Y f b) := by {
    simp[basedsuspension_setoid, quotient_setoid_equiv_iff]
    simp[fa, fb]
    obtain hc1|hc2 := hab2
    · left
      obtain ⟨h1, h2⟩ := hc1
      constructor
      · obtain hd1|hd2:= h1
        · obtain hd1'|hd1'' := hd1
          · left; left
            rw[hd1']
            exact f.pointed_toFun
          · left;right; assumption
        · right; assumption
      · obtain hd1|hd2 := h2
        · obtain hd1'|hd1'' := hd1
          · left;left
            rw[hd1']
            exact f.pointed_toFun
          · left; right; assumption
        · right; assumption
    · right
      rw[hc2]
  }
  exact this
}

--show that if f is continuous, then so is its suspension
variable{X Y} in
lemma continuous_basedmapsuspension: Continuous (BasedMapSuspensionFun f) := by{
  apply Continuous.quotient_lift
  apply Continuous.comp
  · exact continuous_coinduced_rng
  · simp[MapTimesI]
    apply Continuous.prod_map f.continuous_toFun continuous_id
}

variable{X Y} in
lemma pointed_basedmapsuspension: (BasedMapSuspensionFun f) default = default := by{
  let _:= basedsuspension_setoid X
  simp[BasedMapSuspensionFun]
  have : (default : Σ₀ X) = Quotient.mk (basedsuspension_setoid X) ((default:X), 0) := rfl
  simp[this, MapTimesI]
  rfl
}

variable{X Y} in
def BasedMapSuspension : C⋆(Σ₀ X, Σ₀ Y) where
  toFun := BasedMapSuspensionFun f
  continuous_toFun := continuous_basedmapsuspension f
  pointed_toFun := pointed_basedmapsuspension f


lemma basedmapsuspension_id : BasedMapSuspension PointedMap.id = @PointedMap.id (Σ₀ X) _ := by{
  let _hsusX := basedsuspension_setoid X
  simp[BasedMapSuspension]
  ext x
  simp[BasedMapSuspensionFun, MapTimesI]
  obtain ⟨x₁, hx₁⟩ := Quot.exists_rep x
  rw[← hx₁]
  apply Quotient.lift_mk
}


variable (Z: Type) [PointedTopSpace Z]
variable (g: Y →ₜ⋆  Z)

variable {X Y Z} in
lemma basedmapsuspension_comp : BasedMapSuspension (g.comp f) = (BasedMapSuspension g).comp (BasedMapSuspension f) := by{
  ext x
  simp
  obtain ⟨x₁, hx₁⟩ := Quot.exists_rep x
  rw[←hx₁]
  simp[BasedMapSuspension, BasedMapSuspensionFun, MapTimesI]
  rfl
}


variable {X Y Z} in
lemma basedmapsuspension_comp' (f: X → Y) (g: Y → Z) (hf: Continuous f) (hg: Continuous g) (hf': f default = default) (hg': g default = default) : BasedMapSuspension ((PointedMap.mk (ContinuousMap.mk g hg) hg').comp (PointedMap.mk (ContinuousMap.mk f hf) hf')) = (BasedMapSuspension (PointedMap.mk (ContinuousMap.mk g hg) hg')) ∘ (BasedMapSuspension (PointedMap.mk (ContinuousMap.mk f hf) hf')) := by{
  funext x
  simp
  obtain ⟨x₁, hx₁⟩ := Quot.exists_rep x
  rw[←hx₁]
  simp[BasedMapSuspension, BasedMapSuspensionFun, MapTimesI]
  rfl
}


def BasedSuspensionFunctor: Functor PointedTopCat PointedTopCat where
  obj:= fun X ↦ PointedTopCat.of (Σ₀ X)
  map:= fun f ↦ BasedMapSuspension f
  map_id := by{
    simp
    intro X
    exact basedmapsuspension_id X
  }
  map_comp := by{
    dsimp
    intros
    apply basedmapsuspension_comp
  }

--#lint
end pointed_spaces

end
