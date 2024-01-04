import LeanCourse.Common
open Topology TopologicalSpace

/-!

# Warning: Derivative Content
This file is an adaptation of some of the content of the existing Mathlib file for homeomorphisms:
  mathlib4/Mathlib/Topology/Homeomorph.lean
The original Mathlib file is by Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton

# Pointed Functions
This file defines pointed functions of pointed (i.e. inhabited) types.
They are functions with the property
We denote pointed functions with the notation

# Pointed Homeomorphisms
This file defines pointed homeomorphisms between pointed topological spaces.
They are homeomorphisms whose underlying functions are pointed, that is, they are isomorphisms of pointed topological spaces.
We denote pointed homeomorphisms with the notation ` ≃ₜ⋆ `

# Main definitions
... to be filled later

# Main results
... to be filled later

-/


/-- Pointed functions between two pointed (i.e. inhabited) types -/
structure Pointed_Map (X: Type*) (Y: Type*) [Inhabited X] [Inhabited Y] where
  function : X → Y
  pointed : function default = default

@[inherit_doc]
infixl:25 " ≃ₚ " => Pointed_Map


variable (X:Type*) [TopologicalSpace X] [Inhabited X]
variable (Y:Type*) [TopologicalSpace Y] [Inhabited Y]
variable (f: X → Y)

variable {X Y} in
/-- Pointed continuous function between two pointed topological spaces `X` and `Y` -/
structure PointedMorph
  extends Continuous f where
  pointed_fun : f default = default := by simp

@[inherit_doc]
infixl:25 " →ₜ⋆ " => PointedMorph

/-- Pointed homeomorphism between `X` and `Y`, i.e. isomorphism in the category of pointed topological spaces -/
structure PointedHomeo
    extends X ≃ₜ Y where
  /-- The forward map of a pointed homeomorphism is pointed. -/
  pointed_toFun : toFun default = default := by simp

-- Extends pointed maps??? Extends pointed morphism?


--I am not sure what this does
#align pt_homeomorph PointedHomeo

@[inherit_doc]
infixl:25 " ≃ₜ⋆ " => PointedHomeo


variable {X Y} in
theorem pointed_invFun (f: X ≃ₜ⋆ Y) : f.invFun default = default := by{
  have := f.pointed_toFun
  rw[← this]
  simp
}

--should this be defined directly like in the original?
-- I am trying to define this as protected def symm but it says it's already declared
variable {X Y} in
def PointedHomeo.symm (f: X ≃ₜ⋆ Y) : Y ≃ₜ⋆ X := by {
  refine PointedHomeo.mk (f.toHomeomorph).symm ?h
  apply pointed_invFun
}

-- where do I [ @simp] this? Both before and afterwards give errors
variable {X Y} in
theorem pointed_symm_toFun (f: X ≃ₜ⋆ Y) : (PointedHomeo.symm f).toFun = f.invFun := by{
  simp[PointedHomeo.symm]
}

theorem pointed_comp {Z:Type*} [TopologicalSpace Z] [Inhabited Z] (f: X → Y) (g: Y → Z) (hf: f default = default) (hg: g default = default) : (g ∘ f) default = default := by{
  simp[hf, hg]
}



#lint
