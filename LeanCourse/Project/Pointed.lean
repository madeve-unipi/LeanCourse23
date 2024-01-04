import LeanCourse.Common
open Topology TopologicalSpace Set Filter

/-!

# Warning: Derivative Content
This file is an adaptation of some of the content of the existing Mathlib file for homeomorphisms:
  mathlib4/Mathlib/Topology/Homeomorph.lean
The original Mathlib file is by Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton

A further reference is the following:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/FunLike/Equiv.html


# Pointed Homeomorphisms
This file defines pointed homeomorphisms between pointed topological spaces.
They are homeomorphisms whose underlying functions are pointed, that is, they are isomorphisms of pointed topological spaces.
We denote pointed homeomorphisms with the notation ` ≃ₜ⋆ `

# Main definitions
... to be filled later

# Main results
... to be filled later

-/

/- I don't think I ever need this

/-- Pointed functions between two pointed (i.e. inhabited) types -/
structure Pointed_Map (X: Type*) (Y: Type*) [Inhabited X] [Inhabited Y] where
  /-- The carrier function of the structure-/
  function : X → Y
  /-- A pointed function maps the basepoint to the basepoint-/
  pointed : function default = default

@[inherit_doc]
infixl:25 " ≃ₚ " => Pointed_Map



variable (X:Type*) [TopologicalSpace X] [Inhabited X]
variable (Y:Type*) [TopologicalSpace Y] [Inhabited Y]
variable (f: X → Y)


/-- Pointed continuous function between two pointed topological spaces `X` and `Y` -/
structure PointedMorph
  extends Continuous f where
  pointed_fun : f default = default := by simp

@[inherit_doc]
infixl:25 " →ₜ⋆ " => PointedMorph

-/

variable (X:Type*) [TopologicalSpace X] [Inhabited X]
variable (Y:Type*) [TopologicalSpace Y] [Inhabited Y]

/-- Pointed homeomorphism between `X` and `Y`, i.e. isomorphism in the category of pointed topological spaces -/
structure PointedHomeo
    extends X ≃ₜ Y where
  /-- The forward map of a pointed homeomorphism is pointed. -/
  pointed_toFun : toFun default = default := by simp


@[inherit_doc]
infixl:25 " ≃ₜ⋆ " => PointedHomeo

namespace PointedHomeo
variable{X Y}
variable {Z: Type*} [TopologicalSpace Z] [Inhabited Z]

variable (h: X ≃ₜ⋆ Y )
#check h.toEquiv
#check h.toHomeomorph


@[simp] theorem pointed_invFun (f: X ≃ₜ⋆ Y) : f.invFun default = default := by{
  have := f.pointed_toFun
  rw[← this]
  simp
}

--#check (Homeomorph.toEquiv: X ≃ₜ Y → X ≃ Y)
--#check (toHomeomorph: X ≃ₜ⋆  Y → X ≃ₜ Y)
--#check Homeomorph.toEquiv
--#check PointedHomeo.toEquiv
--#check Homeomorph.toEquiv ∘ toHomeomorph

theorem toHomeomorph_injective : Function.Injective (toHomeomorph: X ≃ₜ⋆ Y → X ≃ₜ Y)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toEquiv_injective : Function.Injective (Homeomorph.toEquiv ∘ toHomeomorph: PointedHomeo X Y → X ≃ Y):= by {
  apply Function.Injective.comp
  · exact Homeomorph.toEquiv_injective
  · exact toHomeomorph_injective
}


instance : EquivLike (PointedHomeo X Y) X Y where
  coe := fun h => h.toEquiv
  inv := fun h => h.toEquiv.symm
  left_inv := fun h => h.left_inv
  right_inv := fun h => h.right_inv
  -- I don't really know what this does to be honest. I know what it's proving but no clue what the syntax does
  coe_injective' := fun _ _ H _ => toEquiv_injective <| FunLike.ext' H



instance : CoeFun (X ≃ₜ⋆ Y) fun _ ↦ X → Y := ⟨FunLike.coe⟩


@[ext] theorem ext {f g: X ≃ₜ⋆ Y} (h : ∀ x, f x = g x) : f = g := FunLike.ext f g h


-- Do I have to do the rest of the things that are suggested in
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/FunLike/Equiv.html#EquivLike
-- ???


-- Here, Pointedhomeo.mk makes a homeo into a pointed homeo, not an equiv into a homeo
-- hence this is a different theorem to the original version
@[simp] theorem pointedhomeo_mk_coe (a : X ≃ₜ Y) (b) : (PointedHomeo.mk a b: X → Y) = a :=
  rfl

-- this should be what we wanted in the first place
@[simp] theorem pointedhomeo_mk_coe' (a : X ≃ Y) (b c d) : (PointedHomeo.mk (Homeomorph.mk a b c) d: X → Y) = a :=
  rfl


/- Here, there is no empty pointed homeomorphism (inhabited types are nonempty)
  Though there should be some notion of trivial pointed homeo between two points
  I don't know if there's a standard way to encode hX and hY below, like some typeclass
-/

/--The trivial pointed isomorphism between two pointed spaces made of a single point-/
protected def trivial [Unique X] [Unique Y]: X ≃ₜ⋆ Y where
  toFun := fun x ↦ default
  invFun := fun y ↦ default
  left_inv := by simp[Function.LeftInverse]
  right_inv := by simp[Function.RightInverse, Function.LeftInverse]


/--Inverse of a pointed homeomorphism-/
protected def symm (h : X ≃ₜ⋆ Y) : Y ≃ₜ⋆  X where
  toEquiv := h.toEquiv.symm
  pointed_toFun := by{
    simp
    apply pointed_invFun
  }


@[simp] theorem symm_symm (h : X ≃ₜ⋆ Y) : h.symm.symm = h := rfl

theorem symm_bijective : Function.Bijective (PointedHomeo.symm: (X ≃ₜ⋆ Y) → Y ≃ₜ⋆ X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩


/- I had written this for a previous definition but it might be redundant now

@[simp] theorem pointed_symm_toFun (f: X ≃ₜ⋆ Y) : (PointedHomeo.symm f).toFun = f.invFun := by{
  simp[PointedHomeo.symm]
}
-/


-- I don't really know what's going on with this 'simps projections' thing

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : X ≃ₜ⋆ Y) : Y → X :=
  h.symm

initialize_simps_projections PointedHomeo (toFun → apply, invFun → symm_apply)

@[simp]
theorem coe_toEquiv (h : X ≃ₜ⋆ Y) : ⇑h.toEquiv = h :=
  rfl

@[simp]
theorem coe_symm_toEquiv (h : X ≃ₜ⋆ Y) : ⇑h.toEquiv.symm = h.symm :=
  rfl


/-- Identity map as a pointed homeomorphism. -/
@[simps! (config := .asFn) apply]
protected def refl (X : Type*) [TopologicalSpace X] [Inhabited X]: X ≃ₜ⋆ X where
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  toEquiv := Equiv.refl X

/-- Composition of two pointed homeomorphisms. -/
protected def trans (h₁ : X ≃ₜ⋆  Y) (h₂ : Y ≃ₜ⋆  Z) : X ≃ₜ⋆  Z where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv
  pointed_toFun := by{
    simp[h₁.pointed_toFun, h₂.pointed_toFun]
    have hyp1: (h₁.toHomeomorph: X → Y) default = default := h₁.pointed_toFun
    have hyp2: (h₂.toHomeomorph: Y → Z) default = default := h₂.pointed_toFun
    simp[hyp1, hyp2]
  }

@[simp]
theorem trans_apply (h₁ : X ≃ₜ⋆  Y) (h₂ : Y ≃ₜ⋆  Z) (x : X) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl

@[simp]
theorem symm_trans_apply (f : X ≃ₜ⋆ Y) (g : Y ≃ₜ⋆ Z) (z : Z) :
    (f.trans g).symm z = f.symm (g.symm z) := rfl


@[simp]
theorem pointed_homeo_mk_coe_symm (a : X ≃ₜ Y) (b) :
    ((PointedHomeo.mk a b).symm : Y → X) = a.symm :=
  rfl


@[simp]
theorem pointed_homeo_mk_coe'_symm (a : X ≃ Y) (b c d) :
    ((PointedHomeo.mk (Homeomorph.mk a b c) d).symm : Y → X) = a.symm :=
  rfl

@[simp]
theorem refl_symm : (PointedHomeo.refl X).symm = PointedHomeo.refl X :=
  rfl


/- Again, the following should morally be redundant by what we have now

theorem pointed_comp {Z:Type*} [TopologicalSpace Z] [Inhabited Z] (f: X → Y) (g: Y → Z) (hf: f default = default) (hg: g default = default) : (g ∘ f) default = default := by{
  simp[hf, hg]
}
-/

-- ARE THE NEXT TWO LEMMAS ABOUT CONTINUITY EVEN NEEDED SINCE WE ARE EXTENDING HOMEO?
@[continuity]
protected theorem continuous (h : X ≃ₜ⋆  Y) : Continuous h :=
  h.continuous_toFun

@[continuity]
protected theorem continuous_symm (h : X ≃ₜ⋆  Y) : Continuous h.symm :=
  h.continuous_invFun


@[simp]
theorem apply_symm_apply (h : X ≃ₜ⋆ Y) (y : Y) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (h : X ≃ₜ⋆  Y) (x : X) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

@[simp]
theorem self_trans_symm (h : X ≃ₜ⋆  Y) : h.trans h.symm = PointedHomeo.refl X := by
  ext
  apply symm_apply_apply

@[simp]
theorem symm_trans_self (h : X ≃ₜ⋆ Y) : h.symm.trans h = PointedHomeo.refl Y := by
  ext
  apply apply_symm_apply

protected theorem bijective (h : X ≃ₜ⋆ Y) : Function.Bijective h :=
  h.toEquiv.bijective

protected theorem injective (h : X ≃ₜ⋆ Y) : Function.Injective h :=
  h.toEquiv.injective

protected theorem surjective (h : X ≃ₜ⋆  Y) : Function.Surjective h :=
  h.toEquiv.surjective


/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : X ≃ₜ⋆  Y) (g : Y → X) (hg : Function.RightInverse g f) : X ≃ₜ⋆ Y :=
  haveI : g = f.symm := (f.left_inv.eq_rightInverse hg).symm
  { toFun := f
    invFun := g
    left_inv := by convert f.left_inv
    right_inv := by convert f.right_inv using 1
    continuous_toFun := f.continuous
    continuous_invFun := by convert f.symm.continuous
    pointed_toFun := by { simp; apply f.pointed_toFun} }

@[simp]
theorem symm_comp_self (h : X ≃ₜ⋆ Y) : h.symm ∘ h = id :=
  funext h.symm_apply_apply

@[simp]
theorem self_comp_symm (h : X ≃ₜ⋆ Y) : h ∘ h.symm = id :=
  funext h.apply_symm_apply

@[simp]
theorem range_coe (h : X ≃ₜ⋆ Y) : range h = univ :=
  h.surjective.range_eq

theorem image_symm (h : X ≃ₜ⋆  Y) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage

theorem preimage_symm (h : X ≃ₜ⋆ Y) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage).symm

@[simp]
theorem image_preimage (h : X ≃ₜ⋆  Y) (s : Set Y) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s

@[simp]
theorem preimage_image (h : X ≃ₜ⋆ Y) (s : Set X) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s

protected theorem inducing (h : X ≃ₜ⋆ Y) : Inducing h :=
  inducing_of_inducing_compose h.continuous h.symm.continuous <| by
    simp only [symm_comp_self, inducing_id]

theorem induced_eq (h : X ≃ₜ⋆  Y) : TopologicalSpace.induced h ‹_› = ‹_› :=
  h.inducing.1.symm

protected theorem quotientMap (h : X ≃ₜ⋆ Y) : QuotientMap h :=
  QuotientMap.of_quotientMap_compose h.symm.continuous h.continuous <| by
    simp only [self_comp_symm, QuotientMap.id]

theorem coinduced_eq (h : X ≃ₜ⋆ Y) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.quotientMap.2.symm

protected theorem embedding (h : X ≃ₜ⋆  Y) : Embedding h :=
  ⟨h.inducing, h.injective⟩


section Embeddings
variable {f: X → Y} (hfp: f default = default)

instance: Inhabited (Set.range f) where
  default := ⟨f default, by simp⟩


noncomputable def ofPointedEmbedding (hf : Embedding f) : X ≃ₜ⋆  Set.range f where
  continuous_toFun := hf.continuous.subtype_mk _
  continuous_invFun := hf.continuous_iff.2 <| by simp [continuous_subtype_val]
  toEquiv := Equiv.ofInjective f hf.inj
  pointed_toFun := rfl


end Embeddings

-- I don't think I'm gonna need anything more from the main file (current line: 262)

end PointedHomeo
/-
Final comments:
- The original source does a bunch of #align things and I don't understand what those are supposed to do

- Should this file be made compatible with
https://github.com/leanprover-community/mathlib4/blob/8666bd82efec40b8b3a5abca02dc9b24bbdf2652/Mathlib/CategoryTheory/Category/Pointed.lean#L29-L33
???
-/


--#lint
