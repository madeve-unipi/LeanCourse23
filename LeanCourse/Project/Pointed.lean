import LeanCourse.Common
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Elementwise
open Topology TopologicalSpace Set Filter

/-!

# Warning: Derivative Content
This file is an adaptation of some of the content of the existing Mathlib files for continuous functions and homeomorphisms, namely

  Mathlib.Topology.ContinuousFunction.Basic
  by Nicolò Cavalleri

  Mathlib.Topology.Homeomorph
  by Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton

  Mathlib.Topology.Category.TopCat.Basic
  by Patrick Massot, Scott Morrison, Mario Carneiro

Further references are:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/FunLike/Basic.html
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

/- Extending mathlib4/Mathlib/Topology/ContinuousFunction/Basic.lean -/


class PointedTopSpace (X:Type*)
  extends TopologicalSpace X where
  default : X

instance PointedTopOfTopOfInhabited (X:Type*) [TopologicalSpace X] [Inhabited X] : PointedTopSpace X where
  default := Inhabited.default

instance (X:Type*) [PointedTopSpace X] : Inhabited X where
  default := PointedTopSpace.default

variable (X:Type*) (Y:Type*) (Z:Type*) [PointedTopSpace X] [PointedTopSpace Y] [PointedTopSpace Z]


/--Pointed continuous functions between `X` and `Y`-/
structure PointedMap (X:Type*) (Y:Type*) [PointedTopSpace X] [PointedTopSpace Y]
    extends C(X, Y) where
  /-The underlying function maps the base point of the domain to the base point of the target-/
  pointed_toFun : toFun default = default := by simp



/-ISSUE HERE:

-- toFun is protected in ContinuousMap, which I think is the reason why PointedMap.toFun does not work
#check PointedMap.pointed_toFun
#check (PointedMap.toContinuousMap)
#check (PointedMap.toContinuousMap _).toFun
#check PointedMap.toFun

-- But then if I try to define toFun manually it tells me the structure already has that field!
protected def PointedMap.toFun := (PointedMap.toContinuousMap _).toFun
-/



@[inherit_doc]
infixl:25 " →ₜ⋆ " => PointedMap

notation "C⋆" "(" A "," B ")" => PointedMap A B

namespace PointedMap


class PointedMapClass (F : Type*) (A B : outParam <| Type*) [TopologicalSpace A] [Inhabited A] [TopologicalSpace B] [Inhabited B]
   extends ContinuousMapClass F A B where
  /--Pointed maps have to be pointed, i.e. map the base point to the base point -/
  map_pointed : ∀ (f : F), f default = default

variable {X Y} in
@[simp] lemma map_pointed {F: Type*} [PointedMapClass F X Y] (f : F) : f default = default := PointedMapClass.map_pointed f

theorem toContinuousMap_injective : Function.Injective (toContinuousMap: (X →ₜ⋆ Y ) → C(X, Y))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toFun_injective : Function.Injective (ContinuousMap.toFun ∘ toContinuousMap : (X →ₜ⋆ Y) → (X → Y) ) := by{
  apply Function.Injective.comp
  · apply FunLike.coe_injective'
  · exact toContinuousMap_injective X Y
}

instance : PointedMapClass (PointedMap X Y) X Y :=
  { coe := fun f ↦ (PointedMap.toContinuousMap f).toFun,
    coe_injective' := toFun_injective X Y
    map_continuous := by {
      intro f
      apply (PointedMap.toContinuousMap f).continuous_toFun
    }
    map_pointed := PointedMap.pointed_toFun }


instance : CoeFun (X →ₜ⋆ Y) fun _ ↦ X → Y := ⟨FunLike.coe⟩

@[ext] theorem ext {f g: X →ₜ⋆ Y} (h : ∀ x, f x = g x) : f = g := FunLike.ext f g h


protected def copy (f : PointedMap X Y) (f' : X → Y) (h : f' = ⇑f) : PointedMap X Y :=
  { toFun := f',
    pointed_toFun := by simp[h]
  }

@[simp] theorem apply (f: X →ₜ⋆ Y) (x: X ) : f.toContinuousMap x = f x := by rfl

@[simp] theorem apply' (f: X→ₜ⋆ Y) : (ContinuousMap.toFun ∘ toContinuousMap) f = f := by rfl

@[simp] theorem apply'' (f: X →ₜ⋆  Y) (x:X) : (ContinuousMap.toFun ∘ toContinuousMap) f x = f x := by rfl

@[simp] theorem pointedmap_mk_coe (f : C(X,Y) ) (b) : (PointedMap.mk f b: X → Y) = f :=
  rfl

-- this should be what we wanted in the first place
@[simp] theorem pointedmap_mk_coe' (a : X → Y) (b c) : (PointedMap.mk (ContinuousMap.mk a b) c: X → Y) = a :=
  rfl


variable{X Y Z} in
/-- Composition of two pointed maps. -/
protected def comp (h₂ : Y →ₜ⋆  Z) (h₁ : X →ₜ⋆  Y) : X →ₜ⋆  Z where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  pointed_toFun := by{
    simp[h₁.pointed_toFun, h₂.pointed_toFun]
    --have hyp1: (h₁.toContinuousMap: X → Y) default = default := h₁.pointed_toFun
    --have hyp2: (h₂.toContinuousMap: Y → Z) default = default := h₂.pointed_toFun
    --simp[hyp1, hyp2]
  }

@[simp]
theorem comp_apply (h₁ : X →ₜ⋆  Y) (h₂ : Y →ₜ⋆  Z) (x : X) : h₂.comp h₁ x = h₂ (h₁ x) :=
  rfl



/--The subspace topology induced by the compact-open topology on the type of pointed continuous maps.-/
protected def compactOpen :TopologicalSpace (C⋆(X, Y)) := TopologicalSpace.induced (PointedMap.toContinuousMap : C⋆(X,Y) → C(X,Y)) ContinuousMap.compactOpen

/--The constant map to the basepoint on the target as a pointed continuous map-/
protected def trivial : C⋆(X, Y) where
  toFun := fun _ ↦ default

variable{X} in
protected def id : C⋆(X, X) where
  toFun := @id X


@[simp] theorem id_apply (x:X) : id x = x := rfl


-- [TODO] Adapt more of the original file

end PointedMap

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


instance toPointedMap (f : PointedHomeo X Y) : PointedMap X Y where
  toFun := f.toFun
  continuous_toFun := f.continuous_toFun
  pointed_toFun := f.pointed_toFun



/-
Do I have to do the rest of the things that are suggested in
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/FunLike/Equiv.html#EquivLike
to turn it into a class too???

Similar to what is done for PointedMap

I don't think I strictly need this
-/


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
  toFun := fun _ ↦ default
  invFun := fun _ ↦ default
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


/- Again, the following should be redundant by what we have now

theorem pointed_comp {Z:Type*} [TopologicalSpace Z] [Inhabited Z] (f: X → Y) (g: Y → Z) (hf: f default = default) (hg: g default = default) : (g ∘ f) default = default := by{
  simp[hf, hg]
}
-/


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

/-
theorem induced_eq (h : X ≃ₜ⋆  Y) : TopologicalSpace.induced h ‹_› = ‹_› :=
  h.inducing.1.symm
-/

protected theorem quotientMap (h : X ≃ₜ⋆ Y) : QuotientMap h :=
  QuotientMap.of_quotientMap_compose h.symm.continuous h.continuous <| by
    simp only [self_comp_symm, QuotientMap.id]

/-
theorem coinduced_eq (h : X ≃ₜ⋆ Y) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.quotientMap.2.symm
-/

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




section PointedCategory

open CategoryTheory TopologicalSpace
universe u
variable (X:Type*) [PointedTopSpace X]
variable (Y:Type*) [PointedTopSpace Y]

/--The category of pointed topological spaces and pointed continuous maps-/
@[to_additive existing PointedTopCat]
def PointedTopCat: Type (u+1) := Bundled PointedTopSpace

#check (@PointedMap.toContinuousMap X Y _ _ _).toFun

namespace PointedTopCat


instance bundledHom : BundledHom @PointedMap where
  toFun := fun _ _ ↦ ContinuousMap.toFun ∘ PointedMap.toContinuousMap
  id := @PointedMap.id
  comp := @PointedMap.comp
  hom_ext := @PointedMap.toFun_injective
  id_toFun := fun _ => rfl
  comp_toFun := fun _ _ _ _ _ => rfl


deriving instance LargeCategory for PointedTopCat

instance concreteCategory : ConcreteCategory PointedTopCat := by
  dsimp [PointedTopCat]
  infer_instance


--@[to_additive existing PointedTopCat.instCoeSortPointedTopCatType]
instance instCoeSortTopCatType : CoeSort PointedTopCat (Type*) :=
  Bundled.coeSort

instance pointedtopologicalSpaceUnbundled (x : PointedTopCat) : PointedTopSpace x :=
  x.str

instance topspace_ofPointedTopCat (x: PointedTopCat) : TopologicalSpace x := by infer_instance

instance inhabited_ofPointedTopCat (x:PointedTopCat) : Inhabited x := by infer_instance


attribute [instance] ConcreteCategory.funLike in
instance (X Y : PointedTopCat.{u}) : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe f := f

@[simp] theorem id_app (X : PointedTopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

@[simp] theorem id_app' (X: PointedTopCat.{u}) : 𝟙 X = @PointedMap.id X (pointedtopologicalSpaceUnbundled X) := rfl

@[simp] theorem comp_app {X Y Z : PointedTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl

@[simp] theorem comp_app'{X Y Z : PointedTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f := rfl







/-- Construct a bundled `PointedTop` from the underlying type and the typeclass. -/
def of (X : Type u) [PointedTopSpace X] : PointedTopCat :=
  ⟨X, inferInstance⟩

instance topologicalSpace_coe (X : PointedTopCat) : PointedTopSpace X :=
  X.str

@[reducible]
instance topologicalSpace_forget (X : PointedTopCat) : PointedTopSpace <| (forget PointedTopCat).obj X :=
  X.str

@[simp]
theorem coe_of (X : Type u) [PointedTopSpace X] : (of X : Type u) = X := rfl

-- of forget
@[simp]
theorem of_forget (X: PointedTopCat) : of ((forget PointedTopCat).obj X) = X := rfl

@[simp]
theorem forget_of (X: Type u) [PointedTopSpace X] : (forget PointedTopCat).obj (of X) = X := rfl


def Point : PointedTopCat where
  α := Fin 1


instance inhabited : Inhabited PointedTopCat := ⟨Point⟩



--@[simp] theorem coe_pointed_hom_comp {X Y Z: Type u} [PointedTopSpace X] [PointedTopSpace Y] [PointedTopSpace Z] (f:C⋆(X, Y)) (g:)



lemma hom_apply {X Y : PointedTopCat} (f : X ⟶ Y) (x : X) : f x = (ContinuousMap.toFun ∘ PointedMap.toContinuousMap) f x := rfl



@[simp] def coe_pointed_hom {X Y : Type u} [PointedTopSpace X] [PointedTopSpace Y] (f: C⋆(X,Y)) : X ⟶ Y := f


@[simp] def coe_pointed_hom' {X Y : Type u} [PointedTopSpace X] [PointedTopSpace Y] (f: C⋆(X,Y)) : of X ⟶ of Y := f



@[simp] theorem coe_pointed_hom_apply {X Y : Type u} [PointedTopSpace X] [PointedTopSpace Y] (f: C⋆(X,Y)) (x:X) : coe_pointed_hom f x = f x := by rfl



@[ext] theorem ext (X Y : PointedTopCat) {f g: X ⟶ Y} (h : ∀ x, f x = g x) : f = g := FunLike.ext f g h

@[ext] theorem ext' (X Y : PointedTopCat) {f g : X ⟶ Y} (h: f.toFun = g.toFun) : f = g := by {
  apply FunLike.ext f g
  intro x
  have :=congrFun h x
  exact this
}

@[simp] theorem pointedmap_mk_coe' {X Y Z : PointedTopCat.{u}}  (f : X ⟶ Y) (g : Y ⟶ Z) : (coe_pointed_hom (PointedMap.mk (ContinuousMap.mk f.toFun f.continuous_toFun) f.pointed_toFun)) ≫ coe_pointed_hom (PointedMap.mk (ContinuousMap.mk g g.continuous_toFun) g.pointed_toFun)  = g ∘ f := by {
  -- note this relies on coe_pointed_hom_apply being in simp. At the moment, that one is broken
  funext x
  simp
  rfl
}


/-- Any pointed homeomorphism induces an isomorphism in `PointedTopCat`. -/
@[simps]
def isoOfPointedHomeo {X Y : PointedTopCat.{u}} (f : X ≃ₜ⋆  Y) : X ≅ Y where
  hom := f.toPointedMap
  inv := (f.symm).toPointedMap
  hom_inv_id := by ext; exact f.symm_apply_apply _
  inv_hom_id := by ext; exact f.apply_symm_apply _


/-- Any isomorphism in `PointedTopCat` induces a pointed homeomorphism. -/
@[simps]
def pointedhomeoOfIso {X Y : PointedTopCat.{u}} (f : X ≅ Y) : X ≃ₜ⋆ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous
  pointed_toFun := f.hom.pointed_toFun


@[simp]
theorem of_isoOfPointedHomeo {X Y : PointedTopCat.{u}} (f : X ≃ₜ⋆ Y) : pointedhomeoOfIso (isoOfPointedHomeo f) = f := by
  dsimp [pointedhomeoOfIso, isoOfPointedHomeo]
  ext
  rfl


@[simp]
theorem of_pointedhomeoOfIso {X Y : PointedTopCat.{u}} (f : X ≅ Y) : isoOfPointedHomeo (pointedhomeoOfIso f) = f := by
  dsimp [pointedhomeoOfIso, isoOfPointedHomeo]
  ext
  rfl

end PointedTopCat



end PointedCategory







/-
Final comments:

- [TODO] Do I need more simp lemmas for PointedMap?
- [TODO] Rephrase the embedding Y ⋁ Z → Y × Z in Suspension.lean in terms of the Embeddings section here


- Should this file be made compatible with
https://github.com/leanprover-community/mathlib4/blob/8666bd82efec40b8b3a5abca02dc9b24bbdf2652/Mathlib/CategoryTheory/Category/Pointed.lean#L29-L33
???
-/

--#lint
