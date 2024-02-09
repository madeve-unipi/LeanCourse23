import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Maps
import LeanCourse.Project.Quotients
import LeanCourse.Project.PointedTopSpaces

open BigOperators Function Set Filter Topology TopologicalSpace CategoryTheory

variable (X: Type) [PointedTopSpace X] (Y:Type) [PointedTopSpace Y]

/- This file defines the wedge sum and the smash product of two pointed topological spaces.
  It proves some basic properties, including the adjunction between the functor - ⋀ Y and C⋆(Y, -)
  for Y locally compact.
  A previous version of this file with clumsier proofs can be found in the repository history as part of
  the file Suspension.lean.
  Some small lemmas that were used then have been removed because they were not needed here.
 -/


-- define the wedge sum X ⋁ Y of two pointed spaces X and Y
namespace PointedTopSpace

def wedge_setoid : Setoid (X ⊕ Y) := by{
  let A: Set (X ⊕ Y) := { p : X ⊕ Y | p = Sum.inl (default:X) ∨ p = Sum.inr (default:Y)}
  exact quotient_setoid A
}


def wedge := Quotient (wedge_setoid X Y)

instance : PointedTopSpace (wedge X Y) where
  toTopologicalSpace := instTopologicalSpaceQuotient
  default := Quotient.mk (wedge_setoid X Y) (Sum.inl (default:X))


infix:50 " ⋁ " => wedge

@[simp]
theorem wedge_defaults_equiv: Quotient.mk (wedge_setoid X Y) (Sum.inl default) = Quotient.mk (wedge_setoid X Y) (Sum.inr default) := by{
  let _hwedge := wedge_setoid X Y
  refine Quotient.eq.mpr ?_
  have : (wedge_setoid X Y).r (Sum.inl default) (Sum.inr default) := by simp
  exact this
}


/--The quotient map X ⊕ Y → X ⋁ Y -/
def wedge_quot_mk := Quotient.mk (wedge_setoid X Y)

/-- The natural inclusion map X → X ⋁ Y -/
def wedge_inl : C⋆ (X, X ⋁ Y) where
  toFun:= wedge_quot_mk _ _ ∘ Sum.inl
  pointed_toFun := rfl
  continuous_toFun := Continuous.comp continuous_coinduced_rng continuous_inl

def wedge_inl_hom : PointedTopCat.of X ⟶ PointedTopCat.of (X ⋁ Y) := wedge_inl X Y

/-- The natural inclusion map Y → X ⋁ Y -/
def wedge_inr : C⋆ (Y, X ⋁ Y) where
  toFun := wedge_quot_mk _ _ ∘ Sum.inr
  pointed_toFun := by{
    simp[wedge_quot_mk]
    rw[defaults_eq, ← wedge_defaults_equiv]
    rfl
  }
  continuous_toFun := Continuous.comp continuous_coinduced_rng continuous_inr

def wedge_inr_hom : PointedTopCat.of Y ⟶ PointedTopCat.of (X ⋁ Y) := wedge_inr X Y

variable {Z: Type} [PointedTopSpace Z]

variable {X Y} in
/--The function induced on the wedge sum X ⋁ Y by two pointed continuous functions X → Z and Y → Z. This is the underlying function in wedge_induced-/
def wedge_induced_fun (f: C⋆ (X, Z)) (g: C⋆(Y, Z)) : (X ⋁ Y) → Z := by{
  let _:= wedge_setoid X Y
  apply Quotient.lift (Sum.elim f.toFun g.toFun)
  intro x y hxy
  have hxy' : (wedge_setoid X Y).r x y := hxy
  simp[quotient_setoid_equiv_iff] at hxy'
  obtain ⟨h1, h2⟩|h3:= hxy'
  obtain hc1|hc2 := h1
  · obtain hd1| hd2 :=h2
    · rw[hc1, hd1]
    · rw[hc1, hd2]
      rw[← defaults_eq, ← defaults_eq]
      simp[f.pointed_toFun, g.pointed_toFun]
  · obtain hd1|hd2 := h2
    · rw[hc2, hd1]
      rw[← defaults_eq, ← defaults_eq]
      simp[f.pointed_toFun, g.pointed_toFun]
    · rw[hc2, hd2]
  · rw[h3]
}


variable{X Y} in
lemma wedge_induced_pointed (f: C⋆(X, Z)) (g: C⋆(Y,Z)) : wedge_induced_fun f g default = default := by{
  let _:=wedge_setoid X Y
  simp[wedge_induced_fun]
  have : (default : X ⋁ Y) = Quotient.mk (wedge_setoid X Y) (Sum.inl (default:X)) := rfl
  rw[this, Quotient.lift_mk]
  rw[←defaults_eq]
  simp [f.pointed_toFun]
  rfl
}

variable {X Y} in
/--The pointed continuous function induced on the wedge sum X ⋁ Y to Z by two pointed continuous functions X → Z and Y → Z.-/
def wedge_induced (f: C⋆(X, Z)) (g: C⋆(Y, Z)) : C⋆(X ⋁ Y, Z) where
  toFun := wedge_induced_fun f g
  pointed_toFun := wedge_induced_pointed f g
  continuous_toFun := by{
    apply Continuous.quotient_lift
    simp [continuous_sum_dom]
    constructor
    · exact f.continuous_toFun
    · exact g.continuous_toFun
  }

variable{X Y} in
def wedge_induced_hom (f: PointedTopCat.of X ⟶ PointedTopCat.of Z) (g: PointedTopCat.of Y ⟶ PointedTopCat.of Z) : PointedTopCat.of (X ⋁ Y) ⟶ PointedTopCat.of Z := wedge_induced f g

/- [TODO] The wedge sum is a coproduct. Just copying the one for pointed types get stuck in coercions. -/

variable {X Y} in
theorem wedge_induced_iff (f g : C⋆(X ⋁ Y, Z)) : f = g ↔ (f ∘ (wedge_inl X Y) = g ∘ (wedge_inl X Y) ∧ f ∘ (wedge_inr X Y) = g ∘ (wedge_inr X Y)) := by{
  constructor
  · intro h; rw[h]; tauto
  · intro ⟨h₁, h₂⟩
    ext p
    obtain ⟨p', hp'⟩ := Quotient.exists_rep p
    rw[← hp']
    induction p'
    case inl x => exact congrFun h₁ x
    case inr y => exact congrFun h₂ y
}

/--The pointed continuous function X ⋁ Y → Y ⋁ X induced by including each summand into itself -/
def wedge_swap := wedge_induced (wedge_inr Y X) (wedge_inl Y X)


lemma wedge_swap_swap : (wedge_swap X Y).comp (wedge_swap Y X) = PointedMap.id := by{
  rw[wedge_induced_iff]
  constructor
  · ext x; rfl
  · ext y; rfl
}

/- There really should be a nicer way to get this directly from the previous one.-/
lemma wedge_swap_swap' : ∀ p : X ⋁ Y, wedge_swap Y X (wedge_swap X Y p) = p := by{
  intro p
  obtain ⟨p', hp'⟩ := Quotient.exists_rep p
  rw[← hp']
  induction p'
  case inl x => rfl
  case inr y => rfl
}

/--The pointed homeomorphism X ⋁ Y → Y ⋁ X induced by swapping the two summands-/
def wedge_swap_homeo : X ⋁ Y ≃ₜ⋆  Y ⋁ X where
  toFun:= wedge_swap X Y
  invFun := wedge_swap Y X
  left_inv := wedge_swap_swap' X Y
  right_inv := wedge_swap_swap' Y X

def wedge_swap_iso : PointedTopCat.of (X ⋁ Y) ≅ PointedTopCat.of (Y ⋁ X) where
  hom := wedge_swap X Y
  inv := wedge_swap Y X
  hom_inv_id := wedge_swap_swap Y X
  inv_hom_id := wedge_swap_swap X Y

-- Alternatively, define the iso and then use PointedTopCat.pointedhomeoOfIso


instance: PointedTopSpace (X × Y) := by infer_instance


def prodFst : C⋆(X × Y, X) where
  toFun := fun p ↦ p.1
  pointed_toFun := rfl
  continuous_toFun := continuous_fst

def prodSnd : C⋆(X × Y, Y) where
  toFun := fun p ↦ p.2
  pointed_toFun := rfl
  continuous_toFun := continuous_snd

variable {X Y} in
def prod_induced (f: C⋆(Z, X)) (g: C⋆(Z, Y)) : C⋆(Z, X × Y) where
  toFun := fun c ↦ (f.toFun c, g.toFun c)
  pointed_toFun:= by simp[f.pointed_toFun, g.pointed_toFun]; rfl


/- [TODO] This is the categorical product -/

theorem prod_induced_iff (f g : C⋆ (Z, X × Y)) : f = g ↔ ((prodFst X Y) ∘ f = (prodFst X Y) ∘ g) ∧ ((prodSnd X Y) ∘ f = (prodSnd X Y) ∘ g) := by{
  constructor
  · intro h; rw[h]; tauto
  · intro ⟨h₁, h₂⟩
    ext z
    · exact congrFun h₁ z
    · exact congrFun h₂ z
}


def prod_inl : C⋆(X, X × Y) where
  toFun := fun x ↦ (x, default)
  pointed_toFun:= rfl


def prod_inr : C⋆(Y, X × Y)  where
  toFun := fun y ↦ (default, y)
  pointed_toFun := rfl

def prod_swap : C⋆(X × Y, Y × X) where
  toFun := fun (a, b) ↦ (b,a)
  pointed_toFun := rfl

def prod_swap_homeo: (X × Y) ≃ₜ⋆ (Y × X) where
  toFun := prod_swap X Y
  invFun := prod_swap Y X
  left_inv := by simp[LeftInverse]; intros; rfl
  right_inv := by simp[Function.RightInverse, LeftInverse]; intros; rfl


def wedge_embedding := wedge_induced (prod_inl X Y) (prod_inr X Y)



--if something is in the image of the wedge embedding, then at least one of its coordinates is default
variable{X Y} in
@[simp] lemma wedge_embedding_ran {p: X × Y} (h: p ∈ range (wedge_embedding X Y)) : p.1=(default:X) ∨ p.2= (default:Y) := by{
  let _:= wedge_setoid X Y
  simp at h
  obtain ⟨t, ht⟩:=h
  obtain ⟨t', ht'⟩:= Quotient.exists_rep t
  rw[←ht, ← ht']
  induction t'
  case inl a => right; rfl
  case inr b => left; rfl
}


lemma wedge_embedding_inl (x:X) : (wedge_embedding X Y).toFun ((wedge_inl X Y).toFun x) = (x, default) := rfl

lemma wedge_embedding_inr (y:Y) : (wedge_embedding X Y).toFun ((wedge_inr X Y).toFun y) = (default, y) := rfl

variable{X Y} in
lemma wedge_embedding_ran_iff (p: X × Y) : p ∈ range (wedge_embedding X Y) ↔ p.1=(default:X) ∨ p.2= (default:Y) := by{
  let _:= wedge_setoid X Y
  constructor
  · intro h
    apply wedge_embedding_ran h
  · intro h
    have : p = (p.1, p.2) := rfl
    rw[this]
    obtain h1|h2:= h
    · use wedge_inr X Y p.2
      rw[h1]
      rfl
    · use wedge_inl X Y p.1
      rw[h2]
      rfl
}

@[simp] lemma wedge_embedding_ran' {p: X × Y} : (∃ y, (wedge_embedding X Y).toFun y = p) ↔ p.1 = default ∨ p.2= default := by{
  constructor
  · intro h
    have : p ∈ range (wedge_embedding X Y).toFun := h
    exact wedge_embedding_ran this
  · intro h
    obtain hc1|hc2 := h
    · use (wedge_inr X Y).toFun p.2
      rw[wedge_embedding_inr, ←hc1]
    · use (wedge_inl X Y).toFun p.1
      rw[wedge_embedding_inl, ←hc2]
}

-- [FIX] Put it in simp but fix what gets broken below
lemma wedge_embedding_ran'' (p: X × Y) : (∃ z, ((wedge_embedding X Y) z = p)) ↔ p.1=default ∨ p.2=default := by{
  rw[← wedge_embedding_ran']
  simp
}



-- This proof may be easier to write down efficiently, I just copied the old one with a much more complicated definition of wedge_embedding
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
            simp[wedge_embedding] at hp
            rw[← hp']
            exact hp.1
          }
          case inr y => {
            simp[wedge_embedding] at hp
            rw[← hp']
            exact hp.2
          }
        · intro hp
          rw[Set.mem_preimage]
          obtain ⟨p', hp'⟩ := Quotient.exists_rep p
          rw[← hp']
          induction p'
          case inl x => {
            simp[wedge_embedding]
            constructor
            · exact mem_of_eq_of_mem hp' hp
            · have : ((wedge_induced (prod_inl X Y) (prod_inr X Y)) (Quotient.mk (wedge_setoid X Y) (Sum.inl x))).2 = default := rfl
              rw[this, ← wedge_defaults_equiv]
              exact hcase
          }
          case inr y => {
            simp[wedge_embedding]
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
            simp[wedge_embedding] at hp
            obtain hp1|hp2 := hp
            · exact mem_of_eq_of_mem (id hp'.symm) hp1
            · have : default ∈ A := by {
                have : ((wedge_induced (prod_inl X Y) (prod_inr X Y)) (Quotient.mk (wedge_setoid X Y) (Sum.inl x))).2 = default := rfl
                rw[this, ← wedge_defaults_equiv] at hp2
                exact hp2
                }
              contradiction
          }
          case inr y => {
            simp[wedge_embedding] at hp
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
            simp[wedge_embedding]
            left
            exact mem_of_eq_of_mem hp' hp
          }
          case inr y => {
            simp[wedge_embedding]
            right
            exact mem_of_eq_of_mem hp' hp
          }
  · have hcont : Continuous (wedge_embedding X Y) := (wedge_embedding X Y).continuous_toFun
    intro hA
    rw[isOpen_induced_iff] at hA
    obtain ⟨B, hB1, hB2⟩ := hA
    have that := IsOpen.preimage hcont hB1
    rw[hB2] at that
    assumption
}


theorem wedge_embeds_into_product: Embedding (wedge_embedding X Y) := by{
  let _hwedge := wedge_setoid X Y
  rw[embedding_iff]
  constructor
  --induced topology
  · exact wedge_embedding_inducing X Y

  --injectivity
  · intro a b hab
    obtain ⟨a', ha'⟩ := Quotient.exists_rep a
    obtain ⟨b', hb'⟩:= Quotient.exists_rep b
    rw[← ha', ← hb'] at hab
    rw[← ha', ← hb']
    apply Quotient.eq.mpr
    have : Setoid.r a' b' := by {
      rw[quotient_setoid_equiv_iff]
      simp
      induction a'
      case inl xa => {
        have : wedge_embedding X Y (Quotient.mk (wedge_setoid X Y) (Sum.inl xa)) = (xa, default) := rfl
        rw[this] at hab
        induction b'
        case inl xb => {
          have : wedge_embedding X Y (Quotient.mk (wedge_setoid X Y) (Sum.inl xb)) = (xb, default) := rfl
          rw[this] at hab
          simp at hab
          rw[hab]
          tauto
        }
        case inr yb => {
          have : wedge_embedding X Y (Quotient.mk (wedge_setoid X Y) (Sum.inr yb)) = (default, yb) := rfl
          simp[this] at hab
          simp[hab]
        }
      }

      case inr ya => {
        have : wedge_embedding X Y (Quotient.mk (wedge_setoid X Y) (Sum.inr ya)) = (default, ya) := rfl
        rw[this] at hab
        induction b'
        case inl xb => {
          have : wedge_embedding X Y (Quotient.mk (wedge_setoid X Y) (Sum.inl xb)) = (xb, default) := rfl
          simp[this] at hab
          simp[hab]
        }
        case inr yb => {
          have : wedge_embedding X Y (Quotient.mk (wedge_setoid X Y) (Sum.inr yb)) = (default, yb) := rfl
          simp[this] at hab
          simp[hab]
        }
      }
    }
    exact this
}


/-The setoid of X × Y associated to the smash product-/
def smash_setoid : Setoid (X × Y) := by{
  let A : Set (X × Y) := (wedge_embedding X Y).toFun '' univ
  exact quotient_setoid A
}

/-The smash product of two pointed topological spaces X and Y, denoted by X ⋀ Y -/
def smash := Quotient (smash_setoid X Y)

instance : PointedTopSpace (smash X Y) where
  toTopologicalSpace := instTopologicalSpaceQuotient
  default := Quotient.mk (smash_setoid X Y) (default, default)


infix:50 " ⋀  " => smash

variable {X Y} in
def smash_elt (x: X) (y : Y) : X ⋀ Y := Quotient.mk (smash_setoid X Y) (x,y)

infix:50 " ∧' " => smash_elt


variable {X Y} in
lemma smash_elt_eq_iff (x x' : X) (y y' : Y) : (smash_elt x y = smash_elt x' y') ↔ ( (x=default ∨ y=default) ∧ (x'=default ∨ y'=default) )∨ ( (x,y) = (x', y') ) := by{
  let _:= smash_setoid X Y
  let _:= wedge_setoid X Y
  simp[smash_elt]
  constructor
  · intro h
    have : (smash_setoid X Y).r (x, y) (x', y') := Quotient.eq'.mp h
    simp[wedge_embedding_ran''] at this
    assumption
  · intro h
    have : (smash_setoid X Y).r (x, y) (x', y') := by {
      rw[quotient_setoid_equiv_iff]
      simp[wedge_embedding_ran'']
      assumption
    }
    exact Quotient.eq.mpr this
}

variable {X Y} in
lemma smash_elt_eq_iff' (p q : X × Y) : Quotient.mk (smash_setoid X Y) p = Quotient.mk (smash_setoid X Y) q ↔ ( (p.1=default ∨ p.2=default) ∧ (q.1=default ∨ q.2=default) )∨ ( p = q ) := by{
  constructor
  · intro h
    have : (p.1 ∧' p.2) = (q.1 ∧' q.2) := h
    apply (smash_elt_eq_iff p.1 q.1 p.2 q.2).mp this
  · intro h
    rw[← smash_elt_eq_iff] at h
    exact h
}


@[simp] theorem smash_defaults_left (x : X) : (x ∧' (default:Y)) = (default : X ⋀ Y) := by{
  have : (default : X ⋀ Y) = ((default:X) ∧' (default:Y)) := rfl
  rw[this]
  simp[smash_elt_eq_iff]
}

@[simp] theorem smash_defaults_right (y : Y) : ((default:X) ∧' y) = (default : X ⋀ Y) := by{
  have : (default: X ⋀ Y) = ((default:X) ∧' (default:Y)) := rfl
  rw[this]
  rw[smash_elt_eq_iff]
  left
  simp
}

def smash_swap_fun : X ⋀ Y → Y ⋀ X := by {
  let _ := smash_setoid X Y
  let _ := smash_setoid Y X
  apply Quotient.lift ((Quotient.mk (smash_setoid Y X))∘ (prod_swap X Y))
  intro x y hxy
  rw[← Quotient.eq, smash_elt_eq_iff'] at hxy
  simp
  rw[← Quotient.eq]
  have hx : (prod_swap X Y) x = (x.2, x.1) := rfl
  have hy : (prod_swap X Y) y = (y.2, y.1) := rfl
  rw[hx, hy, smash_elt_eq_iff']
  simp
  tauto
}

def smash_swap : C⋆(X ⋀ Y, Y ⋀ X) where
  toFun := smash_swap_fun X Y
  continuous_toFun := by{
    apply Continuous.quotient_lift
    exact Continuous.comp continuous_quot_mk (prod_swap X Y).continuous_toFun
  }
  pointed_toFun := rfl


lemma smash_swap_swap: (smash_swap X Y).comp (smash_swap Y X) = PointedMap.id := by{
  ext x
  simp[smash_swap, smash_swap_fun]
  obtain ⟨x', hx'⟩ := Quotient.exists_rep x
  rw[← hx']
  rfl
}

def smash_swap_iso : PointedTopCat.of (X ⋀ Y) ≅ PointedTopCat.of (Y ⋀ X) where
  hom := smash_swap X Y
  inv := smash_swap Y X
  hom_inv_id := smash_swap_swap Y X
  inv_hom_id := smash_swap_swap X Y


def smash_swap_homeo : X ⋀ Y ≃ₜ⋆ Y ⋀ X := PointedTopCat.pointedhomeoOfIso (smash_swap_iso X Y)


/-Next goal: define the induced map X ⋀ Y → X' ⋀ Y' from two pointed continuous maps X → X' and Y → Y'-/

variable {X Y}
variable {X': Type} [PointedTopSpace X'] {Y':Type} [PointedTopSpace Y']
variable (f: C⋆(X, X')) (g: C⋆(Y, Y'))

def prod_map : C⋆(X × Y, X' × Y') where
  toFun := fun p ↦ (f (p.1), g (p.2))
  pointed_toFun := by {
    have : (Inhabited.default : X × Y) = ((Inhabited.default : X), (Inhabited.default : Y)) := rfl
    rw[this]
    simp
    rfl
  }


def smash_maps_fun : (X ⋀ Y) → (X' ⋀ Y') := by{
  let _ := smash_setoid X Y
  let _:= smash_setoid X' Y'
  apply Quotient.lift ( (Quotient.mk (smash_setoid X' Y') )∘ (prod_map f g))
  intro x y hxy
  rw[← Quotient.eq, smash_elt_eq_iff'] at hxy
  rw[Function.comp, Function.comp, smash_elt_eq_iff']
  simp[prod_map]

  have : x.1 = Inhabited.default → f.toFun x.1 = Inhabited.default := by intro k; rw[k]; exact f.pointed_toFun
  have : y.1 = Inhabited.default → f.toFun y.1 = Inhabited.default := by intro k; rw[k]; exact f.pointed_toFun
  have : x.2 = Inhabited.default → g.toFun x.2 = Inhabited.default := by intro k; rw[k]; exact g.pointed_toFun
  have : y.2 = Inhabited.default → g.toFun y.2 = Inhabited.default := by intro k; rw[k]; exact g.pointed_toFun

  tauto
}

def smash_maps : C⋆(X ⋀ Y, X' ⋀ Y') where
  toFun := smash_maps_fun f g
  continuous_toFun := by{
    simp[smash_maps_fun]
    apply Continuous.quotient_lift
    apply Continuous.comp
    · exact continuous_quot_mk
    · exact (prod_map f g).continuous_toFun
  }
  pointed_toFun := by{
    let _:= smash_setoid X Y
    simp[smash_maps_fun]
    have : (Inhabited.default: X ⋀ Y) = Quotient.mk (smash_setoid X Y) (default, default) := rfl
    rw[this, Quotient.lift_mk]
    simp[smash_maps_fun, f.pointed_toFun, g.pointed_toFun, prod_map, ←defaults_eq]
    rfl
  }

lemma smash_maps_id : smash_maps (@PointedMap.id X _) (@PointedMap.id Y _) = PointedMap.id := by{
  ext p
  obtain ⟨p', hp'⟩ := Quotient.exists_rep p
  rw[← hp']
  rfl
}

lemma smash_maps_comp {W:Type} [PointedTopSpace W] (f': C⋆(X', Z)) (g': C⋆(Y', W)) : (smash_maps f' g').comp (smash_maps f g) = smash_maps (f'.comp f) (g'.comp g) := by{
  ext p
  obtain ⟨p', hp'⟩ := Quotient.exists_rep p
  rw[← hp']
  rfl
}


/- To prove the later adjunction, we need to define the functor - ⋀ Y -/

def smash_id (f: C⋆(X, Z)) : C⋆(X ⋀ Y, Z ⋀ Y) := smash_maps f PointedMap.id

lemma smash_id_comp {W:Type} [PointedTopSpace W] (f: C⋆(X, Z)) (g: C⋆(Z, W)) : smash_id (g.comp f) = (smash_id g).comp (@smash_id X _ Y _ Z _ f) := by{
  rw[smash_id, smash_id, smash_id]
  have : @PointedMap.id Y _ = (@PointedMap.id Y _).comp (@PointedMap.id Y _) := rfl
  nth_rewrite 1 [this]
  rw [smash_maps_comp]
}

variable (Y) in
def smash_whisker_r : Functor PointedTopCat PointedTopCat where
  obj (W: PointedTopCat) := PointedTopCat.of (W ⋀ Y)
  map := smash_id
  map_comp := by{ intros; apply smash_id_comp}
  map_id := by{intros; apply smash_maps_id}


variable (Y) in
def homeo_smash_compare (h: X ≃ₜ⋆ Z) : X ⋀ Y ≃ₜ⋆ Z ⋀ Y := by{
  let h' : PointedTopCat.of X ≃ₜ⋆ PointedTopCat.of Z := h
  apply @PointedTopCat.pointedhomeoOfIso (PointedTopCat.of (X ⋀ Y)) (PointedTopCat.of (Z ⋀ Y))
  apply (smash_whisker_r Y).mapIso (PointedTopCat.isoOfPointedHomeo h')
}

variable (Y) in
def homeo_smash_compare' (h: X ≃ₜ⋆ Z) : Y ⋀ X ≃ₜ⋆ Y ⋀ Z := ((smash_swap_homeo Y X).trans (homeo_smash_compare Y h)).trans (smash_swap_homeo Z Y)

end PointedTopSpace


--Goal of the section: prove the adjunction Top_* (X ⋀ Y, Z) ≃ Top_* (X, Top_* (Y,Z)) for Y locally compact
section adjunction

/- The non-categorical part of the following is adapted from Mathlib.Topology.CompactOpen,
  starting on line 364. The original file is by Reid Barton.
-/

variable {X: Type} [PointedTopSpace X] {Y:Type} [PointedTopSpace Y] [LocallyCompactSpace Y] {Z:Type} [PointedTopSpace Z]
instance : TopologicalSpace C⋆(Y,Z) := PointedMap.compactOpen Y Z
instance : Inhabited C⋆(Y,Z) where
  default := PointedMap.trivial Y Z


namespace PointedMap
open PointedTopSpace

lemma continuous_function_curry' (f : C⋆(X ⋀ Y, Z)) : Continuous (f ∘ Quotient.mk (smash_setoid X Y)) := by {
  apply Continuous.comp
  · exact f.continuous_toFun
  · exact continuous_quot_mk
}


/-- Auxiliary definition, see `PointedMap.curry`. -/
def curry' (f : C⋆(X ⋀ Y, Z)) (x : X) : C⋆(Y, Z) where
  toFun := Function.curry (f ∘ Quotient.mk (smash_setoid X Y)) x
  continuous_toFun := by {
    apply Continuous.comp
    · exact continuous_function_curry' f
    · exact Continuous.Prod.mk x
  }
  pointed_toFun := by{
    simp
    have : Quotient.mk (smash_setoid X Y) (x, Inhabited.default) = ( x ∧' Inhabited.default) := rfl
    rw[this, defaults_eq, smash_defaults_left, ←defaults_eq]
    simp[f.pointed_toFun]
  }


  /-- If a map `X ⋀ Y → Z` is continuous, then its curried form `X → C⋆(Y, Z)` is continuous. -/
theorem continuous_curry' (f : C⋆(X ⋀ Y, Z)) : Continuous (curry' f) := by{
  simp[curry']
  have : Continuous (PointedMap.toContinuousMap  ∘ (curry' f)) := by {
    have : toContinuousMap ∘ (curry' f) = ContinuousMap.curry' (ContinuousMap.mk (f ∘ Quotient.mk (smash_setoid X Y)) (continuous_function_curry' f)) := rfl
    rw[this]
    exact ContinuousMap.continuous_curry' (ContinuousMap.mk (↑f ∘ Quotient.mk (smash_setoid X Y)) (continuous_function_curry' f))
  }

  -- universal property of induced topology
  exact continuous_induced_rng.mpr this
}


  /-- If a map `X ⋀ Y → Z` is pointed, then its curried form `X → C⋆(Y, Z)` is pointed. -/
theorem pointed_curry' (f : C⋆(X ⋀ Y, Z)) : (curry' f) Inhabited.default = Inhabited.default := by{
  let _:= smash_setoid X Y
  simp[curry', Function.curry]
  ext y
  simp[Inhabited.default, PointedMap.trivial]
  have : Quotient.mk (smash_setoid X Y) ((Inhabited.default:X), y) = Inhabited.default := by apply smash_defaults_right
  rw[← defaults_eq, this]
  exact f.pointed_toFun
}

/-- The curried form of a pointed continuous map `X ⋀ Y → Z` as a pointed continuous map `X → C⋆(Y, Z)`.
    If `Y` is locally compact, this is a bijection and carries an adjunction of functors `- ⋀ Y  ⊣ C⋆(Y, -)` . -/
def curry (f : C⋆(X ⋀ Y, Z)) : C⋆(X, C⋆(Y, Z)) where
  continuous_toFun:= continuous_curry' f
  pointed_toFun:= pointed_curry' f

@[simp]
theorem curry_apply (f : C⋆(X ⋀ Y, Z)) (x : X) (y : Y) : f.curry x y = f (x ∧'y) :=
  rfl


def toFun_toFun (f:C⋆(X, C⋆(Y, Z))) : X → (Y → Z) := fun y ↦ (fun z ↦ (f y) z)

/-- The uncurrying of a pointed function X → (Y → Z)  to a function X ⋀ Y → Z. This is not the same as Function.uncurry, which maps to X × Y → Z -/
def uncurry' (f:C⋆(X, C⋆(Y, Z))) : X ⋀ Y → Z := by {
  let _:= smash_setoid X Y
  apply Quotient.lift (Function.uncurry f.toFun_toFun)
  intro a b hab
  have hab' : Setoid.r a b := hab
  simp[quotient_setoid_equiv_iff] at hab'
  obtain hc1|hc2 := hab'
  · simp[Function.uncurry, toFun_toFun]
    obtain ⟨h1, h2⟩:= hc1
    have h1' := wedge_embedding_ran h1
    have h2' := wedge_embedding_ran h2

    have h1'' : (f.toContinuousMap a.1).toContinuousMap a.2 = Inhabited.default := by{
      obtain hl|hr := h1'
      · simp[hl, ←defaults_eq]
        rfl
      · simp[hr, ←defaults_eq, (f a.1).pointed_toFun]
    }
    have h2'' : (f.toContinuousMap b.1).toContinuousMap b.2 = Inhabited.default := by{
      obtain hl|hr := h2'
      · simp[hl, ←defaults_eq]
        rfl
      · simp[hr, ←defaults_eq, (f a.1).pointed_toFun]
    }

    simp[FunLike.coe]
    rw[h1'', h2'']
  · rw[hc2]
}



/-- The uncurried form of a continuous map `X → C⋆(Y, Z)` for `Y` locally compact is a continuous map `X ⋀ Y → Z`. -/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace Y] (k:C⋆(X, C⋆(Y, Z))) : Continuous (k.uncurry') := by{
  simp[uncurry']
  apply Continuous.quotient_lift
  simp[toFun_toFun]
  let g : X → C(Y, Z) := fun x ↦ (k x).toContinuousMap
  exact ContinuousMap.continuous_uncurry_of_continuous (ContinuousMap.mk g (by continuity))
}

theorem pointed_uncurry (f:C⋆(X, C⋆(Y, Z))) : f.uncurry' Inhabited.default = Inhabited.default := by{
  let _:= smash_setoid X Y
  simp[uncurry']
  have : (Inhabited.default : X ⋀ Y) = Quotient.mk _ (Inhabited.default, Inhabited.default) := rfl
  rw[this]
  simp[toFun_toFun]
}

/-- The uncurrying of a pointed function X → (Y → Z)  to a map in C⋆(X ⋀ Y, Z). This is not the same as Function.uncurry, which maps to X × Y → Z -/
def uncurry (f:C⋆(X, C⋆(Y, Z))) : C⋆(X ⋀ Y, Z) where
  toFun := f.uncurry'
  continuous_toFun := f.continuous_uncurry_of_continuous
  pointed_toFun := f.pointed_uncurry


/- [TODO] Turn curry and uncurry into continuous maps between the corresponding pointed topological spaces (see original file).-/


/-- Currying is an equivalence for Y locally compact, with inverse given by uncurrying-/
def equiv_curry : C⋆(X ⋀ Y, Z) ≃ C⋆(X, C⋆(Y,Z)) where
  toFun := curry
  invFun := uncurry
  left_inv := by{
    simp[LeftInverse]
    intro F
    ext p
    obtain ⟨p', hp'⟩ := Quotient.exists_rep p
    rw[← hp']
    rfl
  }
  right_inv := by{
    simp[Function.RightInverse, LeftInverse]
    intro F
    ext x y
    rfl
  }

theorem pointed_equiv_curry: @equiv_curry X _ Y _ _ Z _  Inhabited.default = Inhabited.default := rfl


/- Rephrasing this in categorical terms and showing naturality, we show the desired adjunction-/

-- First, we need to define the hom endofunctor C⋆(X,-)
variable {X Y} in
def hom_induced (f: C⋆(Y, Z)) : C⋆(C⋆(X, Y), C⋆(X,Z)) where
  toFun := fun g ↦ f.comp g
  pointed_toFun := by {
    ext x
    simp
    have : (Inhabited.default: C⋆(X,Y)).toFun x = Inhabited.default := rfl
    simp[FunLike.coe, this, f.pointed_toFun]
    rfl
  }
  continuous_toFun := by{
    apply continuous_induced_rng.mpr
    have : toContinuousMap ∘ (fun (g:C⋆(X,Y)) ↦ PointedMap.comp f g ) = (fun g ↦ ContinuousMap.comp f g) ∘ toContinuousMap := rfl
    rw[this]
    apply Continuous.comp
    · apply ContinuousMap.continuous_comp
    · exact continuous_induced_dom
  }


def inner_hom_left (Y: PointedTopCat) : Functor PointedTopCat PointedTopCat where
  obj (X:PointedTopCat) := PointedTopCat.of (PointedMap Y X)
  map := hom_induced
  --why isn't this giving me any error? Does aesop show everything else on its own?


/--The natural equivalence carrying the adjunction-/
def hom_smash_core (Y:Type) [PointedTopSpace Y] [LocallyCompactSpace Y]  : Adjunction.CoreHomEquiv (smash_whisker_r Y) (inner_hom_left (PointedTopCat.of Y)) where
  homEquiv (X Z : PointedTopCat) := equiv_curry
  homEquiv_naturality_left_symm := by{
    intros
    simp
    ext x
    simp at x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw[← hx']
    rfl
  }
  homEquiv_naturality_right := by{
    intros
    simp
    ext
    rfl
  }

/--The adjunction between the functor α ⋀ - and the internal hom functor Hom(α, -).-/
def smash_hom_adjunction : (smash_whisker_r Y) ⊣ (inner_hom_left (PointedTopCat.of Y)) := CategoryTheory.Adjunction.mkOfHomEquiv (hom_smash_core Y)

instance smash_leftadjoint : IsLeftAdjoint (smash_whisker_r Y) where
  right := (inner_hom_left (PointedTopCat.of Y))
  adj := smash_hom_adjunction






/- For Y = J the quotient of the unit interval by its extremes, we get a natural equivalence
  C⋆(X ⋀ J, Z) ≃ C⋆ (X, C⋆(J, Z))
  I haven't studied in detail how GenLoop is defined in Mathlib.Topology.Homotopy.HomotopyGroup
  but C⋆(J, Y) should be GenLoop 1 Y (= ΩY)
  In MoreWork.lean, I proved X ⋀ J ≃ₜ⋆ Σ₀ X is the pointed suspension
  Since pointed homeomorphisms A ≃ₜ⋆ A' and B ≃ₜ B' induce a natural equivalence
  C⋆(A, B) ≃ C⋆(A', B')
  we get a natural equivalence
  C⋆(Σ₀ X, Z) ≃ C⋆ (X, ΩZ)
  for all spaces X, Z.
  Now, if we prove that this maps homotopic maps to homotopic maps (probably just carry the homotopy to the other side)
  we can construct a natural
  [Σ₀ X, Z]⋆ ≃ [X, ΩZ]⋆
  which is what we ultimately want to show.
-/


end PointedMap

end adjunction
