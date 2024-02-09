import LeanCourse.Common
import Mathlib.Topology.Instances.Real

/-
This file defines the setoid associated to collapsing a subset into a point and provides some basic lemmas.
It is mostly useful to streamline definitions of quotient subspaces obtained by collapsing a subspace.
-/

variable {X:Type*}


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


@[simp] theorem quotient_setoid_equiv_iff (A: Set X) (x y : X) : (quotient_setoid A).r x y ↔ ((x ∈ A ∧ y ∈ A) ∨ x = y ) := by {
  exact Iff.rfl
}

@[simp] theorem quotient_setoid_equiv (A: Set X) (s: Setoid X) (h : s = quotient_setoid A) (x y : X) : x ≈ y ↔  ((x ∈ A ∧ y ∈ A) ∨ x = y ) := by {
  have: s.r x y ↔ x ≈ y := by exact Iff.rfl
  rw[← this]
  simp[h]
}

/--The setoid for taking a quotient in which to two disjoint subspaces A and B are collapsed to one point each-/
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


-- I don't think I have ever used the following in the actual project, it does not save that much time anyway:

-- This defines a function X/∼  → Y/∼
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
