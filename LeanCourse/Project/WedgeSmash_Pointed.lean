--import LeanCourse.Common
import Mathlib.CategoryTheory.Category.Pointed
import LeanCourse.Project.Quotients
import Mathlib.CategoryTheory.Closed.Monoidal

open BigOperators Function Set Filter Topology TopologicalSpace CategoryTheory

/- This file defines the wedge sum and smash product in the category of pointed types.
It shows that the cartesian product is the categorical product, the wedge sum is the coproduct,
and the wedge product is the tensor product, giving Pointed the structure of a closed monoidal category.

(This is not strictly related to the rest of the project, but it is currently still listed as "To do"
in Mathlib.CategoryTheory.Category.Pointed and I had done most of the work towards it for pointed topological spaces)
-/


universe u
variable (α: Pointed.{u}) (β: Pointed.{u})

namespace Pointed

instance : Inhabited α  where
  default := α.point


--I thought this would be in simp but never done in mathlib Pointed.lean
lemma forget_morph (f: α ⟶ β) : (forget Pointed).map f = f.toFun := rfl

/--For pointed types α and β, the setoid of their disjoint union α ⊕ β identifying the basepoints of the two types. Used to construct the wedge sum α ⋁ β.-/
def wedge_setoid : Setoid (α ⊕ β) := by{
  let A: Set (α ⊕ β) := { p : α ⊕ β | p = Sum.inl (α.point) ∨ p = Sum.inr (β.point)}
  exact quotient_setoid A
}

/--The wedge sum of two pointed types. That is, the quotient of the disjoint union identifying the two basepoints.-/
def wedge : Pointed where
  X := Quotient (wedge_setoid α β)
  point := Quotient.mk (wedge_setoid α β) (Sum.inl (α.point))


infix:50 " ⋁ " => wedge

@[simp] theorem wedge_defaults_equiv: Quotient.mk (wedge_setoid α  β) (Sum.inl (α.point)) = Quotient.mk (wedge_setoid α β) (Sum.inr (β.point)) := by{
  let _hwedge := wedge_setoid α β
  refine Quotient.eq.mpr ?_
  have : (wedge_setoid α β).r (Sum.inl default) (Sum.inr default) := by simp; constructor; rfl; rfl
  exact this
}


/--The quotient map α ⊕ β → α ⋁ β -/
def wedge_quot_mk := Quotient.mk (wedge_setoid α β)

/-- The natural inclusion map α → α ⋁ β -/
def wedge_inl : Pointed.Hom α (α ⋁ β) where
  toFun:= wedge_quot_mk _ _ ∘ Sum.inl
  map_point := rfl

/-- The natural inclusion map β → α ⋁ β -/
def wedge_inr : Pointed.Hom β (α ⋁ β) where
  toFun := wedge_quot_mk _ _ ∘ Sum.inr
  map_point := by{
    simp
    rw[wedge_quot_mk, ← wedge_defaults_equiv]
    rfl
  }


notation a "⋆⋁" B => wedge_inl _ B a
notation A "⋁⋆" b => wedge_inr A _ b

variable {γ: Pointed.{u}}

variable {α β} in
/--The function induced on the wedge sum α ⋁ β by two pointed functions α → γ and β → γ. This is the underlying function in wedge_induced-/
def wedge_induced_fun (f: Pointed.Hom α γ) (g: Pointed.Hom β γ) : (α ⋁ β) → γ := by{
  let _:= wedge_setoid α β
  apply Quotient.lift (Sum.elim f.toFun g.toFun)
  intro x y hxy
  have hxy' : (wedge_setoid α β).r x y := hxy
  simp[quotient_setoid_equiv_iff] at hxy'
  obtain ⟨h1, h2⟩|h3:= hxy'
  obtain hc1|hc2 := h1
  · obtain hd1| hd2 :=h2
    · rw[hc1, hd1]
    · rw[hc1, hd2]
      simp
      rw[f.map_point, g.map_point]
  · obtain hd1|hd2 := h2
    · rw[hc2, hd1]
      simp
      rw[f.map_point, g.map_point]
    · rw[hc2, hd2]
  · rw[h3]
}

variable{α β} in
lemma wedge_induced_pointed (f: Pointed.Hom α γ) (g: Pointed.Hom β γ) : wedge_induced_fun f g (α ⋁ β).point = γ.point := by{
  let _:=wedge_setoid α β
  simp[wedge_induced_fun]
  have : (α ⋁ β).point = Quotient.mk (wedge_setoid α β) (Sum.inl (α.point)) := rfl
  rw[this, Quotient.lift_mk]
  simp
  rw[f.map_point]
}


variable {α β} in
/--The pointed function induced on the wedge sum α ⋁ β to γ by two pointed functions α → γ and β → γ.-/
def wedge_induced (f: Pointed.Hom α γ) (g: Pointed.Hom β γ) : Pointed.Hom (α ⋁ β) γ where
  toFun := wedge_induced_fun f g
  map_point := wedge_induced_pointed f g


/-The wedge sum is a coproduct-/
open CategoryTheory.Limits

def wedge_cofan : BinaryCofan α β := BinaryCofan.mk (wedge_inl α β) (wedge_inr α β)

variable{α β} in
def wedge_desc (s: BinaryCofan α β) : α ⋁ β ⟶ s.pt := wedge_induced s.inl s.inr

instance wedge_iscolimit : IsColimit (wedge_cofan α β) := by{
  apply BinaryCofan.isColimitMk wedge_desc
  · intros; rfl
  · intros; rfl
  · intro s f hf₁ hf₂
    ext x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw[← hx']
    induction x'
    case inl a => {
      rw[Pointed.Hom.ext_iff] at hf₁
      have := congrFun hf₁ a
      exact this
    }
    case inr b => {
      rw[Pointed.Hom.ext_iff] at hf₂
      have := congrFun hf₂ b
      exact this
    }
}


-- I think the following maps are actually already defined for any binary coproduct in CategoryTheory.Limits.Shapes.BinaryProducts but I'll keep them here for now
-- Actually, there are also theorems (co)prod.hom_ext allowing to check equality of morphisms (from) to (co)products on the morphisms that induce them.
-- This might speed up some of the things below

/--The pointed function α ⋁ β → β ⋁ α induced by including each summand into itself -/
def wedge_swap := wedge_induced (wedge_inr β α) (wedge_inl β α)

lemma wedge_swap_swap : (wedge_swap α β).comp (wedge_swap β α) = Pointed.Hom.id _ := by{
  ext x
  simp[wedge_swap]
  obtain ⟨x', hx'⟩:= Quotient.exists_rep x
  rw[← hx']
  induction x'
  case inl y => rfl
  case inr z => rfl
}

/--The pointed equivalence α ⋁ β → β ⋁ α induced by swapping the two summands-/
def wedge_swap_iso : α ⋁ β ≅ β ⋁ α where
  hom:= wedge_swap α β
  inv := wedge_swap β α
  hom_inv_id := wedge_swap_swap α β
  inv_hom_id := wedge_swap_swap β α


protected def prod : Pointed where
  X:= α.X × β.X
  point := (α.point, β.point)



infix:50 " ×⋆ " => Pointed.prod


def prodFst : Pointed.Hom (α ×⋆ β) α where
  toFun := fun p ↦ p.1
  map_point := rfl

def prodSnd : Pointed.Hom (α ×⋆ β) β where
  toFun := fun p ↦ p.2
  map_point := rfl

-- This product is a categorical product
variable {α β} in
def prod_induced (f: Pointed.Hom γ α) (g: Pointed.Hom γ β) : Pointed.Hom γ (α ×⋆ β) where
  toFun := fun c ↦ (f.toFun c, g.toFun c)
  map_point:= by simp[f.map_point, g.map_point]; rfl

def prod_fan : BinaryFan α β := BinaryFan.mk (prodFst α β) (prodSnd α β)

variable{α β} in
def prod_lift (s: BinaryFan α β) : s.pt ⟶ α ×⋆ β := prod_induced s.fst s.snd

instance prod_isLimit : IsLimit (prod_fan α β) := by{
  apply BinaryFan.isLimitMk prod_lift
  · intros; rfl
  · intros; rfl
  · intro s f hf₁ hf₂
    ext x
    rw[Pointed.Hom.ext_iff] at hf₁
    have h1 : (f.toFun x).1 = ((prod_lift s).toFun x).1 := congrFun hf₁ x
    rw[Pointed.Hom.ext_iff] at hf₂
    have h2 : (f.toFun x).2 = ((prod_lift s).toFun x).2 := congrFun hf₂ x
    simp[FunLike.coe, forget_morph]
    have : f.toFun x = ((f.toFun x).1, (f.toFun x).2) := rfl
    rw[this]
    have : (prod_lift s).toFun x = (((prod_lift s).toFun x).1, ((prod_lift s).toFun x).2) := rfl
    rw[this, h1, h2]
}


def prod_inl : Pointed.Hom α (α ×⋆ β) where
  toFun := fun a ↦ (a, β.point)
  map_point:= by simp; rfl

def prod_inr : Pointed.Hom β (α ×⋆ β) where
  toFun := fun b ↦ (α.point, b)
  map_point := by simp; rfl

def prod_swap : Pointed.Hom (α ×⋆ β) (β ×⋆ α) where
  toFun:= fun (a, b) ↦ (b, a)
  map_point := by simp; rfl


-- this is not needed
theorem prod_swap_swap : (prod_swap α β).comp (prod_swap β α) = Pointed.Hom.id _ := rfl


def prod_swap_iso: (α ×⋆ β) ≅ (β ×⋆ α) where
  hom := prod_swap α β
  inv := prod_swap β α





def wedge_embedding := wedge_induced (prod_inl α β) (prod_inr α β)

--if something is in the image of the wedge embedding, then at least one of its coordinates is default
variable{α β} in
@[simp] lemma wedge_embedding_ran {p: α × β} (h: p ∈ range (wedge_embedding α β).toFun) : p.1=α.point ∨ p.2= β.point := by{
  let _:= wedge_setoid α β
  simp at h
  obtain ⟨t, ht⟩:=h
  obtain ⟨t', ht'⟩:= Quotient.exists_rep t
  rw[←ht, ← ht']
  induction t'
  case inl a => right; rfl
  case inr b => left; rfl
}


lemma wedge_embedding_inl (a : α) : (wedge_embedding α β).toFun ((wedge_inl α β).toFun a) = (a, β.point) := rfl

lemma wedge_embedding_inr (b : β) : (wedge_embedding α β).toFun ((wedge_inr α β).toFun b) = (α.point, b) := rfl

@[simp] lemma wedge_embedding_ran' {p: α × β} : (∃ y, (wedge_embedding α β).toFun y = p) ↔ p.1 = α.point ∨ p.2= β.point := by{
  constructor
  · intro h
    have : p ∈ range (wedge_embedding α β).toFun := h
    exact wedge_embedding_ran this
  · intro h
    obtain hc1|hc2 := h
    · use (wedge_inr α β).toFun p.2
      rw[wedge_embedding_inr, ←hc1]
    · use (wedge_inl α β).toFun p.1
      rw[wedge_embedding_inl, ←hc2]
}
-- Add more lemmas if needed

/-The setoid of α × β associated to the smash product-/
def smash_setoid : Setoid (α × β) := by{
  let A : Set (α × β) := (wedge_embedding α β).toFun '' univ
  exact quotient_setoid A
}

/-The smash product of two pointed types α and β, denoted by α ⋀ β -/
def smash : Pointed where
  X:= Quotient (smash_setoid α β)
  point := Quotient.mk (smash_setoid α β) (α.point, β.point)

infix:50 " ⋀  " => smash

variable {α β} in
def smash_elt (a:α) (b:β) : α ⋀ β := Quotient.mk (smash_setoid α β) (a,b)

infix:50 " ∧' " => smash_elt


variable {α β} in
lemma smash_elt_eq_iff (a a' : α) (b b' : β) : (smash_elt a b = smash_elt a' b') ↔ ( (a=α.point ∨ b=β.point) ∧ (a'=α.point ∨ b'=β.point) )∨ ( (a,b) = (a', b') ) := by{
  let _:= smash_setoid α β
  let _:= wedge_setoid α β
  simp[smash_elt]
  constructor
  · intro h
    have : (smash_setoid α β).r (a, b) (a', b') := Quotient.eq'.mp h
    simp at this
    assumption
  · intro h
    have : (smash_setoid α β).r (a, b) (a', b') := by {
      rw[quotient_setoid_equiv_iff]
      simp
      assumption
    }
    exact Quotient.eq.mpr this
}

variable {α β} in
lemma smash_elt_eq_iff' (p q : α × β) : Quotient.mk (smash_setoid α β) p = Quotient.mk (smash_setoid α β) q ↔ ( (p.1=α.point ∨ p.2=β.point) ∧ (q.1=α.point ∨ q.2=β.point) )∨ ( p = q ) := by{
  constructor
  · intro h
    have : (p.1 ∧' p.2) = (q.1 ∧' q.2) := h
    apply (smash_elt_eq_iff p.1 q.1 p.2 q.2).mp this
  · intro h
    rw[← smash_elt_eq_iff] at h
    exact h
}


@[simp] theorem smash_defaults_left (a: α) : (a ∧' β.point) = (α ⋀ β).point := by{
  have : (α ⋀ β).point = (α.point ∧' β.point) := rfl
  rw[this]
  simp[smash_elt_eq_iff]
}

@[simp] theorem smash_defaults_right (b:β) : (α.point ∧' b) = (α ⋀ β).point := by{
  have : (α ⋀ β).point = (α.point ∧' β.point) := rfl
  rw[this]
  rw[smash_elt_eq_iff]
  left
  simp
}

/-Construct an isomorphism α ⋀ β ≅ β ⋀ α -/

def smash_swap_fun : α ⋀ β → β ⋀ α := by {
  let _ : Setoid ((α ×⋆ β).X):= smash_setoid α β
  let _ : Setoid ((β ×⋆ α).X):= smash_setoid β α
  let _ := smash_setoid β α
  apply Quotient.lift ((Quotient.mk (smash_setoid β α))∘ (prod_swap α β).toFun)
  intro x y hxy
  rw[← Quotient.eq, smash_elt_eq_iff'] at hxy
  simp
  rw[← Quotient.eq]
  have hx : (prod_swap α β).toFun x = (x.2, x.1) := rfl
  have hy : (prod_swap α β).toFun y = (y.2, y.1) := rfl
  rw[hx, hy, smash_elt_eq_iff']
  simp
  tauto
}


def smash_swap : Pointed.Hom (α ⋀ β) (β ⋀ α) where
  toFun := smash_swap_fun α β
  map_point := rfl


lemma smash_swap_swap: (smash_swap α β).comp (smash_swap β α) = Pointed.Hom.id _ := by{
  ext x
  simp[smash_swap, smash_swap_fun]
  obtain ⟨x', hx'⟩ := Quotient.exists_rep x
  rw[← hx']
  rfl
}

def smash_swap_iso: (α ⋀ β) ≅ (β ⋀ α) where
  hom := smash_swap α β
  inv := smash_swap β α
  hom_inv_id := smash_swap_swap α β
  inv_hom_id := smash_swap_swap β α


-- From now on, the goal is to prove that the category of pointed types has the structure of a closed monoidal category

/--The pointed type {0,1} consisting of two points, with basepoint 0.-/
protected def two : Pointed.{u} where
  X := ULift (Fin 2)
  point := ⟨0, by norm_num⟩



instance fin_lift : Fintype (ULift (Fin 2)) := by infer_instance

protected def two_1 : Pointed.two := ⟨1, by norm_num⟩

@[simp]
lemma two_elts : Pointed.two_1 ≠ Pointed.two.point := by simp[Pointed.two_1, Pointed.two]

def left_uni_inv : Pointed.Hom α (Pointed.two ⋀ α) where
  toFun := fun a ↦ (Pointed.two_1 ∧' a)
  map_point := by simp


def left_uni_prod : Pointed.two × α → α := fun
  (x, a) ↦ if x.down.val = 0  then α.point else a

def left_uni_fun :(Pointed.two ⋀ α) → α := by{
  let _:= smash_setoid Pointed.two α
  apply Quotient.lift (left_uni_prod α)
  intro x y hxy
  rw[← Quotient.eq, smash_elt_eq_iff'] at hxy
  simp[left_uni_prod]
  obtain ⟨h1, h2⟩ |h3 := hxy
  · obtain hc1| hc1':= h1
    · obtain hc2|hc2' := h2
      · simp[hc1, hc2]
      · simp[hc1, hc2']
    · obtain hc2|hc2' := h2
      · simp[hc1', hc2]
      · simp[hc1', hc2']
  · rw[h3]
}


def left_uni : Pointed.Hom (Pointed.two ⋀ α) α where
  toFun := left_uni_fun α
  map_point:= by {
    let _:= smash_setoid Pointed.two α
    have : (Pointed.two ⋀ α).point = Quotient.mk (smash_setoid Pointed.two α) (Pointed.two.point, α.point) := rfl
    rw[this, left_uni_fun, Quotient.lift_mk]
    rfl
  }

lemma left_uni_hom_inv_id : (left_uni α).comp (left_uni_inv α) = Pointed.Hom.id _ := by{
  let _:= smash_setoid Pointed.two α
  let _: Fintype Pointed.two.X := fin_lift
  ext x
  obtain ⟨x', hx'⟩ := Quotient.exists_rep x
  rw[← hx']
  have : x' = (x'.1, x'.2) := rfl
  rw[this]

  obtain ⟨a, ha⟩ := @exists_eq _ x'.1

  fin_cases a
  · simp[Equiv.ulift] at ha
    rw[← ha]
    simp[left_uni_inv, left_uni, smash_elt, Pointed.two_1, left_uni_fun, left_uni_prod]
    rw[smash_elt_eq_iff']
    simp
    left
    left
    rfl
  · simp[Equiv.ulift] at ha
    rw[← ha]
    rfl
}


def left_uni_iso : (Pointed.two ⋀ α) ≅ α where
  hom := left_uni α
  inv := left_uni_inv α
  hom_inv_id := by apply left_uni_hom_inv_id
  inv_hom_id := rfl


def right_uni_iso : ( α ⋀ Pointed.two) ≅ α := (smash_swap_iso _ _).trans (left_uni_iso α)

variable {α β}
variable {α' β' : Pointed}
variable (f: Pointed.Hom α α') (g: Pointed.Hom β β')


def prod_map : Pointed.Hom (α ×⋆ β) (α' ×⋆ β') where
  toFun := fun x ↦ (f.toFun x.1, g.toFun x.2)
  map_point := by {
    have : (α ×⋆ β).point = (α.point, β.point) := rfl
    simp[this, f.map_point, g.map_point]
    rfl
  }

def smash_maps_fun : (α ⋀ β) → (α' ⋀ β') := by{
  let _ : Setoid (α ×⋆ β).X := smash_setoid α β
  let _:= smash_setoid α' β'
  apply Quotient.lift ( (Quotient.mk (smash_setoid α' β') )∘ (prod_map f g).toFun)
  intro x y hxy
  rw[← Quotient.eq, smash_elt_eq_iff'] at hxy
  rw[Function.comp, Function.comp, smash_elt_eq_iff']
  simp[prod_map]

  have : x.1 = α.point → f.toFun x.1 = α'.point := by intro k; rw[k]; exact f.map_point
  have : y.1 = α.point → f.toFun y.1 = α'.point := by intro k; rw[k]; exact f.map_point
  have : x.2 = β.point → g.toFun x.2 = β'.point := by intro k; rw[k]; exact g.map_point
  have : y.2 = β.point → g.toFun y.2 = β'.point := by intro k; rw[k]; exact g.map_point

  tauto
}


def smash_maps: Pointed.Hom (α ⋀ β) (α' ⋀ β') where
  toFun := smash_maps_fun f g
  map_point := by{
    let _: Setoid (α ×⋆ β).X := smash_setoid α β
    simp[smash_maps_fun, prod_map]
    have : (α ⋀ β).point = Quotient.mk (smash_setoid α β) (α.point, β.point) := rfl
    rw[this, Quotient.lift_mk]
    simp[f.map_point, g.map_point]
    rfl
  }

lemma smash_maps_id : smash_maps (Pointed.Hom.id α) (Pointed.Hom.id β) = Pointed.Hom.id (α ⋀ β) := by {
  ext x
  obtain ⟨x', hx'⟩:= Quotient.exists_rep x
  rw[← hx']
  rfl
}


variable (α) in
def smash_lw := smash_maps (Pointed.Hom.id α) g

def smash_rw {α α':Pointed} (f: Pointed.Hom α α') (β:Pointed):= smash_maps f (Pointed.Hom.id β)

lemma smash_lw_id : smash_lw α (Pointed.Hom.id β) = Pointed.Hom.id _ := by{
  rw[smash_lw]
  apply smash_maps_id
}

lemma smash_id_rw : smash_rw (Pointed.Hom.id α) β = Pointed.Hom.id _ := by{
  rw[smash_rw]
  apply smash_maps_id
}


lemma smash_maps_w : smash_maps f g = (smash_rw f β).comp (smash_lw α' g) := by{
  ext x
  obtain ⟨x', hx'⟩ := Quotient.exists_rep x
  rw[← hx']
  rfl
}

lemma smash_maps_comp (α₁ α₂ β₁ β₂ γ₁ γ₂ : Pointed) (f₁: Pointed.Hom α₁ β₁) (f₂: Pointed.Hom α₂ β₂) (g₁: Pointed.Hom β₁ γ₁) (g₂: Pointed.Hom β₂ γ₂) : (smash_maps f₁ f₂).comp (smash_maps g₁ g₂) = smash_maps (f₁.comp g₁) (f₂.comp g₂) := by{
  ext x
  obtain ⟨x', hx'⟩ := Quotient.exists_rep x
  rw[← hx']
  rfl
}


variable (α β γ)

namespace Hom

/--The pointed type of pointed maps between two pointed types.-/
protected def set : Pointed where
  X := Pointed.Hom α β
  point := ⟨fun _ ↦ β.point, by simp⟩

variable {α β γ} in
def set_induced (f: Pointed.Hom β γ) : Pointed.Hom (Pointed.Hom.set α β) (Pointed.Hom.set α γ) where
  toFun := fun g ↦ g.comp f
  map_point := by {
    apply Pointed.Hom.ext
    ext x
    simp
    have : (Hom.set α β).point.toFun x = β.point := rfl
    rw[this, f.map_point]
    rfl
  }


/-- The endofunctor Hom(α, -) -/
def setLeft (α:Pointed) : Functor Pointed Pointed where
  obj := Pointed.Hom.set α
  map := set_induced




variable {α β γ}


def coe (f: Pointed.Hom.set α (Pointed.Hom.set β γ)) : α → (β → γ) := fun a ↦ (f.toFun a).toFun


-- This part (definitions and properties of currying and uncurrying) is adapted from Mathlib.Topology.CompactOpen

def curry' (f: Pointed.Hom (α ⋀ β) γ) : α → (Pointed.Hom β γ) := fun a ↦ ⟨fun b ↦ f.toFun (a ∧' b), by simp[f.map_point]⟩


def curry (f: Pointed.Hom (α ⋀ β) γ) : Pointed.Hom α (Pointed.Hom.set β γ) where
  toFun := curry' f
  map_point := by simp[curry', f.map_point]; rfl


def curry_hom : Pointed.Hom (Pointed.Hom.set (α ⋀ β) γ) (Pointed.Hom.set α (Pointed.Hom.set β γ)) where
  toFun := curry
  map_point := rfl


@[simp]
theorem curry_apply (f: Pointed.Hom (α ⋀ β) γ) (a : α) (b : β) : (f.curry.toFun a).toFun b = f.toFun (a ∧'b) := rfl

def uncurry' (f: Pointed.Hom α (Pointed.Hom.set β γ)) : α ⋀ β → γ := by {
  let _:= smash_setoid α β
  apply Quotient.lift (Function.uncurry (coe f))
  intro x y hxy
  rw[←Quotient.eq, smash_elt_eq_iff' ] at hxy
  simp[Function.uncurry]
  have h1 : x.1 = α.point → coe f x.1 x.2 = γ.point := by intro h; simp[h, coe, f.map_point]; rfl
  have h2 : y.1 = α.point → coe f y.1 y.2 = γ.point := by intro h; simp[h, coe, f.map_point]; rfl
  have h3 : x.2 = β.point → coe f x.1 x.2 = γ.point := by intro h; simp[h, coe, (f.toFun x.1).map_point]
  have h4 : y.2 = β.point → coe f y.1 y.2 = γ.point := by intro h; simp[h, coe, (f.toFun y.1).map_point]

  obtain ⟨ha | hb, hc| hd⟩|he := hxy
  · rw[h1 ha, h2 hc]
  · rw[h1 ha, h4 hd]
  · rw[h3 hb, h2 hc]
  · rw[h3 hb, h4 hd]
  · rw[he]
}

def uncurry (f: Pointed.Hom α (Pointed.Hom.set β γ)) : Pointed.Hom (α ⋀ β) γ where
  toFun := uncurry' f
  map_point := by {
    let _ := smash_setoid α β
    simp[uncurry']
    have : (α ⋀ β).point = Quotient.mk _ (α.point, β.point) := rfl
    rw[this]
    simp[coe, f.map_point]
    rfl
  }


def uncurry_hom : Pointed.Hom (Pointed.Hom.set α (Pointed.Hom.set β γ)) (Pointed.Hom.set (α ⋀ β ) γ) where
  toFun := uncurry
  map_point := by{
    apply Pointed.Hom.ext
    ext x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw [← hx']
    rfl
  }

lemma uncurry_curry (f:Pointed.Hom (α ⋀ β) γ) : uncurry (curry f) = f := by {
  ext x
  obtain ⟨x', hx'⟩ := Quotient.exists_rep x
  rw [← hx']
  rfl
}

lemma curry_uncurry (f: Pointed.Hom α (Pointed.Hom.set β γ)) : curry (uncurry f) = f := rfl

def curry_equiv: Pointed.Hom (α ⋀ β) γ ≃ Pointed.Hom α (Pointed.Hom.set β γ) where
  toFun := curry
  invFun := uncurry
  left_inv := by{intro f; apply uncurry_curry}
  right_inv := by{intro f; apply curry_uncurry}


def curry_iso : Pointed.Hom.set (α ⋀ β) γ ≅ Pointed.Hom.set α (Pointed.Hom.set β γ) where
  hom := curry_hom
  inv := uncurry_hom
  hom_inv_id := by {apply Pointed.Hom.ext; ext; apply uncurry_curry}
  inv_hom_id := by {apply Pointed.Hom.ext; ext; apply curry_uncurry}




end Hom

variable {α β γ}

def smash_assoc_curried'' (a:α) (b:β) : Pointed.Hom γ (α ⋀ (β ⋀ γ)) where
  toFun := fun c ↦ a ∧' (b ∧' c)
  map_point := by simp

def smash_assoc_curried' (a:α) : Pointed.Hom β (Pointed.Hom.set γ (α ⋀ (β ⋀ γ))) where
  toFun := fun b ↦ smash_assoc_curried'' a b
  map_point := by {simp; apply Pointed.Hom.ext; ext c; simp[smash_assoc_curried'']; rfl}


def smash_assoc_curried : Pointed.Hom α (Pointed.Hom.set β (Pointed.Hom.set γ (α ⋀ (β ⋀ γ)))) where
  toFun := fun a ↦ smash_assoc_curried' a
  map_point := by simp[smash_assoc_curried', smash_assoc_curried'']; rfl

variable (α β γ) in
def smash_assoc := Pointed.Hom.uncurry (Pointed.Hom.uncurry (@smash_assoc_curried α β γ))




def smash_assoc_inv_curried'' (a:α) (b:β) : Pointed.Hom γ ((α ⋀ β) ⋀ γ) where
  toFun := fun c ↦ ((a ∧' b) ∧' c)
  map_point := by simp


def smash_assoc_inv_curried' (a:α) : Pointed.Hom β (Pointed.Hom.set γ ((α ⋀ β) ⋀ γ)) where
  toFun := fun b ↦ smash_assoc_inv_curried'' a b
  map_point := by {simp; apply Pointed.Hom.ext; ext c; simp[smash_assoc_inv_curried'']; rfl}


def smash_assoc_inv_curried : Pointed.Hom α (Pointed.Hom.set (β ⋀ γ) ((α ⋀ β) ⋀ γ)) where
  toFun := fun a ↦ Pointed.Hom.uncurry (smash_assoc_inv_curried' a)
  map_point := by {
    simp[smash_assoc_inv_curried', smash_assoc_inv_curried'']
    apply Pointed.Hom.ext
    ext x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw[← hx']
    rfl
  }

variable (α β γ) in
def smash_assoc_inv := Pointed.Hom.uncurry (@smash_assoc_inv_curried α β γ)

lemma smash_assoc_comp_inv : (smash_assoc α β γ).comp (smash_assoc_inv α β γ) = Pointed.Hom.id _ := by {
  ext x
  obtain ⟨x', hx'⟩ := Quotient.exists_rep x
  rw[← hx']
  have : x' = (x'.1, x'.2) := rfl
  rw[this]
  obtain ⟨y, hy⟩ := Quotient.exists_rep x'.1
  rw[← hy]
  rfl
}

lemma smash_assoc_comp_inv' : (smash_assoc_inv α β γ).comp (smash_assoc α β γ) = Pointed.Hom.id _ := by {
  ext x
  obtain ⟨x', hx'⟩ := Quotient.exists_rep x
  rw[← hx']
  have : x' = (x'.1, x'.2) := rfl
  rw[this]
  obtain ⟨y, hy⟩ := Quotient.exists_rep x'.2
  rw[← hy]
  rfl
}

variable (α β γ) in
def smash_associator : (α ⋀ β) ⋀ γ ≅ α ⋀ (β ⋀ γ) where
  hom := smash_assoc α β γ
  inv := smash_assoc_inv α β γ
  hom_inv_id := smash_assoc_comp_inv
  inv_hom_id := smash_assoc_comp_inv'


open MonoidalCategory



instance : MonoidalCategory Pointed where
  tensorObj := smash
  whiskerLeft := smash_lw
  whiskerRight := smash_rw
  tensorUnit := Pointed.two
  associator := smash_associator
  leftUnitor := left_uni_iso
  rightUnitor := right_uni_iso

  tensorHom := smash_maps
  tensorHom_def := by {intros; apply smash_maps_w}
  tensor_id := by {intros; apply smash_maps_id}
  tensor_comp := by {intros; symm; apply smash_maps_comp}
  whiskerLeft_id := by {intros; apply smash_lw_id}
  id_whiskerRight := by {intros; apply smash_id_rw}
  associator_naturality := by {
    intros
    ext x
    simp at x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    have : x' = (x'.1, x'.2) := rfl
    rw[← hx', this]
    obtain ⟨y, hy⟩ := Quotient.exists_rep x'.1
    rw[← hy]
    rfl
    }
  leftUnitor_naturality := by{
    let _ :Fintype Pointed.two.X := fin_lift
    intro X Y f
    ext x
    simp at x
    obtain ⟨x', hx'⟩:= Quotient.exists_rep x
    rw[← hx']
    have : x' = (x'.1, x'.2) := rfl
    rw[this]
    obtain ⟨a, ha⟩ := @exists_eq _ x'.1
    rw[← ha]
    simp
    fin_cases a
    · simp[Equiv.ulift]
      have : (Quotient.mk (smash_setoid Pointed.two X) ({ down := 0 }, x'.2)) = (Pointed.two ⋀ X).point := by{
        have : (Pointed.two ⋀ X).point = (Quotient.mk (smash_setoid Pointed.two X) ({ down := 0 }, X.point)) := rfl
        rw[this, smash_elt_eq_iff']
        simp; left; rfl
      }
      rw[this]
      simp[FunLike.coe, forget_morph]
      simp[left_uni_iso]
      rw[(left_uni X).map_point, f.map_point, (smash_maps (𝟙 Pointed.two) f).map_point, (left_uni Y).map_point]
    · simp[Equiv.ulift]
      rfl
  }
  rightUnitor_naturality := by{
    let _ :Fintype Pointed.two.X := fin_lift
    intro X Y f
    ext x
    simp at x
    obtain ⟨x', hx'⟩:= Quotient.exists_rep x
    rw[← hx']
    have : x' = (x'.1, x'.2) := rfl
    rw[this]
    obtain ⟨a, ha⟩ := @exists_eq _ x'.2
    rw[← ha]
    simp
    fin_cases a
    · simp[Equiv.ulift]
      have : (Quotient.mk (smash_setoid X Pointed.two) (x'.1, { down := 0 })) = (X ⋀ Pointed.two).point := by{
        have : (X ⋀ Pointed.two).point = (Quotient.mk (smash_setoid X Pointed.two) (X.point, { down := 0 })) := rfl
        rw[this, smash_elt_eq_iff']
        simp; left; right; rfl
      }
      rw[this]
      simp[right_uni_iso, smash_swap_iso, left_uni_iso]
      simp[FunLike.coe, forget_morph]
      rw[(smash_swap X Pointed.two).map_point, (left_uni X).map_point, f.map_point, (smash_maps f (𝟙 Pointed.two)).map_point, (smash_swap Y Pointed.two).map_point, (left_uni Y).map_point]
    · simp[Equiv.ulift]
      rfl
  }

  pentagon := by{
    intros
    simp
    ext x
    simp at x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    have : x' = (x'.1, x'.2) := rfl
    rw[← hx', this]
    obtain ⟨y, hy⟩ := Quotient.exists_rep x'.1
    have : y = (y.1, y.2) := rfl
    rw[← hy, this]
    obtain ⟨y', hy'⟩ := Quotient.exists_rep y.1
    rw[←hy']
    rfl
    }
  triangle := by{
    let _ :Fintype Pointed.two.X := fin_lift
    intro X Y
    simp
    ext x
    obtain ⟨x', hx'⟩:= Quotient.exists_rep x
    rw[← hx']
    have : x' = (x'.1, x'.2) := rfl
    rw[this]
    obtain ⟨y, hy⟩ := Quotient.exists_rep x'.1
    rw[← hy]
    have : y= (y.1, y.2) := rfl
    rw[this]
    obtain ⟨a, ha⟩ := @exists_eq _ y.2
    rw[← ha]
    fin_cases a
    · simp[FunLike.coe, forget_morph]
      have h1 : Quotient.mk (smash_setoid X Pointed.two) (y.1, EquivLike.coe Equiv.ulift.symm 0)  = (X ⋀ Pointed.two).point := by {
        simp[EquivLike.coe, Equiv.ulift]
        have : (X ⋀ Pointed.two).point = (Quotient.mk (smash_setoid X Pointed.two) (X.point, { down := 0 })) := rfl
        rw[this, smash_elt_eq_iff']
        simp
        left; right; rfl
      }
      have h2 : Quotient.mk (smash_setoid (X ⋀ Pointed.two) Y) ((X ⋀ Pointed.two).point, x'.2) = ((X ⋀ Pointed.two) ⋀ Y).point := by{
        have : ((X ⋀ Pointed.two) ⋀ Y).point = Quotient.mk (smash_setoid (X ⋀ Pointed.two) Y) ((X ⋀ Pointed.two).point, Y.point) := rfl
        rw[this, smash_elt_eq_iff']
        simp
      }
      rw[h1, h2, (smash_maps _ _).map_point, (smash_associator _ _ _).hom.map_point, (smash_maps _ _).map_point]
    · rfl
  }


-- Show that this category is monoidal closed (aka hom-tensor adjunction, where tensor=smash)
variable (α β γ)


def smash_symm_hom (f:Pointed.Hom (α ⋀ β) γ): Pointed.Hom (β ⋀ α) γ := (smash_swap β α).comp f

def smash_symm_hom_equiv : Pointed.Hom (α ⋀ β) γ ≃ Pointed.Hom (β ⋀ α) γ where
  toFun := smash_symm_hom α β γ
  invFun := smash_symm_hom β α γ
  left_inv := by {
    simp[LeftInverse]
    intros
    ext x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw[← hx']
    rfl
  }
  right_inv := by{
    simp[Function.RightInverse, LeftInverse]
    intros
    ext x
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    rw[← hx']
    rfl
  }


def hom_smash_core : Adjunction.CoreHomEquiv (tensorLeft α) (Hom.setLeft α) where
  homEquiv (β γ : Pointed) := (smash_symm_hom_equiv α β γ).trans Hom.curry_equiv
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
def smash_hom_adjunction : (tensorLeft α) ⊣ (Hom.setLeft α) := CategoryTheory.Adjunction.mkOfHomEquiv (hom_smash_core α)

instance smash_leftadjoint : IsLeftAdjoint (tensorLeft α) where
  right := Hom.setLeft α
  adj := smash_hom_adjunction α


instance isclosed : Closed α where
  isAdj := smash_leftadjoint α

instance : MonoidalClosed Pointed where
  closed := isclosed


end Pointed

--#lint
