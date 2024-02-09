import LeanCourse.Project.WedgeSmash_Spaces
import LeanCourse.Project.Suspension


open BigOperators Function Set Filter Topology TopologicalSpace CategoryTheory

noncomputable section

/- This file shows that smashing a pointed space with a sphere - ⋀ 𝕊¹ is (TODO: naturally) isomorphic to taking its suspension.
  This would ideally allow to derive the suspension-loop space adjunction from the general adjunction in WedgeSmash_Spaces.

  Strategy:
  - Show that 𝕊¹ is (pointed) homeomorphic to the unit interval I quotiented out by its endpoints
  - Show that X ⋀ I/~ is (pointed) homeomorphic to the based suspension Σ₀ X (ONE PROOF STILL MISSING)
-/


--define the spheres Sⁿ

variable (n:ℕ)
notation "𝕊" n => Metric.sphere (0:EuclideanSpace ℝ (Fin (n+1) )) 1
noncomputable instance: TopologicalSpace (EuclideanSpace ℝ (Fin (n+1) )) := by exact UniformSpace.toTopologicalSpace
instance: TopologicalSpace (𝕊 n) := instTopologicalSpaceSubtype


instance: Inhabited (𝕊 n) where
  default := ⟨EuclideanSpace.single (0: Fin 1) (1:ℝ) , by simp⟩ --for some reason, writing Fin 1 works for all n, but n+1 fails



--Goal: Show that S¹≃ₜ I/∼
notation "circle" => 𝕊 1


@[simp] theorem fin_simplify (t: Fin (1+1)) : t = 0 ∨ t = 1 := by{
  fin_cases t
  simp
  simp
}


def wrap : I → circle := fun t ↦ ⟨ fun i ↦ i * Real.sin (2*Real.pi*t) + (1-i) * Real.cos (2 * Real.pi * t), by {simp[EuclideanSpace.norm_eq, Finset.sum_range_succ, Finset.sum_fin_eq_sum_range]} ⟩


lemma Icc_distance' (a b : I) :  b.val - a.val ≤ 1 := by {
  have := b.2
  simp at this
  have that := a.2
  simp at that
  simp
  calc b.val ≤ 1 := this.2
  _ ≤ 1 + 0 := by {ring; simp}
  _ ≤ 1 + a.val := by {simp[that.1]}
}


lemma Icc_distance (a b : I) : (b.val - a.val ≤ 1 ) ∧ (b.val - a.val ≥ -1) := by {
  constructor
  · exact Icc_distance' a b
  · have := Icc_distance' b a
    simp
    exact tsub_le_iff_left.mp this
}

lemma Icc_distance_one' (a b : I) (h: b.val - a.val = 1) : b=1 := by{
  have := b.2
  have that := a.2
  simp at this
  simp at that
  apply ge_antisymm
  · calc 1 = b.val -a.val := h.symm
    _ ≤ b := by simp[that.1]
  · exact this.2
}

lemma Icc_distance_one (a b : I) (h: b.val - a.val = 1) : b=1 ∧ a = 0 := by{
  constructor
  · exact Icc_distance_one' a b h
  · have := Icc_distance_one' a b h
    rw[this] at h
    norm_num at h
    assumption
}

-- How is this not in mathlib? Was I just bad at searching?
lemma Real.sin_cos_eq_iff {t s : ℝ} (hsin: Real.sin t = Real.sin s) (hcos: Real.cos t = Real.cos s) : ∃ k: ℤ, s = 2*k*Real.pi + t := by {
  obtain ⟨k, hk⟩ :=  Real.cos_eq_cos_iff.mp hcos
  obtain hc1|hc2 := hk
  · use k
  · have h1 : sin s = - sin s := by {
    calc
    sin s = sin (2*k*Real.pi - t) := congrArg Real.sin hc2
    _ = - sin t := by {rw[←Real.sin_neg t, Real.sin_eq_sin_iff]; use -k; left; push_cast; ring}
    _ = - sin s := by rw[hsin]
  }
    have h2s : sin s = 0 := by {simp at h1; assumption}
    have h2t : sin t = 0 := by {rw[hsin]; assumption}
    obtain ⟨i,hi⟩ := Real.sin_eq_zero_iff.mp h2s
    obtain ⟨j,hj⟩ := Real.sin_eq_zero_iff.mp h2t
    rw[←hi, ←hj] at hc2
    have hc2' : j * Real.pi = 2*k*Real.pi - i*Real.pi := by simp[hc2]
    use i-k
    rw[← hi, ←hj, hc2']
    have : 2 * ↑(i-k) * Real.pi = 2*i*Real.pi - 2*k*Real.pi := by {push_cast; ring}
    rw[this]
    ring
}



lemma wrap_eq_iff_mp (a b : I) (h: wrap a = wrap b) : ((a=0 ∨ a=1) ∧ (b=0 ∨ b=1)) ∨ a=b := by{
  have : (wrap a).val 1 = (wrap b).val 1 := by exact congrFun (congrArg Subtype.val h) 1
  have h1 : Real.sin (2*Real.pi * a) = Real.sin (2*Real.pi * b) := by{
    simp[wrap] at this
    assumption
  }

  have : (wrap a).val 0 = (wrap b).val 0 := by exact congrFun (congrArg Subtype.val h) 0
  have h2 : Real.cos (2*Real.pi * a) = Real.cos (2*Real.pi * b) := by{
    simp[wrap] at this
    assumption
  }

  obtain ⟨k, hk⟩ := Real.sin_cos_eq_iff h1 h2
  rw[mul_assoc 2 (k:ℝ), mul_comm (k:ℝ), ←mul_assoc, ←mul_add (2*Real.pi)] at hk
  simp [Real.pi_ne_zero, mul_right_inj' ] at hk
  have hk' := eq_sub_of_add_eq (id hk.symm)
  have hk1 : k ≤ 1 ∧ k ≥ -1 := by {
    constructor
    · apply (@Int.cast_le ℝ _ _ k 1).mp
      rw[hk']
      have : ((1:ℤ ) : ℝ ) = 1 := by norm_num
      rw[this]
      exact (Icc_distance a b).1
    · apply (@Int.cast_le ℝ _ _ (-1) k).mp
      have : ((-1:ℤ ) : ℝ ) = -1 := by norm_num
      rw[hk', this]
      exact (Icc_distance a b).2
  }

  have hk2 : k=0 ∨ k=1 ∨ k =-1 := by{
    obtain ⟨hk1a, hk1b⟩ := hk1
    interval_cases k <;> tauto
  }

  obtain hd1|hd2|hd3 := hk2
  · right
    rw[hd1] at hk
    simp at hk
    exact SetCoe.ext (id hk.symm)
  · have hc1'': b.val -a.val = 1 := by simp[hk, hd2]
    have := Icc_distance_one a b hc1''
    tauto
  · have hc1'' : a.val - b.val = 1 := by simp [hk, hd3]
    have := Icc_distance_one b a hc1''
    tauto
}


lemma wrap_eq_iff (a b : I): wrap a = wrap b ↔ ((a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1)) ∨ a = b := by{
  constructor
  · exact fun a_1 ↦ wrap_eq_iff_mp a b a_1
  · intro h
    obtain hc1|hc2 := h
    · have: wrap 0 = wrap 1 := by simp[wrap]
      obtain ⟨hx, hy⟩ := hc1
      obtain hd1|hd2 := hx
      · obtain he1|he2 := hy
        · rw[hd1, he1]
        · rw[hd1, he2, this]
      · obtain he1|he2 := hy
        · rw[hd2, he1, this]
        · rw[hd2, he2]
    · rw[hc2]
}

lemma continuous_wrap: Continuous wrap := by {
  simp[wrap]
  refine Continuous.subtype_mk ?h fun x ↦ wrap.proof_2 x
  rw [continuous_pi_iff]
  intro i
  continuity
}


def I_quotient: Setoid (I) := quotient_setoid ({x: I | x = 0 ∨ x = 1})

def J := Quotient I_quotient
instance: TopologicalSpace J := instTopologicalSpaceQuotient
instance: Inhabited J where
  default:= Quotient.mk I_quotient 0

lemma I_quotient_default (t: I) : Quotient.mk I_quotient t = (default:J) ↔ (t=0 ∨ t=1) := by{
  let _:= I_quotient
  simp[default]
  have : t ≈ 0 ↔ Setoid.r t 0 := Iff.rfl
  rw[this]
  simp[quotient_setoid_equiv_iff]
  tauto
}

lemma I_quotient_eq (s t : I) : Quotient.mk I_quotient s = Quotient.mk I_quotient t ↔ ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨ s = t := by{
  let _:= I_quotient
  rw[Quotient.eq]
  have : ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ↔ s ∈ ({x: I | x = 0 ∨ x = 1}) ∧ t ∈ ({x: I | x = 0 ∨ x = 1}) := by simp
  rw[this]
  apply quotient_setoid_equiv
  rfl
}


def wrap_quot: J → circle := by{
  apply Quotient.lift wrap
  intro x y hxy
  rw[wrap_eq_iff]
  have: (I_quotient).r x y := hxy
  simp[quotient_setoid_equiv_iff] at this
  exact this
}


lemma continuous_wrap_quot : Continuous wrap_quot := by {
  apply Continuous.quotient_lift
  exact continuous_wrap
}

lemma injective_wrap_quot : Injective wrap_quot := by{
  let _:= I_quotient
  rw[Injective]
  intro s t hst
  simp[wrap_quot] at hst
  obtain ⟨i, hi⟩ := Quotient.exists_rep s
  obtain ⟨j, hj⟩ := Quotient.exists_rep t
  rw[← hi, ← hj, Quotient.lift_mk, Quotient.lift_mk] at hst

  have h' : (I_quotient).r i j := by {
    simp[quotient_setoid_equiv_iff]
    rw[← wrap_eq_iff]
    assumption
  }
  rw[← hi, ← hj]
  rw [Quotient.eq]
  exact h'
}


lemma surjective_wrap_quot : Surjective wrap_quot := by {
  simp[wrap_quot]
  rw [Quot.surjective_lift]
  simp[wrap, Surjective]
  intro x hx
  simp[EuclideanSpace.norm_eq, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hx
  have hx': (x 1)^2 = 1 - (x 0)^2 := by simp [eq_sub_of_add_eq' hx]

  have hx₁: (x 0)^2 ≤ 1 := by{
    calc (x 0)^2 ≤ (x 0)^2 + (x 1)^2 := by apply le_add_of_nonneg_right; simp[sq_nonneg]
    _ = 1 := by simp[hx]
  }
  simp at hx₁
  have hx₂ := neg_le_of_abs_le hx₁
  have hx₃ := le_of_abs_le hx₁

  have hπ : Real.pi * (Real.pi)⁻¹ = 1 := mul_inv_cancel Real.pi_ne_zero

  by_cases h: x 1 ≥ 0
  · use (Real.arccos (x 0)) / (2*Real.pi)
    constructor
    · constructor
      · rw[div_nonneg_iff]
        left; constructor
        · exact Real.arccos_nonneg _
        · norm_num; apply le_of_lt Real.pi_pos
      · rw[div_le_one (by norm_num; apply Real.pi_pos)]
        calc Real.arccos (x 0) ≤ Real.pi := Real.arccos_le_pi (x 0)
        _ = 1 * Real.pi := by rw[one_mul]
        _ ≤ 2 * Real.pi := by gcongr; norm_num

    · rw[mul_comm]
      ring
      rw[mul_assoc, hπ]
      ring
      rw[Real.cos_arccos hx₂ hx₃]
      rw[Real.sin_arccos]

      have hx₄: x 1 = Real.sqrt (1 - (x 0)^2) := by {
        have := congrArg Real.sqrt hx'
        simp[h] at this
        simp[this]
      }
      funext i
      fin_cases i
      · simp
      · simp[hx₄]


  · use (2 * Real.pi - Real.arccos (x 0)) /(2*Real.pi)
    simp at h
    constructor
    · constructor
      · apply div_nonneg
        · simp
          calc Real.arccos (x 0) ≤ Real.pi := Real.arccos_le_pi (x 0)
          _ = 1 * Real.pi := (one_mul Real.pi).symm
          _ ≤ 2 * Real.pi := by gcongr; norm_num
        · norm_num; exact le_of_lt Real.pi_pos
      · rw[div_le_one (by norm_num; apply Real.pi_pos)]
        simp
        exact Real.arccos_nonneg (x 0)
    · ring
      rw[mul_assoc, mul_comm (Real.arccos (x 0)), ←mul_assoc, pow_two, mul_assoc Real.pi Real.pi, hπ]
      simp

      have hx₄: x 1 = - Real.sqrt (1 - (x 0)^2) := by {
        have := congrArg Real.sqrt hx'
        simp[Real.sqrt_sq_eq_abs, abs_of_neg h] at this
        have := congrArg Neg.neg this
        simp at this
        simp[this]
      }

      funext i
      fin_cases i
      · ring; simp
        rw[mul_comm, Real.cos_add_two_pi, Real.cos_neg, Real.cos_arccos hx₂ hx₃]
      · ring; simp[hx₄]
        rw[mul_comm, Real.sin_add_two_pi, Real.sin_neg, Real.sin_arccos]
}



def wrap_quot_equiv: J ≃ circle := by{
  apply Equiv.ofBijective wrap_quot
  rw[Bijective]
  constructor
  · exact injective_wrap_quot
  · exact surjective_wrap_quot
}

lemma continuous_wrap_quot_equiv : Continuous wrap_quot_equiv := continuous_wrap_quot

instance: CompactSpace J := Quotient.compactSpace

def wrap_quot_homeo: J ≃ₜ circle := by{
  apply Continuous.homeoOfEquivCompactToT2 continuous_wrap_quot_equiv
}

instance : T2Space J := Homeomorph.t2Space (wrap_quot_homeo).symm


lemma pointed_wrap_quot : wrap_quot_equiv default = default := by{
  let _:= I_quotient
  simp[wrap_quot_equiv, wrap_quot]
  have : (default : J) = Quotient.mk I_quotient 0 := rfl
  rw[this]
  rw[Quotient.lift_mk]
  simp[wrap, default, EuclideanSpace.single]
  funext t
  simp
  obtain hc1|hc2 := fin_simplify t
  · simp[hc1]
  · simp[hc2]
}


def wrap_quot_pointed_homeo: J ≃ₜ⋆ circle where
  toHomeomorph:= wrap_quot_homeo
  pointed_toFun := pointed_wrap_quot


variable (X:Type) [PointedTopSpace X]
open PointedTopSpace

/-- A pointed homeomorphism between X ⋀ 𝕊¹ and X ⋀ [0,1]/∼, where the equivalence relation quotients out the extremes. -/
def smash_circle_J_pointed_homeo : X ⋀ (𝕊 1) ≃ₜ⋆ X ⋀ J := PointedHomeo.symm (homeo_smash_compare' X (wrap_quot_pointed_homeo))


-- [one proof missing] Now I can show that X ⋀ J ≃ₜ⋆  Σ₀ X

/-- The identity on X times the quotient map from the unit interval to the unit interval mod its extreme points-/
def prod_I_quot: C(X × I, X × J) := ContinuousMap.prodMap (ContinuousMap.id X) (⟨Quotient.mk I_quotient, by apply continuous_quot_mk⟩)

/-- The map (x,t) ↦ x ∧ [t], where [t] is the class of t with respect to quotienting out the extemes of the unit interval-/
def prod_to_wedge : C(X × I, X ⋀ J) := ContinuousMap.comp (⟨Quotient.mk (smash_setoid X J), by apply continuous_quot_mk ⟩) (prod_I_quot X)


def sus_to_wedge : Σ₀ X → (X ⋀ J) := by{
  let _:= basedsuspension_setoid X
  let _:= smash_setoid X J
  apply Quotient.lift (prod_to_wedge X)
  intro a b hab
  have : (basedsuspension_setoid X).r a b := hab
  simp[quotient_setoid_equiv_iff] at this

  simp[prod_to_wedge, smash_elt_eq_iff, prod_I_quot]
  rw[Quotient.eq]
  have hran : (smash_setoid X J).r (a.1, (Quotient.mk I_quotient a.2)) (b.1, Quotient.mk I_quotient b.2) := by{
    rw[quotient_setoid_equiv_iff]
    have this : range (wedge_embedding X J) = wedge_embedding X J '' univ := image_univ.symm
    have that : (wedge_embedding X J).toContinuousMap.toFun = FunLike.coe (wedge_embedding X J) := rfl
    rw[that, ← this]
    simp_rw[wedge_embedding_ran_iff]
    rw[← defaults_eq, ← defaults_eq, I_quotient_default, I_quotient_default]
    simp[I_quotient_default]
    tauto
  }
  exact hran
}


lemma continuous_sus_to_wedge : Continuous (sus_to_wedge X) := by{
  apply Continuous.quotient_lift
  exact (prod_to_wedge X).continuous_toFun
}

lemma pointed_sus_to_wedge : (sus_to_wedge X) Inhabited.default = Inhabited.default := by{
  let _hset:= basedsuspension_setoid X
  simp[Cylinder] at _hset
  simp[sus_to_wedge]
  have : (Inhabited.default:Σ₀ X) = Quotient.mk _ (Inhabited.default, 0) := rfl
  rw[this, Quotient.lift_mk]
  simp[prod_to_wedge, prod_I_quot]
  rfl
}

lemma injective_sus_to_wedge : Injective (sus_to_wedge X) := by {
  let _hset:= basedsuspension_setoid X
  let _:= smash_setoid X J
  let _hquot:= I_quotient
  simp [Cylinder] at _hset
  let _hset':= basedsuspension_setoid X
  simp[Injective]
  intro a b hab
  simp[sus_to_wedge] at hab
  obtain ⟨a', ha'⟩:= Quotient.exists_rep a
  obtain ⟨b', hb'⟩:= Quotient.exists_rep b
  rw[← ha', ← hb'] at hab
  simp[prod_to_wedge, prod_I_quot] at hab
  have hab' : (smash_setoid X J).r (a'.1, Quotient.mk I_quotient a'.2) (b'.1, Quotient.mk I_quotient b'.2) := Quotient.eq'.mp hab
  simp at hab'
  rw[← ha', ← hb']
  rw[Quotient.eq]
  have : Setoid.r a' b' := by{
    simp
    simp[wedge_embedding_ran''] at hab'
    rw[← defaults_eq, ← defaults_eq, I_quotient_default, I_quotient_default] at hab'
    rw[I_quotient_eq] at hab'
    obtain hc1|hc2 := hab'
    · left
      tauto
    · obtain ⟨h1, h2⟩:= hc2
      obtain hd1|hd2 := h2
      · tauto
      · right
        calc
        a' = (a'.1, a'.2) := rfl
        _ = (b'.1, b'.2) := by rw[h1, ← hd2]
        _ = b' := rfl
  }
  exact this
}

lemma surjective_sus_to_wedge : Surjective (sus_to_wedge X) := by {
  let _hsus : Setoid (X × I):= basedsuspension_setoid X
  rw[Surjective]
  intro b
  obtain ⟨p, hp⟩ := Quotient.exists_rep b
  obtain ⟨i, hi⟩ := Quotient.exists_rep p.2
  use Quotient.mk _ (p.1, i)
  simp[sus_to_wedge, prod_to_wedge, prod_I_quot]
  rw[hi, hp]
}

def equiv_sus_to_wedge : Σ₀ X ≃  (X ⋀ J) := by {
  apply Equiv.ofBijective (sus_to_wedge X)
  constructor
  · exact injective_sus_to_wedge X
  · exact surjective_sus_to_wedge X
}

/- Irrelevant
lemma isClosed_IJ : IsClosedMap (Quotient.mk I_quotient) := by{
  have _hq :  T2Space (_root_.Quotient I_quotient) := Homeomorph.t2Space (wrap_quot_homeo).symm
  apply Continuous.isClosedMap
  exact continuous_coinduced_rng
}
-/


lemma isOpen_sus_to_wedge : IsOpenMap (sus_to_wedge X) := by {
  let _: Setoid (X × I):= basedsuspension_setoid X
  let _:= basedsuspension_setoid X
  rw[IsOpenMap]
  intro U hU
  have hU₂ := @quotientMap_quot_mk (Cylinder X) _ (basedsuspension_setoid X).r
  have hU₃ := (QuotientMap.isOpen_preimage hU₂).mpr hU
  let U' := Quot.mk Setoid.r ⁻¹' U

  have hU' := (@isOpen_prod_iff X I _ _ U').mp hU₃

  let V':= (prod_I_quot X)'' U'

  let f : X × I → Σ₀ X := Quotient.mk (basedsuspension_setoid X)
  let g : Σ₀ X → X ⋀ J := sus_to_wedge X
  let h : X × I → X × J := prod_I_quot X
  let i : X × J → X ⋀ J := Quotient.mk (smash_setoid X J)

  have hf : f '' (f ⁻¹' U) = U := by{
    apply Function.Surjective.image_preimage
    exact QuotientMap.surjective hU₂
  }

  have hcomp : g ∘ f = i ∘ h := by{
    dsimp
    rw[sus_to_wedge, Quotient.lift_comp_mk]
    rfl
  }

  have hpreim : g '' U = i '' V' := by {
    rw[←hf, Set.image_image]
    have : (fun x ↦ g (f x) ) = g ∘ f := rfl
    rw[this, hcomp ]
    have : i ∘ h = (fun x ↦ i (h x)) := rfl
    rw[this, ←Set.image_image ]
    rfl
  }


  rw[hpreim]
  have hV'₂ := @quotientMap_quot_mk _ _ (smash_setoid X J).r
  apply (QuotientMap.isOpen_preimage hV'₂).mp
  sorry
}

  /-
  have hV'₃ : ((wedge_embedding X J) '' univ) ∩ V' = ∅  ∨ ((wedge_embedding X J) '' univ ⊆ V') := by{
    by_contra hcontr
    push_neg at hcontr
    obtain ⟨h1, h2⟩ := hcontr
    rw[Nonempty] at h1
    rw[Set.inter_nonempty_iff_exists_left] at h1
    obtain ⟨v, hv⟩ := h1
  }


  have hpre':  i ⁻¹' (i '' V') = V' := by {
    sorry
    -- the idea is that V' either contains the whole X ⋁ J or it is disjoint from it
  }
  have : @Quot.mk (X × J) (smashsetoid X J).r = i := rfl
  rw[this, hpre']

  -- similar to hpre'
  apply (@isOpen_prod_iff X J _ _ V').mpr
  intro a b hab
  obtain ⟨b', hb'⟩ := Quotient.exists_rep b
  specialize hU' a b'
  sorry

  -- this is a bit of a mess
}

#check Function.Surjective.image_preimage


#check isOpen_prod_iff

-/


def homeo_sus_to_wedge : Σ₀ X ≃ₜ (X ⋀ J) := by {
  apply Homeomorph.homeomorphOfContinuousOpen (equiv_sus_to_wedge X)
  · exact continuous_sus_to_wedge X
  · exact isOpen_sus_to_wedge X
}

def pointed_homeo_sus_to_wedge: Σ₀ X ≃ₜ⋆  (X ⋀ J)  where
  toHomeomorph:= homeo_sus_to_wedge X
  pointed_toFun:= pointed_sus_to_wedge X


--Finally, compose all the pointed homeomorphisms to show that X ⋀ S¹ ≃ₜ⋆  Σ₀ X
def smashcircle_is_suspension : X ⋀ circle ≃ₜ⋆  Σ₀ X := PointedHomeo.trans (homeo_smash_compare' X (wrap_quot_pointed_homeo).symm) (pointed_homeo_sus_to_wedge X).symm

--[Ideally, one should show this isomorphism is natural in X]





-- [TODO] Prove that the free suspension of 𝕊ⁿ is homeomorphic to 𝕊^{n+1}
/- I had started working on this but I couldn't do much, I had other parts of the project to work on
 and I just ran out of time.
 This is the only code I have and I did not want to delete it and pretend it never existed,
 but it does nothing at this point.
 -/

lemma target_in_sphere (y : 𝕊 n) (t: I) : @norm (EuclideanSpace ℝ (Fin (n + 1))) SeminormedAddGroup.toNorm (Fin.snoc (fun i ↦ Real.sqrt (1 - (↑t+1)/2 * (↑t+1)/2) * (y.1 i) ) ((↑t +1)/2))  = 1 := by{
  simp[Fin.snoc, EuclideanSpace.norm_eq, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

  sorry
  -- I remember this working earlier (???)
}

#check Finset.sum_congr

def cyl_to_sphere: (𝕊 n) × I  → (𝕊 (n+1)) :=
  fun (⟨x, p⟩, t) ↦ ⟨Fin.snoc ( fun i ↦ Real.sqrt (1-((↑t +1)/2)*((↑t +1)/2)) * (x i) ) ((↑t +1)/2) ,  by{simp; /-exact target_in_sphere n (⟨x, p⟩) t}-/ sorry} ⟩


def sus_to_sphere: S (𝕊 n) → 𝕊 (n+1) := by{
  apply Quotient.lift (cyl_to_sphere n)
  intro a b hab
  ext i
  simp[cyl_to_sphere, Fin.snoc]
  sorry
}


theorem injective_sus_to_sphere : Injective (sus_to_sphere n) := by{
  sorry
}

theorem surjective_sus_to_sphere : Surjective (sus_to_sphere n) := by{
  sorry
}

def sus_to_sphere_equiv : S (𝕊 n) ≃ (𝕊 (n+1)) := by{
  apply Equiv.ofBijective (sus_to_sphere n)
  rw[Bijective]
  constructor
  · exact injective_sus_to_sphere n
  · exact surjective_sus_to_sphere n
}

theorem continuous_sus_to_sphere : Continuous (sus_to_sphere_equiv n) := by{
  sorry
}


instance : CompactSpace (Cylinder (𝕊 n)) := instCompactSpaceProdInstTopologicalSpaceProd
instance : CompactSpace (S (𝕊 n)) := Quotient.compactSpace


def sus_to_sphere_homeo: S (𝕊 n)  ≃ₜ (𝕊 (n+1))  := by{
  apply Continuous.homeoOfEquivCompactToT2 (continuous_sus_to_sphere n)
}

-- add pointed

end
