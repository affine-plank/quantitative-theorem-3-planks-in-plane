/- Compatibility interfaces for the former generic planar reduction.
The claim arguments remain for existing callers; the proof now comes directly
from PlanarAffineCover. The main planar reader does not import this module. -/
module
public import Plank.Convex.PlanarAffineCover
public import Plank.Convex.PlanarCoverClaim
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ThreePlankPlaneReduction
open scoped BigOperators
open DeficientHeightTilt

abbrev Point2 := Fin 2 → ℝ
abbrev Point3 := Fin 3 → ℝ

/-- The normalized positive-plane cube statement: a convex subset of the unit cube attaining `0`
and `1` in every coordinate, lying on a plane with positive coefficients, and covered by three
ordered coordinate windows, has total window width at least one. -/
def NormalizedPlaneClaim : Prop :=
  ∀ (K : Set Point3), Convex ℝ K → (∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1) →
    (∀ i, ∃ x ∈ K, x i = 0) → (∀ i, ∃ x ∈ K, x i = 1) →
    ∀ (A : Point3) (D : ℝ), (∀ i, 0 < A i) → (∀ x ∈ K, ∑ i, A i * x i = D) →
    ∀ (lo hi : Point3), (∀ i, lo i ≤ hi i) → (∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) →
    1 ≤ ∑ i, (hi i - lo i)

/-- Any nontrivial affine relation reduces the cover directly to the normalized
statement. Some coefficients may vanish; every relative width is preserved. -/
theorem relation_bound_nontrivial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (_hclaim : NormalizedPlaneClaim)
    (K : Set E) (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Point3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, lo i ≤ hi i)
    (a : Point3) (d : ℝ) (ha : ∃ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i * f i x = d)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) / rangeWidth K (f i) := by
  exact PlanarAffineCover.relation_bound K hK hne hconv f lo hi hW horder a d ha hplane hcover

/-- Compatibility form for a relation whose three coefficients are nonzero. -/
theorem relation_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hclaim : NormalizedPlaneClaim)
    (K : Set E) (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Point3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, lo i ≤ hi i)
    (a : Point3) (d : ℝ) (ha : ∀ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i * f i x = d)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) / rangeWidth K (f i) := by
  exact relation_bound_nontrivial hclaim K hK hne hconv f lo hi hW horder a d
    ⟨0, ha 0⟩ hplane hcover

/-! ### The bridge -/

/-- Apply the planar argument in any real space of dimension at most two,
without changing the body or its affine functions. -/
theorem bound_of_finrank_le_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E ≤ 2)
    (_hclaim : NormalizedPlaneClaim)
    (K : Set E) (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) / rangeWidth K (f i) := by
  exact PlanarAffineCover.width_bound hdim K hK hne hconv f lo hi hW horder hcover

/-- The normalized positive-plane cube statement implies the three-plank bound
for every compact convex planar body. An arbitrary nontrivial affine relation
handles all directions, including parallel ones. -/
theorem planar_of_normalized (hclaim : NormalizedPlaneClaim) :
    ApproximatePlanarCover.PlanarCoverClaim := by
  intro K hK hconv hne f lo hi hw hW hc
  exact bound_of_finrank_le_two (by simp) hclaim K hK hne hconv f lo hi hW hw hc

end Plank.Convex.ThreePlankPlaneReduction

/-- info: 'Plank.Convex.ThreePlankPlaneReduction.relation_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.ThreePlankPlaneReduction.relation_bound

/-- info: 'Plank.Convex.ThreePlankPlaneReduction.planar_of_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.ThreePlankPlaneReduction.planar_of_normalized
