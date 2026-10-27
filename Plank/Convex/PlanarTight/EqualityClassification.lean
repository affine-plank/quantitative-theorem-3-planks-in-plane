/- Exhaustive explicit equality families on positive planes and for three distinct affine directions. -/
module
public import Plank.Convex.PlanarTight.StrictEqualityCompletion
public import Plank.Convex.PlanarTight.AffinePlaneFamilies
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.EqualityClassification
open StrictEqualityCompletion
open DeficientHeightTilt (rangeWidth)

abbrev Point := Fin 3 → ℝ

/-- Complete equality classification on a normalized positive plane,
including zero-width, full, and all boundary windows. Endpoints are arbitrary
ordered reals; no cap assumptions or geometric cases remain to be discharged. -/
theorem normalized_tight_iff (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) ↔
      NormalizedFamilies.Normal K lo hi :=
  NormalizedFamilies.tight_iff_of_representatives rowA rowC K hK hbox hL hU A D hA hplane lo hi horder

/-- Complete equality classification for the original affine plank
functions in three pairwise independent planar directions. Zero and boundary
windows are allowed and each original relative width is preserved. -/
theorem three_direction_tight_iff
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : Fin 3 → (Fin 2 → ℝ) →ᵃ[ℝ] ℝ)
    (h01 : LinearIndependent ℝ ![(f 0).linear, (f 1).linear])
    (h02 : LinearIndependent ℝ ![(f 0).linear, (f 2).linear])
    (h12 : LinearIndependent ℝ ![(f 1).linear, (f 2).linear])
    (lo hi : Point) (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, lo i ≤ hi i) :
    ((∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1 ∧
      ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) ↔ AffinePlaneFamilies.Normal K f lo hi :=
  AffinePlaneFamilies.three_direction_tight_iff rowA rowC K hK hne hconv f h01 h02 h12 lo hi hW horder

end Plank.Convex.PlanarTight.EqualityClassification

/-- info: 'Plank.Convex.PlanarTight.EqualityClassification.normalized_tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.EqualityClassification.normalized_tight_iff

/-- info: 'Plank.Convex.PlanarTight.EqualityClassification.three_direction_tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.EqualityClassification.three_direction_tight_iff
