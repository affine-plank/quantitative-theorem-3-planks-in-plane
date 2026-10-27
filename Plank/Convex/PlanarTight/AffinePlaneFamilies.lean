/- Exact equality families for affine planks whose three directions have a full relation. -/
module
public import Plank.Convex.PlanarTight.ExactRangeNormalization
public import Plank.Convex.PlanarTight.IndependentReflection
public import Plank.Convex.PlanarTight.NormalizedFamilies
public import Plank.Convex.ThreePlanarDirections
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AffinePlaneFamilies
open ExactRangeNormalization (chart endpoint)
open IndependentReflection (reflection)
open DeficientHeightTilt (rangeWidth)
open StrictCapSetting (Excluded)
open StrictTriangleTransport (Triangular)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

abbrev Point := Fin 3 → ℝ

/-- Normalize by the actual attained directional ranges and independently
orient the three functions. The remaining predicate is the explicit body
and endpoint family list, with no covering or tightness predicate. -/
def Normal (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Point) : Prop :=
  let W : Point := fun i => rangeWidth K (f i)
  ∃ (m : Point) (flip : Fin 3 → Bool),
    (∀ x ∈ K, ∀ i, m i ≤ f i x ∧ f i x ≤ m i + W i) ∧
    (∀ i, ∃ x ∈ K, f i x = m i) ∧ (∀ i, ∃ x ∈ K, f i x = m i + W i) ∧
    NormalizedFamilies.Normal (reflection flip '' (chart f m W '' K))
      (OrientedCommonChord.lower flip (endpoint m W lo) (endpoint m W hi))
      (OrientedCommonChord.upper flip (endpoint m W lo) (endpoint m W hi))

omit [FiniteDimensional ℝ E] in
theorem Normal.tight (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Point)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, lo i ≤ hi i)
    (hn : Normal K f lo hi) :
    (∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1 ∧
      ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i := by
  obtain ⟨m, flip, hb, hL, hU, hn⟩ := hn
  let W : Point := fun i => rangeWidth K (f i)
  let J := chart f m W '' K
  have hbJ := ExactRangeNormalization.box K f m W hW hb
  have hLJ := ExactRangeNormalization.zero_contacts K f m W hL
  have hUJ := ExactRangeNormalization.unit_contacts K f m W hW hU
  have ht := NormalizedFamilies.Normal.tight (reflection flip '' J)
    (Convex.affine_image (reflection flip) (Convex.affine_image (chart f m W) hK))
    (IndependentReflection.box J flip hbJ) (IndependentReflection.zero_contacts J flip hLJ hUJ)
    (IndependentReflection.unit_contacts J flip hLJ hUJ)
    (OrientedCommonChord.lower flip (endpoint m W lo) (endpoint m W hi))
    (OrientedCommonChord.upper flip (endpoint m W lo) (endpoint m W hi))
    (IndependentReflection.ordered flip _ _ (ExactRangeNormalization.ordered m W lo hi hW horder)) hn
  refine ⟨?_, ?_⟩
  · simpa only [OrientedCommonChord.width_eq, ExactRangeNormalization.width_eq] using ht.1
  · exact (ExactRangeNormalization.cover_iff K f m W lo hi hW).mp
      ((IndependentReflection.cover_iff J flip (endpoint m W lo) (endpoint m W hi)).mp ht.2)

/-- Any affine relation with all three coefficients nonzero orients into
the normalized positive-plane classification. Every original endpoint is retained. -/
theorem of_tight (hrepA : Triangular ⟨63, 0⟩) (hrepC : Excluded ⟨56, 3⟩)
    (K : Set E) (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Point)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, lo i ≤ hi i)
    (a : Point) (d : ℝ) (ha : ∀ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i * f i x = d)
    (hsum : (∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) : Normal K f lo hi := by
  obtain ⟨m, hb, hL, hU⟩ := ExactRangeNormalization.exists_ranges K hK hne f
  let W : Point := fun i => rangeWidth K (f i)
  let J := chart f m W '' K
  have hbJ := ExactRangeNormalization.box K f m W hW hb
  have hLJ := ExactRangeNormalization.zero_contacts K f m W hL
  have hUJ := ExactRangeNormalization.unit_contacts K f m W hW hU
  obtain ⟨flip, A, D, hA, hp⟩ := IndependentReflection.positive_plane J
    (fun i => a i * W i) (d - ∑ i, a i * m i)
    (fun i => mul_ne_zero (ha i) (hW i).ne')
    (ExactRangeNormalization.plane K f m W a d (fun i => (hW i).ne') hplane)
  refine ⟨m, flip, hb, hL, hU, ?_⟩
  apply (NormalizedFamilies.tight_iff_of_representatives hrepA hrepC (reflection flip '' J)
    (Convex.affine_image (reflection flip) (Convex.affine_image (chart f m W) hconv))
    (IndependentReflection.box J flip hbJ) (IndependentReflection.zero_contacts J flip hLJ hUJ)
    (IndependentReflection.unit_contacts J flip hLJ hUJ) A D hA hp _ _
    (IndependentReflection.ordered flip _ _ (ExactRangeNormalization.ordered m W lo hi hW horder))).mp
  refine ⟨?_, ?_⟩
  · simpa only [OrientedCommonChord.width_eq, ExactRangeNormalization.width_eq] using hsum
  · exact (IndependentReflection.cover_iff J flip (endpoint m W lo) (endpoint m W hi)).mpr
      ((ExactRangeNormalization.cover_iff K f m W lo hi hW).mpr hcover)

/-- Three pairwise independent planar directions always have the required
full affine relation. This classifies their original affine plank windows. -/
theorem three_direction_tight_iff (hrepA : Triangular ⟨63, 0⟩) (hrepC : Excluded ⟨56, 3⟩)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : Fin 3 → (Fin 2 → ℝ) →ᵃ[ℝ] ℝ)
    (h01 : LinearIndependent ℝ ![(f 0).linear, (f 1).linear])
    (h02 : LinearIndependent ℝ ![(f 0).linear, (f 2).linear])
    (h12 : LinearIndependent ℝ ![(f 1).linear, (f 2).linear])
    (lo hi : Point) (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, lo i ≤ hi i) :
    ((∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1 ∧
      ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) ↔ Normal K f lo hi := by
  constructor
  · rintro ⟨hsum, hcover⟩
    obtain ⟨a, b, c, ha, hb, hrel⟩ := ThreePlanarDirections.exists_coefficients
      (f 0) (f 1) (f 2) h01 h02 h12
    apply of_tight hrepA hrepC K hK hne hconv f lo hi hW horder ![a, b, -1] (-c)
      (by intro i; fin_cases i; exact ha; exact hb; norm_num) ?_ hsum hcover
    intro x _
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      neg_one_mul]
    linarith only [hrel x]
  · exact Normal.tight K hconv f lo hi hW horder

end Plank.Convex.PlanarTight.AffinePlaneFamilies

/-- info: 'Plank.Convex.PlanarTight.AffinePlaneFamilies.Normal.tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AffinePlaneFamilies.Normal.tight

/-- info: 'Plank.Convex.PlanarTight.AffinePlaneFamilies.three_direction_tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AffinePlaneFamilies.three_direction_tight_iff
