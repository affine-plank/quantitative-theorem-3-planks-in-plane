/- Close zero windows and full affine relations in the exact original range coordinates. -/
module
public import Plank.Convex.PlanarTight.EqualityClassification
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AffineRangeFamilyCompletion
open DeficientHeightTilt (rangeWidth)
open ExactRangeNormalization (chart endpoint)
open IndependentReflection (reflection)

abbrev E := Fin 2 → ℝ
abbrev P := Fin 3 → ℝ

theorem of_zero (K : Set E) (hK : Convex ℝ K) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : P) (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, lo i ≤ hi i)
    (hz : ∃ i, lo i = hi i) (m : P)
    (hb : ∀ x ∈ K, ∀ i, m i ≤ f i x ∧ f i x ≤ m i + rangeWidth K (f i))
    (hL : ∀ i, ∃ x ∈ K, f i x = m i)
    (hU : ∀ i, ∃ x ∈ K, f i x = m i + rangeWidth K (f i))
    (hsum : (∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1)
    (hc : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    AffinePlaneFamilies.Normal K f lo hi := by
  let W : P := fun i => rangeWidth K (f i)
  let J := chart f m W '' K
  have hbJ := ExactRangeNormalization.box K f m W hW hb
  have hLJ := ExactRangeNormalization.zero_contacts K f m W hL
  have hUJ := ExactRangeNormalization.unit_contacts K f m W hW hU
  have hzJ : ∃ i, endpoint m W lo i = endpoint m W hi i := by
    obtain ⟨i, hi'⟩ := hz
    exact ⟨i, by simp only [endpoint, hi']⟩
  have hn : NormalizedFamilies.Normal J (endpoint m W lo) (endpoint m W hi) :=
    Or.inl ((ZeroWidthClassification.tight_iff J (Convex.affine_image _ hK) hbJ hLJ hUJ
      _ _ (ExactRangeNormalization.ordered m W lo hi hW ho) hzJ).mp
      ⟨(ExactRangeNormalization.sum_width_eq m W lo hi).trans hsum,
        (ExactRangeNormalization.cover_iff K f m W lo hi hW).mpr hc⟩)
  have hid : reflection (fun _ => false) = AffineMap.id ℝ P := by
    ext x i
    rfl
  refine ⟨m, fun _ => false, hb, hL, hU, ?_⟩
  rw [hid]
  change NormalizedFamilies.Normal ((AffineMap.id ℝ P) '' J) (endpoint m W lo) (endpoint m W hi)
  simpa only [AffineMap.coe_id, Set.image_id] using hn

/-- A full affine relation among the already normalized functions feeds
the complete positive-plane iff. No original endpoint is clipped. -/
theorem of_relation (K : Set E) (hK : Convex ℝ K) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : P) (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, lo i ≤ hi i)
    (m : P)
    (hb : ∀ x ∈ K, ∀ i, m i ≤ f i x ∧ f i x ≤ m i + rangeWidth K (f i))
    (hL : ∀ i, ∃ x ∈ K, f i x = m i)
    (hU : ∀ i, ∃ x ∈ K, f i x = m i + rangeWidth K (f i))
    (a : P) (d : ℝ) (ha : ∀ i, a i ≠ 0)
    (hp : ∀ x ∈ K, ∑ i, a i * ExactRangeNormalization.forms f m
      (fun j => rangeWidth K (f j)) i x = d)
    (hsum : (∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1)
    (hc : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    AffinePlaneFamilies.Normal K f lo hi := by
  let W : P := fun i => rangeWidth K (f i)
  let J := chart f m W '' K
  have hbJ := ExactRangeNormalization.box K f m W hW hb
  have hLJ := ExactRangeNormalization.zero_contacts K f m W hL
  have hUJ := ExactRangeNormalization.unit_contacts K f m W hW hU
  have hpJ : ∀ z ∈ J, ∑ i, a i * z i = d := by
    rintro _ ⟨x, hx, rfl⟩
    exact hp x hx
  obtain ⟨flip, A, D, hA, hplane⟩ := IndependentReflection.positive_plane J a d ha hpJ
  refine ⟨m, flip, hb, hL, hU, ?_⟩
  apply (EqualityClassification.normalized_tight_iff (reflection flip '' J)
    (Convex.affine_image _ (Convex.affine_image _ hK))
    (IndependentReflection.box J flip hbJ) (IndependentReflection.zero_contacts J flip hLJ hUJ)
    (IndependentReflection.unit_contacts J flip hLJ hUJ) A D hA hplane _ _
    (IndependentReflection.ordered flip _ _ (ExactRangeNormalization.ordered m W lo hi hW ho))).mp
  refine ⟨?_, ?_⟩
  · simpa only [OrientedCommonChord.width_eq, ExactRangeNormalization.width_eq] using hsum
  · exact (IndependentReflection.cover_iff J flip (endpoint m W lo) (endpoint m W hi)).mpr
      ((ExactRangeNormalization.cover_iff K f m W lo hi hW).mpr hc)

end Plank.Convex.PlanarTight.AffineRangeFamilyCompletion

/-- info: 'Plank.Convex.PlanarTight.AffineRangeFamilyCompletion.of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AffineRangeFamilyCompletion.of_zero

/-- info: 'Plank.Convex.PlanarTight.AffineRangeFamilyCompletion.of_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AffineRangeFamilyCompletion.of_relation
