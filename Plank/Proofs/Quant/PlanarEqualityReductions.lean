/- Equality reductions for the planar quantitative area bound.
This is not an exhaustive classification in the positive-deficit regime. -/
module

public import Plank.Proofs.Quant.PlanarThreePlank
public import Plank.Proofs.Quant.PlanarNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarEqualityReductions

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarNormalization
open Plank.Convex.DeficientHeightTilt

/-- Equality in the actual-area formula, including its positive part. -/
def Equality {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints m) : Prop :=
  gapArea K f p = (max 0 (1-budget K f p))^2 * (volume K).toReal

/-- Once the budget is exhausted, equality means an actual closed cover. -/
theorem equality_iff_cover_of_one_le {m : ℕ} {K : Set Point}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (hR : 1 ≤ budget K f p) :
    Equality K f p ↔ K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
  have hz : max 0 (1-budget K f p) = 0 := max_eq_left (sub_nonpos.mpr hR)
  simp only [Equality, hz, zero_pow (by decide : 2 ≠ 0), zero_mul, gapArea]
  exact PlanarGapAnalysis.gap_area_eq_zero_iff_cover hK hconv hV f p.1 p.2

/-- Zero total relative width is precisely the all-zero-width case. -/
theorem budget_eq_zero_iff {m : ℕ} {K : Set Point}
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i) :
    budget K f p = 0 ↔ ∀ i, p.1 i = p.2 i := by
  have hn (i : Fin m) : 0 ≤ (p.2 i-p.1 i)/rangeWidth K (f i) :=
    div_nonneg (sub_nonneg.mpr (ho i)) (hW i).le
  constructor
  · intro h i
    have he : (p.2 i-p.1 i)/rangeWidth K (f i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp h i (Finset.mem_univ i)
    exact (sub_eq_zero.mp ((div_eq_zero_iff).mp he |>.resolve_right (hW i).ne')).symm
  · intro h
    simp [budget, h]

/-- Zero-width planks are null, wherever their supporting lines lie. -/
theorem equality_of_budget_zero {m : ℕ} {K : Set Point} (hne : K.Nonempty)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hR : budget K f p = 0) : Equality K f p := by
  have he := (budget_eq_zero_iff f p hW ho).mp hR
  have hz : volume (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) = 0 := by
    apply measure_iUnion_null
    intro i
    have hs : {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = {x | f i x = p.1 i} := by
      ext x
      simp only [mem_ofPred_eq, ← he i]
      exact ⟨fun h => le_antisymm h.2 h.1, fun h => by simp [h]⟩
    rw [hs]
    exact PlanarGapCells.measure_level_zero (f i)
      (PlanarGapCells.linear_ne_zero_of_rangeWidth_pos hne (f i) (hW i)) _
  simp only [Equality, gapArea, measure_sdiff_null hz, hR]
  norm_num

/-- Equality below budget one forbids any strict reduction of total width
that leaves the actual gap unchanged. This works for every proved sharp bound. -/
theorem budget_eq_of_gap_eq {m : ℕ} (hbound : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p q : Endpoints m)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (hq : ∀ i, q.1 i ≤ q.2 i)
    (hR : budget K f p < 1) (he : Equality K f p)
    (hle : budget K f q ≤ budget K f p) (hg : gapArea K f q = gapArea K f p) :
    budget K f q = budget K f p := by
  have hb := hbound K hK hconv hne f q.1 q.2 hq hW
  change (max 0 (1-budget K f q))^2 * (volume K).toReal ≤ gapArea K f q at hb
  rw [hg, he, max_eq_right (sub_pos.mpr hR).le,
    max_eq_right (sub_nonneg.mpr (hle.trans hR.le))] at hb
  have hs := (mul_le_mul_iff_left₀ hV).mp hb
  have hl := (sq_le_sq₀ (sub_nonneg.mpr (hle.trans hR.le))
    (sub_pos.mpr hR).le).mp hs
  linarith

/-- Clipping a normalized equality configuration preserves every unit of
its total relative width, rather than merely preserving its area. -/
theorem budget_clip_eq {m : ℕ} (hbound : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (ho : ∀ i, p.1 i ≤ p.2 i) (hR : budget K f p < 1)
    (he : Equality K f p) : budget K f (clipEndpoints p) = budget K f p := by
  apply budget_eq_of_gap_eq hbound hK hconv hne hV f p (clipEndpoints p) hW
    (fun i => monotone_clip (ho i)) hR he (budget_clip_le f hW p ho)
  exact gapArea_clip hne f hW hnorm p

/-- For three planks this reduction has no unproved sharp-bound premise. -/
theorem budget_clip_eq_three {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (ho : ∀ i, p.1 i ≤ p.2 i) (hR : budget K f p < 1)
    (he : Equality K f p) : budget K f (clipEndpoints p) = budget K f p :=
  budget_clip_eq PlanarThreePlank.sharpPlanarBound_three hK hconv hne hV f p hW hnorm ho hR he

/-- A positive interval retains its length on clipping exactly when both
endpoints were already in the support interval. -/
theorem clip_length_eq_iff {lo hi : ℝ} (h : lo < hi) :
    clip hi-clip lo = hi-lo ↔ 0 ≤ lo ∧ hi ≤ 1 := by
  constructor
  · intro he
    by_cases hh : hi ≤ 0
    · have hchi : clip hi = 0 := max_eq_left ((min_le_right 1 hi).trans hh)
      have hclo : clip lo = 0 := max_eq_left ((min_le_right 1 lo).trans (h.le.trans hh))
      rw [hchi, hclo] at he
      linarith
    by_cases hl : 1 ≤ lo
    · have hclo : clip lo = 1 := by simp [clip, min_eq_left hl]
      have hchi : clip hi = 1 := by simp [clip, min_eq_left (hl.trans h.le)]
      rw [hchi, hclo] at he
      linarith
    have hchi : clip hi = min 1 hi := max_eq_right (le_min (by norm_num) (le_of_not_ge hh))
    have hclo : clip lo = max 0 lo := by rw [clip, min_eq_right (le_of_not_ge hl)]
    rw [hchi, hclo] at he
    constructor
    · linarith [min_le_right (1 : ℝ) hi, le_max_left (0 : ℝ) lo]
    · linarith [min_le_left (1 : ℝ) hi, le_max_right (0 : ℝ) lo]
  · rintro ⟨hl, hh⟩
    simp [clip, min_eq_right hh, min_eq_right (h.le.trans hh),
      max_eq_right hl, max_eq_right (hl.trans h.le)]

/-- Every positive-width member of an equality triple lies inside its
normalized directional range. A zero-width member can be an arbitrary line. -/
theorem positive_window_no_waste_three {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (ho : ∀ i, p.1 i ≤ p.2 i) (hR : budget K f p < 1)
    (he : Equality K f p) (i : Fin 3) (hi : p.1 i < p.2 i) :
    0 ≤ p.1 i ∧ p.2 i ≤ 1 := by
  have ht := budget_clip_eq_three hK hconv hne hV f p hW hnorm ho hR he
  have hle (j : Fin 3) : (clip (p.2 j)-clip (p.1 j))/rangeWidth K (f j) ≤
      (p.2 j-p.1 j)/rangeWidth K (f j) :=
    (div_le_div_iff_of_pos_right (hW j)).mpr (clip_sub_le (ho j))
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp ht i (Finset.mem_univ i)
  apply (clip_length_eq_iff hi).mp
  exact (div_left_inj' (hW i).ne').mp heq

end Plank.PlanarEqualityReductions

/-- info: 'Plank.PlanarEqualityReductions.equality_iff_cover_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarEqualityReductions.equality_iff_cover_of_one_le
/-- info: 'Plank.PlanarEqualityReductions.equality_of_budget_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarEqualityReductions.equality_of_budget_zero
/-- info: 'Plank.PlanarEqualityReductions.positive_window_no_waste_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarEqualityReductions.positive_window_no_waste_three
