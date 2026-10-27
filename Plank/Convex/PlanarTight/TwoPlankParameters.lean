/- Bounds encoded by the explicit two-plank parameter families. -/
module
public import Plank.Convex.PlanarTight.TwoPlankClassification
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TwoPlankParameters

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem anchored_bounds (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l u m v : ℝ)
    (h : TwoPlankClassification.Anchored K X Y l u m v) :
    0 ≤ l ∧ u ≤ 1 ∧ 0 ≤ m ∧ v ≤ 1 := by
  obtain ⟨hl, hu, hu₁, c, hc, hc₁, hm, hv, _⟩ := h
  refine ⟨by rw [hl], hu₁.le, ?_, ?_⟩
  · rw [hm]
    exact mul_nonneg hu.le hc
  · rw [hv]
    have hp := mul_nonneg hu.le (sub_nonneg.mpr hc₁)
    nlinarith only [hp]

theorem bounds (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l u m v : ℝ)
    (h : TwoPlankClassification.Normal K X Y l u m v) :
    0 ≤ l ∧ u ≤ 1 ∧ 0 ≤ m ∧ v ≤ 1 := by
  rcases h with h | h | h | h | h
  · obtain ⟨g, q, p, hg, hg₁, hq, hq₁, hp, hp₁, hl, hu, hm, hv, _⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hl]
      exact mul_nonneg (sub_pos.mpr hg₁).le hq.le
    · rw [hu]
      have h := mul_nonneg (sub_pos.mpr hg₁).le (sub_pos.mpr hq₁).le
      nlinarith only [h]
    · rw [hm]
      exact mul_nonneg hg.le hp.le
    · rw [hv]
      have h := mul_nonneg hg.le (sub_pos.mpr hp₁).le
      nlinarith only [h]
  · exact anchored_bounds K X Y l u m v h
  · obtain ⟨hl, hu, hm, hv⟩ := anchored_bounds K (TwoPlankClassification.reflect X) Y
      (1 - u) (1 - l) m v h
    exact ⟨by linarith only [hu], by linarith only [hl], hm, hv⟩
  · obtain ⟨hm, hv, hl, hu⟩ := anchored_bounds K Y X m v l u h
    exact ⟨hl, hu, hm, hv⟩
  · obtain ⟨hm, hv, hl, hu⟩ := anchored_bounds K (TwoPlankClassification.reflect Y) X
      (1 - v) (1 - m) l u h
    exact ⟨hl, hu, by linarith only [hv], by linarith only [hm]⟩

end Plank.Convex.PlanarTight.TwoPlankParameters

/-- info: 'Plank.Convex.PlanarTight.TwoPlankParameters.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankParameters.bounds
