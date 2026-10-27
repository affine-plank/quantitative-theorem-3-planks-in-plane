/- Exact closed covers of positive-measure compact convex bodies. -/
module
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Plank.ConvexBodyMeasure
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Positive Haar measure supplies interior points of a convex body. -/
theorem interior_nonempty_of_measure_pos (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (harea : 0 < (μ K).toReal) : (interior K).Nonempty := by
  by_contra hn
  have hempty : interior K = ∅ := not_nonempty_iff_eq_empty.mp hn
  have hfrontier : frontier K = K := by
    rw [frontier, hK.isClosed.closure_eq, hempty, sdiff_empty]
  have hzero : μ K = 0 := by
    rw [← hfrontier]
    exact hconv.addHaar_frontier μ
  simp [hzero] at harea

/-- A closed set missing any point of a positive-measure convex body misses a
positive-measure part. This includes a missed boundary point of the body. -/
theorem measure_sdiff_pos_of_not_subset (μ : Measure E) [μ.IsAddHaarMeasure] {K C : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (harea : 0 < (μ K).toReal)
    (hC : IsClosed C) (hnot : ¬ K ⊆ C) : 0 < (μ (K \ C)).toReal := by
  have hint := interior_nonempty_of_measure_pos μ hK hconv harea
  have hclosure : closure (interior K) = K :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hint).trans hK.isClosed.closure_eq
  obtain ⟨x, hxK, hxC⟩ := not_subset.mp hnot
  have hne : (interior K ∩ Cᶜ).Nonempty :=
    (closure_inter_open_nonempty_iff hC.isOpen_compl).mp (by
      rw [hclosure]
      exact ⟨x, hxK, hxC⟩)
  have hopen : IsOpen (interior K ∩ Cᶜ) := isOpen_interior.inter hC.isOpen_compl
  have hpositive : 0 < μ (K \ C) :=
    (hopen.measure_pos μ hne).trans_le (measure_mono (fun _ hx =>
      ⟨interior_subset hx.1, hx.2⟩))
  exact ENNReal.toReal_pos hpositive.ne'
    (ne_top_of_le_ne_top hK.measure_ne_top (measure_mono sdiff_subset))

/-- On a positive-measure compact convex body, zero uncovered measure is equivalent
to an actual closed cover; it is not merely an almost-everywhere cover. -/
theorem measure_sdiff_eq_zero_iff_subset (μ : Measure E) [μ.IsAddHaarMeasure] {K C : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (harea : 0 < (μ K).toReal) (hC : IsClosed C) :
    (μ (K \ C)).toReal = 0 ↔ K ⊆ C := by
  constructor
  · intro hzero
    by_contra hnot
    have hpositive := measure_sdiff_pos_of_not_subset μ hK hconv harea hC hnot
    linarith
  · intro hcover
    simp [sdiff_eq_empty.mpr hcover]


end Plank.ConvexBodyMeasure
