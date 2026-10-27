/- Standard convex geometry: a convex set of positive finite Haar measure is bounded. -/
module

public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace ResearchFormalized.ConvexFiniteMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Positive measure gives interior points without compactness or closedness. -/
theorem interior_nonempty_of_measure_pos (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hc : Convex ℝ K) (hpos : 0 < μ K) : (interior K).Nonempty := by
  by_contra h
  have hm := measure_interior_of_null_frontier (hc.addHaar_frontier μ)
  rw [not_nonempty_iff_eq_empty.mp h, measure_empty] at hm
  exact hpos.ne' hm.symm

/-- An unbounded convex set with nonempty interior has infinite measure.
Proof: every point generates a ball of fixed radius inside the set; finite
measure cannot accommodate such a ball outside a sufficiently large compact core. -/
theorem isBounded_of_measure_pos_ne_top (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hc : Convex ℝ K) (hpos : 0 < μ K) (hfin : μ K ≠ ∞) :
    Bornology.IsBounded K := by
  obtain ⟨a, ha⟩ := interior_nonempty_of_measure_pos μ hc hpos
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  have hr2 : 0 < r / 2 := by positivity
  have hclosure : μ (closure K) = μ K :=
    measure_closure_of_null_frontier (hc.addHaar_frontier μ)
  obtain ⟨D, _, hD, hsmall⟩ :=
    (isClosed_closure : IsClosed (closure K)).measurableSet.exists_isCompact_sdiff_lt
      (by rwa [hclosure]) (measure_ball_pos μ a hr2).ne'
  obtain ⟨R, hR⟩ := hD.isBounded.subset_closedBall a
  apply (Metric.isBounded_closedBall (x := a) (r := 2 * (R + r))).subset
  intro x hx
  change dist x a ≤ 2 * (R + r)
  by_contra! hfar
  let c := (1 / 2 : ℝ) • (a + x)
  have hdist : dist c a = (1 / 2 : ℝ) * dist x a := by
    rw [dist_eq_norm, show c - a = (1 / 2 : ℝ) • (x - a) by dsimp [c]; module]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num), ← dist_eq_norm]
  have hsub : ball c (r / 2) ⊆ closure K \ D := by
    intro z hz
    have hzc : dist z c < r / 2 := hz
    let y := a + (2 : ℝ) • (z - c)
    have hya : dist y a = 2 * dist z c := by
      simp [y, dist_eq_norm, norm_smul]
    have hy : y ∈ K := hball (by change dist y a < r; rw [hya]; linarith)
    have hzK : z ∈ K := by
      have hmid := hc hy hx (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
      convert hmid using 1 <;> dsimp [y, c] <;> module
    refine ⟨subset_closure hzK, ?_⟩
    intro hzD
    have hzR : dist z a ≤ R := hR hzD
    have ht := dist_triangle c z a
    rw [dist_comm c z] at ht
    linarith
  have hmeasure : μ (ball a (r / 2)) ≤ μ (closure K \ D) := by
    calc
      μ (ball a (r / 2)) = μ (ball c (r / 2)) := by
        simp only [Measure.addHaar_ball_center]
      _ ≤ μ (closure K \ D) := measure_mono hsub
  exact hsmall.not_ge hmeasure

end ResearchFormalized.ConvexFiniteMeasure

#print axioms ResearchFormalized.ConvexFiniteMeasure.isBounded_of_measure_pos_ne_top
