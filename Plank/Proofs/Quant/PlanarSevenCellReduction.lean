/- Actual sign-cell counts leave precisely seven cells for three planks. -/
module

public import Plank.Proofs.Quant.PlanarCellCountStrict
public import ResearchFormalized.Algebra.SignedSum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenCellReduction

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarCounterexampleChart
open PlanarParameterDomain (Endpoints budget gapArea)
open PlanarPositiveCellRank PlanarCellCountStrict
open Plank.Convex.DeficientHeightTilt

/-- A nontrivial constant affine relation forbids the exterior sign pattern
which increases all nonzero weighted coordinates beyond the plank midpoints. -/
theorem empty_cell_of_relation {κ : Type*} [Fintype κ]
    (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ) (lo hi : κ → ℝ)
    (horder : ∀ i, lo i < hi i) (a : κ → ℝ) (ha : ∃ i, a i ≠ 0) (d : ℝ)
    (hrel : ∀ x, ∑ i, a i*f i x = d) (hmid : d ≤ ∑ i, a i*((lo i+hi i)/2)) :
    signCell K f lo hi (Finset.univ.filter (fun i => 0 < a i)) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hsum := ResearchFormalized.sum_mul_lt_sum_mul_of_signs a
    (fun i => (lo i + hi i) / 2) (fun i => f i x) ha fun i => by
      have hh := hx.2 i
      constructor
      · intro hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp, ite_true] at hh
        linarith [horder i]
      · intro hn
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt_of_ge hn.le, ite_false] at hh
        linarith [horder i]
  rw [hrel] at hsum
  exact hsum.not_ge hmid

/-- Three strict planar planks always have an empty exterior sign cell.
The proof uses affine dependence, without a generic line-arrangement assumption. -/
theorem exists_empty_signCell_three (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (horder : ∀ i, lo i < hi i) :
    ∃ s : Finset (Fin 3), signCell K f lo hi s = ∅ := by
  classical
  obtain ⟨a, ha, d, hrel⟩ := Plank.Convex.PlanarAffineRelation.exists_relation f
  by_cases hm : d ≤ ∑ i, a i*((lo i+hi i)/2)
  · exact ⟨_, empty_cell_of_relation K f lo hi horder a ha d hrel hm⟩
  · have harel : ∀ x, ∑ i, (-a i)*f i x = -d := by
      intro x
      simpa only [neg_mul, Finset.sum_neg_distrib] using congrArg Neg.neg (hrel x)
    have hane : ∃ i, (-a i) ≠ 0 := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, neg_ne_zero.mpr hi⟩
    have hamid : -d ≤ ∑ i, (-a i)*((lo i+hi i)/2) := by
      rw [show (∑ i, (-a i)*((lo i+hi i)/2)) = -(∑ i, a i*((lo i+hi i)/2)) by
        simp only [neg_mul, Finset.sum_neg_distrib]]
      exact neg_le_neg (le_of_not_ge hm)
    exact ⟨_, empty_cell_of_relation K f lo hi horder (fun i => -a i) hane (-d) harel hamid⟩

theorem positive_signCell_count_le_seven (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (horder : ∀ i, lo i < hi i) :
    (Finset.univ.filter (fun s : Finset (Fin 3) =>
      0 < (volume (signCell K f lo hi s)).toReal)).card ≤ 7 := by
  classical
  obtain ⟨s, hs⟩ := exists_empty_signCell_three K f lo hi horder
  have hproper : Finset.univ.filter (fun t : Finset (Fin 3) =>
      0 < (volume (signCell K f lo hi t)).toReal) ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hm : s ∈ Finset.univ.filter (fun t : Finset (Fin 3) =>
        0 < (volume (signCell K f lo hi t)).toReal) := by rw [heq]; exact Finset.mem_univ s
    simp [hs] at hm
  have hc := Finset.card_lt_card hproper
  simp only [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at hc
  omega

/-- The selected chart has points strictly inside the actual smaller
endpoint domain, even when its selected minimum is on an incidence wall. -/
theorem exists_ordered_chart_point {m : ℕ} {K : Set Point}
    {f : Fin m → Point →ᵃ[ℝ] ℝ} (ch : CounterexampleChart K f) :
    ∃ e ∈ ch.chart.region, e ∈ interior (PlanarShiftedDomain.domain K f ch.B) := by
  have hh := mem_closure_iff_nhds.mp ch.chart.closure_point
    (interior (PlanarShiftedDomain.domain K f ch.B))
    (isOpen_interior.mem_nhds ch.chart.interior_point)
  obtain ⟨e, he, hc⟩ := hh
  exact ⟨e, hc, he⟩

/-- Exactly seven actual positive cells remain for any three-plank
counterexample chart. Exact extrapolation handles vanishing boundary cells. -/
theorem counterexample_cell_count_seven {K : Set Point} {f : Fin 3 → Point →ᵃ[ℝ] ℝ}
    (ch : CounterexampleChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) : Fintype.card (Cells ch) = 7 := by
  obtain ⟨e, he, hi⟩ := exists_ordered_chart_point ch
  have hstrict := PlanarShiftedDomain.strict_windows_of_interior K f ch.B hi
  have hupper := positive_signCell_count_le_seven K f e.1 e.2 hstrict
  rw [← activeCells_eq_positive ch hK hconv e he] at hupper
  have hlower := endpoint_count_lt ch hK hconv hV (by norm_num : 0 < 3)
  simp only [Cells, Fintype.card_coe] at hlower ⊢
  omega

/-- The sharp two-plank bound for normalized windows on a transverse
polygon. Approximation removing these body/direction restrictions remains
separate; this is not the full `SharpPlanarBound 2` theorem. -/
theorem bound_two_normalized_polygon {ι : Type*} [Fintype ι]
    (K : Set Point) (hcompact : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (F : ι → Point →ᵃ[ℝ] ℝ) (c : ι → ℝ) (hK : K = {x | ∀ j, F j x ≤ c j})
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (hf : ∀ i, 0 < rangeWidth K (f i))
    (hbody : ∀ i j, PlanarDirectionDerivatives.cross (f i) (F j) ≠ 0)
    (hpairs : ∀ i j, i ≠ j → PlanarDirectionDerivatives.cross (f i) (f j) ≠ 0)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (p : Endpoints 2) (hp : p ∈ PlanarParameterDomain.domain K f) :
    (max 0 (1-budget K f p))^2*(volume K).toReal ≤ gapArea K f p := by
  by_contra hn
  obtain ⟨ch⟩ := exists_counterexample_chart (m := 1) (by norm_num)
    PlanarOnePlank.sharpPlanarBound_one K hcompact hconv hne hV F c hK f hf hbody hpairs
    hnorm hp (lt_of_not_ge hn)
  exact no_counterexample_of_pow_le ch hcompact hconv hV (by norm_num) (by norm_num)

end Plank.PlanarSevenCellReduction
