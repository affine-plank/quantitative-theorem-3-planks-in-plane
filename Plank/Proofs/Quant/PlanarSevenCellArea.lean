/- Inclusion-exclusion identifies the actual seven-cell uncovered area. -/
module

public import Plank.Proofs.Quant.PlanarWindowData

public import Plank.Proofs.Quant.PlanarPairArea
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenCellArea

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarSevenCellGeometry
open PlanarPairArea PlanarDirectionDerivatives PlanarCounterexampleChart
open PlanarParameterDomain (Endpoints gapArea)

/-- Finite real-area inclusion-exclusion with an empty triple intersection. -/
theorem area_sdiff_three {K A B C : Set Point} (hK : IsCompact K)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hCK : C ⊆ K) (htriple : (A ∩ B) ∩ C = ∅) :
    (volume (K \ ((A ∪ B) ∪ C))).toReal = (volume K).toReal-
      (volume A).toReal-(volume B).toReal-(volume C).toReal+
      (volume (A ∩ B)).toReal+(volume (A ∩ C)).toReal+(volume (B ∩ C)).toReal := by
  have hAfin : volume A ≠ ⊤ := measure_ne_top_of_subset hAK hK.measure_ne_top
  have hBfin : volume B ≠ ⊤ := measure_ne_top_of_subset hBK hK.measure_ne_top
  have hCfin : volume C ≠ ⊤ := measure_ne_top_of_subset hCK hK.measure_ne_top
  have hABK : A ∪ B ⊆ K := union_subset hAK hBK
  have hABfin : volume (A ∪ B) ≠ ⊤ := measure_ne_top_of_subset hABK hK.measure_ne_top
  have hACfin : volume (A ∩ C) ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hAfin
  have hBCfin : volume (B ∩ C) ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hBfin
  have hab := measureReal_union_add_inter (μ := volume) (s := A) hB hAfin hBfin
  have habc := measureReal_union_add_inter (μ := volume) (s := A ∪ B) hC hABfin hCfin
  have hcross := measureReal_union_add_inter (μ := volume) (s := A ∩ C) (hB.inter hC) hACfin hBCfin
  have heq : (A ∩ C) ∩ (B ∩ C) = ∅ := by
    calc
      (A ∩ C) ∩ (B ∩ C) = (A ∩ B) ∩ C := by ext x; simp only [mem_inter_iff]; tauto
      _ = ∅ := htriple
  rw [heq, measureReal_empty, add_zero, ← union_inter_distrib_right] at hcross
  have hdiff := measureReal_sdiff_add_inter (μ := volume) (s := K) ((hA.union hB).union hC)
    hK.measure_ne_top
  rw [inter_eq_right.mpr (union_subset hABK hCK)] at hdiff
  change (volume (A ∪ B)).toReal+(volume (A ∩ B)).toReal =
    (volume A).toReal+(volume B).toReal at hab
  change (volume ((A ∪ B) ∪ C)).toReal+(volume ((A ∪ B) ∩ C)).toReal =
    (volume (A ∪ B)).toReal+(volume C).toReal at habc
  change (volume ((A ∪ B) ∩ C)).toReal =
    (volume (A ∩ C)).toReal+(volume (B ∩ C)).toReal at hcross
  change (volume (K \ ((A ∪ B) ∪ C))).toReal+(volume ((A ∪ B) ∪ C)).toReal =
    (volume K).toReal at hdiff
  linarith only [hab, habc, hcross, hdiff]

/-- Given full pair containment and empty triple intersection, actual gap
area equals body area minus the three individual plank areas plus full pair
areas. The real measure identity includes all measurable boundary terms. -/
theorem gap_inclusion_exclusion {K : Set Point} (hK : IsCompact K)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3)
    (hpairs : ∀ i j, i ≠ j → plank (f i) (e.1 i) (e.2 i) ∩ plank (f j) (e.1 j) (e.2 j) ⊆ K)
    (htriple : {x | ∀ i, e.1 i ≤ f i x ∧ f i x ≤ e.2 i} = ∅) :
    gapArea K f e = (volume K).toReal-
      ∑ i, (volume (K ∩ plank (f i) (e.1 i) (e.2 i))).toReal+
      (volume (plank (f 0) (e.1 0) (e.2 0) ∩ plank (f 1) (e.1 1) (e.2 1))).toReal+
      (volume (plank (f 0) (e.1 0) (e.2 0) ∩ plank (f 2) (e.1 2) (e.2 2))).toReal+
      (volume (plank (f 1) (e.1 1) (e.2 1) ∩ plank (f 2) (e.1 2) (e.2 2))).toReal := by
  let P (i : Fin 3) := plank (f i) (e.1 i) (e.2 i)
  let A (i : Fin 3) := K ∩ P i
  have hA (i : Fin 3) : MeasurableSet (A i) := hK.measurableSet.inter (isClosed_plank _ _ _).measurableSet
  have hzero : (A 0 ∩ A 1) ∩ A 2 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh : x ∈ {x | ∀ i, e.1 i ≤ f i x ∧ f i x ≤ e.2 i} := by
      intro i
      fin_cases i
      · exact hx.1.1.2
      · exact hx.1.2.2
      · exact hx.2.2
    rw [htriple] at hh
    exact hh
  have hpair (i j : Fin 3) (hij : i ≠ j) : A i ∩ A j = P i ∩ P j := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.2, hx.2.2⟩
    · intro hx
      have hmem := hpairs i j hij hx
      exact ⟨⟨hmem, hx.1⟩, ⟨hmem, hx.2⟩⟩
  have hset : K \ ((A 0 ∪ A 1) ∪ A 2) =
      K \ ⋃ i, {x | e.1 i ≤ f i x ∧ f i x ≤ e.2 i} := by
    ext x
    simp only [mem_sdiff, mem_union, mem_iUnion, mem_ofPred_eq, Fin.exists_fin_succ,
      Fin.exists_fin_zero, or_false,
      A, P, plank, mem_inter_iff]
    tauto
  have hh := area_sdiff_three hK (hA 0) (hA 1) (hA 2)
    inter_subset_left inter_subset_left inter_subset_left hzero
  rw [hset, hpair 0 1 (by decide), hpair 0 2 (by decide), hpair 1 2 (by decide)] at hh
  change gapArea K f e = _ at hh
  simpa only [Fin.sum_univ_three, sub_add_eq_sub_sub] using hh

/-- Exact actual-area formula on the selected seven-cell chart. All pair
containment and triple-intersection obligations are proved from that chart. -/
theorem chart_gap_area {K : Set Point} {f : Fin 3 → Point →ᵃ[ℝ] ℝ}
    (ch : CounterexampleChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (hne : K.Nonempty)
    (hf : ∀ i, 0 < Plank.Convex.DeficientHeightTilt.rangeWidth K (f i))
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (e : Endpoints 3) (he : e ∈ ch.chart.region) (horder : ∀ i, e.1 i ≤ e.2 i) :
    ch.chart.gapFormula.eval e = (volume K).toReal-
      ∑ i, (volume (K ∩ plank (f i) (e.1 i) (e.2 i))).toReal+
      pairCoefficient (f 0) (f 1) (hpairs 0 1 (by decide))*(e.2 0-e.1 0)*(e.2 1-e.1 1)+
      pairCoefficient (f 0) (f 2) (hpairs 0 2 (by decide))*(e.2 0-e.1 0)*(e.2 2-e.1 2)+
      pairCoefficient (f 1) (f 2) (hpairs 1 2 (by decide))*(e.2 1-e.1 1)*(e.2 2-e.1 2) := by
  rw [← ch.chart.gap_area e (subset_closure he) horder]
  change gapArea K f e = _
  rw [gap_inclusion_exclusion hK f e
    (fun i j hij => chart_pair_subset ch hK hconv hV e he i j hij (hpairs i j hij))
    (chart_triple_empty ch hK hconv hV hne hf e he)]
  simp only [plank]
  rw [area_pair (f 0) (f 1) _ _ _ _ _ (horder 0) (horder 1),
    area_pair (f 0) (f 2) _ _ _ _ _ (horder 0) (horder 2),
    area_pair (f 1) (f 2) _ _ _ _ _ (horder 1) (horder 2)]

end Plank.PlanarSevenCellArea
