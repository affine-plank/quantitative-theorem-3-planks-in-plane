/- Strictly feasible convex-body cuts have positive planar area. -/
module

public import Plank.Proofs.Quant.PlanarGapAnalysis

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarStrictCellPositivity

open Set MeasureTheory PlanarQuantitative PlanarCellArea

theorem positive_of_strict {ι : Type*} [Fintype ι] {K : Set Point}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f : ι → Point →L[ℝ] ℝ) (u : ι → ℝ) (x : Point) (hx : x ∈ K)
    (hs : ∀ i, f i x < u i) : 0 < (volume (cell K f u)).toReal := by
  let O : Set Point := ⋂ i, {z | f i z < u i}
  have hO : IsOpen O := isOpen_iInter_of_finite fun i =>
    isOpen_lt (f i).continuous continuous_const
  have hint := PlanarGapAnalysis.interior_nonempty_of_area_pos hK hconv hV
  have hclosure : closure (interior K) = K :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hint).trans hK.isClosed.closure_eq
  have hmeet : (interior K ∩ O).Nonempty := by
    apply (closure_inter_open_nonempty_iff hO).mp
    exact ⟨x,by rwa [hclosure],mem_iInter.mpr hs⟩
  have hsub : interior K ∩ O ⊆ cell K f u := by
    intro z hz
    refine ⟨interior_subset hz.1,mem_iInter.mpr fun i => ?_⟩
    have hh : f i z < u i := mem_iInter.mp hz.2 i
    exact hh.le
  have hp : 0 < volume (cell K f u) :=
    ((isOpen_interior.inter hO).measure_pos volume hmeet).trans_le (measure_mono hsub)
  exact ENNReal.toReal_pos hp.ne' (isCompact_cell hK f u).measure_ne_top

end Plank.PlanarStrictCellPositivity

/-- info: 'Plank.PlanarStrictCellPositivity.positive_of_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarStrictCellPositivity.positive_of_strict
