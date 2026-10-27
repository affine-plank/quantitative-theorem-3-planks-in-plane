/- Four positive cells exclude support endpoints and force a zero window. -/
module

public import Plank.Proofs.Quant.PlanarFourCellEqualityRay

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFourCellZeroWidth

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarParameterDomain
  PlanarEqualityFlatDirection PlanarFourCellEqualityRay
open Plank.Convex.DeficientHeightTilt

theorem positive_cells_exclude_supports {K : Set Point} (hne : K.Nonempty)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) (p : Endpoints 2)
    (hpos : ∀ s, 0 < (volume (signCell K f p.1 p.2 s)).toReal) :
    ∀ i, p.1 i ≠ 0 ∧ p.2 i ≠ 1 := by
  classical
  intro i
  have hlinear := linear_ne_zero_of_rangeWidth_pos hne (f i) (hW i)
  constructor
  · intro he
    have hsub : signCell K f p.1 p.2 ∅ ⊆ {x | f i x = 0} := by
      intro x hx
      have hf : f i x ≤ p.1 i := by
        simpa using hx.2 i
      rw [he] at hf
      exact le_antisymm hf (hnorm i x hx.1).1
    have hz := measure_mono_null hsub (measure_level_zero (f i) hlinear 0)
    have hh := hpos ∅
    rw [hz,ENNReal.toReal_zero] at hh
    exact lt_irrefl 0 hh
  · intro he
    have hsub : signCell K f p.1 p.2 Finset.univ ⊆ {x | f i x = 1} := by
      intro x hx
      have hf : p.2 i ≤ f i x := by
        simpa only [Finset.mem_univ,if_pos] using hx.2 i
      rw [he] at hf
      exact le_antisymm (hnorm i x hx.1).2 hf
    have hz := measure_mono_null hsub (measure_level_zero (f i) hlinear 1)
    have hh := hpos Finset.univ
    rw [hz,ENNReal.toReal_zero] at hh
    exact lt_irrefl 0 hh

/-- Under actual unit support bounds, the global four-cell equality ray
reaches a zero-width window. Every uncovered cell remains positive there.
Both windows may vanish together; the theorem does not exclude that case. -/
theorem exists_zero_window {K : Set Point} {f : Fin 2 → Point →ᵃ[ℝ] ℝ}
    (ch : OpenChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hp : ch.point ∈ interior (domain K f)) (hR : budget K f ch.point < 1)
    (hpos : ∀ s, 0 < (ch.cellFormula s).eval ch.point)
    (heq : gapArea K f ch.point = (1-budget K f ch.point)^2*(volume K).toReal) :
    ∃ q : Endpoints 2, q ≠ ch.point ∧ q ∈ domain K f ∧ budget K f q ≤ budget K f ch.point ∧
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal ∧
      (∀ s, 0 < (volume (signCell K f q.1 q.2 s)).toReal) ∧ ∃ i, q.1 i = q.2 i := by
  obtain ⟨z,hzne,c,hc,_,hline⟩ := exists_global_ray ch hK hconv hne hV hW hp hR hpos heq
  obtain ⟨t,ht,hq,hqnot⟩ := PlanarEqualityChartExit.exists_ray_endpoint
    (isCompact_domain K f) ch.point z hp hzne
  obtain ⟨hqeq,hb,hscales⟩ := hline t ht.le (fun i => (hq.1 i).2.1)
  have hpositive (s) : 0 < (volume (signCell K f
      (ch.point+t • z).1 (ch.point+t • z).2 s)).toReal := by
    rw [hscales s]
    exact mul_pos (hpos s) (sq_pos_of_pos (by positivity))
  have hn := positive_cells_exclude_supports hne f hW hnorm (ch.point+t • z) hpositive
  refine ⟨ch.point+t • z,?_,hq,hb,hqeq,hpositive,?_⟩
  · intro he
    have hz0 : t • z = 0 := add_left_cancel (he.trans (add_zero ch.point).symm)
    exact (smul_ne_zero ht.ne' hzne) hz0
  · rcases boundary_cases K f hq hqnot with hbad | ⟨i,hh⟩
    · exact (not_lt_of_ge hb (hbad ▸ hR)).elim
    · exact ⟨i,hh.resolve_left (hn i).1 |>.resolve_right (hn i).2⟩

/-- The zero-window reduction with all chart obligations discharged for
a finite-halfplane body away from its finite affine cell walls. -/
theorem zero_window_off_cellWalls {ι : Type*} [Fintype ι]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (a b c d : ℝ) (A B C : ι → ℝ)
    (hrep : K = PlanarPolygonHalfplanes.boxedRegion a b c d A B C)
    (hbody : ∀ i, B i = 0 → A i ≠ 0) (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) (p : Endpoints 2)
    (hoff : ∀ w, PlanarPlankCellCharts.cellWalls a b c d A B C f w ≠ 0 →
      PlanarPlankCellCharts.cellWalls a b c d A B C f w p ≠ 0)
    (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (hpos : ∀ s, 0 < (volume (signCell K f p.1 p.2 s)).toReal)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ q : Endpoints 2, q ≠ p ∧ q ∈ domain K f ∧ budget K f q ≤ budget K f p ∧
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal ∧
      (∀ s, 0 < (volume (signCell K f q.1 q.2 s)).toReal) ∧ ∃ i, q.1 i = q.2 i := by
  obtain ⟨ch,hch,_⟩ := PlanarPolygonEqualityMotion.exists_chart_off_walls
    hK hne a b c d A B C hrep hbody f hW p hoff
  have hpositive (s) : 0 < (ch.cellFormula s).eval ch.point := by
    rw [← ch.cell_area s ch.point (subset_closure ch.point_mem),hch]
    exact hpos s
  obtain ⟨q,hqne,hqD,hqB,hqEq,hqpos,hqwindow⟩ := exists_zero_window ch hK hconv hne hV hW
    hnorm (by rwa [hch]) (by rwa [hch]) hpositive (by rwa [hch])
  exact ⟨q,by simpa only [hch] using hqne,hqD,by simpa only [hch] using hqB,
    hqEq,hqpos,hqwindow⟩

end Plank.PlanarFourCellZeroWidth

/-- info: 'Plank.PlanarFourCellZeroWidth.exists_zero_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFourCellZeroWidth.exists_zero_window
/-- info: 'Plank.PlanarFourCellZeroWidth.zero_window_off_cellWalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFourCellZeroWidth.zero_window_off_cellWalls
