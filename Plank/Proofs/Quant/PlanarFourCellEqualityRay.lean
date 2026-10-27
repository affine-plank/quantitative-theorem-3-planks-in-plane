/- Four positive cells allow equality motion through every chart wall. -/
module

public import Plank.Proofs.Quant.PlanarEqualityCellScaling
public import Plank.Proofs.Quant.PlanarCellRayConcavity
public import Plank.Proofs.Quant.PlanarEqualityChartExit
public import Plank.Proofs.Quant.PlanarPolygonEqualityMotion

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFourCellEqualityRay

open Set MeasureTheory PlanarQuantitative PlanarPolygonCharts PlanarPlankCellCharts
  PlanarParameterDomain QuadraticChartCalculus PlanarEqualityFlatDirection
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

/-- For four positive uncovered cells, a nonzero equality ray continues
through all chart changes for as long as the windows stay ordered. The
initial actual-area chart is the only chart premise. -/
theorem exists_global_ray {K : Set Point} {f : Fin 2 → Point →ᵃ[ℝ] ℝ}
    (ch : OpenChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hp : ch.point ∈ interior (domain K f)) (hR : budget K f ch.point < 1)
    (hpos : ∀ s, 0 < (ch.cellFormula s).eval ch.point)
    (heq : gapArea K f ch.point = (1-budget K f ch.point)^2*(volume K).toReal) :
    ∃ z : Endpoints 2, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      (deficit K f 1).linear z = (1-budget K f ch.point)*c ∧ ∀ t : ℝ, 0 ≤ t →
      (∀ i, (ch.point+t • z).1 i ≤ (ch.point+t • z).2 i) →
      gapArea K f (ch.point+t • z) =
        (1-budget K f (ch.point+t • z))^2*(volume K).toReal ∧
      budget K f (ch.point+t • z) ≤ budget K f ch.point ∧
      ∀ s, (volume (PlanarGapCells.signCell K f
        (ch.point+t • z).1 (ch.point+t • z).2 s)).toReal =
        (ch.cellFormula s).eval ch.point*(1+t*c)^2 := by
  classical
  obtain ⟨z,hzne,c,hc,hd,hscale⟩ := PlanarEqualityCellScaling.exists_common_scaling ch
    hK hconv hne hV hW hp hR hpos heq
  have hopen : IsOpen {t : ℝ | ch.point+t • z ∈ ch.region ∧ 0 < 1+t*c} := by
    have h₁ : IsOpen {t : ℝ | ch.point+t • z ∈ ch.region} :=
      ch.open_region.preimage (by fun_prop)
    have h₂ : IsOpen {t : ℝ | 0 < 1+t*c} := isOpen_lt continuous_const (by fun_prop)
    exact h₁.inter h₂
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
    (show (0 : ℝ) ∈ {t | ch.point+t • z ∈ ch.region ∧ 0 < 1+t*c} by
      simpa only [mem_ofPred_eq,zero_smul,add_zero,zero_mul,add_zero] using
        And.intro ch.point_mem (show (0 : ℝ) < 1 by norm_num)))
  let ε := δ/2
  have hε : 0 < ε := by dsimp [ε]; linarith only [hδ]
  have hback : ch.point+(-ε) • z ∈ ch.region ∧ 0 < 1+(-ε)*c := hball (by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_neg,abs_of_pos hε]
    dsimp [ε]; linarith only [hδ])
  have hbackne (s) :
      (PlanarGapCells.signCell K f (ch.point+(-ε) • z).1 (ch.point+(-ε) • z).2 s).Nonempty := by
    apply PlanarCellChartCalculus.nonempty_of_area_pos
    rw [hscale s (-ε) (subset_closure hback.1)]
    exact mul_pos (hpos s) (sq_pos_of_pos hback.2)
  have hbackroot (s) :
      Real.sqrt (volume (PlanarGapCells.signCell K f
        (ch.point+(-ε) • z).1 (ch.point+(-ε) • z).2 s)).toReal =
      (1-ε*c)*Real.sqrt (volume (PlanarGapCells.signCell K f ch.point.1 ch.point.2 s)).toReal := by
    rw [hscale s (-ε) (subset_closure hback.1),
      ch.cell_area s ch.point (subset_closure ch.point_mem),
      Real.sqrt_mul (hpos s).le,Real.sqrt_sq_eq_abs,abs_of_pos hback.2]
    ring
  have hsum : (∑ s, (ch.cellFormula s).eval ch.point) =
      (1-budget K f ch.point)^2*(volume K).toReal := by
    rw [← ch.gap_sum,← ch.gap_area hK hne hW ch.point (subset_closure ch.point_mem)
      (fun i => ((interior_subset hp).1 i).2.1)]
    exact heq
  refine ⟨z,hzne,c,hc,hd,?_⟩
  intro t ht ho
  have hdef : 1-budget K f (ch.point+t • z) = (1-budget K f ch.point)*(1+t*c) := by
    have hh := affine_eval_line (deficit K f 1) ch.point z t
    simp only [deficit_apply] at hh
    rw [hd] at hh
    nlinarith only [hh]
  have hb : budget K f (ch.point+t • z) ≤ budget K f ch.point := by
    have hh : 0 ≤ (1-budget K f ch.point)*(t*c) :=
      mul_nonneg (sub_nonneg.mpr hR.le) (mul_nonneg ht hc)
    nlinarith only [hdef,hh]
  have hcell (s) : (volume (PlanarGapCells.signCell K f
      (ch.point+t • z).1 (ch.point+t • z).2 s)).toReal ≤
      (ch.cellFormula s).eval ch.point*(1+t*c)^2 := by
    have hh := PlanarCellRayConcavity.forward_area_le hK hconv f s ch.point z
      ε c hε (hbackne s) (hbackroot s) t ht
    rwa [ch.cell_area s ch.point (subset_closure ch.point_mem)] at hh
  have hupper : gapArea K f (ch.point+t • z) ≤
      (1-budget K f (ch.point+t • z))^2*(volume K).toReal := by
    rw [gapArea,PlanarGapCells.area_gap_eq_sum_signCells hK hne f hW _ _ ho]
    calc
      (∑ s, (volume (PlanarGapCells.signCell K f
          (ch.point+t • z).1 (ch.point+t • z).2 s)).toReal) ≤
          ∑ s, (ch.cellFormula s).eval ch.point*(1+t*c)^2 := by
        apply Finset.sum_le_sum
        intro s _
        exact hcell s
      _ = (1-budget K f (ch.point+t • z))^2*(volume K).toReal := by
        rw [← Finset.sum_mul,hsum,hdef]
        ring
  have hgeq : gapArea K f (ch.point+t • z) =
      (1-budget K f (ch.point+t • z))^2*(volume K).toReal := by
    apply le_antisymm hupper
    have hlower := PlanarTwoPlank.sharpPlanarBound_two K hK hconv hne f
      (ch.point+t • z).1 (ch.point+t • z).2 ho hW
    change (max 0 (1-budget K f (ch.point+t • z)))^2*(volume K).toReal ≤
      gapArea K f (ch.point+t • z) at hlower
    rwa [max_eq_right (sub_nonneg.mpr (hb.trans hR.le))] at hlower
  refine ⟨hgeq,hb,?_⟩
  have hse : (∑ s, (volume (PlanarGapCells.signCell K f
      (ch.point+t • z).1 (ch.point+t • z).2 s)).toReal) =
      ∑ s, (ch.cellFormula s).eval ch.point*(1+t*c)^2 := by
    rw [← PlanarGapCells.area_gap_eq_sum_signCells hK hne f hW _ _ ho]
    change gapArea K f (ch.point+t • z) = _
    rw [hgeq,← Finset.sum_mul,hsum,hdef]
    ring
  have hex := (Finset.sum_eq_sum_iff_of_le (fun s (_ : s ∈ Finset.univ) => hcell s)).mp hse
  exact fun s => hex s (Finset.mem_univ s)

/-- With four positive cells, an interior equality reaches an actual
zero/support window boundary. Affine chart walls are no longer endpoints
of the argument. The body and the two directions stay fixed. -/
theorem exists_window_boundary {K : Set Point} {f : Fin 2 → Point →ᵃ[ℝ] ℝ}
    (ch : OpenChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hp : ch.point ∈ interior (domain K f)) (hR : budget K f ch.point < 1)
    (hpos : ∀ s, 0 < (ch.cellFormula s).eval ch.point)
    (heq : gapArea K f ch.point = (1-budget K f ch.point)^2*(volume K).toReal) :
    ∃ q : Endpoints 2, q ≠ ch.point ∧ q ∈ domain K f ∧ budget K f q ≤ budget K f ch.point ∧
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal ∧
      ∃ i, q.1 i = 0 ∨ q.1 i = q.2 i ∨ q.2 i = 1 := by
  obtain ⟨z,hzne,c,hc,hd,hline⟩ := exists_global_ray ch hK hconv hne hV hW hp hR hpos heq
  obtain ⟨t,ht,hq,hqnot⟩ := PlanarEqualityChartExit.exists_ray_endpoint
    (isCompact_domain K f) ch.point z hp hzne
  obtain ⟨hqeq,hb,_⟩ := hline t ht.le (fun i => (hq.1 i).2.1)
  refine ⟨ch.point+t • z,?_,hq,hb,hqeq,?_⟩
  · intro he
    have hz0 : t • z = 0 := add_left_cancel (he.trans (add_zero ch.point).symm)
    exact (smul_ne_zero ht.ne' hzne) hz0
  · rcases boundary_cases K f hq hqnot with hbad | hh
    · exact (not_lt_of_ge hb (hbad ▸ hR)).elim
    · exact hh

/-- A finite-halfplane specialization stated entirely with actual cell
areas. The initial open chart is constructed, with no transversality
assumption; subsequent chart walls do not obstruct the motion. -/
theorem window_boundary_off_cellWalls {ι : Type*} [Fintype ι]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (a b c d : ℝ) (A B C : ι → ℝ)
    (hrep : K = PlanarPolygonHalfplanes.boxedRegion a b c d A B C)
    (hbody : ∀ i, B i = 0 → A i ≠ 0) (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (p : Endpoints 2)
    (hoff : ∀ w, cellWalls a b c d A B C f w ≠ 0 → cellWalls a b c d A B C f w p ≠ 0)
    (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (hpos : ∀ s, 0 < (volume (PlanarGapCells.signCell K f p.1 p.2 s)).toReal)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ q : Endpoints 2, q ≠ p ∧ q ∈ domain K f ∧ budget K f q ≤ budget K f p ∧
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal ∧
      ∃ i, q.1 i = 0 ∨ q.1 i = q.2 i ∨ q.2 i = 1 := by
  obtain ⟨ch,hch,_⟩ := PlanarPolygonEqualityMotion.exists_chart_off_walls
    hK hne a b c d A B C hrep hbody f hW p hoff
  have hpositive (s) : 0 < (ch.cellFormula s).eval ch.point := by
    rw [← ch.cell_area s ch.point (subset_closure ch.point_mem),hch]
    exact hpos s
  obtain ⟨q,hqne,hqD,hqB,hqEq,hqwindow⟩ := exists_window_boundary ch hK hconv hne hV hW
    (by rwa [hch]) (by rwa [hch]) hpositive (by rwa [hch])
  exact ⟨q,by simpa only [hch] using hqne,hqD,by simpa only [hch] using hqB,hqEq,hqwindow⟩

end Plank.PlanarFourCellEqualityRay

/-- info: 'Plank.PlanarFourCellEqualityRay.exists_window_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFourCellEqualityRay.exists_window_boundary
/-- info: 'Plank.PlanarFourCellEqualityRay.window_boundary_off_cellWalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFourCellEqualityRay.window_boundary_off_cellWalls
