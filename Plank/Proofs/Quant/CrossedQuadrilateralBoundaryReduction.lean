/- A genuine-quadrilateral equality line reaches a zero window, never a support. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralInterior
public import Plank.Proofs.Quant.PlanarEqualityFullLine
public import Plank.Proofs.Quant.PlanarEqualityChartExit

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralBoundaryReduction
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells PlanarEqualityReductions
open Plank.Convex.DeficientHeightTilt
open PlanarShiftedDomain (deficit deficit_apply)

/-- Every two-positive-window equality on a genuine quadrilateral has a
distinct equality endpoint with the same body and directions, nonincreasing
actual total relative width, and at least one zero window. No chart or cell-count
condition is assumed. Simultaneous collapse is explicitly still allowed. -/
theorem exists_zero_window {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1) (he : Equality K f p) :
    ∃ q : Endpoints 2, q ≠ p ∧ q ∈ domain K f ∧ budget K f q ≤ budget K f p ∧
      Equality K f q ∧ ∃ i, q.1 i = q.2 i := by
  have hK := CrossedQuadrilateralSupportOriginal.genuine_compact hG
  have hc := CrossedQuadrilateralSupportOriginal.genuine_convex hG
  have hne : K.Nonempty := by
    obtain ⟨v,_,hbody,_⟩ := hG
    refine ⟨v 0,?_⟩
    rw [hbody]
    exact subset_convexHull ℝ _ (mem_range_self 0)
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; exact zero_lt_one
  have hp := CrossedQuadrilateralInterior.mem_interior hG hV f p hnorm hunit ho hR he
  have heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal := by
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at he
    rwa [max_eq_right (sub_pos.mpr hR).le] at he
  obtain ⟨z,hzne,c,hc0,hd,_,hline⟩ := PlanarEqualityFullLine.exists_line
    hK hc hne hV f hW p hp hR heq
  obtain ⟨t,ht,hq,hqnot⟩ := PlanarEqualityChartExit.exists_ray_endpoint
    (isCompact_domain K f) p z hp hzne
  have hfactor : 0 < 1+t*c := by positivity
  obtain ⟨hqeq,_⟩ := hline t hfactor.le (fun i => (hq.1 i).2.1)
  have hb : budget K f (p+t • z) ≤ budget K f p := by
    have hh := PlanarPolygonCharts.affine_eval_line (deficit K f 1) p z t
    simp only [deficit_apply] at hh
    rw [hd] at hh
    have hn := mul_nonneg (mul_nonneg ht.le (sub_pos.mpr hR).le) hc0
    nlinarith only [hh,hn]
  have hqR : budget K f (p+t • z) < 1 := hb.trans_lt hR
  have heq' : Equality K f (p+t • z) := by
    change gapArea K f (p+t • z) = (max 0 (1-budget K f (p+t • z)))^2*(volume K).toReal
    rwa [max_eq_right (sub_pos.mpr hqR).le]
  refine ⟨p+t • z,?_,hq,hb,heq',CrossedQuadrilateralInterior.boundary_zero_window
    hG hV f (p+t • z) hnorm hunit hq hqnot hqR heq'⟩
  intro hh
  have hz0 : t • z = 0 := add_left_cancel (hh.trans (add_zero p).symm)
  exact (smul_ne_zero ht.ne' hzne) hz0

end Quant.CrossedQuadrilateralBoundaryReduction

/-- info: 'Quant.CrossedQuadrilateralBoundaryReduction.exists_zero_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralBoundaryReduction.exists_zero_window
