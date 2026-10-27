/- Every normalized positive-deficit two-plank equality has a finite polygon body. -/
module

public import Plank.Proofs.Quant.PlanarFiniteExtremeHull
public import Plank.Proofs.Quant.PlanarSimultaneousExtreme
public import Plank.Proofs.Quant.PlanarBoundaryShape
public import Plank.Proofs.Quant.PlanarEqualityChartExit

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarTwoPlankPolygon

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open Plank.Convex.PlanarTight TwoPlankClassification
open scoped BigOperators Topology

theorem eight_of_four {K : Set Point}
    (h : ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) :
    ∃ S : Finset Point, S.card ≤ 8 ∧ K = convexHull ℝ (↑S : Set Point) := by
  classical
  obtain ⟨a,b,c,d,h⟩ := h
  refine ⟨{a,b,c,d},?_,by simpa using h⟩
  have h1 := Finset.card_insert_le a ({b,c,d} : Finset Point)
  have h2 := Finset.card_insert_le b ({c,d} : Finset Point)
  have h3 := Finset.card_insert_le c ({d} : Finset Point)
  simp only [Finset.card_singleton] at h3
  omega

/-- Every actual normalized two-plank equality with 0<R<1 has a body
which is the convex hull of at most eight points. The equality line,
collapse and extreme-point hypotheses are all derived, and no polygon,
cell-count, transversality or genericity hypothesis is assumed. This is
a necessary body reduction, not a sufficient condition on placements. -/
theorem eight_vertices {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : Ranges K (f 0) (f 1))
    (p : Endpoints 2) (hp : p ∈ domain K f)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ S : Finset Point, S.card ≤ 8 ∧ K = convexHull ℝ (↑S : Set Point) := by
  obtain ⟨hW0,hW1⟩ := PlanarCriticalNormalForm.rangeWidth_eq_one (f 0) (f 1) H
  have hW : ∀ i, 0 < rangeWidth K (f i) := by
    intro i
    fin_cases i
    · change 0 < rangeWidth K (f 0)
      rw [hW0]
      exact zero_lt_one
    · change 0 < rangeWidth K (f 1)
      rw [hW1]
      exact zero_lt_one
  by_cases hnot : p ∉ interior (domain K f)
  · exact eight_of_four (PlanarBoundaryShape.four_vertices hK hconv hne hV f H p hp hnot hR0 hR1 heq)
  obtain ⟨z,hzne,c,hc,hd,hu,hline⟩ := PlanarEqualityFullLine.exists_line
    hK hconv hne hV f hW p (not_not.mp hnot) hR1 heq
  obtain ⟨t,ht,hq,hqnot⟩ := PlanarEqualityChartExit.exists_ray_endpoint
    (isCompact_domain K f) p z (not_not.mp hnot) hzne
  have hfactor : 0 < 1+t*c := by positivity
  obtain ⟨hqeq,_⟩ := hline t hfactor.le (fun i => (hq.1 i).2.1)
  have hb : budget K f (p+t • z) ≤ budget K f p := by
    have hh := affine_eval_line (deficit K f 1) p z t
    simp only [deficit_apply] at hh
    rw [hd] at hh
    have hn := mul_nonneg (mul_nonneg ht.le (sub_pos.mpr hR1).le) hc
    nlinarith only [hh,hn]
  by_cases hB : 0 < budget K f (p+t • z)
  · exact eight_of_four (PlanarBoundaryShape.four_vertices hK hconv hne hV f H
      (p+t • z) hq hqnot hB (hb.trans_lt hR1) hqeq)
  · have hB0 : budget K f (p+t • z) = 0 :=
      le_antisymm (le_of_not_gt hB) (budget_nonneg f hW hq)
    have hall : ∀ i, (p+t • z).1 i = (p+t • z).2 i := by
      have hn (i : Fin 2) : 0 ≤ ((p+t • z).2 i-(p+t • z).1 i)/rangeWidth K (f i) :=
        div_nonneg (sub_nonneg.mpr (hq.1 i).2.1) (hW i).le
      intro i
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hB0 i
        (Finset.mem_univ i)
      exact (sub_eq_zero.mp ((div_eq_zero_iff).mp hh |>.resolve_right (hW i).ne')).symm
    have hloc := PlanarSimultaneousExtreme.critical_extreme_locations hK hconv hne hV f hW
      p z c (fun i => (hp.1 i).2.1) hR0 hR1 heq hd hu t ht hall
    obtain ⟨S,hSc,_,hshape⟩ := PlanarFiniteExtremeHull.eight_of_locations hK hconv hne f hW
      (p+t • z) (p+(-(c⁻¹)) • z) hloc
    exact ⟨S,hSc,hshape⟩

end Plank.PlanarTwoPlankPolygon

/-- info: 'Plank.PlanarTwoPlankPolygon.eight_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarTwoPlankPolygon.eight_vertices
