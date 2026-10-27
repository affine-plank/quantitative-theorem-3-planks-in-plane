/- Four positive exterior cells force a quadrilateral body in a two-plank equality. -/
module

public import Plank.Proofs.Quant.PlanarCriticalQuadrilateral
public import Plank.Proofs.Quant.PlanarOnlyOnePositive
public import Plank.Proofs.Quant.PlanarFourCellZeroWidth

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFourCellShape

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open Plank.Convex.PlanarTight
open scoped BigOperators Topology

/-- Normalized actual unit widths give the attained ranges needed by the
full-cover classification. -/
theorem ranges_of_unit {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1) :
    TwoPlankClassification.Ranges K (f 0) (f 1) := by
  have hends (i : Fin 2) : (∃ x ∈ K, f i x = 0) ∧ (∃ x ∈ K, f i x = 1) := by
    obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne (continuous_form (f i))
    have hspan : f i a-f i b = 1 :=
      (Body.width_eq_of_realisers ha hb hmax hmin).symm.trans (hunit i)
    refine ⟨⟨b,hb,?_⟩,⟨a,ha,?_⟩⟩ <;>
      linarith only [hspan,(hnorm i a ha).2,(hnorm i b hb).1]
  exact ⟨fun x hx => ⟨hnorm 0 x hx,hnorm 1 x hx⟩,
    (hends 0).1,(hends 0).2,(hends 1).1,(hends 1).2⟩

/-- On an arbitrary compact convex planar body, a positive-deficit tight
two-plank configuration with four positive exterior cells forces the body
to be the convex hull of at most four points. Endpoints are not assumed
clipped or strictly internal, and zero-width windows are allowed. -/
theorem shape_of_four_positive {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : TwoPlankClassification.Ranges K (f 0) (f 1))
    (p : Endpoints 2) (hp : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (hpos : ∀ s, 0 < (volume (signCell K f p.1 p.2 s)).toReal)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
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
  have hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1 := by
    intro i x hx
    fin_cases i
    · exact (H.box x hx).1
    · exact (H.box x hx).2
  have hpD : p ∈ domain K f := by
    refine ⟨?_,hR1.le⟩
    obtain ⟨a,ha⟩ := PlanarCellChartCalculus.nonempty_of_area_pos K f ∅ p (hpos ∅)
    obtain ⟨b,hb⟩ := PlanarCellChartCalculus.nonempty_of_area_pos K f Finset.univ p
      (hpos Finset.univ)
    intro i
    have hlow : f i a ≤ p.1 i := by simpa using ha.2 i
    have hhi : p.2 i ≤ f i b := by simpa only [Finset.mem_univ,if_pos] using hb.2 i
    exact ⟨(hnorm i a ha.1).1.trans hlow,hp i,hhi.trans (hnorm i b hb.1).2⟩
  by_cases hz : ∃ i, p.1 i = p.2 i
  · exact PlanarOnlyOnePositive.two_of_zero_window hK hconv hne hV f p hW hp hz
      hR0 hR1 heq
  have hpstrict : ∀ i, p.1 i < p.2 i :=
    fun i => lt_of_le_of_ne (hp i) (fun hi => hz ⟨i,hi⟩)
  have hpint : p ∈ interior (domain K f) := by
    have hs := PlanarFourCellZeroWidth.positive_cells_exclude_supports hne f hW hnorm p hpos
    exact mem_interior_of_strict K f (fun i =>
      ⟨lt_of_le_of_ne (hpD.1 i).1 (hs i).1.symm,hpstrict i,
        lt_of_le_of_ne (hpD.1 i).2.2 (hs i).2⟩) hR1
  obtain ⟨z,hzne,c,hc,hd,hu,hline⟩ := PlanarEqualityFullLine.exists_line
    hK hconv hne hV f hW p hpint hR1 heq
  obtain ⟨t,ht,hq,hqnot⟩ := PlanarEqualityChartExit.exists_ray_endpoint
    (isCompact_domain K f) p z hpint hzne
  have hfactor : 0 < 1+t*c := by positivity
  obtain ⟨hqeq,hscale⟩ := hline t hfactor.le (fun i => (hq.1 i).2.1)
  have hb : budget K f (p+t • z) ≤ budget K f p := by
    have hh := affine_eval_line (deficit K f 1) p z t
    simp only [deficit_apply] at hh
    rw [hd] at hh
    have hn := mul_nonneg (mul_nonneg ht.le (sub_pos.mpr hR1).le) hc
    nlinarith only [hh,hn]
  have hpositive (s) : 0 < (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal := by
    rw [hscale s]
    exact mul_pos (hpos s) (sq_pos_of_pos hfactor)
  have hzero : ∃ i, (p+t • z).1 i = (p+t • z).2 i := by
    have hn := PlanarFourCellZeroWidth.positive_cells_exclude_supports hne f hW hnorm
      (p+t • z) hpositive
    rcases boundary_cases K f hq hqnot with hbad | ⟨i,hh⟩
    · exact (not_lt_of_ge hb (hbad ▸ hR1)).elim
    · exact ⟨i,hh.resolve_left (hn i).1 |>.resolve_right (hn i).2⟩
  by_cases hB : 0 < budget K f (p+t • z)
  · exact PlanarOnlyOnePositive.two_of_zero_window hK hconv hne hV f (p+t • z) hW
      (fun i => (hq.1 i).2.1) hzero hB (hb.trans_lt hR1) hqeq
  · have hB0 : budget K f (p+t • z) = 0 :=
      le_antisymm (le_of_not_gt hB) (budget_nonneg f hW hq)
    have hall : ∀ i, (p+t • z).1 i = (p+t • z).2 i := by
      have hn (i : Fin 2) : 0 ≤ ((p+t • z).2 i-(p+t • z).1 i)/rangeWidth K (f i) :=
        div_nonneg (sub_nonneg.mpr (hq.1 i).2.1) (hW i).le
      intro i
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hB0 i
        (Finset.mem_univ i)
      exact (sub_eq_zero.mp ((div_eq_zero_iff).mp hh |>.resolve_right (hW i).ne')).symm
    exact PlanarCriticalQuadrilateral.shape_of_simultaneous_collapse hK hconv hne hV f H
      p z c hpstrict hR0 hR1 heq hd hu hpos t ht hall

end Plank.PlanarFourCellShape

/-- info: 'Plank.PlanarFourCellShape.shape_of_four_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFourCellShape.shape_of_four_positive
