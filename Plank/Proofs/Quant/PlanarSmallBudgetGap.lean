/- A uniform positive budget gap outside the four-point body class. -/
module

public import Plank.Proofs.Quant.PlanarSectionPeakRigidity
public import Plank.Proofs.Quant.PlanarCompactEqualityFiber

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSmallBudgetGap

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarSevenCellArea
open PlanarBodySectionDensity PlanarSectionPeakRigidity
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

/-- The covered area is at most the sum of the actual individual areas,
including all overlaps and degenerate windows. -/
theorem covered_le_sum {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) :
    (volume K).toReal-gapArea K f p ≤
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i) := by
  let P (i : Fin m) := plank (f i) (p.1 i) (p.2 i)
  have hm : MeasurableSet (⋃ i, P i) :=
    MeasurableSet.iUnion fun i => (isClosed_plank _ _ _).measurableSet
  have hd := measureReal_sdiff_add_inter (μ := volume) (s := K) hm hK.measure_ne_top
  have hu := measureReal_iUnion_fintype_le (μ := volume) (fun i => K ∩ P i)
  rw [← inter_iUnion] at hu
  change gapArea K f p+(volume (K ∩ ⋃ i, P i)).toReal = (volume K).toReal at hd
  change (volume (K ∩ ⋃ i, P i)).toReal ≤
    ∑ i, coveredArea K (f i) (p.1 i) (p.2 i) at hu
  linarith only [hd,hu]

/-- For three fixed normalized directions on a body outside the four-point
class, no sufficiently small positive budget can attain quantitative equality.
The bound is uniform over all positions, null widths and overlaps. -/
theorem exists_positive_budget_gap {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hnf : ¬∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ domain K f, 0 < budget K f p →
      gapArea K f p = (1-budget K f p)^2*(volume K).toReal →
      ε ≤ budget K f p := by
  have hex (i : Fin 3) := exists_strict_window_bound hK hc hne hV
    (f i) (hnorm i) (hunit i) hnf
  choose M hM hbound using hex
  let B := max (M 0) (max (M 1) (M 2))
  have hB : B < 2*(volume K).toReal := max_lt (hM 0) (max_lt (hM 1) (hM 2))
  have hMB (i : Fin 3) : M i ≤ B := by
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨(2*(volume K).toReal-B)/(volume K).toReal,
    div_pos (sub_pos.mpr hB) hV,?_⟩
  intro p hp hR he
  have hsum : (∑ i, (p.2 i-p.1 i)) = budget K f p := by
    unfold budget
    simp only [hunit,div_one]
  have hu := (covered_le_sum hK f p).trans
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (hbound i _ _ (hp.1 i).1 (hp.1 i).2.1 (hp.1 i).2.2).trans
        (mul_le_mul_of_nonneg_right (hMB i) (sub_nonneg.mpr (hp.1 i).2.1))))
  rw [← Finset.mul_sum,hsum,he] at hu
  apply (div_le_iff₀ hV).mpr
  have hh : budget K f p*(2*(volume K).toReal-B-budget K f p*(volume K).toReal) ≤ 0 := by
    nlinarith only [hu]
  have hz := nonpos_of_mul_nonpos_right hh hR
  linarith only [hz]

/-- A positive budget gap and local equality lines are incompatible with
an actual subcritical equality. No connectedness or convexity of the equality
set, or common line joining its endpoint budgets, is assumed. -/
theorem no_equality_of_gap_and_local_lines {m : ℕ} {K : Set Point}
    (hK : IsCompact K) (hne : K.Nonempty) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ p ∈ domain K f, 0 < budget K f p →
      gapArea K f p = (1-budget K f p)^2*(volume K).toReal → ε ≤ budget K f p)
    (hline : ∀ p ∈ domain K f, 0 < budget K f p → budget K f p < 1 →
      gapArea K f p = (1-budget K f p)^2*(volume K).toReal →
      ∃ z : Endpoints m, z ≠ 0 ∧ ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t| < η →
        p+t • z ∈ domain K f ∧
        gapArea K f (p+t • z) = (1-budget K f (p+t • z))^2*(volume K).toReal)
    (p : Endpoints m) (hp : p ∈ domain K f) (hp0 : 0 < budget K f p)
    (hp1 : budget K f p < 1)
    (he : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) : False := by
  let S := domain K f ∩ {q | gapArea K f q = (1-budget K f q)^2*(volume K).toReal} ∩
    {q | ε ≤ budget K f q}
  have hS : IsCompact S := ((isCompact_domain K f).inter_right
    (isClosed_eq (continuous_gapArea hK hne f hW)
      (((continuous_const.sub (continuous_budget K f)).pow 2).mul_const _))).inter_right
        (isClosed_le continuous_const (continuous_budget K f))
  have hpS : p ∈ S := ⟨⟨hp,he⟩,hgap p hp hp0 he⟩
  have hloc : ∀ q ∈ S, 0 < budget K f q → budget K f q < 1 →
      ∃ z : Endpoints m, z ≠ 0 ∧ ∃ η : ℝ, 0 < η ∧
        ∀ t : ℝ, |t| < η → q+t • z ∈ S := by
    intro q hq hq0 hq1
    obtain ⟨z,hz,η,hη,hl⟩ := hline q hq.1.1 hq0 hq1 hq.1.2
    have hopen : IsOpen {t : ℝ | 0 < budget K f (q+t • z)} :=
      isOpen_lt continuous_const ((continuous_budget K f).comp (by fun_prop))
    obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
      (show (0 : ℝ) ∈ {t | 0 < budget K f (q+t • z)} by simpa using hq0))
    refine ⟨z,hz,min η δ,lt_min hη hδ,?_⟩
    intro t ht
    have htη := ht.trans_le (min_le_left _ _)
    have htδ := ht.trans_le (min_le_right _ _)
    have hb : 0 < budget K f (q+t • z) := hball (by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using htδ)
    exact ⟨hl t htη,hgap _ (hl t htη).1 hb (hl t htη).2⟩
  have hh := PlanarCompactEqualityFiber.exists_zero_and_one hS
    (PlanarShiftedDomain.budgetLinear K f)
  simp only [PlanarShiftedDomain.budgetLinear_apply] at hh
  obtain ⟨⟨q,hq,hq0⟩,_⟩ := hh
    (fun q hq => ⟨budget_nonneg f hW hq.1.1,hq.1.1.2⟩)
    p hpS hp0 hp1 hloc
  have hh : ε ≤ budget K f q := hq.2
  rw [hq0] at hh
  exact hε.not_ge hh

end Plank.PlanarSmallBudgetGap

/-- info: 'Plank.PlanarSmallBudgetGap.exists_positive_budget_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSmallBudgetGap.exists_positive_budget_gap
/-- info: 'Plank.PlanarSmallBudgetGap.no_equality_of_gap_and_local_lines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSmallBudgetGap.no_equality_of_gap_and_local_lines
