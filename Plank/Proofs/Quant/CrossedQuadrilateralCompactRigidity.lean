/- Compact equality sets propagate rigidity from four cells and one window. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralEmptyCellMotion

public import Plank.Convex.FiniteExtremeMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCompactRigidity
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open Plank.Convex.DeficientHeightTilt

/-- A direction property that holds for one surviving window and for four
nonempty closed cells holds for every positive window, provided positive
equality configurations avoid the support boundary. An extreme maximizer of
the chosen window width keeps that window positive and rules out an empty
cell via the proved constant-budget local motion. -/
theorem propagate {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p : Endpoints 2) (hp : p ∈ domain K f) (hR : budget K f p < 1)
    (he : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (Good : Fin 2 → Prop)
    (hsingle : ∀ q : Endpoints 2, q ∈ domain K f → budget K f q < 1 →
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal →
      ∀ j, q.1 j < q.2 j → (∀ i, i ≠ j → q.1 i = q.2 i) → Good j)
    (hfour : ∀ q : Endpoints 2, q ∈ domain K f → budget K f q < 1 →
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal →
      (∀ i, q.1 i < q.2 i) → (∀ s, (signCell K f q.1 q.2 s).Nonempty) → ∀ j, Good j)
    (hinterior : ∀ q : Endpoints 2, q ∈ domain K f → budget K f q < 1 →
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal →
      (∀ i, q.1 i < q.2 i) → q ∈ interior (domain K f)) :
    ∀ j, p.1 j < p.2 j → Good j := by
  classical
  intro j hj
  by_contra hbad
  let E : Set (Endpoints 2) := domain K f ∩
    ({q | budget K f q = budget K f p} ∩
      {q | gapArea K f q = (1-budget K f p)^2*(volume K).toReal})
  have hpE : p ∈ E := ⟨hp,rfl,he⟩
  have hcompact : IsCompact E := (isCompact_domain K f).inter_right
    ((isClosed_eq (continuous_budget K f) continuous_const).inter
      (isClosed_eq (continuous_gapArea hK hne f hW) continuous_const))
  let L : Endpoints 2 →ₗ[ℝ] ℝ := (LinearMap.proj j).comp
    (LinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)-LinearMap.fst ℝ _ _)
  obtain ⟨q,hqext,hmin⟩ := Plank.Convex.ExtremeMinimum.exists_finite_extreme_minimizer
    E hcompact ⟨p,hpE⟩ (-L).toContinuousLinearMap
  have hq := hqext.1
  have hqb : budget K f q = budget K f p := hq.2.1
  have hqR : budget K f q < 1 := hq.2.1 ▸ hR
  have hqe : gapArea K f q = (1-budget K f q)^2*(volume K).toReal := by
    rw [hq.2.1]
    exact hq.2.2
  have hqj : q.1 j < q.2 j := by
    have hh : p.2 j-p.1 j ≤ q.2 j-q.1 j := neg_le_neg_iff.mp (hmin hpE)
    linarith only [hh,hj]
  have hqo : ∀ i, q.1 i < q.2 i := by
    intro i
    by_contra hn
    have hzi : q.1 i = q.2 i := le_antisymm (hq.1.1 i).2.1 (le_of_not_gt hn)
    apply hbad
    apply hsingle q hq.1 hqR hqe j hqj
    intro k hkj
    have hij : i ≠ j := by rintro rfl; exact (ne_of_lt hqj) hzi
    have hki : k = i := by fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    exact hki ▸ hzi
  have hempty : ∃ s, ¬ (signCell K f q.1 q.2 s).Nonempty := by
    by_contra hn
    push Not at hn
    exact hbad (hfour q hq.1 hqR hqe hqo hn j)
  obtain ⟨z,hzne,ε,hε,hmotion⟩ := CrossedQuadrilateralEmptyCellMotion.exists_motion
    hK hc hne hV f hW q (hinterior q hq.1 hqR hqe hqo) hqR hqe hempty
  have hmem (t : ℝ) (ht : |t| < ε) : q+t • z ∈ E := by
    obtain ⟨hi,hb,he⟩ := hmotion t ht
    refine ⟨interior_subset hi,hb.trans hqb,?_⟩
    change gapArea K f (q+t • z) = _
    simpa only [hqb] using he
  exact Plank.Convex.ExtremeMinimum.extreme_no_motion E q hqext z hzne
    (Metric.eventually_nhds_iff.mpr ⟨ε,hε,fun t ht => hmem t
      (by simpa only [dist_zero_right,Real.norm_eq_abs] using ht)⟩)

end Quant.CrossedQuadrilateralCompactRigidity
