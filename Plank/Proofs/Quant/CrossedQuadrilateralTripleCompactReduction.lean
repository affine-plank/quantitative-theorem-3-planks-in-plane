/- A chosen positive plank survives reduction to a zero window or six cells. -/
module
public import Plank.Proofs.Quant.PlanarThreePlankFewCellMotion

public import Plank.Convex.FiniteExtremeMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralTripleCompactReduction
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarEqualityReductions
open CrossedQuadrilateralSupportOriginal
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- At fixed actual total relative width, every chosen positive plank
survives in an equality with either a zero window or exactly six nonempty
closed cells. The body and all three original normalized affine forms remain
fixed. An extreme maximizer of the chosen window width supplies the configuration. -/
theorem exists_zero_or_six {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hp : p ∈ domain K f) (hR : budget K f p < 1) (he : Equality K f p)
    (j : Fin 3) (hj : p.1 j < p.2 j) :
    ∃ q : Endpoints 3, q ∈ domain K f ∧ budget K f q = budget K f p ∧
      Equality K f q ∧ q.1 j < q.2 j ∧
      ((∃ i, q.1 i = q.2 i) ∨ ((∀ i, q.1 i < q.2 i) ∧
        (PlanarSevenNonemptyCells.nonemptyCells K f q).card = 6)) := by
  classical
  have hK := genuine_compact hG
  have hc := genuine_convex hG
  have hne : K.Nonempty := by
    obtain ⟨v,_,hbody,_⟩ := hG
    exact ⟨v 0,hbody ▸ subset_convexHull ℝ _ (mem_range_self 0)⟩
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; exact zero_lt_one
  have heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal := by
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at he
    rwa [max_eq_right (sub_pos.mpr hR).le] at he
  let E : Set (Endpoints 3) := domain K f ∩
    ({q | budget K f q = budget K f p} ∩
      {q | gapArea K f q = (1-budget K f p)^2*(volume K).toReal})
  have hpE : p ∈ E := ⟨hp,rfl,heq⟩
  have hcompact : IsCompact E := (isCompact_domain K f).inter_right
    ((isClosed_eq (continuous_budget K f) continuous_const).inter
      (isClosed_eq (continuous_gapArea hK hne f hW) continuous_const))
  let L : Endpoints 3 →ₗ[ℝ] ℝ := (LinearMap.proj j).comp
    (LinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ)-LinearMap.fst ℝ _ _)
  obtain ⟨q,hqext,hmin⟩ := Plank.Convex.ExtremeMinimum.exists_finite_extreme_minimizer
    E hcompact ⟨p,hpE⟩ (-L).toContinuousLinearMap
  have hq := hqext.1
  have hqb : budget K f q = budget K f p := hq.2.1
  have hqR : budget K f q < 1 := hqb ▸ hR
  have hqe : gapArea K f q = (1-budget K f q)^2*(volume K).toReal := by
    rw [hqb]
    exact hq.2.2
  have hEq : Equality K f q := by
    change gapArea K f q = (max 0 (1-budget K f q))^2*(volume K).toReal
    rwa [max_eq_right (sub_pos.mpr hqR).le]
  have hqj : q.1 j < q.2 j := by
    have hh : p.2 j-p.1 j ≤ q.2 j-q.1 j := neg_le_neg_iff.mp (hmin hpE)
    linarith only [hh,hj]
  refine ⟨q,hq.1,hqb,hEq,hqj,?_⟩
  by_cases hz : ∃ i, q.1 i = q.2 i
  · exact Or.inl hz
  have hqo (i) : q.1 i < q.2 i :=
    lt_of_le_of_ne (hq.1.1 i).2.1 (fun hh => hz ⟨i,hh⟩)
  refine Or.inr ⟨hqo,?_⟩
  apply le_antisymm (CrossedQuadrilateralGenuine.at_most_six_of_equality hG hV f q hW hqo hqR hEq)
  by_contra hn
  have hcount : (PlanarSevenNonemptyCells.nonemptyCells K f q).card < 6 := lt_of_not_ge hn
  obtain ⟨z,hzne,ε,hε,hmotion⟩ := PlanarThreePlankFewCellMotion.exists_motion hK hc hne hV f hW q
    (CrossedQuadrilateralTripleInterior.mem_interior hG hV f q hnorm hunit hqo hqR hEq) hqR hqe hcount
  have hmem (t : ℝ) (ht : |t| < ε) : q+t • z ∈ E := by
    obtain ⟨hi,hb,he⟩ := hmotion t ht
    refine ⟨interior_subset hi,hb.trans hqb,?_⟩
    change gapArea K f (q+t • z) = _
    simpa only [hqb] using he
  exact Plank.Convex.ExtremeMinimum.extreme_no_motion E q hqext z hzne
    (Metric.eventually_nhds_iff.mpr ⟨ε,hε,fun t ht => hmem t
      (by simpa only [dist_zero_right,Real.norm_eq_abs] using ht)⟩)

end Quant.CrossedQuadrilateralTripleCompactReduction

/-- info: 'Quant.CrossedQuadrilateralTripleCompactReduction.exists_zero_or_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralTripleCompactReduction.exists_zero_or_six
