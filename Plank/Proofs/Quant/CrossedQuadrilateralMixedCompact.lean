/- Compact exclusion once the actual three-band family has a physical realization. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralBoundaryClosure

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralMixedCompact
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarEqualityReductions
open CrossedQuadrilateralSupportOriginal CrossedQuadrilateralBoundaryModel
open Plank.Convex.DeficientHeightTilt
open scoped Topology

/-- A continuous physical realization supplies only coordinate identities and a
direction witness. The compactness, limit exclusion, interiority and local equality
motions are proved here. Constructing that realization for a mixed triple remains
an explicit obligation of applications; this theorem does not assume global motions. -/
theorem no_equality_of_realization {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (k : Fin 2 → ℝ) (hk : ∀ i, k i ≠ 0)
    (e : Endpoints 3 → State) (hec : Continuous e)
    (heo : ∀ q : Endpoints 3, (∀ i, q.1 i ≤ q.2 i) → Ordered (e q))
    (heb : ∀ q, fullBudget S k (e q) = budget K f q)
    (het : ∀ q : Endpoints 3, (∀ i, q.1 i ≤ q.2 i) →
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal → Tight S k (e q))
    (hed : ∀ q : Endpoints 3, (∀ i, q.1 i ≤ q.2 i) → 0 < badBudget S k (e q) →
      ∃ i, q.1 i < q.2 i ∧
        ¬((f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0))
    (p : Endpoints 3) (hp : p ∈ domain K f) (hp1 : budget K f p < 1)
    (hpbad : 0 < badBudget S k (e p))
    (hpeq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) : False := by
  have hK := genuine_compact hG
  have hc := genuine_convex hG
  have hne : K.Nonempty := by
    rw [hbody]
    exact (CrossedQuadrilateralContainedOriginal.body_nonempty S).image T
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; exact zero_lt_one
  let A := domain K f ∩ {q | gapArea K f q = (1-budget K f q)^2*(volume K).toReal}
  let Q := A ∩ {q | 0 < badBudget S k (e q)}
  let C := closure Q
  have hA : IsCompact A := (isCompact_domain K f).inter_right
    (isClosed_eq (continuous_gapArea hK hne f hW)
      (((continuous_const.sub (continuous_budget K f)).pow 2).mul_const _))
  have hCA : C ⊆ A := closure_minimal inter_subset_left hA.isClosed
  have hC : IsCompact C := hA.of_isClosed_subset isClosed_closure hCA
  have hmap : e '' Q ⊆ CrossedQuadrilateralBoundaryClosure.sharp S k := by
    rintro _ ⟨q,hq,rfl⟩
    have hqo (i) : q.1 i ≤ q.2 i := (hq.1.1.1 i).2.1
    refine ⟨⟨⟨heo q hqo,?_⟩,het q hqo hq.1.2⟩,hq.2⟩
    change fullBudget S k (e q) ≤ 1
    rw [heb]
    exact hq.1.1.2
  have hclosure (q) (hq : q ∈ C) : e q ∈ closure (CrossedQuadrilateralBoundaryClosure.sharp S k) :=
    closure_mono hmap (mem_closure_image hec.continuousAt hq)
  have hpositive (q) (hq : q ∈ C) (hq1 : budget K f q < 1) : 0 < badBudget S k (e q) :=
    CrossedQuadrilateralBoundaryClosure.positive_bad_in_closure S k hk (hclosure q hq)
      (by rwa [heb])
  have hloc : ∀ q ∈ C, 0 < budget K f q → budget K f q < 1 →
      ∃ z : Endpoints 3, z ≠ 0 ∧ ∃ η : ℝ, 0 < η ∧
        ∀ t : ℝ, |t| < η → q+t • z ∈ C := by
    intro q hq _ hq1
    have hqa := hCA hq
    have hqo (i) : q.1 i ≤ q.2 i := (hqa.1.1 i).2.1
    have hqe : Equality K f q := by
      change gapArea K f q = (max 0 (1-budget K f q))^2*(volume K).toReal
      rw [max_eq_right (sub_pos.mpr hq1).le]
      exact hqa.2
    have hqbad := hpositive q hq hq1
    obtain ⟨j,hj,hjbad⟩ := hed q hqo hqbad
    have hpos (i) : q.1 i < q.2 i := by
      by_contra hn
      have hz : q.1 i = q.2 i := le_antisymm (hqo i) (le_of_not_gt hn)
      exact hjbad (CrossedQuadrilateralSurvivingDirections.zero_window_surviving
        hG hV S T hbody f q hnorm hunit hqo hq1 hqe ⟨i,hz⟩ j hj)
    have hi := CrossedQuadrilateralTripleInterior.mem_interior hG hV f q hnorm hunit hpos hq1 hqe
    have hcount := CrossedQuadrilateralGenuine.at_most_six_of_equality hG hV f q hW hpos hq1 hqe
    obtain ⟨z,hz,η,hη,hl⟩ := PlanarFewCellEqualityLine.exists_local_motion
      hK hc hne hV f hW q hi hq1 hqa.2 hcount
    have hopen : IsOpen {t : ℝ | 0 < badBudget S k (e (q+t • z))} :=
      isOpen_lt continuous_const (((continuous_badBudget S k).comp hec).comp (by fun_prop))
    obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
      (show (0 : ℝ) ∈ {t | 0 < badBudget S k (e (q+t • z))} by simpa using hqbad))
    refine ⟨z,hz,min η δ,lt_min hη hδ,?_⟩
    intro t ht
    have hsmall := ht.trans_le (min_le_left _ _)
    apply subset_closure
    refine ⟨⟨interior_subset (hl t hsmall).1,(hl t hsmall).2.1⟩,?_⟩
    exact hball (by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using
        ht.trans_le (min_le_right _ _))
  have hpC : p ∈ C := subset_closure ⟨⟨hp,hpeq⟩,hpbad⟩
  have hp0 : 0 < budget K f p := by
    rw [← heb]
    exact hpbad.trans_le (CrossedQuadrilateralBoundaryClosure.bad_le_full S k
      (heo p (fun i => (hp.1 i).2.1)))
  have hh := PlanarCompactEqualityFiber.exists_zero_and_one hC (PlanarShiftedDomain.budgetLinear K f)
  simp only [PlanarShiftedDomain.budgetLinear_apply] at hh
  obtain ⟨⟨q,hq,hq0⟩,_⟩ := hh
    (fun q hq => ⟨budget_nonneg f hW (hCA hq).1,(hCA hq).1.2⟩)
    p hpC hp0 hp1 hloc
  have hpos := CrossedQuadrilateralBoundaryClosure.positive_budget_in_closure S k hk
    (hclosure q hq) (by rw [heb,hq0]; exact zero_lt_one)
  rw [heb,hq0] at hpos
  exact (lt_irrefl 0) hpos

end Quant.CrossedQuadrilateralMixedCompact

/-- info: 'Quant.CrossedQuadrilateralMixedCompact.no_equality_of_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralMixedCompact.no_equality_of_realization
