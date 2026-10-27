/- Every subcritical quadrilateral equality has a positive diagonal plank. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSectionGap
public import Plank.Proofs.Quant.PlanarFewCellEqualityLine

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralOneDiagonal
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  CrossedQuadrilateralImageStrata CrossedQuadrilateralSupportOriginal PlanarEqualityReductions
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem positive_index {m : ℕ} {K : Set Point} (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints m) (ho : ∀ i, p.1 i ≤ p.2 i) (hR : 0 < budget K f p) :
    ∃ i, p.1 i < p.2 i := by
  by_contra hn
  have hz (i) : p.1 i = p.2 i := le_antisymm (ho i)
    (le_of_not_gt (fun h => hn ⟨i,h⟩))
  have hb : budget K f p = 0 := by simp only [budget,hz,sub_self,zero_div,Finset.sum_const_zero]
  rw [hb] at hR
  exact (lt_irrefl 0) hR

/-- The three directions cannot all be non-diagonal. Small-budget strictness
and the actual local six-cell equality motion close a compact argument;
no global straight equality line or overlap assumption is used. -/
theorem normalized {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i ≤ p.2 i) (hR0 : 0 < budget K f p) (hR : budget K f p < 1)
    (he : Equality K f p) :
    ∃ i, p.1 i < p.2 i ∧
      ((f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0) := by
  have hK := genuine_compact hG
  have hc := genuine_convex hG
  have hne : K.Nonempty := by
    rw [hbody]
    exact (CrossedQuadrilateralContainedOriginal.body_nonempty S).image T
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; norm_num
  obtain ⟨j,hj⟩ := positive_index f p ho hR0
  by_cases hz : ∃ i, p.1 i = p.2 i
  · exact ⟨j,hj,CrossedQuadrilateralSurvivingDirections.zero_window_surviving hG hV S T hbody f p
      hnorm hunit ho hR he hz j hj⟩
  have hpos (i) : p.1 i < p.2 i := lt_of_le_of_ne (ho i) (fun hh => hz ⟨i,hh⟩)
  have hp : p ∈ domain K f := interior_subset
    (CrossedQuadrilateralTripleInterior.mem_interior hG hV f p hnorm hunit hpos hR he)
  by_contra hn
  have hbad (i) : ¬((f i).linear (T.linear ![1,0]) = 0 ∨
      (f i).linear (T.linear ![0,1]) = 0) := fun hh => hn ⟨i,hpos i,hh⟩
  obtain ⟨ε,hε,hgap⟩ := CrossedQuadrilateralSectionGap.positive_budget_gap
    hK hc hne hV S T hbody f hnorm hunit hbad
  have heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal := by
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at he
    rwa [max_eq_right (sub_pos.mpr hR).le] at he
  apply PlanarSmallBudgetGap.no_equality_of_gap_and_local_lines
    hK hne f hW ε hε hgap ?_ p hp hR0 hR heq
  intro q hq hq0 hq1 hqe
  have hEq : Equality K f q := by
    change gapArea K f q = (max 0 (1-budget K f q))^2*(volume K).toReal
    rwa [max_eq_right (sub_pos.mpr hq1).le]
  obtain ⟨k,hk⟩ := positive_index f q (fun i => (hq.1 i).2.1) hq0
  have hqo (i) : q.1 i < q.2 i := by
    by_contra hn
    have hzi : q.1 i = q.2 i := le_antisymm (hq.1 i).2.1 (le_of_not_gt hn)
    exact hbad k (CrossedQuadrilateralSurvivingDirections.zero_window_surviving hG hV S T hbody
      f q hnorm hunit (fun i => (hq.1 i).2.1) hq1 hEq ⟨i,hzi⟩ k hk)
  have hi := CrossedQuadrilateralTripleInterior.mem_interior hG hV f q hnorm hunit hqo hq1 hEq
  have hcount := CrossedQuadrilateralGenuine.at_most_six_of_equality hG hV f q hW hqo hq1 hEq
  obtain ⟨z,hz,η,hη,hl⟩ := PlanarFewCellEqualityLine.exists_local_motion
    hK hc hne hV f hW q hi hq1 hqe hcount
  exact ⟨z,hz,η,hη,fun t ht => ⟨interior_subset (hl t ht).1,(hl t ht).2.1⟩⟩

/-- Original affine scales and endpoints, in every supplied diagonal chart.
The diagonal member is positive; a freely placed null line is not a witness. -/
theorem original_in_chart {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR : budget K f p < 1) (he : Equality K f p) :
    ∃ i, p.1 i < p.2 i ∧
      ((f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0) := by
  have hK := genuine_compact hG
  have hne : K.Nonempty := by
    rw [hbody]
    exact (CrossedQuadrilateralContainedOriginal.body_nonempty S).image T
  choose g a hg hnorm hunit using fun i => PlanarNormalization.exists_unit_form hK hne (f i) (hW i)
  let q : Endpoints 3 := (fun i => (p.1 i-a i)/rangeWidth K (f i),
    fun i => (p.2 i-a i)/rangeWidth K (f i))
  have hqo (i) : q.1 i ≤ q.2 i :=
    (div_le_div_iff_of_pos_right (hW i)).mpr (sub_le_sub_right (ho i) _)
  have hband (i) : {x | q.1 i ≤ g i x ∧ g i x ≤ q.2 i} =
      {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
    ext x
    simp only [mem_ofPred_eq,hg]
    dsimp only [q]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  have hb : budget K g q = budget K f p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hunit]
    dsimp only [q]
    ring
  have hgap : gapArea K g q = gapArea K f p := by simp only [gapArea,hband]
  have hEq : Equality K g q := by
    change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal
    rwa [hgap,hb]
  obtain ⟨i,hi,hd⟩ := normalized hG hV S T hbody g q hnorm hunit hqo
    (by rwa [hb]) (by rwa [hb]) hEq
  have hpi : p.1 i < p.2 i := by
    dsimp only [q] at hi
    exact (sub_lt_sub_iff_right _).mp ((div_lt_div_iff_of_pos_right (hW i)).mp hi)
  refine ⟨i,hpi,?_⟩
  have hlin := PlanarTransverseNormalization.linear_eq_of_formula (f i) (g i) (a i) _ (hg i)
  have hz (v : Point) (h : (g i).linear v = 0) : (f i).linear v = 0 := by
    rw [hlin,LinearMap.smul_apply,smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (hW i).ne')
  exact hd.imp (hz _) (hz _)

/-- Every genuine quadrilateral at positive subcritical equality has an
actual positive plank parallel to one of its two diagonals. All directions,
placements, intersections, null members and affine scales are allowed. -/
theorem original {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR : budget K f p < 1) (he : Equality K f p) :
    ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point),
      K = T '' CrossedQuadrilateralFormDirections.body S ∧
      ∃ i, p.1 i < p.2 i ∧
        ((f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0) := by
  obtain ⟨S,T,hbody⟩ := CrossedQuadrilateralGenuine.exists_model hG hV
  exact ⟨S,T,hbody,original_in_chart hG hV S T hbody f p hW ho hR0 hR he⟩

end Quant.CrossedQuadrilateralOneDiagonal

/-- info: 'Quant.CrossedQuadrilateralOneDiagonal.normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralOneDiagonal.normalized
/-- info: 'Quant.CrossedQuadrilateralOneDiagonal.original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralOneDiagonal.original
