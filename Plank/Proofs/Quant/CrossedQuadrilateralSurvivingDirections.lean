/- Surviving positive directions in every supplied diagonal chart. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralTripleCompactReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSurvivingDirections
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarEqualityReductions CrossedQuadrilateralImageStrata
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Two-positive-plank diagonal necessity holds in every affine diagonal
presentation of the body, not only the chart chosen by an existence proof. -/
theorem two_in_chart {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1) (he : Equality K f p) :
    ∀ i, (f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0 := by
  have hK := CrossedQuadrilateralSupportOriginal.genuine_compact hG
  have hc := CrossedQuadrilateralSupportOriginal.genuine_convex hG
  have hne : K.Nonempty := by
    rw [hbody]
    exact (CrossedQuadrilateralContainedOriginal.body_nonempty S).image T
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; exact zero_lt_one
  have hp := CrossedQuadrilateralInterior.mem_interior hG hV f p hnorm hunit ho hR he
  have heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal := by
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at he
    rwa [max_eq_right (sub_pos.mpr hR).le] at he
  let Good (i : Fin 2) :=
    (f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0
  have hprop := CrossedQuadrilateralCompactRigidity.propagate hK hc hne hV f hW p
    (interior_subset hp) hR heq Good
  have hsingle : ∀ q : Endpoints 2, q ∈ domain K f → budget K f q < 1 →
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal →
      ∀ j, q.1 j < q.2 j → (∀ i, i ≠ j → q.1 i = q.2 i) → Good j := by
    intro q _ hqR hqe j hj hz
    let g (i) := pre T (f i)
    have hpreW (i) : 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (g i) := by
      rw [width_pre,← hbody]
      exact hW i
    have hpreB : budget (CrossedQuadrilateralFormDirections.body S) g q = budget K f q := by
      rw [budget_pre,← hbody]
    have hEq : Equality K f q := by
      change gapArea K f q = (max 0 (1-budget K f q))^2*(volume K).toReal
      rwa [max_eq_right (sub_pos.mpr hqR).le]
    rw [hbody] at hEq
    have hmodel := (equality_iff T (CrossedQuadrilateralFormDirections.body S) f q).mp hEq
    change gapArea (CrossedQuadrilateralFormDirections.body S) g q =
      (max 0 (1-budget (CrossedQuadrilateralFormDirections.body S) g q))^2*
        (volume (CrossedQuadrilateralFormDirections.body S)).toReal at hmodel
    have hRmodel : budget (CrossedQuadrilateralFormDirections.body S) g q < 1 := by
      rwa [hpreB]
    rw [max_eq_right (sub_pos.mpr hRmodel).le] at hmodel
    obtain ⟨hg,hb⟩ := PlanarOnlyOnePositive.gap_and_budget
      (CrossedQuadrilateralContainedOriginal.body_nonempty S) g q hpreW j hz
    rw [hg,hb] at hmodel
    exact CrossedQuadrilateralFormDirections.one_window_direction S (g j) _ _ hj (hpreW j)
      (by rwa [← hb]) hmodel
  have hfour : ∀ q : Endpoints 2, q ∈ domain K f → budget K f q < 1 →
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal →
      (∀ i, q.1 i < q.2 i) → (∀ s, (signCell K f q.1 q.2 s).Nonempty) → ∀ j, Good j := by
    intro q _ hqR hqe hqo hcells
    have hEq : Equality K f q := by
      change gapArea K f q = (max 0 (1-budget K f q))^2*(volume K).toReal
      rwa [max_eq_right (sub_pos.mpr hqR).le]
    exact directions_of_four_cells S T f q (by simpa only [← hbody] using hW) hqo
      (by simpa only [← hbody] using hqR) (by simpa only [← hbody] using hcells)
      (by simpa only [← hbody] using hEq)
  have hinterior : ∀ q : Endpoints 2, q ∈ domain K f → budget K f q < 1 →
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal →
      (∀ i, q.1 i < q.2 i) → q ∈ interior (domain K f) := by
    intro q _ hqR hqe hqo
    apply CrossedQuadrilateralInterior.mem_interior hG hV f q hnorm hunit hqo hqR
    change gapArea K f q = (max 0 (1-budget K f q))^2*(volume K).toReal
    rwa [max_eq_right (sub_pos.mpr hqR).le]
  exact fun i => hprop hsingle hfour hinterior i (ho i)

theorem single_in_chart {m : ℕ} {K : Set Point} (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hR : budget K f p < 1) (he : Equality K f p) (j : Fin m) (hj : p.1 j < p.2 j)
    (hz : ∀ i, i ≠ j → p.1 i = p.2 i) :
    (f j).linear (T.linear ![1,0]) = 0 ∨ (f j).linear (T.linear ![0,1]) = 0 := by
  let g (i) := pre T (f i)
  have hpreW (i) : 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (g i) := by
    rw [width_pre,← hbody]
    exact hW i
  have hpreB : budget (CrossedQuadrilateralFormDirections.body S) g p = budget K f p := by
    rw [budget_pre,← hbody]
  rw [hbody] at he
  have hmodel := (equality_iff T (CrossedQuadrilateralFormDirections.body S) f p).mp he
  change gapArea (CrossedQuadrilateralFormDirections.body S) g p =
    (max 0 (1-budget (CrossedQuadrilateralFormDirections.body S) g p))^2*
      (volume (CrossedQuadrilateralFormDirections.body S)).toReal at hmodel
  have hRmodel : budget (CrossedQuadrilateralFormDirections.body S) g p < 1 := by rwa [hpreB]
  rw [max_eq_right (sub_pos.mpr hRmodel).le] at hmodel
  obtain ⟨hg,hb⟩ := PlanarOnlyOnePositive.gap_and_budget
    (CrossedQuadrilateralContainedOriginal.body_nonempty S) g p hpreW j hz
  rw [hg,hb] at hmodel
  exact CrossedQuadrilateralFormDirections.one_window_direction S (g j) _ _ hj (hpreW j)
    (by rwa [← hb]) hmodel

theorem two_surviving_in_chart {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i ≤ p.2 i) (hR : budget K f p < 1) (he : Equality K f p)
    (j : Fin 2) (hj : p.1 j < p.2 j) :
    (f j).linear (T.linear ![1,0]) = 0 ∨ (f j).linear (T.linear ![0,1]) = 0 := by
  by_cases hpos : ∀ i, p.1 i < p.2 i
  · exact two_in_chart hG hV S T hbody f p hnorm hunit hpos hR he j
  · obtain ⟨i,hi⟩ := not_forall.mp hpos
    have hzi : p.1 i = p.2 i := le_antisymm (ho i) (le_of_not_gt hi)
    have hij : i ≠ j := by rintro rfl; exact (ne_of_lt hj) hzi
    apply single_in_chart S T hbody f p (fun i => by rw [hunit]; exact zero_lt_one) hR he j hj
    intro k hkj
    have hki : k = i := by fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    exact hki ▸ hzi

/-- A null member of an equality triple imposes no direction condition on
itself; every remaining positive member is diagonal in any chart of the body. -/
theorem zero_window_surviving {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i ≤ p.2 i) (hR : budget K f p < 1) (he : Equality K f p)
    (hz : ∃ i, p.1 i = p.2 i) (j : Fin 3) (hj : p.1 j < p.2 j) :
    (f j).linear (T.linear ![1,0]) = 0 ∨ (f j).linear (T.linear ![0,1]) = 0 := by
  obtain ⟨k,hk⟩ := hz
  have hjk : j ≠ k := by rintro rfl; exact (ne_of_lt hj) hk
  obtain ⟨j',hj'⟩ := Fin.exists_succAbove_eq hjk
  let g (i : Fin 2) := f (k.succAbove i)
  let q : Endpoints 2 := (fun i => p.1 (k.succAbove i),fun i => p.2 (k.succAbove i))
  have hne : K.Nonempty := by
    rw [hbody]
    exact (CrossedQuadrilateralContainedOriginal.body_nonempty S).image T
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; exact zero_lt_one
  have hu : (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) =
      {x | p.1 k ≤ f k x ∧ f k x ≤ p.2 k} ∪
        ⋃ i : Fin 2, {x | p.1 (k.succAbove i) ≤ f (k.succAbove i) x ∧
          f (k.succAbove i) x ≤ p.2 (k.succAbove i)} := by
    ext x
    simp only [mem_iUnion,mem_union,Fin.exists_iff_succAbove k]
  have hgap : gapArea K f p = gapArea K g q := by
    unfold gapArea
    rw [hu,← hk,PlanarInductionBoundary.area_delete_zero_width K _ (f k)
      (linear_ne_zero_of_rangeWidth_pos hne (f k) (hW k))]
  have hb : budget K f p = budget K g q := by
    unfold budget
    rw [Fin.sum_univ_succAbove _ k]
    simp only [← hk,sub_self,zero_div,zero_add]
    rfl
  have hqEq : Equality K g q := by
    change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal
    rw [← hgap,← hb]
    exact he
  have hh := two_surviving_in_chart hG hV S T hbody g q
    (fun i x hx => hnorm (k.succAbove i) x hx) (fun i => hunit (k.succAbove i))
    (fun i => ho (k.succAbove i)) (by rwa [← hb]) hqEq j'
    (by change p.1 (k.succAbove j') < p.2 (k.succAbove j'); rwa [hj'])
  simpa only [g,hj'] using hh

/-- Any positive direction outside the two diagonals would already occur
in an equality with the same body/forms/budget and exactly six closed exterior
cells. Zero-window alternatives are discharged by the proved two-plank theorem. -/
theorem non_diagonal_forces_six {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hp : p ∈ domain K f) (hR : budget K f p < 1) (he : Equality K f p)
    (j : Fin 3) (hj : p.1 j < p.2 j)
    (hbad : ¬((f j).linear (T.linear ![1,0]) = 0 ∨ (f j).linear (T.linear ![0,1]) = 0)) :
    ∃ q : Endpoints 3, q ∈ domain K f ∧ budget K f q = budget K f p ∧ Equality K f q ∧
      (∀ i, q.1 i < q.2 i) ∧ (PlanarSevenNonemptyCells.nonemptyCells K f q).card = 6 := by
  obtain ⟨q,hq,hb,hEq,hj',hz | hsix⟩ :=
    CrossedQuadrilateralTripleCompactReduction.exists_zero_or_six hG hV f p hnorm hunit hp hR he j hj
  · exact False.elim (hbad (zero_window_surviving hG hV S T hbody f q hnorm hunit
      (fun i => (hq.1 i).2.1) (hb ▸ hR) hEq hz j hj'))
  · exact ⟨q,hq,hb,hEq,hsix⟩

end Quant.CrossedQuadrilateralSurvivingDirections

/-- info: 'Quant.CrossedQuadrilateralSurvivingDirections.non_diagonal_forces_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSurvivingDirections.non_diagonal_forces_six
