/- Every positive window in a two-plank quadrilateral equality is diagonal. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCompactRigidity
public import Plank.Proofs.Quant.PlanarOnlyOnePositive

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralTwoPlankDirections
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarEqualityReductions CrossedQuadrilateralImageStrata
open Plank.Convex.DeficientHeightTilt

/-- Unrestricted two-positive-window direction necessity. The body supplies
its diagonal chart; no overlap, cell-count, equality-line or collapse
hypothesis is imposed. This version normalizes each actual directional range. -/
theorem normalized {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1) (he : Equality K f p) :
    ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point),
      K = T '' CrossedQuadrilateralFormDirections.body S ∧
      ∀ i, (f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0 := by
  obtain ⟨S,T,hbody⟩ := CrossedQuadrilateralGenuine.exists_model hG hV
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
  exact ⟨S,T,hbody,fun i => hprop hsingle hfour hinterior i (ho i)⟩

/-- The same exhaustive direction necessity for the original affine forms,
actual directional widths and arbitrary endpoints. In particular, clipped
pair overlaps and every exterior-cell degeneracy are included. -/
theorem original {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) (he : Equality K f p) :
    ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point),
      K = T '' CrossedQuadrilateralFormDirections.body S ∧
      ∀ i, (f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0 := by
  have hK := CrossedQuadrilateralSupportOriginal.genuine_compact hG
  have hne : K.Nonempty := by
    obtain ⟨v,_,hv,_⟩ := hG
    exact ⟨v 0,hv ▸ subset_convexHull ℝ _ (mem_range_self 0)⟩
  choose g a hg hnorm hunit using fun i => PlanarNormalization.exists_unit_form hK hne (f i) (hW i)
  let q : Endpoints 2 := (fun i => (p.1 i-a i)/rangeWidth K (f i),
    fun i => (p.2 i-a i)/rangeWidth K (f i))
  have hqo (i) : q.1 i < q.2 i :=
    (div_lt_div_iff_of_pos_right (hW i)).mpr (sub_lt_sub_right (ho i) _)
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
  obtain ⟨S,T,hbody,hd⟩ := normalized hG hV g q hnorm hunit hqo (by rwa [hb]) hEq
  refine ⟨S,T,hbody,fun i => ?_⟩
  have hlin := PlanarTransverseNormalization.linear_eq_of_formula (f i) (g i) (a i) _ (hg i)
  have hz (v : Point) (h : (g i).linear v = 0) : (f i).linear v = 0 := by
    rw [hlin,LinearMap.smul_apply,smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (hW i).ne')
  exact (hd i).imp (hz _) (hz _)

end Quant.CrossedQuadrilateralTwoPlankDirections

/-- info: 'Quant.CrossedQuadrilateralTwoPlankDirections.normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralTwoPlankDirections.normalized
/-- info: 'Quant.CrossedQuadrilateralTwoPlankDirections.original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralTwoPlankDirections.original
