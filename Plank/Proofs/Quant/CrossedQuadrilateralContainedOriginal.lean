/- Original-coordinate strictness and the seven-nonempty-cell exclusion. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralContainedPairs
public import Plank.Proofs.Quant.PlanarTransverseNormalization
public import Plank.Proofs.Quant.PlanarNonemptyCellGeometry

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralContainedOriginal
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarSevenCellArea PlanarDirectionDerivatives PlanarNormalization PlanarTransverseNormalization
open PlanarEqualityReductions
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- For an arbitrary compact convex planar body, pair containment and null
triple overlap turn actual three-window equality into three actual individual
window equalities. There is no normalization or endpoint-position premise. -/
theorem individual_equality {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (htriple : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0)
    (heq : Equality K f p) : ∀ i, (volume (K \ plank (f i) (p.1 i) (p.2 i))).toReal =
      (1-(p.2 i-p.1 i)/rangeWidth K (f i))^2*(volume K).toReal := by
  classical
  choose g a hg hnorm hunit using fun i => exists_unit_form hK hne (f i) (hW i)
  let q : Endpoints 3 := (fun i => (p.1 i-a i)/rangeWidth K (f i),
    fun i => (p.2 i-a i)/rangeWidth K (f i))
  have hqo (i) : q.1 i < q.2 i :=
    (div_lt_div_iff_of_pos_right (hW i)).mpr (sub_lt_sub_right (ho i) _)
  have hb (i) : plank (g i) (q.1 i) (q.2 i) = plank (f i) (p.1 i) (p.2 i) := by
    ext x
    simp only [plank,mem_ofPred_eq,hg]
    dsimp only [q]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  have hbudget : budget K g q = budget K f p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hunit]
    dsimp only [q]
    ring
  have hgap : gapArea K g q = gapArea K f p := by
    change (volume (K \ ⋃ i, plank (g i) (q.1 i) (q.2 i))).toReal =
      (volume (K \ ⋃ i, plank (f i) (p.1 i) (p.2 i))).toReal
    simp only [hb]
  have hgpairs (i j) (hij : i ≠ j) : cross (g i) (g j) ≠ 0 := by
    rw [cross_scaled_pair (f i) (g i) (f j) (g j) _ _
      (linear_eq_of_formula _ _ _ _ (hg i)) (linear_eq_of_formula _ _ _ _ (hg j))]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hW i).ne') (inv_ne_zero (hW j).ne'))
      (hpairs i j hij)
  have hct (i j) (hij : i ≠ j) :
      plank (g i) (q.1 i) (q.2 i) ∩ plank (g j) (q.1 j) (q.2 j) ⊆ K := by
    rw [hb,hb]
    exact hcontain i j hij
  have ht : {x | ∀ i, q.1 i ≤ g i x ∧ g i x ≤ q.2 i} =
      {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
    ext x
    simp only [mem_ofPred_eq]
    apply forall_congr'
    intro i
    change x ∈ plank (g i) (q.1 i) (q.2 i) ↔ x ∈ plank (f i) (p.1 i) (p.2 i)
    rw [hb]
  have hge : Equality K g q := by
    change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal
    rwa [hgap,hbudget]
  have hi := CrossedQuadrilateralContainedPairs.individual_equality hK hc hne hV g hnorm hunit
    hgpairs q hqo (by rwa [hbudget]) hct (by rwa [ht]) hge
  intro i
  have hwi : (q.2 i-q.1 i)/rangeWidth K (g i) = (p.2 i-p.1 i)/rangeWidth K (f i) := by
    rw [hunit]
    dsimp only [q]
    ring
  simpa only [hb,hwi] using hi i


theorem compact_body (S : CrossedQuadrilateralAttainment.Shape) :
    IsCompact (CrossedQuadrilateralFormDirections.body S) :=
  ParallelProductPlane.compact_preimage (CrossedQuadrilateralAttainment.compact_body S)

theorem convex_body (S : CrossedQuadrilateralAttainment.Shape) :
    Convex ℝ (CrossedQuadrilateralFormDirections.body S) :=
  (CrossedQuadrilateralAttainment.convex_body S).linear_preimage
    ParallelProductPlane.coordinates.toLinearMap

theorem body_nonempty (S : CrossedQuadrilateralAttainment.Shape) :
    (CrossedQuadrilateralFormDirections.body S).Nonempty :=
  ⟨ParallelProductPlane.coordinates.symm 0,by simpa using CrossedQuadrilateralAttainment.zero_mem S⟩

theorem area_body_pos (S : CrossedQuadrilateralAttainment.Shape) :
    0 < (volume (CrossedQuadrilateralFormDirections.body S)).toReal := by
  rw [ParallelProductPlane.volume_preimage]
  exact CrossedQuadrilateralAttainment.area_body_pos S

/-- The contained-pair/null-triple stratum is strictly above the square bound
on a genuine quadrilateral for three distinct positive directions, using the
original affine forms and actual relative widths. -/
theorem not_equality (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i) (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩
      plank (f j) (p.1 j) (p.2 j) ⊆ CrossedQuadrilateralFormDirections.body S)
    (htriple : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0) :
    ¬Equality (CrossedQuadrilateralFormDirections.body S) f p := by
  intro he
  have hi := individual_equality (compact_body S) (convex_body S) (body_nonempty S)
    (area_body_pos S) f p hW ho hpairs hR hcontain htriple he
  have hRi (i) : (p.2 i-p.1 i)/rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i) < 1 :=
    (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      div_nonneg (sub_pos.mpr (ho j)).le (hW j).le) (Finset.mem_univ i)).trans_lt hR
  obtain ⟨i,j,hij,hij0⟩ := CrossedQuadrilateralFormDirections.three_tight_have_parallel_pair
    S f p.1 p.2 ho hW hRi hi
  exact hpairs i j hij hij0

theorem strict_gap (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i) (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩
      plank (f j) (p.1 j) (p.2 j) ⊆ CrossedQuadrilateralFormDirections.body S)
    (htriple : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0) :
    (1-budget (CrossedQuadrilateralFormDirections.body S) f p)^2*
      (volume (CrossedQuadrilateralFormDirections.body S)).toReal <
      gapArea (CrossedQuadrilateralFormDirections.body S) f p := by
  have hl := PlanarThreePlank.sharpPlanarBound_three (CrossedQuadrilateralFormDirections.body S)
    (compact_body S) (convex_body S) (body_nonempty S) f p.1 p.2 (fun i => (ho i).le) hW
  change (max 0 (1-budget (CrossedQuadrilateralFormDirections.body S) f p))^2*
      (volume (CrossedQuadrilateralFormDirections.body S)).toReal ≤
      gapArea (CrossedQuadrilateralFormDirections.body S) f p at hl
  rw [max_eq_right (sub_pos.mpr hR).le] at hl
  apply lt_of_le_of_ne hl
  intro he
  apply not_equality S f p hW ho hpairs hR hcontain htriple
  change gapArea (CrossedQuadrilateralFormDirections.body S) f p =
    (max 0 (1-budget (CrossedQuadrilateralFormDirections.body S) f p))^2*
      (volume (CrossedQuadrilateralFormDirections.body S)).toReal
  rw [max_eq_right (sub_pos.mpr hR).le]
  exact he.symm

/-- Seven nonempty closed exterior cells, including null cells, are strict.
Their geometry supplies pair containment, null triple overlap, and distinct
directions; none of those is an additional premise here. -/
theorem seven_nonempty_strict (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcount : 7 ≤ (PlanarSevenNonemptyCells.nonemptyCells
      (CrossedQuadrilateralFormDirections.body S) f p).card) :
    (1-budget (CrossedQuadrilateralFormDirections.body S) f p)^2*
      (volume (CrossedQuadrilateralFormDirections.body S)).toReal <
      gapArea (CrossedQuadrilateralFormDirections.body S) f p := by
  have hf (i) : (f i).linear ≠ 0 := linear_ne_zero_of_rangeWidth_pos (body_nonempty S) (f i) (hW i)
  apply strict_gap S f p hW ho
    (PlanarSevenNonemptyCells.pairwise_transverse_of_seven _ f hf p ho hcount) hR
  · exact PlanarSevenNonemptyCells.pair_subset_of_nonempty_seven (compact_body S).isClosed
      (convex_body S) f hf p ho hcount
  · exact PlanarSevenNonemptyCells.triple_null_of_seven _ f hf p hcount

/-- A genuine quadrilateral equality with three positive windows has at most
six nonempty exterior cells. Arbitrary directions, scales and endpoints are included. -/
theorem at_most_six_of_equality (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (he : Equality (CrossedQuadrilateralFormDirections.body S) f p) :
    (PlanarSevenNonemptyCells.nonemptyCells (CrossedQuadrilateralFormDirections.body S) f p).card ≤ 6 := by
  by_contra hn
  have hs := seven_nonempty_strict S f p hW ho hR (by omega)
  change gapArea (CrossedQuadrilateralFormDirections.body S) f p =
    (max 0 (1-budget (CrossedQuadrilateralFormDirections.body S) f p))^2*
      (volume (CrossedQuadrilateralFormDirections.body S)).toReal at he
  rw [max_eq_right (sub_pos.mpr hR).le] at he
  linarith only [hs,he]

end Quant.CrossedQuadrilateralContainedOriginal

/-- info: 'Quant.CrossedQuadrilateralContainedOriginal.at_most_six_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralContainedOriginal.at_most_six_of_equality
