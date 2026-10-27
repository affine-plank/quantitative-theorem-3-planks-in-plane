/- Every subcritical three-plank equality has at most four body vertices. -/
module

public import Plank.Proofs.Quant.PlanarSmallBudgetGap
public import Plank.Proofs.Quant.PlanarNonparallelEqualityMotion
public import Plank.Proofs.Quant.PlanarNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarThreePlankFourVertices

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarDirectionDerivatives PlanarAffineEquality PlanarSevenCellArea
open PlanarNormalization PlanarSmallBudgetGap PlanarSevenNonemptyCells
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Seven nonempty cells already force four vertices; a repeated direction
cannot have seven such cells, with either orientation of its unit range. -/
theorem cell_count_of_not_four {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (p : Endpoints 3) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) (he : Equality K f p.1 p.2)
    (hnf : ¬∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) :
    (nonemptyCells K f p).card ≤ 6 := by
  by_contra hn
  have hcount : 7 ≤ (nonemptyCells K f p).card := by omega
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; exact zero_lt_one
  have hf (i) := linear_ne_zero_of_rangeWidth_pos hne (f i) (hW i)
  exact hnf (PlanarSevenNonemptyCells.four_vertices hK hc hne hV f p hW ho
    (pairwise_transverse_of_seven K f hf p ho hcount) hR hcount he)

/-- The small-budget obstruction closes the compact local-line argument.
No direction independence or global straight equality ray is required. -/
theorem normalized_four_vertices {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (p : Endpoints 3) (hp : p ∈ domain K f)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  by_contra hnf
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; norm_num
  have hcontacts (i) : (∃ x ∈ K, f i x = 0) ∧ ∃ x ∈ K, f i x = 1 := by
    obtain ⟨x,hx,y,hy,hmax,hmin⟩ := Body.exists_realisers hK hne (continuous_form (f i))
    have hd : f i x-f i y = 1 :=
      (Body.width_eq_of_realisers hx hy hmax hmin).symm.trans (hunit i)
    have hy0 : f i y = 0 := by linarith only [hd,(hnorm i x hx).2,(hnorm i y hy).1]
    have hx1 : f i x = 1 := by linarith only [hd,hy0]
    exact ⟨⟨y,hy,hy0⟩,x,hx,hx1⟩
  obtain ⟨ε,hε,hgap⟩ := exists_positive_budget_gap hK hc hne hV f hnorm hunit hnf
  apply no_equality_of_gap_and_local_lines hK hne f hW ε hε hgap ?_ p hp hR0 hR1 heq
  intro q hq hq0 hq1 hqe
  have hs := PlanarTripleEndpointBoundary.strict_of_not_four hK hc hne hV f hW
    hnorm (fun i => (hcontacts i).1) (fun i => (hcontacts i).2) q hq hq0 hq1 hqe hnf
  have he : Equality K f q.1 q.2 := by
    change gapArea K f q = (max 0 (1-budget K f q))^2*(volume K).toReal
    rwa [max_eq_right (sub_pos.mpr hq1).le]
  have hn := cell_count_of_not_four hK hc hne hV f hnorm hunit q
    (fun i => (hs i).2.1) hq1 he hnf
  obtain ⟨z,hz,η,hη,hl⟩ := PlanarFewCellEqualityLine.exists_local_motion
    hK hc hne hV f hW q (mem_interior_of_strict K f hs hq1) hq1 hqe hn
  exact ⟨z,hz,η,hη,fun t ht => ⟨interior_subset (hl t ht).1,(hl t ht).2.1⟩⟩

/-- Exhaustive body rigidity in the original affine coordinates:
every positive-area compact convex planar body attaining the quantitative
three-plank bound at 0<R<1 is a triangle or quadrilateral. Zero-width
windows, repeated directions, arbitrary scales and placements are included. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : Equality K f p.1 p.2) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨g,q,hunit,hnorm,horder,hbudget,hgap⟩ :=
    normalize_data hK hne f p.1 p.2 ho hW
  have hgW (i) : 0 < rangeWidth K (g i) := by rw [hunit]; exact zero_lt_one
  have hqR : budget K g q < 1 := by rwa [hbudget]
  have hgEq : PlanarEqualityReductions.Equality K g q := by
    change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal
    rw [hgap,hbudget]
    exact heq
  have hclip := PlanarEqualityReductions.budget_clip_eq_three
    hK hc hne hV g q hgW hnorm horder hqR hgEq
  apply normalized_four_vertices hK hc hne hV g hnorm hunit (clipEndpoints q)
    (clipEndpoints_mem_domain g hgW q horder hqR.le)
    (by rw [hclip,hbudget]; exact hR0) (by rwa [hclip])
  rw [gapArea_clip hne g hgW hnorm q,hclip]
  simpa only [PlanarEqualityReductions.Equality,max_eq_right (sub_pos.mpr hqR).le] using hgEq

end Plank.PlanarThreePlankFourVertices

/-- info: 'Plank.PlanarThreePlankFourVertices.four_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarThreePlankFourVertices.four_vertices
