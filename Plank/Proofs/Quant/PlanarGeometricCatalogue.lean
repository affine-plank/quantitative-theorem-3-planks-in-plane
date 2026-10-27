/- Exhaustive geometric equality families for three planks on every planar body. -/
module
public import Plank.Proofs.Quant.PlanarGeometricCatalogueBridge
public import Plank.Proofs.Quant.PlanarThreePlankFourVertices
public import Plank.Proofs.Quant.CrossedQuadrilateralCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.PlanarGeometricCatalogue
open Set MeasureTheory PlanarGeometricCatalogueBridge
open Plank.Convex.DeficientHeightTilt
open Plank.PlanarParameterDomain
open scoped BigOperators

/-- The geometric list contains no area-equality or stationarity predicate.
Null lines are arbitrary. Positive-budget bodies are triangles or genuine
quadrilaterals, with their complete geometric band catalogues. -/
def Families (K : Set (ℝ × ℝ)) (p : Fin 3 → Plank) : Prop :=
  (∀ i, (p i).lo=(p i).hi) ∨
  (∃ T : Triangle, T.set=K ∧ TriangleGeometricCatalogue.Families T p) ∨
  (CrossedQuadrilateralGenuine.Genuine (coordinateBody K) ∧
    CrossedQuadrilateralCatalogue.Families (coordinateBody K) (forms p) (ends p))

/-- Every compact convex positive-area body has precisely the listed
subcritical equality families. Directional widths are derived positive;
no polygonality, placement, generic-position or positive-plank-width premise
is assumed. -/
theorem equality_iff_families {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hV : 0 < (volume K).toReal) (p : Fin 3 → Plank)
    (hR : actualBudget K p < 1) : ActualEquality K p ↔ Families K p := by
  have hK' := ParallelProductPlane.compact_preimage hK
  have hc' := hc.linear_preimage ParallelProductPlane.coordinates.toLinearMap
  have hne := coordinate_nonempty (nonempty_of_area hV)
  have hV' : 0 < (volume (coordinateBody K)).toReal := by
    simpa only [coordinateBody,ParallelProductPlane.volume_preimage] using hV
  have hW (i) : 0 < rangeWidth (coordinateBody K) (forms p i) := by
    rw [width_bridge]
    exact width_pos_of_area hK hV (p i)
  have ho (i) : (ends p).1 i ≤ (ends p).2 i := (p i).lo_le_hi
  have hR' : budget (coordinateBody K) (forms p) (ends p) < 1 := by rwa [budget_bridge]
  constructor
  · intro he
    have he' := (equality_bridge K p).mpr he
    by_cases hz : actualBudget K p=0
    · left
      exact (Plank.PlanarEqualityReductions.budget_eq_zero_iff (forms p) (ends p) hW ho).mp
        (by rwa [budget_bridge])
    have hR0 : 0 < budget (coordinateBody K) (forms p) (ends p) := by
      rw [budget_bridge]
      exact lt_of_le_of_ne (budget_nonneg hK hV p) (Ne.symm hz)
    obtain ⟨a,b,c,d,hfour⟩ := Plank.PlanarThreePlankFourVertices.four_vertices
      hK' hc' hne hV' (forms p) (ends p) hW ho hR0 hR' he'
    rcases CrossedQuadrilateralSupportTriangle.triangle_or_genuine a b c d hfour with ht | hg
    · obtain ⟨a,b,c,ht⟩ := ht
      obtain ⟨T,hT⟩ := triangle_of_three_vertices hV a b c ht
      right;left
      refine ⟨T,hT,?_⟩
      have hRT : (∑ i, (p i).relWidth T) < 1 := by rwa [← triangle_budget,hT]
      have h := (TriangleGeometricCatalogue.all_budgets_iff T p).mp
        ((triangle_equality T p).mp (by simpa only [hT] using he))
      simpa only [if_pos hRT] using h
    · exact Or.inr (Or.inr ⟨hg,(CrossedQuadrilateralCatalogue.equality_iff_families
        hg hV' (forms p) (ends p) hW ho hR').mp he'⟩)
  · rintro (hz | ⟨T,hT,hf⟩ | ⟨hg,hf⟩)
    · apply (equality_bridge K p).mp
      exact Plank.PlanarEqualityReductions.equality_of_budget_zero hne (forms p) (ends p) hW ho
        ((Plank.PlanarEqualityReductions.budget_eq_zero_iff (forms p) (ends p) hW ho).mpr hz)
    · have hRT : (∑ i, (p i).relWidth T) < 1 := by rwa [← triangle_budget,hT]
      have h := (TriangleGeometricCatalogue.all_budgets_iff T p).mpr (by simpa [hRT] using hf)
      simpa only [hT] using (triangle_equality T p).mpr h
    · exact (equality_bridge K p).mp ((CrossedQuadrilateralCatalogue.equality_iff_families
        hg hV' (forms p) (ends p) hW ho hR').mpr hf)

theorem equality_iff_cover_of_one_le {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hV : 0 < (volume K).toReal) (p : Fin 3 → Plank)
    (hR : 1 ≤ actualBudget K p) : ActualEquality K p ↔ K ⊆ ⋃ i, (p i).set := by
  rw [← equality_bridge]
  have h := Plank.PlanarEqualityReductions.equality_iff_cover_of_one_le
    (ParallelProductPlane.compact_preimage hK)
    (hc.linear_preimage ParallelProductPlane.coordinates.toLinearMap)
    (by simpa only [coordinateBody,ParallelProductPlane.volume_preimage] using hV)
    (forms p) (ends p) (by
      change 1 ≤ budget (coordinateBody K) (forms p) (ends p)
      rwa [budget_bridge])
  exact h.trans (cover_bridge K p)

/-- Complete classification at every actual width budget on every compact
convex positive-area planar body, for three bands including arbitrary nulls. -/
theorem all_budgets_iff {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hV : 0 < (volume K).toReal) (p : Fin 3 → Plank) :
    ActualEquality K p ↔
      if actualBudget K p < 1 then Families K p else K ⊆ ⋃ i, (p i).set := by
  by_cases hR : actualBudget K p < 1
  · rw [if_pos hR]
    exact equality_iff_families hK hc hV p hR
  · rw [if_neg hR]
    exact equality_iff_cover_of_one_le hK hc hV p (le_of_not_gt hR)

/-- Degenerate bodies have zero uncovered area. This includes that trivial
branch in the exhaustive statement without imposing nonempty interior. -/
theorem all_compact_convex_iff {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (p : Fin 3 → Plank) :
    ActualEquality K p ↔
      if (volume K).toReal=0 then True else
      if actualBudget K p < 1 then Families K p else K ⊆ ⋃ i, (p i).set := by
  by_cases hz : (volume K).toReal=0
  · simp only [if_pos hz,iff_true]
    exact zero_area_equality hK hz p
  · rw [if_neg hz]
    exact all_budgets_iff hK hc (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)) p

/-- The quantitative lower bound whose complete equality list is above. -/
theorem quantitative_bound {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (p : Fin 3 → Plank) :
    (max 0 (1-actualBudget K p))^2*(volume K).toReal ≤
      (volume (K \ ⋃ i, (p i).set)).toReal := by
  by_cases hz : (volume K).toReal=0
  · rw [hz,mul_zero]
    exact ENNReal.toReal_nonneg
  · exact CrossedQuadrilateralCommonSupport.product_lower_bound hK hc
      (nonempty_of_area (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz))) p
      (fun i => width_pos_of_area hK (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)) (p i))

end Quant.PlanarGeometricCatalogue

/-- info: 'Quant.PlanarGeometricCatalogue.all_compact_convex_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.PlanarGeometricCatalogue.all_compact_convex_iff
