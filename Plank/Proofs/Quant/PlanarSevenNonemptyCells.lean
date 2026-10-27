/- Seven weak exterior cells suffice for the four-point equality family. -/
module

public import Plank.Proofs.Quant.PlanarNonemptyCellGeometry
public import Plank.Proofs.Quant.PlanarPairContainedOriginal

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenNonemptyCells

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarSevenCellGeometry PlanarPairContainment PlanarDirectionDerivatives
open PlanarAffineEquality PlanarFourPointClassification
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Seven nonempty cells force the same rigidity as seven positive cells.
Null cells and contact degeneracies are included. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (hcount : 7 ≤ (nonemptyCells K f p).card) (he : Equality K f p.1 p.2) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  apply PlanarPairContainedOriginal.four_vertices hK hc hne hV f p hW ho hpairs hR
    (fun i j hij => pair_subset_of_corners hK.isClosed hc (f i) (f j) (hpairs i j hij)
      _ _ _ _ (corners_of_seven K f p hcount i j hij))
    (triple_null_of_seven K f (fun i => linear_ne_zero_of_rangeWidth_pos hne (f i) (hW i))
      p hcount) he

theorem equality_iff {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (hcount : 7 ≤ (nonemptyCells K f p).card) :
    Equality K f p.1 p.2 ↔ Family K f p.1 p.2 := by
  constructor
  · intro he
    exact (equality_iff_of_four_vertices hV
      (four_vertices hK hc hne hV f p hW ho hpairs hR hcount he)
      f p.1 p.2 hW (fun i => (ho i).le)).mp he
  · exact family_sound f p.1 p.2 hW (fun i => (ho i).le)

theorem at_most_six_of_not_four {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (he : Equality K f p.1 p.2)
    (hnot : ¬∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) :
    (nonemptyCells K f p).card ≤ 6 := by
  by_contra hn
  exact hnot (four_vertices hK hc hne hV f p hW ho hpairs hR (by omega) he)

end Plank.PlanarSevenNonemptyCells

/-- info: 'Plank.PlanarSevenNonemptyCells.equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSevenNonemptyCells.equality_iff
