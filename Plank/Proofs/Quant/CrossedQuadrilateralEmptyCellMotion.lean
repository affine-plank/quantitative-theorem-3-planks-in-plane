/- An empty closed exterior cell leaves a constant-budget equality motion. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralBoundaryReduction
public import Plank.Proofs.Quant.PlanarCellOffsetLines
public import Plank.Proofs.Quant.PlanarLocalMinimumMotion

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralEmptyCellMotion
open Plank
open Set MeasureTheory Filter PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts PlanarPositiveCellRank
open Plank.Convex.DeficientHeightTilt
open PlanarShiftedDomain (deficit deficit_apply)
open scoped BigOperators Topology

/-- The two-plank equality case of the arbitrary-count local-minimum motion.
An empty closed cell leaves fewer constraints than endpoint variables. -/
theorem exists_motion {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p : Endpoints 2) (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (he : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hempty : ∃ s, ¬ (signCell K f p.1 p.2 s).Nonempty) :
    ∃ z : Endpoints 2, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      p+t • z ∈ interior (domain K f) ∧ budget K f (p+t • z) = budget K f p ∧
      gapArea K f (p+t • z) = (1-budget K f p)^2*(volume K).toReal := by
  classical
  let S := Plank.PlanarMinimumCellRank.nonemptyCells K f p
  have hS (s) : s ∈ S ↔ (signCell K f p.1 p.2 s).Nonempty := by
    simp [S,Plank.PlanarMinimumCellRank.nonemptyCells]
  have hcount : S.card < 4 := by
    obtain ⟨s,hs⟩ := hempty
    have hproper : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,fun hh => hs ((hS s).mp (hh ▸ Finset.mem_univ s))⟩
    have hlt := Finset.card_lt_card hproper
    norm_num only [Finset.card_univ,Fintype.card_finset,Fintype.card_fin] at hlt
    exact hlt
  exact Plank.PlanarLocalMinimumMotion.exists_motion_of_bound
    PlanarTwoPlank.sharpPlanarBound_two hK hc hne hV f hW p hp hR he hcount

end Quant.CrossedQuadrilateralEmptyCellMotion
