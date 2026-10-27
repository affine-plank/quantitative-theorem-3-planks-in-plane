/- Quantitative cover completion in every positive dimension. The preceding
quantitative case and a many-cell bound are hypotheses; covering comes last. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalNormalizedDomain
public import Plank.Measure.ConvexBody

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalMinimumCompletion

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalMinimumCellRank FiniteDimensionalInductionBoundary
  FiniteDimensionalParameterDomain

variable {d : ℕ}

/-- The geometric inequality is needed only at configurations with at least
`2*m+1` nonempty closed cells. It remains an explicit hypothesis. -/
def ManyCellBound {m : ℕ} (K : Set (Point d))
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) : Prop :=
  ∀ p ∈ interior (domain K f), budget K f p < 1 →
    2*m+1 ≤ (nonemptyCells K f p).card →
    (1-budget K f p)^(d+1)*(volume K).toReal ≤ gapVolume K f p

/-- For a positive-volume convex body, a zero gap is an actual closed cover. -/
theorem gap_eq_zero_iff_cover {m : ℕ} {K : Set (Point d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin m)) :
    gapVolume K f p = 0 ↔ K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
  exact ConvexBodyMeasure.measure_sdiff_eq_zero_iff_subset volume hK hc hV
    (isClosed_iUnion_of_finite fun i =>
      (isClosed_le continuous_const (continuous_form (f i))).inter
        (isClosed_le (continuous_form (f i)) continuous_const))

end Plank.FiniteDimensionalMinimumCompletion
