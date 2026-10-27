/- The actual endpoint domain and its inductively paid boundary. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalNormalizedDomain
public import Plank.Proofs.Quant.FiniteDimensionalMinimumCellRank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalParameterDomain

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalMinimumCellRank FiniteDimensionalInductionBoundary
open scoped Topology

variable {d : ℕ}

/-- Actual normalized endpoints supply all compact-domain and boundary inputs
for minimum selection in every positive dimension. Only the preceding full
quantitative plank-count case is assumed; the zero-gap alternative is retained. -/
theorem exists_minimum_zero_or_many {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p₀ : Endpoints (Fin (m+1))} (hp₀ : p₀ ∈ domain K f)
    (hbad : rootCost K f p₀ < 1) :
    ∃ p ∈ interior (domain K f), rootCost K f p < 1 ∧
      (∀ e ∈ domain K f, rootCost K f p ≤ rootCost K f e) ∧
      (gapVolume K f p = 0 ∨ ∃ B, 0 < B ∧ B < 1 ∧ budget K f p < B ∧
        margin K f B p = 0 ∧ 2*(m+1)+1 ≤ (nonemptyCells K f p).card) := by
  exact exists_minimum_zero_or_many_of_boundary hK hc hne hV f hW
    (domain K f) (isCompact_domain K f) (fun _ hp => budget_nonneg f hW hp)
    (fun p hp => strict_windows_of_interior K f hp)
    (fun p hp hn => rootCost_on_boundary hm hK hc hne hV f hW hnorm ⟨subset_closure hp,hn⟩)
    hp₀ hbad

end Plank.FiniteDimensionalParameterDomain

#print axioms Plank.FiniteDimensionalParameterDomain.bound_on_boundary
#print axioms Plank.FiniteDimensionalParameterDomain.exists_minimum_zero_or_many
