/- The seven-cell bound from elementary geometry and finite expansion. -/
module

public import Plank.Proofs.Quant.PlanarNonemptyCellCore
public import Plank.Proofs.Quant.PlanarPairAnchorBound
public import Plank.Proofs.Quant.FiniteDimensionalManyCellBound

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenNonemptyBound

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Seven nonempty closed exterior cells give the sharp quantitative bound
at this configuration. Strict windows and a subunit budget are explicit;
no minimum, shifted barrier or positive-volume assumption is needed. -/
theorem bound_of_seven_cells {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1) (p : Endpoints 3)
    (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1)
    (hcount : 7 ≤ (PlanarSevenNonemptyCells.nonemptyCells K f p).card) :
    (1-budget K f p)^2*(volume K).toReal ≤ gapArea K f p := by
  have hf (i) : (f i).linear ≠ 0 :=
    Body.linear_ne_zero_of_width_pos hne (f i)
      (show 0 < rangeWidth K (f i) by rw [hunit]; norm_num)
  have hnull := PlanarSevenNonemptyCells.triple_null_of_seven K f hf p hcount
  have hR0 : 0 < budget K f p := by
    simp only [budget,hunit,div_one]
    exact Finset.sum_pos (fun i _ => sub_pos.mpr (ho i)) Finset.univ_nonempty
  apply PlanarPairAnchorBound.bound_of_pair_corners hK hconv hne f hnorm hunit p hp hR0 hR
    (PlanarSevenNonemptyCells.corners_of_seven K f p hcount)
  intro i j k hij hik hjk
  apply measure_mono_null _ hnull
  intro x hx l
  have hl : l=i ∨ l=j ∨ l=k := by omega
  rcases hl with rfl | rfl | rfl
  · exact hx.1.1
  · exact hx.1.2
  · exact hx.2

/-- This elementary geometry supplies the all-dimensional minimum API at
its planar specialization, without importing an earlier planar completion. -/
theorem manyCellBound {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1) :
    FiniteDimensionalMinimumCompletion.ManyCellBound K f := by
  intro p hp hR hcount
  exact bound_of_seven_cells hK hconv hne f hnorm hunit p (interior_subset hp).1
    (FiniteDimensionalParameterDomain.strict_windows_of_interior K f hp) hR hcount

end Plank.PlanarSevenNonemptyBound
