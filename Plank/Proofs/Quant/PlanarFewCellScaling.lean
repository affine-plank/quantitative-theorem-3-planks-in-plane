/- Common upper scaling for the six-cell three-plank equality case. -/
module

public import Plank.Proofs.Quant.PlanarMinimumCellScaling
public import Plank.Proofs.Quant.PlanarThreePlank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFewCellScaling

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarShiftedDomain (deficit)
open Plank.Convex.DeficientHeightTilt
open scoped Topology

/-- At most six potentially nonempty cells give a nonzero common scaling
line near every interior equality. Actual cell-area upper bounds hold on
its entire intersection with the indicated open region. No direction,
body-shape, positive-cell or differentiability assumption is imposed. -/
theorem exists_common_upper_scaling {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (C : Finset (Finset (Fin 3))) (hC : C.card ≤ 6)
    (p : Endpoints 3) (hp : p ∈ interior (domain K f))
    (horder : p ∈ region K f C) (hR : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ z : Endpoints 3, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      (deficit K f 1).linear z = (1-budget K f p)*c ∧
      ∀ s t, p+t • z ∈ region K f C → (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
        (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 := by
  apply exists_common_upper_scaling_at_minimum hK hconv hne hV f hW C hC 1 p hp horder hR heq
  have hz : PlanarShiftedDomain.margin K f 1 p = 0 := by
    dsimp only [PlanarShiftedDomain.margin]
    nlinarith only [heq]
  apply Filter.Eventually.mono (isOpen_interior.mem_nhds hp)
  intro e he
  rw [hz]
  apply sub_nonneg.mpr
  have hh := PlanarThreePlank.sharpPlanarBound_three K hK hconv hne f e.1 e.2
    (fun i => ((interior_subset he).1 i).2.1) hW
  change (max 0 (1-budget K f e))^2*(volume K).toReal ≤ gapArea K f e at hh
  rw [max_eq_right (sub_nonneg.mpr (interior_subset he).2)] at hh
  simpa only [mul_comm] using hh

end Plank.PlanarFewCellScaling

/-- info: 'Plank.PlanarFewCellScaling.exists_common_upper_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFewCellScaling.exists_common_upper_scaling
