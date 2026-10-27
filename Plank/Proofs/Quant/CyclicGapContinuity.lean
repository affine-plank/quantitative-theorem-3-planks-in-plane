module
/- Continuity of the actual cyclic gap with directions fixed. -/
public import Plank.Measure.FiniteBandContinuity
public import Plank.Proofs.Quant.CyclicExteriorAssembly

@[expose] public section
noncomputable section

namespace Quant.CyclicGapContinuity

open Set MeasureTheory CyclicWeightedThresholdGeometry

theorem continuous_uncovered_volume (a b c : ℝ) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      volume (CyclicExteriorAssembly.uncovered a b c p.1 p.2)) := by
  have hfin : volume stdTriangle.set ≠ ⊤ := by
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  exact Plank.FiniteBandContinuity.continuous_measure_uncovered volume
    Proofs.Quant.measurableSet_stdTriangle hfin
    (fun i => (continuous_value a b c i).measurable)
    (fun i r => CyclicExteriorAssembly.volume_value_level a b c r i)

/-- The actual gap area is continuous for every real direction triple and every
pair of endpoint vectors, including collapsed and reversed bands. -/
theorem continuous_uncovered_area (a b c : ℝ) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (volume (stdTriangle.set \ ⋃ i,
        Plank.LinearBands.closedBand (value a b c i) (p.1 i) (p.2 i))).toReal) := by
  have hfin : volume stdTriangle.set ≠ ⊤ := by
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  exact Plank.FiniteBandContinuity.continuous_area_uncovered volume
    Proofs.Quant.measurableSet_stdTriangle hfin
    (fun i => (continuous_value a b c i).measurable)
    (fun i r => CyclicExteriorAssembly.volume_value_level a b c r i)

end Quant.CyclicGapContinuity
