/- Canonical finite windows and their actual uncovered volume. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalAffineGeometry

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalWindowFamily

open Set MeasureTheory FiniteDimensionalCapWindowScaling
variable {d : ℕ} {ι : Type*}

/-- The scalar centres need not come from a common point of the body. -/
def windows (f : ι → Point d →ᵃ[ℝ] ℝ) (c r : ι → ℝ) (i : ι) : Set (Point d) :=
  {x | (1-r i)*c i ≤ f i x ∧ f i x ≤ c i+(1-c i)*r i}

def gap (K : Set (Point d)) (f : ι → Point d →ᵃ[ℝ] ℝ) (c r : ι → ℝ) : ℝ :=
  (volume (K \ ⋃ i, windows f c r i)).toReal

theorem measurable_window (f : ι → Point d →ᵃ[ℝ] ℝ) (c r : ι → ℝ) (i : ι) :
    MeasurableSet (windows f c r i) :=
  ((isClosed_le continuous_const (continuous_form (f i))).inter
    (isClosed_le (continuous_form (f i)) continuous_const)).measurableSet

end Plank.FiniteDimensionalWindowFamily
