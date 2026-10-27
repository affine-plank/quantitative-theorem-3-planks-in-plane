/- Planar window data and normalization without section calculus. -/
module

public import Plank.Proofs.Quant.PlanarStatement
public import Plank.Proofs.Quant.FiniteDimensionalAffineGeometry
public import Plank.Proofs.AffineWidthCore
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Plank.PlanarQuantitative

namespace Plank.PlanarParameterDomain

open Plank.Convex.DeficientHeightTilt

abbrev Endpoints (m : ℕ) := (Fin m → ℝ) × (Fin m → ℝ)

def budget {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints m) : ℝ := ∑ i, (p.2 i-p.1 i)/rangeWidth K (f i)

def gapArea {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints m) : ℝ :=
  (volume (K \ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i})).toReal

end Plank.PlanarParameterDomain

namespace Plank.PlanarSevenCellArea

open Plank.FiniteDimensionalCapWindowScaling (continuous_form)

def plank (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) : Set Point := {x | lo ≤ f x ∧ f x ≤ hi}

theorem isClosed_plank (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) : IsClosed (plank f lo hi) :=
  (isClosed_le continuous_const (continuous_form f)).inter
    (isClosed_le (continuous_form f) continuous_const)

end Plank.PlanarSevenCellArea

namespace Plank.PlanarBodySectionDensity

open Plank.PlanarSevenCellArea

def coveredArea (K : Set Point) (g : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) : ℝ :=
  (volume (K ∩ plank g lo hi)).toReal

/-- Unit actual width and normalized body values identify the entire
support interval, not just an enclosing interval. -/
theorem image_eq_unitInterval {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (g : Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1)
    (hunit : Plank.Convex.DeficientHeightTilt.rangeWidth K g = 1) :
    g '' K = Icc 0 1 := by
  obtain ⟨⟨b, hb, hgb⟩, ⟨a, ha, hga⟩⟩ :=
    FiniteDimensionalNormalization.unit_realisers hK hne g hnorm hunit
  apply Subset.antisymm
  · rintro t ⟨x, hx, rfl⟩
    exact hnorm x hx
  · exact (hconv.affine_image g).ordConnected.out ⟨b, hb, hgb⟩ ⟨a, ha, hga⟩

end Plank.PlanarBodySectionDensity
