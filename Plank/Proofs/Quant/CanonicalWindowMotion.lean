/- Canonical width motion shared by the quantitative proof and its probes.
Existing declaration names are preserved while their common implementation
is part of the registered library. -/
module

public import Plank.Proofs.Quant.PlanarSevenCellSections

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SupportAnchorBudget
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev WindowSpace (ι : Type*) := (ι → ℝ) × (ι → ℝ)

def width (e : WindowSpace ι) (i : ι) : ℝ := e.2 i-e.1 i
def lowerWeight (e : WindowSpace ι) (i : ι) : ℝ := e.1 i/(e.1 i+(1-e.2 i))
def upperWeight (e : WindowSpace ι) (i : ι) : ℝ := (1-e.2 i)/(e.1 i+(1-e.2 i))

def velocity (e : WindowSpace ι) (i : ι) : WindowSpace ι :=
  (Pi.single i (-lowerWeight e i), Pi.single i (upperWeight e i))

theorem weighted_velocity_lower (e : WindowSpace ι) (j : ι) :
    (∑ i, width e i • velocity e i).1 j = -width e j*lowerWeight e j := by
  simp [velocity, Finset.sum_apply, Prod.fst_sum, Pi.single_apply, mul_ite]

theorem weighted_velocity_upper (e : WindowSpace ι) (j : ι) :
    (∑ i, width e i • velocity e i).2 j = width e j*upperWeight e j := by
  simp [velocity, Finset.sum_apply, Prod.snd_sum, Pi.single_apply, mul_ite]

end Plank.SupportAnchorBudget

namespace Plank.ActualSupportAnchor
open PlanarQuantitative PlanarPolygonCharts PlanarSeparableChart QuadraticChartCalculus SupportAnchorBudget
open PlanarParameterDomain (Endpoints)
open Plank.Convex.DeficientHeightTilt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem weights_add (e : WindowSpace ι)
    (hs : ∀ i, e.1 i+(1-e.2 i) ≠ 0) (i : ι) :
    lowerWeight e i+upperWeight e i = 1 := by
  unfold lowerWeight upperWeight
  rw [← add_div, div_self (hs i)]

omit [Fintype ι] in
theorem velocity_eq (e : WindowSpace ι) (i : ι) :
    velocity e i = (-lowerWeight e i) • lowerDirection i+
      upperWeight e i • upperDirection i := by
  apply Prod.ext <;> funext j <;> by_cases hj : j=i <;>
    simp [velocity, lowerDirection, upperDirection, hj]

theorem derivative_velocity (P : QuadraticFormula (WindowSpace ι))
    (e x : WindowSpace ι) (i : ι) :
    derivative P x (velocity e i) =
      -lowerWeight e i*derivative P x (lowerDirection i)+
        upperWeight e i*derivative P x (upperDirection i) := by
  rw [velocity_eq]
  simp

theorem deficit_linear {m : ℕ} {K : Set Point} {f : Fin m → Point →ᵃ[ℝ] ℝ}
    (B : ℝ) (hunit : ∀ i, rangeWidth K (f i) = 1) (z : Endpoints m) :
    (PlanarShiftedDomain.deficit K f B).linear z = -∑ i, (z.2 i-z.1 i) := by
  simp [PlanarShiftedDomain.deficit, PlanarShiftedDomain.budgetLinear, hunit]

theorem deficit_velocity {m : ℕ} {K : Set Point} {f : Fin m → Point →ᵃ[ℝ] ℝ}
    (B : ℝ) (hunit : ∀ i, rangeWidth K (f i) = 1)
    (e : Endpoints m) (hs : ∀ i, e.1 i+(1-e.2 i) ≠ 0) (i : Fin m) :
    (PlanarShiftedDomain.deficit K f B).linear (velocity e i) = -1 := by
  rw [deficit_linear B hunit]
  simp [velocity, Pi.single_apply,
    add_comm (upperWeight e i), weights_add e hs i]

end Plank.ActualSupportAnchor

namespace Plank.ConcurrentAnchorFinish
open SupportAnchorBudget
open PlanarParameterDomain (Endpoints)

theorem canonical_endpoints {m : ℕ} (e : Endpoints m)
    (hends : ∀ i, 0 < e.1 i ∧ e.2 i < 1) (i : Fin m) :
    (1-width e i)*lowerWeight e i = e.1 i ∧
      lowerWeight e i+(1-lowerWeight e i)*width e i = e.2 i := by
  have hs : e.1 i+(1-e.2 i) ≠ 0 := ne_of_gt
    (add_pos (hends i).1 (sub_pos.mpr (hends i).2))
  constructor <;> unfold width lowerWeight <;> field_simp [hs] <;> ring

end Plank.ConcurrentAnchorFinish
