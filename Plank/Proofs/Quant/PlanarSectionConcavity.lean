/- Concavity and supporting-slope bounds for actual polygon sections. -/
module

public import Plank.Proofs.Quant.PlanarSevenCellArea
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSectionConcavity

open Set PlanarSectionDerivatives

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

theorem lowerEnvelope_combo_le (ls lc : ι → ℝ) (x y a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    lowerEnvelope ls lc (a*x+b*y) ≤ a*lowerEnvelope ls lc x+b*lowerEnvelope ls lc y := by
  apply (lowerEnvelope_le_iff _ _ _ _).mpr
  intro i
  have hx := (lowerEnvelope_le_iff ls lc x _).mp le_rfl i
  have hy := (lowerEnvelope_le_iff ls lc y _).mp le_rfl i
  calc
    ls i*(a*x+b*y)+lc i = a*(ls i*x+lc i)+b*(ls i*y+lc i) := by
      linear_combination -(lc i)*hab
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

theorem combo_le_upperEnvelope (us uc : κ → ℝ) (x y a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a*upperEnvelope us uc x+b*upperEnvelope us uc y ≤ upperEnvelope us uc (a*x+b*y) := by
  apply (le_upperEnvelope_iff _ _ _ _).mpr
  intro i
  have hx := (le_upperEnvelope_iff us uc x _).mp le_rfl i
  have hy := (le_upperEnvelope_iff us uc y _).mp le_rfl i
  calc
    _ ≤ a*(us i*x+uc i)+b*(us i*y+uc i) :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = us i*(a*x+b*y)+uc i := by linear_combination (uc i)*hab

/-- On a convex interval of nonempty sections, the actual section length
is concave. No active-edge selection or vertex case analysis is needed. -/
theorem concaveOn_sectionLength (ls lc : ι → ℝ) (us uc : κ → ℝ)
    {S : Set ℝ} (hS : Convex ℝ S)
    (horder : ∀ x ∈ S, lowerEnvelope ls lc x ≤ upperEnvelope us uc x) :
    ConcaveOn ℝ S (sectionLength ls lc us uc) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := horder _ (hS hx hy ha hb hab)
  simp only [smul_eq_mul] at hc ⊢
  simp only [sectionLength, max_eq_right (sub_nonneg.mpr (horder x hx)),
    max_eq_right (sub_nonneg.mpr (horder y hy)), max_eq_right (sub_nonneg.mpr hc)]
  have hl := lowerEnvelope_combo_le ls lc x y a b ha hb hab
  have hu := combo_le_upperEnvelope us uc x y a b ha hb hab
  nlinarith only [hl, hu]

omit [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] in
/-- A tangent slope of a nonnegative concave density is bounded by the
available density and the distances to the support endpoints. -/
theorem supporting_slope_bounds {D : ℝ → ℝ} (hD : ConcaveOn ℝ (Icc 0 1) D)
    (hzero : 0 ≤ D 0) (hone : 0 ≤ D 1) {x p : ℝ} (hx : x ∈ Ioo 0 1)
    (hd : HasDerivAt D p x) : p*x ≤ D x ∧ (-p)*(1-x) ≤ D x := by
  have hl := hD.le_slope_of_hasDerivAt (show 0 ∈ Icc (0 : ℝ) 1 by norm_num)
    ⟨hx.1.le, hx.2.le⟩ hx.1 hd
  have hu := hD.slope_le_of_hasDerivAt ⟨hx.1.le, hx.2.le⟩
    (show 1 ∈ Icc (0 : ℝ) 1 by norm_num) hx.2 hd
  simp only [slope_def_field, sub_zero] at hl hu
  have hl' := (le_div_iff₀ hx.1).mp hl
  have hu' := (div_le_iff₀ (sub_pos.mpr hx.2)).mp hu
  constructor <;> nlinarith only [hl', hu', hzero, hone]

end Plank.PlanarSectionConcavity
