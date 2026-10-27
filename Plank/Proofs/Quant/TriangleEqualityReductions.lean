/- Actual-area equality on a triangle: null-plank reduction, the explicit
one-plank tent classification, and two attained positive-deficit families.
No exhaustiveness claim is made for two or three positive-width planks. -/
module

public import Plank.Proofs.Quant.Calibration
public import Plank.Proofs.Quant.CalwCone

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.TriangleEqualityReductions

/-- Equality in the triangle's positive-part area bound. -/
def Equality (C : Config) : Prop :=
  C.gapArea = (max 0 C.deficit)^2 * (1/2)

/-- Null planks have no effect on equality, irrespective of their locations
and directions. This reduces the whole one-positive-plank stratum to the
surviving plank's calibration. -/
theorem equality_iff_calibrated_of_two_null (C : Config)
    (h1 : (C.plank 1).lo = (C.plank 1).hi)
    (h2 : (C.plank 2).lo = (C.plank 2).hi) (hs : C.sumRelW ≤ 1) :
    Equality C ↔ Calibrated (C.plank 0) := by
  have hw1 : C.relW 1 = 0 := relWidth_of_degenerate h1
  have hw2 : C.relW 2 = 0 := relWidth_of_degenerate h2
  have hsum : C.sumRelW = C.relW 0 := by
    simp only [Config.sumRelW, Fin.sum_univ_three, hw1, hw2, add_zero]
  have hd : 0 ≤ C.deficit := by unfold Config.deficit; linarith
  rw [Equality, max_eq_right hd, gapArea_of_degenerate C h2,
    pairGap_of_degenerate _ h1, Config.deficit, hsum, relW_eq]
  exact (calibrated_iff_gap (C.plank 0)).symm

/-- An explicit if-and-only-if for the normalized non-edge single-plank
stratum. The other two planks may be arbitrary zero-width lines; no clipping
hypothesis is needed. Vertex shadows of the surviving normal are 0, a, 1. -/
theorem equality_iff_tent_position (C : Config) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hu : (C.plank 0).u = (a,1))
    (hp : (C.plank 0).lo < (C.plank 0).hi)
    (h1 : (C.plank 1).lo = (C.plank 1).hi)
    (h2 : (C.plank 2).lo = (C.plank 2).hi) (hs : C.sumRelW ≤ 1) :
    Equality C ↔ (C.plank 0).lo = a * (1-((C.plank 0).hi-(C.plank 0).lo)) := by
  have hw1 : C.relW 1 = 0 := relWidth_of_degenerate h1
  have hw2 : C.relW 2 = 0 := relWidth_of_degenerate h2
  have hwidth : C.relW 0 = (C.plank 0).hi-(C.plank 0).lo := by
    rw [Config.relW, Plank.relWidth, hu, width_tent ha.le ha1.le, div_one]
  have hw : (C.plank 0).hi-(C.plank 0).lo ≤ 1 := by
    simpa only [Config.sumRelW, Fin.sum_univ_three, hw1, hw2, add_zero, hwidth] using hs
  rw [equality_iff_calibrated_of_two_null C h1 h2 hs]
  exact ⟨fun h => (calibrated_position_tent ha ha1 (C.plank 0) hu hp hw h).2.2,
    calibrated_of_position_tent ha ha1 (C.plank 0) hu hw⟩

/-- Barycentric edge bands attain equality for every nonnegative width
triple of total width at most one. -/
theorem equality_calw {r₁ r₂ r₃ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (h₃ : 0 ≤ r₃)
    (hs : r₁+r₂+r₃ ≤ 1) : Equality (calwConfig r₁ r₂ r₃ h₁ h₂ h₃) := by
  have hd : (calwConfig r₁ r₂ r₃ h₁ h₂ h₃).deficit = 1-(r₁+r₂+r₃) := by
    simp [Config.deficit, Config.sumRelW, Fin.sum_univ_three, calwConfig_relW]
  rw [Equality, hd, max_eq_right (sub_nonneg.mpr hs), calwConfig_gapArea h₁ h₂ h₃ hs]
  ring

/-- The ordered common-middle stack attains the same bound. Its gap can
have several triangular components, so equality does not force one gap cell. -/
theorem equality_stack {c₀ c₁ c₂ w₀ w₁ w₂ : ℝ}
    (hc0 : 0 ≤ c₀) (hc1 : 0 ≤ c₁) (hc2 : 0 ≤ c₂)
    (hw0 : 0 ≤ w₀) (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂)
    (hc01 : c₀ ≤ c₁) (hc12 : c₁ ≤ c₂) (hs : w₀+w₁+w₂ ≤ 1) :
    Equality (Proofs.Quant.stackConfig c₀ c₁ c₂ w₀ w₁ w₂ hc0 hc1 hc2 hw0 hw1 hw2) := by
  have hd : (Proofs.Quant.stackConfig c₀ c₁ c₂ w₀ w₁ w₂ hc0 hc1 hc2 hw0 hw1 hw2).deficit =
      1-(w₀+w₁+w₂) := by
    simp [Config.deficit, Config.sumRelW, Fin.sum_univ_three, Proofs.Quant.stackConfig_relW]
  rw [Equality, hd, max_eq_right (sub_nonneg.mpr hs),
    Proofs.Quant.stackConfig_gapArea hc01 hc12 hs]
  ring

end Quant.TriangleEqualityReductions

/-- info: 'Quant.TriangleEqualityReductions.equality_iff_calibrated_of_two_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleEqualityReductions.equality_iff_calibrated_of_two_null
/-- info: 'Quant.TriangleEqualityReductions.equality_iff_tent_position' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleEqualityReductions.equality_iff_tent_position
/-- info: 'Quant.TriangleEqualityReductions.equality_calw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleEqualityReductions.equality_calw
/-- info: 'Quant.TriangleEqualityReductions.equality_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleEqualityReductions.equality_stack
