/- Merge a vertical pair in the opposite-Y-support sector, with actual area. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSectionGeometry
public import Plank.Proofs.Quant.UnimodalPlanarMerge

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralObliqueMerge
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralSectionProfile
open CrossedQuadrilateralSectionGeometry UnimodalPlanarMerge
open Plank.PlanarConvexSectionLength

/-- An arbitrary oblique band with opposite Y supports leaves a unimodal
section density. Thus two separated vertical bands merge at exactly the same
total width and with no increase in actual uncovered area. -/
theorem exists_interval (S : Shape) {k lo hi : ℝ} (hk : YSupports S k) (ho : lo < hi)
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ∃ l u : ℝ, a ≤ l ∧ u ≤ d ∧ l ≤ u ∧ u-l = (b-a)+(d-c) ∧
      (volume (S.body \ (band l u ∪ oblique k lo hi))).toReal ≤
        (volume (S.body \ ((band a b ∪ band c d) ∪ oblique k lo hi))).toReal := by
  have he : length (closedResidual S k lo hi) = residual S k lo hi :=
    funext (length_closedResidual S k ho)
  have hf : Continuous (length (closedResidual S k lo hi)) := by
    rw [he]
    exact continuous_residual S k lo hi
  have hin : MonotoneOn (length (closedResidual S k lo hi)) (Iic 0) := by
    rw [he]
    exact residual_monotone S hk lo hi
  have hout : AntitoneOn (length (closedResidual S k lo hi)) (Ici 0) := by
    rw [he]
    exact residual_antitone S hk lo hi
  obtain ⟨l,u,hal,hud,hlu,hw,hm⟩ := UnimodalPlanarMerge.exists_interval
    (compact_closedResidual S k lo hi) hf hin hout hab hbc hcd
  refine ⟨l,u,hal,hud,hlu,hw,?_⟩
  rw [gap_eq_closedResidual,gap_eq_closedResidual]
  exact hm

/-- The same actual-area merger allows arbitrary overlap and label order. -/
theorem arbitrary_pair (S : Shape) {k lo hi : ℝ} (hk : YSupports S k) (ho : lo < hi)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∃ l u : ℝ, l ≤ u ∧ u-l = (b-a)+(d-c) ∧
      (volume (S.body \ (band l u ∪ oblique k lo hi))).toReal ≤
        (volume (S.body \ ((band a b ∪ band c d) ∪ oblique k lo hi))).toReal := by
  have he : length (closedResidual S k lo hi) = residual S k lo hi :=
    funext (length_closedResidual S k ho)
  have hf : Continuous (length (closedResidual S k lo hi)) := by
    rw [he]; exact continuous_residual S k lo hi
  have hin : MonotoneOn (length (closedResidual S k lo hi)) (Iic 0) := by
    rw [he]; exact residual_monotone S hk lo hi
  have hout : AntitoneOn (length (closedResidual S k lo hi)) (Ici 0) := by
    rw [he]; exact residual_antitone S hk lo hi
  obtain ⟨l,u,hlu,hw,hm⟩ := UnimodalPlanarMerge.exists_interval_unordered
    (compact_closedResidual S k lo hi) hf hin hout hab hcd
  refine ⟨l,u,hlu,hw,?_⟩
  rw [gap_eq_closedResidual,gap_eq_closedResidual]
  exact hm

end Quant.CrossedQuadrilateralObliqueMerge

/-- info: 'Quant.CrossedQuadrilateralObliqueMerge.exists_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralObliqueMerge.exists_interval
