/- Exclude a vertical pair and a third band supported by the opposite X vertices. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralPairBudget

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralOppositeXExclusion
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralDiagonalSplit
open CrossedQuadrilateralCommonSupport CrossedQuadrilateralObliquePhysical
open CrossedQuadrilateralPlacement CrossedQuadrilateralPairBudget CommonMiddleAffineTransport
open scoped BigOperators

theorem common (S : Shape) {k : ℝ} (hk₁ : S.b/S.a ≤ k) (hk₂ : S.d/S.c ≤ k)
    (a b c d lo hi : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (ho : lo ≤ hi) :
    ∀ i, CommonSupports S (family k a b c d lo hi hab hcd ho i) := by
  have hka := (div_le_iff₀ S.ha).mp hk₁
  have hkc := (div_le_iff₀ S.hc).mp hk₂
  have hk : 0 < k := (div_pos S.hb S.ha).trans_le hk₁
  have hpa := mul_pos hk S.ha
  have hpc := mul_pos hk S.hc
  intro i j
  fin_cases i <;> cases j <;>
    dsimp [CommonExtremes,CrossedQuadrilateralObliquePhysical.family,axisPlank,
      obliquePlank,half,Shape.Y,vector,dot]
  all_goals constructor <;> nlinarith only [hka,hkc,hpa,hpc,S.ha,S.hb,S.hc,S.hd]

theorem not_equality (S : Shape) {k a b c d lo hi : ℝ}
    (hk₁ : S.b/S.a ≤ k) (hk₂ : S.d/S.c ≤ k)
    (hab : a < b) (hcd : c < d) (ho : lo < hi)
    (hR : budget S k a b c d lo hi < 1) :
    gap S k a b c d lo hi ≠ (1-budget S k a b c d lo hi)^2*(volume S.body).toReal := by
  intro he
  let p := family k a b c d lo hi hab.le hcd.le ho.le
  have hp : ∀ i, (p i).lo < (p i).hi := by
    intro i; fin_cases i; exact hab; exact hcd; exact ho
  have hw (i) : 0 < relativeWidth S (p i) :=
    div_pos (sub_pos.mpr (hp i)) (direction_width_pos S (p i).u_ne_zero)
  have hd := parallel_of_equality S p (common S hk₁ hk₂ a b c d lo hi hab.le hcd.le ho.le)
    hw (by rw [actual_budget]; exact hR)
    (by rw [actual_budget,CrossedQuadrilateralObliquePhysical.family_union]; exact he)
  have h := hd 2
  exact one_ne_zero (show (1 : ℝ) = 0 from h)

end Quant.CrossedQuadrilateralOppositeXExclusion

/-- info: 'Quant.CrossedQuadrilateralOppositeXExclusion.not_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralOppositeXExclusion.not_equality
