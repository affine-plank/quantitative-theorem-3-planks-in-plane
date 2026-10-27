/- Six supporting rows and attained coordinate extrema give width budgets.
A nonnegative slope gap turns those budgets into the relative-width bound. -/
module
public import Plank.Convex.PlanarSupportBudgets
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace Plank.Convex.PlanarSupportWidth
open PlanarSlopeGap (Triple)
open PlanarSupportMatrix

/-- Evaluate three alternating supporting rows at each coordinate extremum. -/
theorem opposite_bounds {E : Type*} (S : Set E) (X : Fin 3 → E → ℝ)
    (lo hi a b R : Triple) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hzero : ∀ i, ∃ x ∈ S, X i x = 0) (hrange : ∀ i, ∃ x ∈ S, X i x = R i)
    (hupper : ∀ i, ∀ x ∈ S, X i x + a i * X (i + 1) x ≤ hi i + a i * hi (i + 1))
    (hlower : ∀ i, ∀ x ∈ S, lo i + b i * lo (i + 1) ≤ X i x + b i * X (i + 1) x) :
    (∀ i, lo i * lower a b i ≤
      b i * ((hi (i + 1) - lo (i + 1)) + a (i + 1) * (hi (i + 2) - lo (i + 2)))) ∧
    (∀ i, (R i - hi i) * upper a b i ≤
      a i * ((hi (i + 1) - lo (i + 1)) + b (i + 1) * (hi (i + 2) - lo (i + 2)))) := by
  have hn (i : Fin 3) : (i + 1) + 1 = i + 2 := by fin_cases i <;> rfl
  have hp (i : Fin 3) : (i + 2) + 1 = i := by fin_cases i <;> rfl
  constructor
  · intro i
    obtain ⟨p, hpS, hpi⟩ := hzero i
    have hl := hlower i p hpS
    have hu := hupper (i + 1) p hpS
    have hl' := hlower (i + 2) p hpS
    rw [hpi, zero_add] at hl
    rw [hn] at hu
    rw [hp, hpi, mul_zero, add_zero] at hl'
    have H := mul_le_mul_of_nonneg_left hu (hb i)
    have L := mul_le_mul_of_nonneg_left hl' (mul_nonneg (hb i) (ha (i + 1)))
    dsimp [lower]
    nlinarith only [H, L, hl]
  · intro i
    obtain ⟨p, hpS, hpi⟩ := hrange i
    have hu := hupper i p hpS
    have hl := hlower (i + 1) p hpS
    have hu' := hupper (i + 2) p hpS
    rw [hpi] at hu
    rw [hn] at hl
    rw [hp, hpi] at hu'
    have L := mul_le_mul_of_nonneg_left hl (ha i)
    have H := mul_le_mul_of_nonneg_left hu' (mul_nonneg (ha i) (hb (i + 1)))
    dsimp [upper, lower]
    nlinarith only [H, L, hu]

/-- The support budgets work for arbitrary positive coordinate ranges. -/
theorem support_width_bound {E : Type*} (S : Set E) (X : Fin 3 → E → ℝ)
    (lo hi a b R : Triple) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (horder : ∀ i, lo i ≤ hi i) (hR : ∀ i, 0 < R i)
    (hzero : ∀ i, ∃ x ∈ S, X i x = 0) (hrange : ∀ i, ∃ x ∈ S, X i x = R i)
    (hupper : ∀ i, ∀ x ∈ S, X i x + a i * X (i + 1) x ≤ hi i + a i * hi (i + 1))
    (hlower : ∀ i, ∀ x ∈ S, lo i + b i * lo (i + 1) ≤ X i x + b i * X (i + 1) x)
    (hgap : 0 ≤ PlanarSlopeGap.gap a b) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  obtain ⟨hL, hU⟩ := opposite_bounds S X lo hi a b R ha hb hzero hrange hupper hlower
  apply PlanarSupportMatrix.scalar_width_bound a b (fun i => hi i - lo i) R ha hb
    (fun i => sub_nonneg.mpr (horder i)) hR ?_ hgap
  intro i
  have hLi : 0 ≤ lower a b i := add_nonneg zero_le_one
    (mul_nonneg (mul_nonneg (hb i) (ha (i + 1))) (hb (i + 2)))
  have hUi : 0 ≤ upper a b i := add_nonneg zero_le_one
    (mul_nonneg (mul_nonneg (ha i) (hb (i + 1))) (ha (i + 2)))
  have L := mul_le_mul_of_nonneg_right (hL i) hUi
  have U := mul_le_mul_of_nonneg_right (hU i) hLi
  dsimp only [budget, denom]
  nlinarith only [L, U]

end Plank.Convex.PlanarSupportWidth
