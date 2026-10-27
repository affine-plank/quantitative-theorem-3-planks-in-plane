/- Positive central coefficients make the opposite-cap width bound strict. -/
module
public import Plank.Convex.OppositeCapsWidth
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.OppositeCaps

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- Retaining the central coefficient gives a quantitative width gap for
opposite-cap constraints. Only four attained contacts are needed. -/
theorem coefficient_slack_bound (K : Set E) (hK : Convex ℝ K)
    (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (b : ℝ) (a : ι → ℝ) (d : ℝ) (hb : 0 ≤ b) (ha : ∀ j, 0 ≤ a j)
    (hplane : ∀ x ∈ K, b * Y x + ∑ j, a j * X j x = d)
    (i : ι) (hai : 0 < a i) (hmax : ∀ j, a j ≤ a i)
    (l h : ι → ℝ) (lm hm : ℝ) (horder : ∀ j, l j ≤ h j) (hmorder : lm ≤ hm)
    (hlm : 0 < lm) (hhm : hm < 1)
    (hLm : ∃ x ∈ K, Y x = 0) (hUm : ∃ x ∈ K, Y x = 1)
    (hLi : ∃ x ∈ K, X i x = 0 ∧ 0 ≤ Y x ∧ Y x ≤ 1)
    (hUi : ∃ x ∈ K, X i x = 1 ∧ 0 ≤ Y x ∧ Y x ≤ 1)
    (hupper : ∀ x ∈ K, hm < Y x → ∀ j, l j ≤ X j x)
    (hlower : ∀ x ∈ K, Y x < lm → ∀ j, X j x ≤ h j) :
    b * (hm - lm) ≤ a i * ((hm - lm + ∑ j, (h j - l j)) - 1) := by
  obtain ⟨Q, hQ, hQi, hQy⟩ := hLi
  obtain ⟨R, hR, hRi, hRy⟩ := hUi
  have hu := OppositeCapsWidth.upper_gate_affine K hK Y X b a d hb ha hplane i hai l hm
    (hlm.le.trans hmorder) hhm hUm ⟨Q, hQ, hQi, hQy.1⟩ ⟨R, hR, hRi, hRy.1⟩ hupper
  have hl := OppositeCapsWidth.lower_gate_affine K hK Y X b a d hb ha hplane i hai h lm
    hlm (hmorder.trans hhm.le) hLm ⟨Q, hQ, hQi, hQy.2⟩ ⟨R, hR, hRi, hRy.2⟩ hlower
  have hsum : (∑ j, a j * (h j - l j)) ≤ a i * ∑ j, (h j - l j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hmax j) (sub_nonneg.mpr (horder j))
  have hsum_eq : (∑ j, a j * (h j - l j)) = (∑ j, a j * h j) - ∑ j, a j * l j := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  nlinarith only [hu, hl, hsum, hsum_eq]

/-- A positive central coefficient and positive central window exclude
equality in the opposite-cap pattern. This includes the four mixed caps
of the planar row-H family. -/
theorem strict_width_bound (K : Set E) (hK : Convex ℝ K)
    (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (b : ℝ) (a : ι → ℝ) (d : ℝ) (hb : 0 < b) (ha : ∀ j, 0 ≤ a j)
    (hplane : ∀ x ∈ K, b * Y x + ∑ j, a j * X j x = d)
    (i : ι) (hai : 0 < a i) (hmax : ∀ j, a j ≤ a i)
    (l h : ι → ℝ) (lm hm : ℝ) (horder : ∀ j, l j ≤ h j) (hmorder : lm < hm)
    (hlm : 0 < lm) (hhm : hm < 1)
    (hLm : ∃ x ∈ K, Y x = 0) (hUm : ∃ x ∈ K, Y x = 1)
    (hLi : ∃ x ∈ K, X i x = 0 ∧ 0 ≤ Y x ∧ Y x ≤ 1)
    (hUi : ∃ x ∈ K, X i x = 1 ∧ 0 ≤ Y x ∧ Y x ≤ 1)
    (hupper : ∀ x ∈ K, hm < Y x → ∀ j, l j ≤ X j x)
    (hlower : ∀ x ∈ K, Y x < lm → ∀ j, X j x ≤ h j) :
    1 < hm - lm + ∑ j, (h j - l j) := by
  have hs := coefficient_slack_bound K hK Y X b a d hb.le ha hplane i hai hmax
    l h lm hm horder hmorder.le hlm hhm hLm hUm hLi hUi hupper hlower
  have hp := mul_pos hb (sub_pos.mpr hmorder)
  nlinarith only [hs, hp, hai]

end Plank.Convex.PlanarTight.OppositeCaps

/-- info: 'Plank.Convex.PlanarTight.OppositeCaps.coefficient_slack_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.OppositeCaps.coefficient_slack_bound

/-- info: 'Plank.Convex.PlanarTight.OppositeCaps.strict_width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.OppositeCaps.strict_width_bound
