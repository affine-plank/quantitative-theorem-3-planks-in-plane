/- Elementary strict comparison of a finite weighted sum. -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ResearchFormalized

/-- A nonzero weighted sum strictly increases when each coordinate with
nonzero weight moves strictly in the direction of that weight. -/
theorem sum_mul_lt_sum_mul_of_signs {ι : Type*} [Fintype ι]
    (a u v : ι → ℝ) (ha : ∃ i, a i ≠ 0)
    (hmove : ∀ i, (0 < a i → u i < v i) ∧ (a i < 0 → v i < u i)) :
    ∑ i, a i * u i < ∑ i, a i * v i := by
  have hstrict (i) (hi : a i ≠ 0) : a i * u i < a i * v i := by
    rcases lt_or_gt_of_ne hi with hn | hp
    · exact mul_lt_mul_of_neg_left ((hmove i).2 hn) hn
    · exact mul_lt_mul_of_pos_left ((hmove i).1 hp) hp
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hi : a i = 0
    · simp [hi]
    · exact (hstrict i hi).le
  · obtain ⟨i, hi⟩ := ha
    exact ⟨i, Finset.mem_univ i, hstrict i hi⟩

end ResearchFormalized
