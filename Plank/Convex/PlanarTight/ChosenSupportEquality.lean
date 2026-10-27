/- Equality in the chosen-support width bound saturates the original contact
inequalities. No balanced-cycle or pair-corner hypothesis is needed. -/
module
public import Plank.Convex.PlanarSupportWidth
public import Plank.Convex.PlanarTight.BudgetEquality
public import Mathlib.Tactic.LinearCombination
@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace Plank.Convex.PlanarTight.ChosenSupportEquality
open PlanarSlopeGap (Triple)
open PlanarSupportMatrix

/-- Enlarging any range would strictly decrease the sum of positive relative
widths. Therefore every support budget is saturated at total width one. -/
theorem budgets_eq (a b w R : Triple)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hw : ∀ i, 0 < w i) (hR : ∀ i, 0 < R i)
    (hbudget : ∀ i, denom a b i * R i ≤ budget a b w i)
    (hgap : 0 ≤ PlanarSlopeGap.gap a b)
    (hsum : ∑ i, w i / R i = 1) :
    ∀ i, denom a b i * R i = budget a b w i := by
  have hL (i : Fin 3) : 0 < lower a b i :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (hb i) (ha (i + 1))) (hb (i + 2)))
  have hU (i : Fin 3) : 0 < upper a b i :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (ha i) (hb (i + 1))) (ha (i + 2)))
  have hD (i : Fin 3) : 0 < denom a b i := mul_pos (hL i) (hU i)
  let T : Triple := fun i => budget a b w i / denom a b i
  have hRT (i : Fin 3) : R i ≤ T i :=
    (le_div_iff₀ (hD i)).mpr (by simpa only [mul_comm] using hbudget i)
  have hT (i : Fin 3) : 0 < T i := (hR i).trans_le (hRT i)
  have hbound : 1 ≤ ∑ i, w i / T i :=
    scalar_width_bound a b w T ha hb (fun i => (hw i).le) hT
      (fun i => by dsimp [T]; rw [mul_div_cancel₀ _ (hD i).ne']) hgap
  have hle (i : Fin 3) : w i / T i ≤ w i / R i :=
    div_le_div_of_nonneg_left (hw i).le (hR i) (hRT i)
  intro i
  have he : T i = R i := by
    apply le_antisymm ?_ (hRT i)
    by_contra! hlt
    have hstrict : (∑ j, w j / T j) < ∑ j, w j / R j :=
      Finset.sum_lt_sum (fun j _ => hle j)
        ⟨i, Finset.mem_univ i, div_lt_div_of_pos_left (hw i) (hR i) hlt⟩
    rw [hsum] at hstrict
    exact (not_lt_of_ge hbound) hstrict
  have he' := (div_eq_iff (hD i).ne').mp he
  simpa only [mul_comm] using he'.symm

/-- Both opposite-coordinate inequalities are equalities at positive-width
equality. The ranges may differ and the points need not fill the body. -/
theorem opposite_eq {E : Type*} (S : Set E) (X : Fin 3 → E → ℝ)
    (lo hi a b R : Triple) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hw : ∀ i, lo i < hi i) (hR : ∀ i, 0 < R i)
    (hzero : ∀ i, ∃ x ∈ S, X i x = 0) (hrange : ∀ i, ∃ x ∈ S, X i x = R i)
    (hupper : ∀ i, ∀ x ∈ S, X i x + a i * X (i + 1) x ≤ hi i + a i * hi (i + 1))
    (hlower : ∀ i, ∀ x ∈ S, lo i + b i * lo (i + 1) ≤ X i x + b i * X (i + 1) x)
    (hgap : 0 ≤ PlanarSlopeGap.gap a b)
    (hsum : ∑ i, (hi i - lo i) / R i = 1) :
    ∀ i,
      lo i * lower a b i =
        b i * ((hi (i + 1) - lo (i + 1)) + a (i + 1) * (hi (i + 2) - lo (i + 2))) ∧
      (R i - hi i) * upper a b i =
        a i * ((hi (i + 1) - lo (i + 1)) + b (i + 1) * (hi (i + 2) - lo (i + 2))) := by
  have hL (i : Fin 3) : 0 < lower a b i :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (hb i).le (ha (i + 1)).le) (hb (i + 2)).le)
  have hU (i : Fin 3) : 0 < upper a b i :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (ha i).le (hb (i + 1)).le) (ha (i + 2)).le)
  obtain ⟨hlo, hhi⟩ := PlanarSupportWidth.opposite_bounds S X lo hi a b R
    (fun i => (ha i).le) (fun i => (hb i).le) hzero hrange hupper hlower
  have hbudget (i : Fin 3) : denom a b i * R i ≤ budget a b (fun j => hi j - lo j) i := by
    have L := mul_le_mul_of_nonneg_right (hlo i) (hU i).le
    have U := mul_le_mul_of_nonneg_right (hhi i) (hL i).le
    dsimp only [budget, denom]
    nlinarith only [L, U]
  have he := budgets_eq a b (fun i => hi i - lo i) R
    (fun i => (ha i).le) (fun i => (hb i).le) (fun i => sub_pos.mpr (hw i))
    hR hbudget hgap hsum
  intro i
  apply BudgetEquality.split_eq (upper a b i) (lower a b i) _ _ _ _
    (hU i) (hL i) (hlo i) (hhi i)
  have heq := he i
  dsimp only [budget, denom] at heq
  nlinarith only [heq]

/-- At a coordinate maximum, the two adjacent upper support rows are exact.
This is the geometric information needed to identify the triangle sides. -/
theorem upper_contacts {E : Type*} (S : Set E) (X : Fin 3 → E → ℝ)
    (lo hi a b R : Triple) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hupper : ∀ i, ∀ x ∈ S, X i x + a i * X (i + 1) x ≤ hi i + a i * hi (i + 1))
    (hlower : ∀ i, ∀ x ∈ S, lo i + b i * lo (i + 1) ≤ X i x + b i * X (i + 1) x)
    (heq : ∀ i, (R i - hi i) * upper a b i =
      a i * ((hi (i + 1) - lo (i + 1)) + b (i + 1) * (hi (i + 2) - lo (i + 2))))
    (i : Fin 3) (x : E) (hx : x ∈ S) (hxi : X i x = R i) :
    X i x + a i * X (i + 1) x = hi i + a i * hi (i + 1) ∧
    X (i + 2) x + a (i + 2) * X i x = hi (i + 2) + a (i + 2) * hi i := by
  have hn (j : Fin 3) : (j + 1) + 1 = j + 2 := by fin_cases j <;> rfl
  have hp (j : Fin 3) : (j + 2) + 1 = j := by fin_cases j <;> rfl
  have h₁ := hupper i x hx
  have h₂ := hlower (i + 1) x hx
  have h₃ := hupper (i + 2) x hx
  rw [hn] at h₂
  rw [hp] at h₃
  let s := hi i + a i * hi (i + 1) - (X i x + a i * X (i + 1) x)
  let t := X (i + 1) x + b (i + 1) * X (i + 2) x -
    (lo (i + 1) + b (i + 1) * lo (i + 2))
  let u := hi (i + 2) + a (i + 2) * hi i - (X (i + 2) x + a (i + 2) * X i x)
  have hs : 0 ≤ s := sub_nonneg.mpr h₁
  have ht : 0 ≤ t := sub_nonneg.mpr h₂
  have hu : 0 ≤ u := sub_nonneg.mpr h₃
  have htotal : s + a i * t + (a i * b (i + 1)) * u = 0 := by
    have he := heq i
    dsimp only [upper, lower] at he
    dsimp [s, t, u]
    rw [hxi]
    linear_combination -he
  have hat := mul_nonneg (ha i).le ht
  have habu := mul_nonneg (mul_pos (ha i) (hb (i + 1))).le hu
  have hsz : s = 0 := by linarith only [htotal, hs, hat, habu]
  have huz : u = 0 := by nlinarith only [htotal, hs, hat, hu, mul_pos (ha i) (hb (i + 1))]
  exact ⟨(sub_eq_zero.mp hsz).symm, (sub_eq_zero.mp huz).symm⟩

end Plank.Convex.PlanarTight.ChosenSupportEquality
