module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.TriangleWindowCover
abbrev Point := Fin 3 → ℝ

def coordinate (q t : Point) (i : Fin 3) : ℝ := q i * t i + t (i+2)

theorem sum_cycle (t : Point) (i : Fin 3) : t i + t (i+1) + t (i+2) = ∑ j, t j := by
  rw [Fin.sum_univ_three]
  fin_cases i
  · rfl
  · change t 1 + t 2 + t 0 = _
    ring
  · change t 2 + t 0 + t 1 = _
    ring

theorem next_add_two (i : Fin 3) : (i+1)+2 = i := by fin_cases i <;> rfl

/-- The upper supporting line is the edge joining the first and third triangle vertices. -/
theorem upper_support (q t : Point) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (ht : ∀ i, 0 ≤ t i) (hsum : (∑ i, t i) = 1) (i : Fin 3) :
    coordinate q t i + (1-q i)*coordinate q t (i+1) ≤ 1 := by
  have hqq : (1-q i)*q (i+1) ≤ 1 := by
    nlinarith only [hq0 i, hq1 i, hq0 (i+1), hq1 (i+1), mul_nonneg (hq0 i) (hq0 (i+1))]
  have hmul := mul_le_mul_of_nonneg_right hqq (ht (i+1))
  have hs := (sum_cycle t i).trans hsum
  dsimp [coordinate]
  rw [next_add_two]
  nlinarith only [hmul, hs]

/-- The lower supporting line is the edge joining the second and third triangle vertices. -/
theorem lower_support (q t : Point) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (ht : ∀ i, 0 ≤ t i) (hsum : (∑ i, t i) = 1) (i : Fin 3) :
    q (i+1) ≤ q (i+1)*coordinate q t i + coordinate q t (i+1) := by
  have hc : 0 ≤ 1-q (i+1)+q (i+1)*q i :=
    add_nonneg (sub_nonneg.mpr (hq1 _)) (mul_nonneg (hq0 _) (hq0 _))
  have hmul := mul_nonneg hc (ht i)
  have hs := (sum_cycle t i).trans hsum
  have hscaled := congrArg (fun s : ℝ => q (i+1)*s) hs
  dsimp [coordinate]
  rw [next_add_two]
  nlinarith only [hmul, hscaled]

/-- Same-sign pair supports exclude every escape from three windows. -/
theorem cover_of_supports (x lo hi q : Point) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hupper : ∀ i, x i + (1-q i)*x (i+1) ≤ hi i + (1-q i)*hi (i+1))
    (hlower : ∀ i, q (i+1)*lo i + lo (i+1) ≤ q (i+1)*x i + x (i+1)) :
    ∃ i, lo i ≤ x i ∧ x i ≤ hi i := by
  have hlow (i : Fin 3) : ¬ (x i < lo i ∧ x (i+1) < lo (i+1)) := by
    rintro ⟨h1,h2⟩
    exact (not_lt_of_ge (hlower i)) (add_lt_add (mul_lt_mul_of_pos_left h1 (hq0 _)) h2)
  have hhigh (i : Fin 3) : ¬ (hi i < x i ∧ hi (i+1) < x (i+1)) := by
    rintro ⟨h1,h2⟩
    exact (not_lt_of_ge (hupper i)) (add_lt_add h1 (mul_lt_mul_of_pos_left h2 (sub_pos.mpr (hq1 _))))
  by_contra! hn
  have hout (i : Fin 3) : x i < lo i ∨ hi i < x i := (lt_or_ge (x i) (lo i)).imp_right (hn i)
  rcases hout 0 with h0 | h0
  · rcases hout 1 with h1 | h1
    · exact hlow 0 ⟨h0,h1⟩
    · rcases hout 2 with h2 | h2
      · exact hlow 2 ⟨h2,h0⟩
      · exact hhigh 1 ⟨h1,h2⟩
  · rcases hout 1 with h1 | h1
    · rcases hout 2 with h2 | h2
      · exact hlow 1 ⟨h1,h2⟩
      · exact hhigh 2 ⟨h2,h0⟩
    · exact hhigh 0 ⟨h0,h1⟩

/-- Prescribed positive widths of sum one give the strict triangle family directly. -/
theorem width_parameters_cover (w t : Point) (hw : ∀ i, 0 < w i) (hwsum : (∑ i, w i) = 1)
    (ht : ∀ i, 0 ≤ t i) (htsum : (∑ i, t i) = 1) :
    ∃ i, w (i+1) ≤ w (i+1)/(1-w i)*t i + t (i+2) ∧
      w (i+1)/(1-w i)*t i + t (i+2) ≤ 1-w (i+2) := by
  have hs (i : Fin 3) := (sum_cycle w i).trans hwsum
  have hw1 (i : Fin 3) : w i < 1 := by linarith only [hs i, hw (i+1), hw (i+2)]
  let q (i : Fin 3) := w (i+1)/(1-w i)
  have hq0 (i : Fin 3) : 0 < q i := div_pos (hw _) (sub_pos.mpr (hw1 _))
  have hq1 (i : Fin 3) : q i < 1 :=
    (div_lt_one (sub_pos.mpr (hw1 _))).mpr (by linarith only [hs i, hw (i+2)])
  have hqmul (i : Fin 3) : q i * (1-w i) = w (i+1) :=
    div_mul_cancel₀ _ (sub_pos.mpr (hw1 _)).ne'
  apply cover_of_supports (coordinate q t) (fun i => w (i+1)) (fun i => 1-w (i+2)) q hq0 hq1
  · intro i
    have hrow := upper_support q t (fun i => (hq0 i).le) (fun i => (hq1 i).le) ht htsum i
    have he : (1-w (i+2))+(1-q i)*(1-w ((i+1)+2)) = 1 := by
      rw [next_add_two]
      nlinarith only [hs i, hqmul i]
    rwa [he]
  · intro i
    have hrow := lower_support q t (fun i => (hq0 i).le) (fun i => (hq1 i).le) ht htsum i
    have he : q (i+1)*w (i+1) + w ((i+1)+1) = q (i+1) := by
      nlinarith only [hqmul (i+1)]
    rwa [he]

#print axioms width_parameters_cover

def crossSum (w : Point) : ℝ := ∑ i, w (i+1)*w (i+2)
def center (w : Point) (i : Fin 3) : ℝ := w (i+1)*w (i+2)/crossSum w

theorem prev_add_one (i : Fin 3) : (i+2)+1 = i := by fin_cases i <;> rfl
theorem prev_add_two (i : Fin 3) : (i+2)+2 = i+1 := by fin_cases i <;> rfl
theorem next_add_one (i : Fin 3) : (i+1)+1 = i+2 := by fin_cases i <;> rfl

theorem crossSum_cycle (w : Point) (i : Fin 3) :
    crossSum w = w i*w (i+1)+w (i+1)*w (i+2)+w (i+2)*w i := by
  unfold crossSum
  rw [← sum_cycle _ i]
  simp only [next_add_one, next_add_two, prev_add_one, prev_add_two]
  ring

theorem crossSum_pos (w : Point) (hw : ∀ i, 0 < w i) : 0 < crossSum w :=
  Finset.sum_pos (fun i _ => mul_pos (hw (i+1)) (hw (i+2))) Finset.univ_nonempty

theorem center_pos (w : Point) (hw : ∀ i, 0 < w i) (i : Fin 3) : 0 < center w i :=
  div_pos (mul_pos (hw _) (hw _)) (crossSum_pos w hw)

theorem center_sum (w : Point) (hw : ∀ i, 0 < w i) : (∑ i, center w i) = 1 := by
  simp only [center, ← Finset.sum_div]
  exact div_self (crossSum_pos w hw).ne'

private theorem scalar_concurrence (a b c : ℝ) (hsum : a+b+c=1)
    (ha : 1-a ≠ 0) (hT : a*b+b*c+c*a ≠ 0) :
    b/(1-a)*(b*c/(a*b+b*c+c*a)) + a*b/(a*b+b*c+c*a) = b/(1-a) := by
  generalize hden : a*b+b*c+c*a = T at hT ⊢
  field_simp [ha, hT]
  linear_combination b*hden - a*b*hsum

/-- The vertex-parallel lines meet at an interior point with barycentric coordinates proportional to `1/wᵢ`. -/
theorem center_concurrent (w : Point) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i)=1)
    (i : Fin 3) :
    coordinate (fun j => w (j+1)/(1-w j)) (center w) i = w (i+1)/(1-w i) := by
  have hs := (sum_cycle w i).trans hsum
  have hwi : w i < 1 := by linarith only [hs, hw (i+1), hw (i+2)]
  have hT : 0 < w i*w (i+1)+w (i+1)*w (i+2)+w (i+2)*w i := by
    rw [← crossSum_cycle w i]
    exact crossSum_pos w hw
  simp only [coordinate, center, prev_add_one, prev_add_two, crossSum_cycle w i]
  exact scalar_concurrence (w i) (w (i+1)) (w (i+2)) hs (sub_pos.mpr hwi).ne' hT.ne'

/-- This common point is strictly inside every window. -/
theorem center_in_windows (w : Point) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i)=1)
    (i : Fin 3) :
    w (i+1) < coordinate (fun j => w (j+1)/(1-w j)) (center w) i ∧
      coordinate (fun j => w (j+1)/(1-w j)) (center w) i < 1-w (i+2) := by
  rw [center_concurrent w hw hsum]
  have hs := (sum_cycle w i).trans hsum
  have hwi : w i < 1 := by linarith only [hs, hw (i+1), hw (i+2)]
  constructor
  · apply (lt_div_iff₀ (sub_pos.mpr hwi)).mpr
    nlinarith only [mul_pos (hw i) (hw (i+1))]
  · apply (div_lt_iff₀ (sub_pos.mpr hwi)).mpr
    nlinarith only [hs, mul_pos (hw i) (hw (i+2))]

#print axioms center_concurrent
#print axioms center_in_windows

/-- On positive normalized barycentric coordinates, the common-point map is its own inverse. -/
theorem center_center (w : Point) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i)=1) :
    center (center w) = w := by
  funext i
  have hc := (crossSum_pos (center w) (center_pos w hw)).ne'
  apply (div_eq_iff hc).mpr
  rw [crossSum_cycle (center w) i]
  have hT := (crossSum_pos w hw).ne'
  simp only [center, prev_add_one, prev_add_two, next_add_one, next_add_two]
  generalize hden : crossSum w = T at hT ⊢
  field_simp [hT]
  have hs := (sum_cycle w i).trans hsum
  linear_combination -(w i)^2*w (i+1)*w (i+2)*hs

#print axioms center_center
end Plank.Convex.TriangleWindowCover
