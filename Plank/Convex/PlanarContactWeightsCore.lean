/- The six planar contacts give slope weights by cancelling a positive width. -/
module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.PlanarContactWeights

abbrev Triple := Fin 3 → ℝ

/-- Two supporting inequalities and one linear relation cancel a positive width. -/
theorem row_weight (w u v p q r a b : ℝ)
    (hw : 0 < w) (ha : 0 ≤ a) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hplane : p * u + q * w ≤ r * v)
    (hu : a * v ≤ w) (hl : -b * w ≤ u) :
    a * q ≤ r + a * b * p := by
  apply (mul_le_mul_iff_left₀ hw).mp
  have H := mul_le_mul_of_nonneg_left hu hr
  have L := mul_le_mul_of_nonneg_left hl (mul_nonneg ha hp)
  have E := mul_le_mul_of_nonneg_left hplane ha
  nlinarith only [H, L, E]

theorem sum_cycle (x : Triple) (i : Fin 3) :
    (∑ j, x j) = x i + x (i + 1) + x (i + 2) := by
  rw [Fin.sum_univ_three]
  fin_cases i
  · change x 0 + x 1 + x 2 = x 0 + x 1 + x 2
    rfl
  · change x 0 + x 1 + x 2 = x 1 + x 2 + x 0
    ring
  · change x 0 + x 1 + x 2 = x 2 + x 0 + x 1
    ring

/-- Six pair contacts give the positive-plane coefficients as slope weights.
No convexity, coordinate-extremum witnesses, or offset bounds are needed. -/
theorem weights_of_contacts (K : Set Triple) (lo hi a b c : Triple) (D : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    (hwidth : ∀ i, lo i < hi i)
    (hplane : ∀ x ∈ K, (∑ i, c i * x i) = D)
    (hL : ∀ i, ∃ x ∈ K, x i = lo i ∧ x (i + 1) = lo (i + 1))
    (hU : ∀ i, ∃ x ∈ K, x i = hi i ∧ x (i + 1) = hi (i + 1))
    (hupper : ∀ i, ∀ x ∈ K, x i + a i * x (i + 1) ≤ hi i + a i * hi (i + 1))
    (hlower : ∀ i, ∀ x ∈ K, lo i + b i * lo (i + 1) ≤ x i + b i * x (i + 1)) :
    (∀ i, a (i + 1) * c (i + 1) ≤ c (i + 2) + a (i + 1) * b i * c i) ∧
    (∀ i, b (i + 1) * c (i + 1) ≤ c (i + 2) + b (i + 1) * a i * c i) := by
  constructor
  · intro i
    have hn : (i + 1) + 1 = i + 2 := by fin_cases i <;> rfl
    obtain ⟨x, hx, hxi, hxj⟩ := hL i
    obtain ⟨y, hy, hyj, hyk⟩ := hU (i + 1)
    rw [hn] at hyk
    have H := hupper (i + 1) x hx
    have L := hlower i y hy
    rw [hn, hxj] at H
    rw [hyj] at L
    have X := hplane x hx
    have Y := hplane y hy
    rw [sum_cycle (fun j => c j * x j) i] at X
    rw [sum_cycle (fun j => c j * y j) i] at Y
    simp only [hxi, hxj] at X
    simp only [hyj, hyk] at Y
    apply row_weight (hi (i + 1) - lo (i + 1)) (y i - lo i)
      (x (i + 2) - hi (i + 2)) (c i) (c (i + 1)) (c (i + 2)) (a (i + 1)) (b i)
      (sub_pos.mpr (hwidth _)) (ha _) (hc _) (hc _)
    · nlinarith only [X, Y]
    · nlinarith only [H]
    · nlinarith only [L]
  · intro i
    have hn : (i + 1) + 1 = i + 2 := by fin_cases i <;> rfl
    obtain ⟨y, hy, hyi, hyj⟩ := hU i
    obtain ⟨x, hx, hxj, hxk⟩ := hL (i + 1)
    rw [hn] at hxk
    have H := hlower (i + 1) y hy
    have L := hupper i x hx
    rw [hn, hyj] at H
    rw [hxj] at L
    have X := hplane x hx
    have Y := hplane y hy
    rw [sum_cycle (fun j => c j * x j) i] at X
    rw [sum_cycle (fun j => c j * y j) i] at Y
    simp only [hxj, hxk] at X
    simp only [hyi, hyj] at Y
    apply row_weight (hi (i + 1) - lo (i + 1)) (hi i - x i)
      (lo (i + 2) - y (i + 2)) (c i) (c (i + 1)) (c (i + 2)) (b (i + 1)) (a i)
      (sub_pos.mpr (hwidth _)) (hb _) (hc _) (hc _)
    · nlinarith only [X, Y]
    · nlinarith only [H]
    · nlinarith only [L]

end Plank.Convex.PlanarContactWeights
