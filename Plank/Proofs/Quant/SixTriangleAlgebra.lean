module
/-
# A square bound for the six triangular edge terms

This file proves an unconditional scalar inequality. Turning its six
positive-part terms into the actual gap requires a separate geometric
argument; no such area identity is assumed or asserted here.
-/
public import Plank.Proofs.Quant.OrdinalMatrix

@[expose] public section

noncomputable section

namespace Quant.SixTriangleAlgebra

def p (x y z : ℝ) : ℝ := 1 + x * y * z
def q (x y z : ℝ) : ℝ := 1 + (1 - x) * (1 - y) * (1 - z)

def imbalance (x y z : ℝ) : ℝ :=
  (q x y z - p x y z) ^ 2 / (p x y z * q x y z)

def dets (x y z : ℝ) : Fin 3 → ℝ :=
  ![1 - y + x * y, 1 - z + y * z, 1 - x + z * x]

def lowWeight (x y z : ℝ) : Fin 3 → ℝ :=
  ![(1 - z + x * z) / p x y z,
    (1 - x + y * x) / p x y z,
    (1 - y + z * y) / p x y z]

def highWeight (x y z : ℝ) : Fin 3 → ℝ :=
  ![(1 - y + y * z) / q x y z,
    (1 - z + z * x) / q x y z,
    (1 - x + x * y) / q x y z]

def lowDenom (x y z : ℝ) (i : Fin 3) : ℝ := ![y, z, x] i * dets x y z i
def highDenom (x y z : ℝ) (i : Fin 3) : ℝ :=
  ![1 - x, 1 - y, 1 - z] i * dets x y z i

def lowCut (x y z : ℝ) (l : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y * l 0 + l 1 - y, z * l 1 + l 2 - z, x * l 2 + l 0 - x]

def highCut (x y z : ℝ) (h : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![1 - h 0 - (1 - x) * h 1,
    1 - h 1 - (1 - y) * h 2,
    1 - h 2 - (1 - z) * h 0]

def sixArea (x y z : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  (∑ i, (max 0 (lowCut x y z l i)) ^ 2 / lowDenom x y z i) +
  ∑ i, (max 0 (highCut x y z h i)) ^ 2 / highDenom x y z i

theorem p_pos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < p x y z := by unfold p; positivity

theorem q_pos {x y z : ℝ} (hx : x < 1) (hy : y < 1) (hz : z < 1) :
    0 < q x y z := by
  have h := mul_pos (mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)) (sub_pos.mpr hz)
  unfold q
  linarith

theorem imbalance_nonneg {x y z : ℝ}
    (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) :
    0 ≤ imbalance x y z :=
  div_nonneg (sq_nonneg _) (mul_pos (p_pos hx.1 hy.1 hz.1) (q_pos hx.2 hy.2 hz.2)).le

theorem weights_pos {x y z : ℝ}
    (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) (i : Fin 3) :
    0 < lowWeight x y z i ∧ 0 < highWeight x y z i := by
  have hp := p_pos hx.1 hy.1 hz.1
  have hq := q_pos hx.2 hy.2 hz.2
  have hx' := sub_pos.mpr hx.2
  have hy' := sub_pos.mpr hy.2
  have hz' := sub_pos.mpr hz.2
  have hx0 := hx.1
  have hy0 := hy.1
  have hz0 := hz.1
  fin_cases i <;> dsimp [lowWeight, highWeight] <;> constructor <;> positivity

theorem denoms_pos {x y z : ℝ}
    (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) (i : Fin 3) :
    0 < lowDenom x y z i ∧ 0 < highDenom x y z i := by
  have hx' := sub_pos.mpr hx.2
  have hy' := sub_pos.mpr hy.2
  have hz' := sub_pos.mpr hz.2
  have hx0 := hx.1
  have hy0 := hy.1
  have hz0 := hz.1
  fin_cases i <;> dsimp [lowDenom, highDenom, dets] <;> constructor <;> positivity

/-- The linear combination cancels all three positions and gives unit cost
to each width. Its constant exceeds one by the squared imbalance. -/
theorem linear_identity {x y z : ℝ}
    (hp : p x y z ≠ 0) (hq : q x y z ≠ 0) (l h : Fin 3 → ℝ) :
    (∑ i, lowWeight x y z i * lowCut x y z l i) +
        (∑ i, highWeight x y z i * highCut x y z h i) =
      1 - ((h 0 - l 0) + (h 1 - l 1) + (h 2 - l 2)) + imbalance x y z := by
  simp only [Fin.sum_univ_three]
  dsimp [lowWeight, highWeight, lowCut, highCut, imbalance]
  field_simp [hp, hq]
  dsimp [p, q]
  ring

/-- The corresponding quadratic cost is exactly one minus the square of
the imbalance. In particular it is at most one. -/
theorem norm_identity {x y z : ℝ}
    (hp : p x y z ≠ 0) (hq : q x y z ≠ 0) :
    (∑ i, (lowWeight x y z i) ^ 2 * lowDenom x y z i) +
        (∑ i, (highWeight x y z i) ^ 2 * highDenom x y z i) =
      1 - (imbalance x y z) ^ 2 := by
  simp only [Fin.sum_univ_three]
  dsimp [lowWeight, highWeight, lowDenom, highDenom, dets, imbalance]
  field_simp [hp, hq]
  dsimp [p, q]
  ring

private theorem term_bound (k c v w : ℝ) (hk : 0 ≤ k) (hc : 0 ≤ c) (hw : 0 < w) :
    2 * k * c * v - k ^ 2 * c ^ 2 * w ≤ (max 0 v) ^ 2 / w := by
  have hmul : ((max 0 v) ^ 2 / w) * w = (max 0 v) ^ 2 := by
    field_simp
  have hvc : k * c * v ≤ k * c * max 0 v :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg hk hc)
  have hs := sq_nonneg (max 0 v - k * c * w)
  have hprod := mul_nonneg (sub_nonneg.mpr hvc) hw.le
  nlinarith

/-- The six scalar terms dominate the positive-part square, for every
position and every width triple. This is not an actual-gap area formula. -/
theorem positive_part_bound {x y z : ℝ}
    (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1)
    (l h : Fin 3 → ℝ) :
    (max 0 (1 - ((h 0 - l 0) + (h 1 - l 1) + (h 2 - l 2)))) ^ 2 ≤
      sixArea x y z l h := by
  let δ := 1 - ((h 0 - l 0) + (h 1 - l 1) + (h 2 - l 2))
  have hp := (p_pos hx.1 hy.1 hz.1).ne'
  have hq := (q_pos hx.2 hy.2 hz.2).ne'
  have hI := imbalance_nonneg hx hy hz
  by_cases hδ : 0 ≤ δ
  · have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      term_bound δ (lowWeight x y z i) (lowCut x y z l i) (lowDenom x y z i)
        hδ (weights_pos hx hy hz i).1.le (denoms_pos hx hy hz i).1)
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      term_bound δ (highWeight x y z i) (highCut x y z h i) (highDenom x y z i)
        hδ (weights_pos hx hy hz i).2.le (denoms_pos hx hy hz i).2)
    have he : (∑ i, (2 * δ * lowWeight x y z i * lowCut x y z l i -
        δ ^ 2 * (lowWeight x y z i) ^ 2 * lowDenom x y z i)) +
        (∑ i, (2 * δ * highWeight x y z i * highCut x y z h i -
        δ ^ 2 * (highWeight x y z i) ^ 2 * highDenom x y z i)) =
        2 * δ * ((∑ i, lowWeight x y z i * lowCut x y z l i) +
          ∑ i, highWeight x y z i * highCut x y z h i) -
        δ ^ 2 * ((∑ i, (lowWeight x y z i) ^ 2 * lowDenom x y z i) +
          ∑ i, (highWeight x y z i) ^ 2 * highDenom x y z i) := by
      simp only [Fin.sum_univ_three]
      ring
    have hsum := add_le_add hl hh
    rw [he, linear_identity hp hq l h, norm_identity hp hq] at hsum
    change 2 * δ * (δ + imbalance x y z) - δ ^ 2 * (1 - (imbalance x y z) ^ 2) ≤
      sixArea x y z l h at hsum
    change (max 0 δ) ^ 2 ≤ _
    rw [max_eq_right hδ]
    nlinarith [mul_nonneg hδ hI, sq_nonneg (δ * imbalance x y z)]
  · have hnonneg : 0 ≤ sixArea x y z l h := by
      apply add_nonneg <;> apply Finset.sum_nonneg <;> intro i _
      · exact div_nonneg (sq_nonneg _) (denoms_pos hx hy hz i).1.le
      · exact div_nonneg (sq_nonneg _) (denoms_pos hx hy hz i).2.le
    change (max 0 δ) ^ 2 ≤ _
    simpa only [max_eq_left (le_of_not_ge hδ), zero_pow (by decide : 2 ≠ 0)] using hnonneg

end Quant.SixTriangleAlgebra
