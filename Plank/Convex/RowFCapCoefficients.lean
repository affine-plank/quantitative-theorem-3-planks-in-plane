/- Coefficient bounds for the last planar cap class.
A single square bounds one opposite pair. Two path comparisons then bound
each directed cycle separately, avoiding a large polynomial certificate. -/
module
public import Plank.Convex.SameSignCapProduct
public import Plank.Convex.WidthBudgets
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.RowFCapCoefficients
open scoped BigOperators
open SameSignCapAlgebra SameSignCapProduct

def m (A : Point) (d : ℝ) : ℝ := A 1 + A 2 * d
def k (A : Point) (d e : ℝ) : ℝ := A 0 + e * m A d
def ell (A : Point) (c d : ℝ) : ℝ := A 0 * c + m A d
def t (a c : ℝ) : ℝ := a * c / (a + c)
def s (a e : ℝ) : ℝ := e / (1 + a * e)

def forward (A : Point) (a c d e C0 : ℝ) : Point :=
  ![t a c + m A d / k A d e, A 2 / ell A c d, C0 / A 2]

def reverse (A : Point) (a c d e C1 : ℝ) : Point :=
  ![A 2 / k A d e, s a e + A 0 / ell A c d, C1 / A 2 + A 0 * d / k A d e]

def GoodCoefficients (A : Point) (a c d e C0 C1 : ℝ) : Prop :=
  0 ≤ C0 ∧ 0 ≤ C1 ∧ C0 ≤ A 0 + e * A 1 ∧
  C0 ≤ A 0 + s a e * ell A c d ∧ C1 ≤ A 0 * c + A 1 ∧
  C1 ≤ t a c * A 0 + A 1

theorem good_left (A : Point) (a c d e : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    GoodCoefficients A a c d e (A 0) (a * (A 0 * c + A 1) / (a + c)) := by
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  have hac : 0 < a + c := add_pos ha hc
  have hq : a / (a + c) ≤ 1 := (div_le_iff₀ hac).mpr (by linarith only [hc])
  have hL : 0 ≤ ell A c d := by unfold ell m; positivity
  have hs : 0 ≤ s a e := by unfold s; positivity
  refine ⟨hA0.le, by positivity, le_add_of_nonneg_right (mul_pos he hA1).le,
    le_add_of_nonneg_right (mul_nonneg hs hL), ?_, ?_⟩
  · calc
      _ = (a / (a + c)) * (A 0 * c + A 1) := by ring
      _ ≤ 1 * (A 0 * c + A 1) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = _ := one_mul _
  · calc
      _ = t a c * A 0 + (a / (a + c)) * A 1 := by unfold t; ring
      _ ≤ t a c * A 0 + 1 * A 1 :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hq hA1.le)
      _ = _ := by rw [one_mul]

theorem good_right (A : Point) (a c d e : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    GoodCoefficients A a c d e ((A 0 + e * A 1) / (1 + a * e)) (A 1) := by
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  have hae : 0 < 1 + a * e := by positivity
  have hs : 0 ≤ s a e := by unfold s; positivity
  have ht : 0 ≤ t a c := by unfold t; positivity
  have hL : A 1 ≤ ell A c d := by
    unfold ell m
    linarith only [mul_pos hA0 hc, mul_pos hA2 hd]
  refine ⟨by positivity, hA1.le, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hae).mpr
    nlinarith only [mul_nonneg (show 0 ≤ A 0 + e * A 1 by positivity) (mul_pos ha he).le]
  · have h0 : A 0 / (1 + a * e) ≤ A 0 := by
      apply (div_le_iff₀ hae).mpr
      nlinarith only [mul_nonneg hA0.le (mul_pos ha he).le]
    calc
      _ = A 0 / (1 + a * e) + s a e * A 1 := by unfold s; ring
      _ ≤ A 0 + s a e * ell A c d :=
        add_le_add h0 (mul_le_mul_of_nonneg_left hL hs)
  · exact le_add_of_nonneg_left (mul_pos hA0 hc).le
  · exact le_add_of_nonneg_left (mul_nonneg ht hA0.le)

theorem pair_gap (p M a c e : ℝ)
    (hp : 0 < p) (hM : 0 < M) (ha : 0 < a) (hc : 0 < c) (he : 0 < e) :
    (1 - (t a c + M / (p + e * M)) * (s a e + p / (p * c + M))) *
      ((a + c) * (1 + a * e) * (p + e * M) * (p * c + M)) =
        (c * p - a * e * M) ^ 2 := by
  have h1 : a + c ≠ 0 := ne_of_gt (by positivity)
  have h2 : 1 + a * e ≠ 0 := ne_of_gt (by positivity)
  have h3 : p + e * M ≠ 0 := ne_of_gt (by positivity)
  have h4 : p * c + M ≠ 0 := ne_of_gt (by positivity)
  unfold t s
  field_simp
  ring

theorem pair_bound (p M a c e : ℝ)
    (hp : 0 < p) (hM : 0 < M) (ha : 0 < a) (hc : 0 < c) (he : 0 < e) :
    (t a c + M / (p + e * M)) * (s a e + p / (p * c + M)) ≤ 1 := by
  have h := pair_gap p M a c e hp hM ha hc he
  have hD : 0 < (a + c) * (1 + a * e) * (p + e * M) * (p * c + M) := by positivity
  nlinarith only [h, hD, sq_nonneg (c * p - a * e * M)]

/-- Four elementary upper bounds give the three opposite-pair bounds and
two path comparisons needed for a common weighted budget. -/
theorem coefficient_path_bounds (A : Point) (a c d e C0 C1 : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (h0base : C0 ≤ A 0 + e * A 1)
    (h0path : C0 ≤ A 0 + s a e * ell A c d)
    (h1base : C1 ≤ A 0 * c + A 1)
    (h1path : C1 ≤ t a c * A 0 + A 1) :
    (∀ i, 0 ≤ forward A a c d e C0 i) ∧
    (∀ i, 0 ≤ reverse A a c d e C1 i) ∧
    (∀ i, forward A a c d e C0 i * reverse A a c d e C1 (next i) ≤ 1) ∧
    forward A a c d e C0 1 * forward A a c d e C0 2 ≤ reverse A a c d e C1 1 ∧
    reverse A a c d e C1 0 * reverse A a c d e C1 2 ≤ forward A a c d e C0 0 := by
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  have hM : 0 < m A d := by unfold m; positivity
  have hK : 0 < k A d e := by unfold k; positivity
  have hL : 0 < ell A c d := by unfold ell; positivity
  have ht : 0 ≤ t a c := by unfold t; positivity
  have hs : 0 ≤ s a e := by unfold s; positivity
  have hAK : A 0 ≤ k A d e := by
    unfold k
    exact le_add_of_nonneg_right (mul_pos he hM).le
  have hC0K : C0 ≤ k A d e := by
    apply le_trans h0base
    unfold k m
    nlinarith only [mul_nonneg he.le (mul_pos hA2 hd).le]
  have hα : A 0 * A 2 * d / k A d e ≤ A 2 * d := by
    apply (div_le_iff₀ hK).mpr
    have h := mul_le_mul_of_nonneg_right hAK (mul_pos hA2 hd).le
    nlinarith only [h]
  have hCL : C1 + A 0 * A 2 * d / k A d e ≤ ell A c d := by
    calc
      _ ≤ (A 0 * c + A 1) + A 2 * d := add_le_add h1base hα
      _ = _ := by unfold ell m; ring
  have hCF : C1 + A 0 * A 2 * d / k A d e ≤ t a c * k A d e + m A d := by
    calc
      _ ≤ (t a c * A 0 + A 1) + A 2 * d := add_le_add h1path hα
      _ = t a c * A 0 + m A d := by unfold m; ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hAK ht) (le_refl _)
  have hf (i : Fin 3) : 0 ≤ forward A a c d e C0 i := by
    fin_cases i
    · exact add_nonneg ht (div_nonneg hM.le hK.le)
    · exact div_nonneg hA2.le hL.le
    · exact div_nonneg hC0 hA2.le
  have hr (i : Fin 3) : 0 ≤ reverse A a c d e C1 i := by
    fin_cases i
    · exact div_nonneg hA2.le hK.le
    · exact add_nonneg hs (div_nonneg hA0.le hL.le)
    · exact add_nonneg (div_nonneg hC1 hA2.le) (div_nonneg (mul_pos hA0 hd).le hK.le)
  have hpair0 : forward A a c d e C0 0 * reverse A a c d e C1 1 ≤ 1 :=
    pair_bound (A 0) (m A d) a c e hA0 hM ha hc he
  have hpair1 : forward A a c d e C0 1 * reverse A a c d e C1 2 ≤ 1 := by
    have hid : (forward A a c d e C0 1 * reverse A a c d e C1 2) * ell A c d =
        C1 + A 0 * A 2 * d / k A d e := by
      simp only [forward, reverse, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [ne_of_gt hA2, ne_of_gt hL, ne_of_gt hK]
    apply (mul_le_mul_iff_left₀ hL).mp
    rw [hid, one_mul]
    exact hCL
  have hpair2 : forward A a c d e C0 2 * reverse A a c d e C1 0 ≤ 1 := by
    have hid : (forward A a c d e C0 2 * reverse A a c d e C1 0) * k A d e = C0 := by
      simp only [forward, reverse, Matrix.cons_val_zero, Matrix.cons_val]
      field_simp [ne_of_gt hA2, ne_of_gt hK]
    apply (mul_le_mul_iff_left₀ hK).mp
    rw [hid, one_mul]
    exact hC0K
  have hfp : forward A a c d e C0 1 * forward A a c d e C0 2 ≤ reverse A a c d e C1 1 := by
    have hl : (forward A a c d e C0 1 * forward A a c d e C0 2) * ell A c d = C0 := by
      simp only [forward, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
      field_simp [ne_of_gt hA2, ne_of_gt hL]
    have hr : reverse A a c d e C1 1 * ell A c d = s a e * ell A c d + A 0 := by
      simp only [reverse, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp [ne_of_gt hL]
    apply (mul_le_mul_iff_left₀ hL).mp
    rw [hl, hr]
    linarith only [h0path]
  have hrp : reverse A a c d e C1 0 * reverse A a c d e C1 2 ≤ forward A a c d e C0 0 := by
    have hl : (reverse A a c d e C1 0 * reverse A a c d e C1 2) * k A d e =
        C1 + A 0 * A 2 * d / k A d e := by
      simp only [reverse, Matrix.cons_val_zero, Matrix.cons_val]
      field_simp [ne_of_gt hA2, ne_of_gt hK]
    have hr : forward A a c d e C0 0 * k A d e = t a c * k A d e + m A d := by
      simp only [forward, Matrix.cons_val_zero]
      field_simp [ne_of_gt hK]
    apply (mul_le_mul_iff_left₀ hK).mp
    rw [hl, hr]
    exact hCF
  refine ⟨hf, hr, ?_, hfp, hrp⟩
  intro i
  fin_cases i
  · exact hpair0
  · exact hpair1
  · exact hpair2

/-- Compatibility with the older cycle-product interface. -/
theorem coefficient_bounds (A : Point) (a c d e C0 C1 : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (h0base : C0 ≤ A 0 + e * A 1)
    (h0path : C0 ≤ A 0 + s a e * ell A c d)
    (h1base : C1 ≤ A 0 * c + A 1)
    (h1path : C1 ≤ t a c * A 0 + A 1) :
    (∀ i, 0 ≤ forward A a c d e C0 i) ∧
    (∀ i, 0 ≤ reverse A a c d e C1 i) ∧
    (∀ i, forward A a c d e C0 i * reverse A a c d e C1 (next i) ≤ 1) ∧
    (∏ i, forward A a c d e C0 i) + (∏ i, reverse A a c d e C1 i) ≤ 2 := by
  obtain ⟨hf, hr, hp, hfp, hrp⟩ := coefficient_path_bounds A a c d e C0 C1
    hA ha hc hd he hC0 hC1 h0base h0path h1base h1path
  exact ⟨hf, hr, hp, WidthBudgets.cycle_sum_bound_of_paths _ _ (hf 0) (hr 1) (hp 0) hfp hrp⟩

end Plank.Convex.RowFCapCoefficients

/-- info: 'Plank.Convex.RowFCapCoefficients.coefficient_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowFCapCoefficients.coefficient_bounds
