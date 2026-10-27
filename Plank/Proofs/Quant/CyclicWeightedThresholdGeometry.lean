module
/-
# Exact threshold areas for three independent cyclic directions

The positive cyclic weights turn the three functional thresholds into a
simplex. Haar measure computes its whole-plane area. Three additional
linear inequalities ensure that it lies in the original triangle.
-/
public import Plank.Proofs.Quant.CyclicThresholdGeometry
public import Plank.Proofs.Quant.CyclicGeometry

@[expose] public section

noncomputable section

namespace Quant.CyclicWeightedThresholdGeometry

open Set MeasureTheory

/-- In barycentric coordinates, `fᵢ = dᵢ λᵢ + λᵢ₊₂`, with directions
`(a,b,c)` and `(λ₀,λ₁,λ₂) = (p.1,p.2,1-p.1-p.2)`. -/
def value (a b c : ℝ) (i : Fin 3) (p : ℝ × ℝ) : ℝ :=
  ![1 - (1 - a) * p.1 - p.2, p.1 + b * p.2,
    c - c * p.1 + (1 - c) * p.2] i

def k0 (b c : ℝ) : ℝ := 1 - c + b * c
def k1 (a c : ℝ) : ℝ := 1 - a + a * c
def k2 (a b : ℝ) : ℝ := 1 - b + a * b

theorem weights_pos {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    0 < k0 b c ∧ 0 < k1 a c ∧ 0 < k2 a b := by
  exact ⟨add_pos (sub_pos.mpr hc.2) (mul_pos hb.1 hc.1),
    add_pos (sub_pos.mpr ha.2) (mul_pos ha.1 hc.1),
    add_pos (sub_pos.mpr hb.2) (mul_pos ha.1 hb.1)⟩

/-- The existing ABC chart is `(b,1-a,c)` for these barycentric directions. -/
theorem k0_eq_w1 (b c : ℝ) : k0 b c = CyclicGeometry.w1 b c := rfl

theorem k1_eq_w0 (a c : ℝ) : k1 a c = CyclicGeometry.w0 (1 - a) c := by
  dsimp [k1, CyclicGeometry.w0]
  ring

theorem k2_eq_w2 (a b : ℝ) : k2 a b = CyclicGeometry.w2 (1 - a) b := by
  dsimp [k2, CyclicGeometry.w2]
  ring

theorem value_const (d : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    value d d d i p = CyclicCenteredGeometry.value d i p := rfl

theorem continuous_value (a b c : ℝ) (i : Fin 3) : Continuous (value a b c i) := by
  change Continuous (fun p => value a b c i p)
  fin_cases i <;> dsimp [value] <;> fun_prop

theorem weighted_value_sum (a b c : ℝ) (p : ℝ × ℝ) :
    k0 b c * value a b c 0 p + k1 a c * value a b c 1 p +
      k2 a b * value a b c 2 p = 1 + a * b * c := by
  dsimp [value, k0, k1, k2]
  ring

/-- Recover the three barycentric coordinates, up to positive factors. -/
theorem coordinate_identities (a b c : ℝ) (p : ℝ × ℝ) :
    value a b c 1 p + b * value a b c 0 p - b = k2 a b * p.1 ∧
    value a b c 2 p + c * value a b c 1 p - c = k0 b c * p.2 ∧
    value a b c 0 p + a * value a b c 2 p - a =
      k1 a c * (1 - p.1 - p.2) := by
  dsimp [value, k0, k1, k2]
  constructor
  · ring
  constructor <;> ring

/-- Three arbitrary lower thresholds, before clipping to the body. -/
def upperRegion (a b c : ℝ) (t : Fin 3 → ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ i, t i ≤ value a b c i p}

def upperCell (a b c : ℝ) (t : Fin 3 → ℝ) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ upperRegion a b c t

/-- Weighted first-two functional coordinates, with their constants removed. -/
def valueLinear (a b c : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (k0 b c * (-(1 - a) * p.1 - p.2),
    k1 a c * (p.1 + b * p.2))
  map_add' p q := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] <;> ring
  map_smul' r p := by
    apply Prod.ext <;>
      simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul,
        Prod.smul_mk] <;> ring

theorem det_valueLinear (a b c : ℝ) :
    LinearMap.det (valueLinear a b c) = k0 b c * k1 a c * k2 a b := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, valueLinear, Module.Basis.finTwoProd]
  dsimp [k2]
  ring

/-- Exact whole-plane area, including empty and degenerate threshold regions.
There is no restriction on the three threshold levels. -/
theorem volume_upperRegion (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    volume (upperRegion a b c t) =
      ENNReal.ofReal ((max 0 (1 + a * b * c - k0 b c * t 0 -
        k1 a c * t 1 - k2 a b * t 2)) ^ 2 /
          (2 * k0 b c * k1 a c * k2 a b)) := by
  obtain ⟨hk0, hk1, hk2⟩ := weights_pos ha hb hc
  have hdet : 0 < k0 b c * k1 a c * k2 a b := mul_pos (mul_pos hk0 hk1) hk2
  let v : ℝ × ℝ := (k0 b c * (1 - t 0), -(k1 a c * t 1))
  have he : upperRegion a b c t = valueLinear a b c ⁻¹'
      ((fun p => p + v) ⁻¹' RowDeletion.triangle
        (1 + a * b * c - k0 b c * t 0 - k1 a c * t 1 - k2 a b * t 2)) := by
    ext p
    change (∀ i, t i ≤ value a b c i p) ↔
      (0 ≤ k0 b c * (-(1 - a) * p.1 - p.2) + k0 b c * (1 - t 0) ∧
        0 ≤ k1 a c * (p.1 + b * p.2) + -(k1 a c * t 1) ∧
        (k0 b c * (-(1 - a) * p.1 - p.2) + k0 b c * (1 - t 0)) +
          (k1 a c * (p.1 + b * p.2) + -(k1 a c * t 1)) ≤
            1 + a * b * c - k0 b c * t 0 - k1 a c * t 1 - k2 a b * t 2)
    have hsum := weighted_value_sum a b c p
    dsimp [value] at hsum
    constructor
    · intro hp
      have h0 := mul_le_mul_of_nonneg_left (hp 0) hk0.le
      have h1 := mul_le_mul_of_nonneg_left (hp 1) hk1.le
      have h2 := mul_le_mul_of_nonneg_left (hp 2) hk2.le
      dsimp [value] at h0 h1 h2
      exact ⟨by nlinarith only [h0], by nlinarith only [h1],
        by nlinarith only [h2, hsum]⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · apply le_of_mul_le_mul_left (a := k0 b c) _ hk0
        dsimp [value]
        nlinarith only [h0]
      · apply le_of_mul_le_mul_left (a := k1 a c) _ hk1
        dsimp [value]
        nlinarith only [h1]
      · apply le_of_mul_le_mul_left (a := k2 a b) _ hk2
        dsimp [value]
        nlinarith only [h2, hsum]
  rw [he, Measure.addHaar_preimage_linearMap volume
    (by rw [det_valueLinear]; exact hdet.ne'), det_valueLinear,
    measure_preimage_add_right, CyclicCenteredGeometry.volume_triangle_posPart,
    abs_of_pos (inv_pos.mpr hdet), ← ENNReal.ofReal_mul (inv_pos.mpr hdet).le]
  congr 1
  field_simp [hk0.ne', hk1.ne', hk2.ne']

/-- These three threshold conditions suffice to prevent all clipping by
the original triangle. They permit three independent directions and levels. -/
theorem upperRegion_subset_triangle (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht0 : a ≤ t 0 + a * t 2) (ht1 : b ≤ t 1 + b * t 0)
    (ht2 : c ≤ t 2 + c * t 1) :
    upperRegion a b c t ⊆ stdTriangle.set := by
  obtain ⟨hk0, hk1, hk2⟩ := weights_pos ha hb hc
  intro p hp
  obtain ⟨hxid, hyid, hzid⟩ := coordinate_identities a b c p
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have hm0 := mul_le_mul_of_nonneg_left h0 hb.1.le
  have hm1 := mul_le_mul_of_nonneg_left h1 hc.1.le
  have hm2 := mul_le_mul_of_nonneg_left h2 ha.1.le
  have hx : 0 ≤ k2 a b * p.1 := by linarith only [hxid, h1, hm0, ht1]
  have hy : 0 ≤ k0 b c * p.2 := by linarith only [hyid, h2, hm1, ht2]
  have hz : 0 ≤ k1 a c * (1 - p.1 - p.2) := by
    linarith only [hzid, h0, hm2, ht0]
  rw [Proofs.Quant.stdTriangle_set_eq]
  exact ⟨nonneg_of_mul_nonneg_right hx hk2,
    nonneg_of_mul_nonneg_right hy hk0,
    by linarith [nonneg_of_mul_nonneg_right hz hk1]⟩

/-- Exact area in the original body whenever the three threshold conditions
place the entire threshold region inside it. -/
theorem volume_upperCell (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht0 : a ≤ t 0 + a * t 2) (ht1 : b ≤ t 1 + b * t 0)
    (ht2 : c ≤ t 2 + c * t 1) :
    volume (upperCell a b c t) =
      ENNReal.ofReal ((max 0 (1 + a * b * c - k0 b c * t 0 -
        k1 a c * t 1 - k2 a b * t 2)) ^ 2 /
          (2 * k0 b c * k1 a c * k2 a b)) := by
  rw [upperCell, Set.inter_eq_right.mpr
    (upperRegion_subset_triangle a b c t ha hb hc ht0 ht1 ht2),
    volume_upperRegion a b c t ha hb hc]

end Quant.CyclicWeightedThresholdGeometry
