module
/- # Exact areas of three cyclic threshold regions -/
public import Plank.Proofs.Quant.CyclicCenteredGeometry

@[expose] public section

noncomputable section

namespace Quant.CyclicThresholdGeometry

open Set MeasureTheory CyclicCenteredGeometry

/-- Three lower thresholds on the cyclic functionals, before clipping to the body. -/
def upperRegion (d : ℝ) (t : Fin 3 → ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ i, t i ≤ value d i p}

/-- The same region clipped to the original triangle. -/
def upperCell (d : ℝ) (t : Fin 3 → ℝ) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ upperRegion d t

def valueLinear (d : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (-(1 - d) * p.1 - p.2, p.1 + d * p.2)
  map_add' p q := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] <;> ring
  map_smul' r p := by
    apply Prod.ext <;>
      simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul,
        Prod.smul_mk] <;> ring

theorem det_valueLinear (d : ℝ) :
    LinearMap.det (valueLinear d) = 1 - d + d ^ 2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, valueLinear, Module.Basis.finTwoProd]
  ring

theorem det_pos (d : ℝ) : 0 < 1 - d + d ^ 2 := by
  nlinarith only [sq_nonneg (d - 1 / 2)]

/-- The unrestricted region is an affine triangle, including its empty and
degenerate regimes. No sign restriction on the individual thresholds is needed. -/
theorem volume_upperRegion (d : ℝ) (t : Fin 3 → ℝ) :
    volume (upperRegion d t) =
      ENNReal.ofReal ((max 0 (1 + d - t 0 - t 1 - t 2)) ^ 2 /
        (2 * (1 - d + d ^ 2))) := by
  let v : ℝ × ℝ := (1 - t 0, -t 1)
  have he : upperRegion d t = valueLinear d ⁻¹'
      ((fun p => p + v) ⁻¹' RowDeletion.triangle (1 + d - t 0 - t 1 - t 2)) := by
    ext p
    change (∀ i, t i ≤ value d i p) ↔
      (0 ≤ -(1 - d) * p.1 - p.2 + (1 - t 0) ∧
        0 ≤ p.1 + d * p.2 + -t 1 ∧
        (-(1 - d) * p.1 - p.2 + (1 - t 0)) +
          (p.1 + d * p.2 + -t 1) ≤ 1 + d - t 0 - t 1 - t 2)
    constructor
    · intro hp
      have h0 := hp 0
      have h1 := hp 1
      have h2 := hp 2
      dsimp [value] at h0 h1 h2
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i <;> dsimp [value] <;> linarith
  rw [he, Measure.addHaar_preimage_linearMap volume
    (by rw [det_valueLinear]; exact (det_pos d).ne'),
    det_valueLinear, measure_preimage_add_right, volume_triangle_posPart,
    abs_of_pos (inv_pos.mpr (det_pos d)),
    ← ENNReal.ofReal_mul (inv_pos.mpr (det_pos d)).le]
  congr 1
  field_simp [(det_pos d).ne']

/-- Three cyclic linear conditions suffice to prevent clipping by the body's
three sides. They allow unequal thresholds. -/
theorem upperRegion_subset_triangle (d : ℝ) (t : Fin 3 → ℝ)
    (hd : 0 ≤ d) (ht : ∀ i : Fin 3, d ≤ t (i + 1) + d * t i) :
    upperRegion d t ⊆ stdTriangle.set := by
  intro p hp
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have ht0 := ht 0
  have ht1 := ht 1
  have ht2 := ht 2
  have hm0 := mul_le_mul_of_nonneg_left h0 hd
  have hm1 := mul_le_mul_of_nonneg_left h1 hd
  have hm2 := mul_le_mul_of_nonneg_left h2 hd
  have hx : 0 ≤ (1 - d + d ^ 2) * p.1 := by
    dsimp [value] at h1 hm0 ht0
    nlinarith only [h1, hm0, ht0]
  have hy : 0 ≤ (1 - d + d ^ 2) * p.2 := by
    dsimp [value] at h2 hm1 ht1
    nlinarith only [h2, hm1, ht1]
  have hz : 0 ≤ (1 - d + d ^ 2) * (1 - p.1 - p.2) := by
    dsimp [value] at h0 hm2 ht2
    nlinarith only [h0, hm2, ht2]
  rw [Proofs.Quant.stdTriangle_set_eq]
  exact ⟨nonneg_of_mul_nonneg_right hx (det_pos d),
    nonneg_of_mul_nonneg_right hy (det_pos d),
    by linarith [nonneg_of_mul_nonneg_right hz (det_pos d)]⟩

/-- Exact actual area when the cyclic threshold triangle lies in the body. -/
theorem volume_upperCell (d : ℝ) (t : Fin 3 → ℝ)
    (hd : 0 ≤ d) (ht : ∀ i : Fin 3, d ≤ t (i + 1) + d * t i) :
    volume (upperCell d t) =
      ENNReal.ofReal ((max 0 (1 + d - t 0 - t 1 - t 2)) ^ 2 /
        (2 * (1 - d + d ^ 2))) := by
  rw [upperCell, Set.inter_eq_right.mpr (upperRegion_subset_triangle d t hd ht),
    volume_upperRegion]

/-- The mixed threshold used to subtract the third-plank part of a high cell. -/
theorem volume_upperCell_two_equal (d h k : ℝ) (hd : 0 ≤ d ∧ d ≤ 1)
    (hkh : k ≤ h) (hfit : d ≤ k + d * h) :
    volume (upperCell d ![h, h, k]) =
      ENNReal.ofReal ((max 0 (1 + d - k - 2 * h)) ^ 2 /
        (2 * (1 - d + d ^ 2))) := by
  have ht : ∀ i : Fin 3, d ≤ (![h, h, k] : Fin 3 → ℝ) (i + 1) +
      d * (![h, h, k] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> dsimp
    · linarith
    · exact hfit
    · have hm := mul_nonneg (sub_nonneg.mpr hd.2) (sub_nonneg.mpr hkh)
      nlinarith only [hm, hfit]
  have he : 1 + d - (![h, h, k] : Fin 3 → ℝ) 0 -
      (![h, h, k] : Fin 3 → ℝ) 1 - (![h, h, k] : Fin 3 → ℝ) 2 =
      1 + d - k - 2 * h := by
    dsimp
    ring
  rw [volume_upperCell d _ hd.1 ht, he]

end Quant.CyclicThresholdGeometry
