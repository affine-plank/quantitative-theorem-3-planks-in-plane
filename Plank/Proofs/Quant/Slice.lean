/-
# The slice lemma — the geometric content of `hbox`

Port of `Dim2N3/KPlankSlice.lean` — pure planar measure theory, so the
port re-homes namespace and prose only (the one substrate touchpoint,
the linear-preimage Jacobian, is `Chart.lean`'s
`volume_linear_preimage`).

`Chart.lean` reduces (F-CF) to one measure step,

    |chartRegion| = ∫_{−S−A₂}^{−S+A₂} gTrap A₀ A₁ |λ₀λ₁| w dw ,

which decomposes as translate → shear → Fubini.  The only *geometric*
content in that chain is the slice: at a fixed level `w` of the linear
form, the box's slice is an interval whose length is the trapezoid.
That is what this file proves, in the form Fubini will consume
(`volume_slice`, `volume_slice_gTrap`).

The three regimes of the trapezoid are exactly which pair of endpoints
bounds the intersection, isolated as `min_add_min` — a four-case
lattice identity over `ℝ`.  No case analysis on the sign of `λ₁` is
needed anywhere, because the scaling `v ↦ λ₁v` is done by
`Real.volume_preimage_mul_left` *before* the intersection is computed.

§3 proves the two reductions around the slice (translate, shear), so
that after this file the only thing between `Chart.lean` and a
hypothesis-free (F-CF) is the Fubini step for `bandRegion` — whose
inner measure is exactly `volume_slice`.
-/
module

public import Plank.Proofs.Quant.Chart

@[expose] public section


noncomputable section

open MeasureTheory Set

namespace Quant

/-! ## §1  The slice -/

/-- The four-case lattice identity behind the trapezoid: `min a c +
min b c` is the minimum of the three ways the two constraints can
bind. -/
theorem min_add_min (a b c : ℝ) :
    min a c + min b c = min (a + b) (min (min (a + c) (b + c)) (2 * c)) := by
  rcases le_total a c with h1 | h1 <;> rcases le_total b c with h2 | h2 <;>
    simp only [min_def] <;> split_ifs <;> linarith

/-- The slice of the box by a level set of the linear form is an
interval. -/
theorem interval_slice_eq (w A₁ A₂ : ℝ) :
    {u : ℝ | |w - u| ≤ A₁ ∧ |u| ≤ A₂}
      = Icc (max (w - A₁) (-A₂)) (min (w + A₁) A₂) := by
  ext u
  simp only [mem_setOf_eq, mem_Icc, abs_le, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The trapezoid, as the length of that interval. -/
theorem trap_length (w A₁ A₂ : ℝ) :
    max 0 (min (w + A₁) A₂ - max (w - A₁) (-A₂))
      = max 0 (min (A₁ + A₂ - |w|) (min (2 * A₁) (2 * A₂))) := by
  have hneg : -max (w - A₁) (-A₂) = min (A₁ - w) A₂ := by
    rw [← min_neg_neg]
    congr 1 <;> ring
  have hsplit : min (w + A₁) A₂ - max (w - A₁) (-A₂)
      = min (w + A₁) A₂ + min (A₁ - w) A₂ := by
    rw [← hneg]; ring
  rw [hsplit, min_add_min]
  have e1 : w + A₁ + (A₁ - w) = 2 * A₁ := by ring
  have e2 : min (w + A₁ + A₂) (A₁ - w + A₂) = A₁ + A₂ - |w| := by
    rcases abs_cases w with ⟨hw, hw'⟩ | ⟨hw, hw'⟩
    · rw [hw, min_eq_right (by linarith)]; ring
    · rw [hw, min_eq_left (by linarith)]; ring
  rw [e1, e2, min_left_comm]

/-- ★ **The slice lemma** ★  At level `w`, the box `{|v| ≤ c₁}` cut by
the band `{|w − λ₁v| ≤ A₀}` has length `trap(w)/|λ₁|`, with
`A₁ = |λ₁|·c₁`. -/
theorem volume_slice_band (lam₁ A₀ c₁ w : ℝ) (hlam₁ : lam₁ ≠ 0) :
    volume {v : ℝ | |w - lam₁ * v| ≤ A₀ ∧ |v| ≤ c₁}
      = ENNReal.ofReal
        (max 0 (min (A₀ + |lam₁| * c₁ - |w|)
          (min (2 * A₀) (2 * (|lam₁| * c₁)))) / |lam₁|) := by
  have hpos : 0 < |lam₁| := abs_pos.mpr hlam₁
  have hset : {v : ℝ | |w - lam₁ * v| ≤ A₀ ∧ |v| ≤ c₁}
      = (fun v => lam₁ * v) ⁻¹' {u : ℝ | |w - u| ≤ A₀ ∧ |u| ≤ |lam₁| * c₁} := by
    ext v
    simp only [mem_preimage, mem_setOf_eq, abs_mul]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mul_le_mul_of_nonneg_left h2 (abs_nonneg _)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, le_of_mul_le_mul_left (by linarith) hpos⟩
  rw [hset, Real.volume_preimage_mul_left hlam₁, interval_slice_eq,
    Real.volume_Icc, abs_inv]
  set X : ℝ := min (w + A₀) (|lam₁| * c₁) - max (w - A₀) (-(|lam₁| * c₁))
    with hX
  have halg : max 0 X
      = max 0 (min (A₀ + |lam₁| * c₁ - |w|)
          (min (2 * A₀) (2 * (|lam₁| * c₁)))) := by
    rw [hX]; exact trap_length w A₀ (|lam₁| * c₁)
  rcases le_or_gt X 0 with hle | hgt
  · have h0 : max 0 X = 0 := max_eq_left hle
    rw [h0] at halg
    rw [ENNReal.ofReal_eq_zero.mpr hle, mul_zero, ← halg]
    simp
  · have h0 : max 0 X = X := max_eq_right hgt.le
    rw [h0] at halg
    rw [← ENNReal.ofReal_mul (by positivity), ← halg]
    congr 1
    rw [div_eq_inv_mul]

/-- The slice lemma in the `gTrap` vocabulary: the slice length is
`|λ₀|·gTrap A₀ A₁ |λ₀λ₁| w`. -/
theorem volume_slice_gTrap (lam₀ lam₁ c₀ c₁ w : ℝ) (hlam₀ : lam₀ ≠ 0)
    (hlam₁ : lam₁ ≠ 0) :
    volume {v : ℝ | |w - lam₁ * v| ≤ |lam₀| * c₀ ∧ |v| ≤ c₁}
      = ENNReal.ofReal
        (|lam₀| * gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁| w) := by
  rw [volume_slice_band lam₁ (|lam₀| * c₀) c₁ w hlam₁]
  congr 1
  unfold gTrap
  rw [abs_mul]
  have h₀ : |lam₀| ≠ 0 := abs_ne_zero.mpr hlam₀
  have h₁ : |lam₁| ≠ 0 := abs_ne_zero.mpr hlam₁
  field_simp

/-! ## §2  The two reductions around the slice -/

/-- The box centred at the origin, with the concurrency defect `S`
absorbed into the band. -/
def centeredRegion (lam₀ lam₁ c₀ c₁ S A₂ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | |p.1| ≤ c₀ ∧ |p.2| ≤ c₁ ∧ |lam₀ * p.1 + lam₁ * p.2 + S| ≤ A₂}

/-- After the shear the first coordinate IS the level `w` of the
linear form. -/
def bandRegion (lam₁ A₀ c₁ S A₂ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | |p.1 - lam₁ * p.2| ≤ A₀ ∧ |p.2| ≤ c₁ ∧ |p.1 + S| ≤ A₂}

/-- **Reduction 1 (translate).**  Centring the box is a translation. -/
theorem volume_chartRegion_eq_centered (lam₀ lam₁ lam₂ b₀ c₀ b₁ c₁ b₂ A₂ : ℝ) :
    volume (chartRegion lam₀ lam₁ lam₂ b₀ c₀ b₁ c₁ b₂ A₂)
      = volume (centeredRegion lam₀ lam₁ c₀ c₁
          (lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂) A₂) := by
  have hset : chartRegion lam₀ lam₁ lam₂ b₀ c₀ b₁ c₁ b₂ A₂
      = (fun p => p + -(b₀, b₁)) ⁻¹'
        centeredRegion lam₀ lam₁ c₀ c₁
          (lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂) A₂ := by
    ext p
    simp only [chartRegion, centeredRegion, mem_preimage,
      mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by simpa [sub_eq_add_neg] using h1, by simpa [sub_eq_add_neg] using h2, ?_⟩
      have : lam₀ * (p.1 + -b₀) + lam₁ * (p.2 + -b₁)
          + (lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂)
          = lam₀ * p.1 + lam₁ * p.2 + lam₂ * b₂ := by ring
      rw [this]; exact h3
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by simpa [sub_eq_add_neg] using h1, by simpa [sub_eq_add_neg] using h2, ?_⟩
      have : lam₀ * p.1 + lam₁ * p.2 + lam₂ * b₂
          = lam₀ * (p.1 + -b₀) + lam₁ * (p.2 + -b₁)
            + (lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂) := by ring
      rw [this]; exact h3
  rw [hset, measure_preimage_add_right]

/-- The shear `(u,v) ↦ (λ₀u + λ₁v, v)`. -/
def shearLin (lam₀ lam₁ : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (lam₀ * p.1 + lam₁ * p.2, p.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    exact Prod.ext_iff.mpr ⟨by simp; ring, by simp⟩
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Prod.smul_mk,
      smul_eq_mul]
    exact Prod.ext_iff.mpr ⟨by simp; ring, by simp⟩

@[simp] theorem shearLin_apply (lam₀ lam₁ : ℝ) (p : ℝ × ℝ) :
    shearLin lam₀ lam₁ p = (lam₀ * p.1 + lam₁ * p.2, p.2) := rfl

theorem det_shearLin (lam₀ lam₁ : ℝ) :
    LinearMap.det (shearLin lam₀ lam₁) = lam₀ := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, shearLin, Module.Basis.finTwoProd]

/-- **Reduction 2 (shear).**  The centred region is the shear preimage
of the band region, with `A₀ = |λ₀|·c₀`. -/
theorem centered_eq_shear_preimage (lam₀ lam₁ c₀ c₁ S A₂ : ℝ)
    (hlam₀ : lam₀ ≠ 0) :
    centeredRegion lam₀ lam₁ c₀ c₁ S A₂
      = shearLin lam₀ lam₁ ⁻¹' bandRegion lam₁ (|lam₀| * c₀) c₁ S A₂ := by
  have hpos : 0 < |lam₀| := abs_pos.mpr hlam₀
  ext p
  simp only [centeredRegion, bandRegion, mem_preimage, shearLin_apply,
    mem_setOf_eq]
  have hkey : lam₀ * p.1 + lam₁ * p.2 - lam₁ * p.2 = lam₀ * p.1 := by ring
  rw [hkey, abs_mul]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨mul_le_mul_of_nonneg_left h1 (abs_nonneg _), h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨le_of_mul_le_mul_left (by linarith) hpos, h2, h3⟩

/-- The shear's Jacobian step. -/
theorem volume_centered_eq_band (lam₀ lam₁ c₀ c₁ S A₂ : ℝ) (hlam₀ : lam₀ ≠ 0) :
    volume (centeredRegion lam₀ lam₁ c₀ c₁ S A₂)
      = ENNReal.ofReal |lam₀|⁻¹
        * volume (bandRegion lam₁ (|lam₀| * c₀) c₁ S A₂) := by
  have hdetne : LinearMap.det (shearLin lam₀ lam₁) ≠ 0 := by
    rw [det_shearLin]; exact hlam₀
  rw [centered_eq_shear_preimage lam₀ lam₁ c₀ c₁ S A₂ hlam₀,
    volume_linear_preimage hdetne, det_shearLin, abs_inv]

/-- The slice of `bandRegion` at level `w` — the set `volume_slice_band`
computes. -/
theorem bandRegion_slice (lam₁ A₀ c₁ S A₂ w : ℝ) (hw : |w + S| ≤ A₂) :
    {v : ℝ | (w, v) ∈ bandRegion lam₁ A₀ c₁ S A₂}
      = {v : ℝ | |w - lam₁ * v| ≤ A₀ ∧ |v| ≤ c₁} := by
  ext v
  simp only [bandRegion, mem_setOf_eq]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hw⟩⟩

end Quant
