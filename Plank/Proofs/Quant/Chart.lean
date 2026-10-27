/-
# (F-CF) as a Lean bridge: the `(u,v)` chart

Port of `Dim2N3/KPlankChart.lean` onto the `Plank` vocabulary: the
unbundled `(n, b, c)` slabs of the ancestor become bundled planks read
through their **center** and **half-width**.

App AM derives its closed form by reading a point through its levels
along `u₀` and `u₁`, using the cofactor dependency `Σ λᵢ uᵢ = 0` to
turn the third slab into an oblique band.  This file makes that step a
theorem:

* `chartLin u₀ u₁` — the chart `q ↦ (⟪u₀,q⟫, ⟪u₁,q⟫)`, with
  `det_chartLin : det = λ₂ = det(u₀, u₁)`;
* `chartRegion` — the image region: a rectangle met by an oblique band
  `|λ₀x + λ₁y + λ₂b₂| ≤ A₂`, `A₂ = |λ₂|·c₂`;
* `triple_inter_eq_chart_preimage` — ★the set identity★: the triple
  intersection of the planks IS the chart preimage of that region;
* `volume_triple_inter` — and hence its area is `|λ₂|⁻¹·|chartRegion|`
  (the Jacobian step, by `volume_affinePreimage`);
* `tripleD_eq_Ftri_of_boxDensity` — the composition: on an unclipped
  configuration, `tripleD C = Ftri … S` at the concurrency defect
  `S = Σ λᵢbᵢ`, GIVEN the one remaining measure step.

**What is proved and what is assumed.**  The set identity and the
Jacobian are proved here.  The step still assumed — the explicit
hypothesis `hbox` — is the Fubini/co-area computation

    |chartRegion| = ∫_{−S−A₂}^{−S+A₂} gTrap A₀ A₁ |λ₀λ₁| w dw ,

that the linear form pushes the rectangle's area forward to the
trapezoid density.  `Plank/Proofs/Quant/Slice.lean` isolates its
geometry and `Fubini.lean` discharges it, making the chain end-to-end
kernel.

Conventions, pinned exactly in the ancestor's pre-checks: the `λ` must
be the **Cramer cofactors** of the three normals, and `tripleD`
already carries the ledger's `1/|T| = 2`, which is why the conclusion
is `tripleD = Ftri` with no further constant.
-/
module

public import Plank.Proofs.Quant.FtriCells
public import Plank.Proofs.Quant.Affine

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant

namespace Quant

/-! ## §1  Center and half-width -/

/-- The center of a plank's window: the midpoint of `[lo, hi]`. -/
def _root_.Plank.center (p : Plank) : ℝ := (p.lo + p.hi) / 2

/-- The half-width of a plank's window. -/
def _root_.Plank.halfWidth (p : Plank) : ℝ := (p.hi - p.lo) / 2

theorem halfWidth_nonneg (p : Plank) : 0 ≤ p.halfWidth :=
  div_nonneg (by linarith [p.lo_le_hi]) (by norm_num)

/-- Plank membership as a distance-to-center bound. -/
theorem mem_plank_iff_abs (p : Plank) (P : ℝ × ℝ) :
    P ∈ p.set ↔ |dot p.u P - p.center| ≤ p.halfWidth := by
  rw [plank_set_eq, mem_setOf_eq, abs_le, Plank.center, Plank.halfWidth]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ## §2  The chart -/

/-- The `(u,v)` chart: read a point by its levels along `u₀` and `u₁`. -/
def chartLin (u₀ u₁ : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun q := (dot u₀ q, dot u₁ q)
  map_add' x y := by
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    exact Prod.ext_iff.mpr ⟨by ring, by ring⟩
  map_smul' c x := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Prod.smul_mk,
      smul_eq_mul]
    exact Prod.ext_iff.mpr ⟨by ring, by ring⟩

@[simp] theorem chartLin_apply (u₀ u₁ q : ℝ × ℝ) :
    chartLin u₀ u₁ q = (dot u₀ q, dot u₁ q) := rfl

/-- The chart's determinant is the Cramer cofactor `λ₂ = det(u₀, u₁)`. -/
theorem det_chartLin (u₀ u₁ : ℝ × ℝ) :
    LinearMap.det (chartLin u₀ u₁) = u₀.1 * u₁.2 - u₀.2 * u₁.1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, chartLin, dot, Module.Basis.finTwoProd]

/-- The region cut out in the chart: a rectangle met by an oblique
band. -/
def chartRegion (lam₀ lam₁ lam₂ b₀ c₀ b₁ c₁ b₂ A₂ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | |p.1 - b₀| ≤ c₀ ∧ |p.2 - b₁| ≤ c₁ ∧
    |lam₀ * p.1 + lam₁ * p.2 + lam₂ * b₂| ≤ A₂}

/-- Volume of a pure linear preimage (the `c = 0` case of
`volume_affinePreimage`). -/
theorem volume_linear_preimage {L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)}
    (hL : LinearMap.det L ≠ 0) (s : Set (ℝ × ℝ)) :
    volume (⇑L ⁻¹' s) = ENNReal.ofReal |(LinearMap.det L)⁻¹| * volume s := by
  have h : ⇑L ⁻¹' s = (fun P => (0 : ℝ × ℝ) + L P) ⁻¹' s := by
    ext P; simp
  rw [h, volume_affinePreimage hL]

/-! ## §3  The set identity and the Jacobian -/

/-- ★ **The chart identity of (F-CF)** ★  Under the cofactor dependency
`λ₀u₀ + λ₁u₁ + λ₂u₂ = 0` (stated on levels), the triple intersection of
the planks is exactly the chart preimage of `chartRegion`, with
`A₂ = |λ₂|·c₂`. -/
theorem triple_inter_eq_chart_preimage (p₀ p₁ p₂ : Plank)
    (lam₀ lam₁ lam₂ : ℝ) (hlam₂ : lam₂ ≠ 0)
    (hdep : ∀ q : ℝ × ℝ,
      lam₀ * dot p₀.u q + lam₁ * dot p₁.u q + lam₂ * dot p₂.u q = 0) :
    p₀.set ∩ p₁.set ∩ p₂.set
      = chartLin p₀.u p₁.u ⁻¹'
        chartRegion lam₀ lam₁ lam₂ p₀.center p₀.halfWidth p₁.center p₁.halfWidth
          p₂.center (|lam₂| * p₂.halfWidth) := by
  ext q
  have hkey : lam₀ * dot p₀.u q + lam₁ * dot p₁.u q + lam₂ * p₂.center
      = -(lam₂ * (dot p₂.u q - p₂.center)) := by
    linear_combination hdep q
  simp only [mem_inter_iff, mem_preimage, chartLin_apply, chartRegion,
    mem_setOf_eq, mem_plank_iff_abs, hkey, abs_neg, abs_mul]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact ⟨h0, h1, mul_le_mul_of_nonneg_left h2 (abs_nonneg _)⟩
  · rintro ⟨h0, h1, h2⟩
    have hpos : 0 < |lam₂| := abs_pos.mpr hlam₂
    exact ⟨⟨h0, h1⟩, le_of_mul_le_mul_left h2 hpos⟩

/-- The Jacobian step: the triple intersection's area is `|λ₂|⁻¹` times
the chart region's. -/
theorem volume_triple_inter (p₀ p₁ p₂ : Plank) (lam₀ lam₁ lam₂ : ℝ)
    (hlam₂ : lam₂ ≠ 0) (hdet : p₀.u.1 * p₁.u.2 - p₀.u.2 * p₁.u.1 = lam₂)
    (hdep : ∀ q : ℝ × ℝ,
      lam₀ * dot p₀.u q + lam₁ * dot p₁.u q + lam₂ * dot p₂.u q = 0) :
    volume (p₀.set ∩ p₁.set ∩ p₂.set)
      = ENNReal.ofReal |lam₂|⁻¹
        * volume (chartRegion lam₀ lam₁ lam₂ p₀.center p₀.halfWidth
            p₁.center p₁.halfWidth p₂.center (|lam₂| * p₂.halfWidth)) := by
  have hdetne : LinearMap.det (chartLin p₀.u p₁.u) ≠ 0 := by
    rw [det_chartLin, hdet]; exact hlam₂
  rw [triple_inter_eq_chart_preimage p₀ p₁ p₂ lam₀ lam₁ lam₂ hlam₂ hdep,
    volume_linear_preimage hdetne, det_chartLin, hdet, abs_inv]

/-! ## §4  Composition with `Ftri` -/

/-- The unclipped triple overlap is the full triple intersection: the
`∩ T` in `tripleArea` is absorbed. -/
theorem tripleArea_of_unclipped {C : Config}
    (h : (C.plank 0).set ∩ (C.plank 1).set ∩ (C.plank 2).set ⊆ stdTriangle.set) :
    tripleArea C
      = (volume ((C.plank 0).set ∩ (C.plank 1).set ∩ (C.plank 2).set)).toReal := by
  unfold tripleArea
  rw [inter_eq_left.mpr h]

/-- ★ **(F-CF) as a bridge** ★  On an unclipped configuration whose
directions satisfy the cofactor dependency, the ledger's triple term
equals `Ftri` at the concurrency defect `S = Σ λᵢbᵢ` — GIVEN the
box-density step `hbox`, the one measure computation deferred to
`Fubini.lean`. -/
theorem tripleD_eq_Ftri_of_boxDensity (C : Config) (lam₀ lam₁ lam₂ : ℝ)
    (hlam₂ : lam₂ ≠ 0)
    (hdet : (C.plank 0).u.1 * (C.plank 1).u.2
      - (C.plank 0).u.2 * (C.plank 1).u.1 = lam₂)
    (hdep : ∀ q : ℝ × ℝ,
      lam₀ * dot (C.plank 0).u q + lam₁ * dot (C.plank 1).u q
        + lam₂ * dot (C.plank 2).u q = 0)
    (hunclip : (C.plank 0).set ∩ (C.plank 1).set ∩ (C.plank 2).set
      ⊆ stdTriangle.set)
    (hInt : 0 ≤ ∫ w in
        (-(lam₀ * (C.plank 0).center + lam₁ * (C.plank 1).center
            + lam₂ * (C.plank 2).center) - |lam₂| * (C.plank 2).halfWidth)..
        (-(lam₀ * (C.plank 0).center + lam₁ * (C.plank 1).center
            + lam₂ * (C.plank 2).center) + |lam₂| * (C.plank 2).halfWidth),
        gTrap (|lam₀| * (C.plank 0).halfWidth) (|lam₁| * (C.plank 1).halfWidth)
          (|lam₀ * lam₁|) w)
    (hbox : volume (chartRegion lam₀ lam₁ lam₂ (C.plank 0).center
          (C.plank 0).halfWidth (C.plank 1).center (C.plank 1).halfWidth
          (C.plank 2).center (|lam₂| * (C.plank 2).halfWidth))
      = ENNReal.ofReal (∫ w in
          (-(lam₀ * (C.plank 0).center + lam₁ * (C.plank 1).center
              + lam₂ * (C.plank 2).center) - |lam₂| * (C.plank 2).halfWidth)..
          (-(lam₀ * (C.plank 0).center + lam₁ * (C.plank 1).center
              + lam₂ * (C.plank 2).center) + |lam₂| * (C.plank 2).halfWidth),
          gTrap (|lam₀| * (C.plank 0).halfWidth) (|lam₁| * (C.plank 1).halfWidth)
            (|lam₀ * lam₁|) w)) :
    tripleD C
      = Ftri (|lam₀| * (C.plank 0).halfWidth) (|lam₁| * (C.plank 1).halfWidth)
          (|lam₂| * (C.plank 2).halfWidth) (|lam₀ * lam₁|) |lam₂|
          (lam₀ * (C.plank 0).center + lam₁ * (C.plank 1).center
            + lam₂ * (C.plank 2).center) := by
  have habs₂ : (0:ℝ) < |lam₂| := abs_pos.mpr hlam₂
  unfold tripleD Ftri Wtri
  rw [tripleArea_of_unclipped hunclip,
    volume_triple_inter (C.plank 0) (C.plank 1) (C.plank 2) lam₀ lam₁ lam₂
      hlam₂ hdet hdep, hbox, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) hInt)]
  field_simp

end Quant
