/-
# The calibration bound on an arbitrary triangle

Port of `Dim2N3/KPlankAffine.lean`.  `plankDeficit_nonneg` is stated on
`stdTriangle`; the wedge arguments of the rigidity chapter need it on a
*general* triangle — a vertex wedge, not the standard one.  This file
supplies the transport.

A triangle is presented as the preimage of `stdTriangle` under an
invertible affine chart `q ↦ S (q − v)` (`triPre`); every triangle
arises this way, and preimages are what the Haar-measure lemmas handle
directly, so no image/injectivity machinery is needed.  The chart's
Jacobian appears on *both* sides of the inequality and cancels.

★ SCOPE NOTE (ancestor record, preserved).  The rigidity queue's R5
("free area of a wedge ≥ (free base chord)²/(2g)") is FALSE as
written: a strip parallel to the base chord can cover area while
meeting the chord in nothing (exact counterexample: wedge
`conv{(0,0),(0,1),(1,1)}`, strip `{2/5 ≤ y ≤ 3/5}`, covered `1/10`
against a bound of `0`).  What is true is the statement below, with
the covered base-chord fraction replaced by the strip's **relative
width** against the wedge; the two agree exactly when the strip hugs a
wedge edge, which is why R5 looked right on the equality stratum. -/
module

public import Plank.Proofs.Quant.Calibration

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant

namespace Quant

/-! ## §1  Triangles as affine preimages of `stdTriangle` -/

/-- The triangle presented by the invertible affine chart
`q ↦ S (q − v)`. -/
def triPre (S : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (v : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun q => S (q - v)) ⁻¹' stdTriangle.set

/-- The chart scales Lebesgue measure by the constant `|det S|⁻¹`, on
every set. -/
theorem volume_chart_preimage {S : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)}
    (hS : LinearMap.det S ≠ 0) (v : ℝ × ℝ) (A : Set (ℝ × ℝ)) :
    volume ((fun q => S (q - v)) ⁻¹' A)
      = ENNReal.ofReal |(LinearMap.det S)⁻¹| * volume A := by
  have h : (fun q : ℝ × ℝ => S (q - v)) ⁻¹' A = (fun q => -(S v) + S q) ⁻¹' A := by
    ext q
    simp only [Set.mem_preimage, sub_eq_neg_add, map_add, map_neg]
  rw [h, volume_affinePreimage hS]

theorem volume_triPre {S : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)} (hS : LinearMap.det S ≠ 0)
    (v : ℝ × ℝ) :
    volume (triPre S v)
      = ENNReal.ofReal |(LinearMap.det S)⁻¹| * ENNReal.ofReal (1 / 2) := by
  rw [triPre, volume_chart_preimage hS, Proofs.Quant.volume_stdTriangle]

/-- A plank pulls back to a plank: if `m''` is the plank's normal read
in the chart (`⟪m'', S ·⟫ = ⟪q.u, ·⟫`), the chart carries the standard
plank with window shifted by `⟪q.u, v⟫` back to `q` itself. -/
theorem chart_preimage_plank {S : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)} (v : ℝ × ℝ) (q : Plank)
    {m'' : ℝ × ℝ} (hmm : ∀ x, dot m'' (S x) = dot q.u x) (hm0 : m'' ≠ 0) :
    (fun x => S (x - v)) ⁻¹'
        (Plank.mk m'' (q.lo - dot q.u v) (q.hi - dot q.u v) hm0
          (sub_le_sub_right q.lo_le_hi _)).set
      = q.set := by
  have hlin : ∀ x : ℝ × ℝ, dot m'' (S (x - v)) = dot q.u x - dot q.u v := by
    intro x
    rw [hmm]
    simp only [dot, Prod.fst_sub, Prod.snd_sub]
    ring
  ext x
  show (q.lo - dot q.u v ≤ dot m'' (S (x - v)) ∧
        dot m'' (S (x - v)) ≤ q.hi - dot q.u v)
      ↔ (q.lo ≤ dot q.u x ∧ dot q.u x ≤ q.hi)
  rw [hlin x]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-! ## §2  The calibration bound transported -/

/-- **The one-plank calibration on an arbitrary triangle.**  For any
triangle `Δ = triPre S v` and any plank `q` whose relative width
`w = (q.hi − q.lo)/W` — measured against `Δ`'s own width `W` in the
plank's direction, which is `stdTriangle.width m''` for the chart-read
normal `m''` — satisfies `w ≤ 1`,

    |Δ \ q| ≥ (1 − w)² · |Δ| .

The chart's Jacobian cancels between the two sides; the content is
`plankDeficit_nonneg` on the standard triangle. -/
theorem one_plank_general_triangle {S : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)}
    (hS : LinearMap.det S ≠ 0) (v : ℝ × ℝ) (q : Plank) {m'' : ℝ × ℝ}
    (hmm : ∀ x, dot m'' (S x) = dot q.u x) (hm0 : m'' ≠ 0)
    (hw : (q.hi - q.lo) / stdTriangle.width m'' ≤ 1) :
    ENNReal.ofReal ((1 - (q.hi - q.lo) / stdTriangle.width m'') ^ 2)
        * volume (triPre S v)
      ≤ volume (triPre S v \ q.set) := by
  set K := ENNReal.ofReal |(LinearMap.det S)⁻¹| with hK
  -- the chart carries the general configuration to the standard one
  set p₂ : Plank := Plank.mk m'' (q.lo - dot q.u v) (q.hi - dot q.u v) hm0
    (sub_le_sub_right q.lo_le_hi _) with hp₂
  have hrelW : p₂.relWidth stdTriangle = (q.hi - q.lo) / stdTriangle.width m'' := by
    show (q.hi - dot q.u v - (q.lo - dot q.u v)) / stdTriangle.width m''
        = (q.hi - q.lo) / stdTriangle.width m''
    ring_nf
  have hpull : triPre S v \ q.set
      = (fun x => S (x - v)) ⁻¹' (stdTriangle.set \ p₂.set) := by
    rw [Set.preimage_diff, chart_preimage_plank v q hmm hm0, triPre]
  have hgap : volume (triPre S v \ q.set)
      = K * volume (stdTriangle.set \ p₂.set) := by
    rw [hpull, volume_chart_preimage hS]
  -- the standard-frame bound is the one-plank calibration
  have hstd : ENNReal.ofReal ((1 - (q.hi - q.lo) / stdTriangle.width m'') ^ 2 * (1 / 2))
      ≤ volume (stdTriangle.set \ p₂.set) := by
    have h1 := plankGap_ge p₂ (by rw [hrelW]; exact hw)
    rw [hrelW] at h1
    have hfin : volume (stdTriangle.set \ p₂.set) ≠ ⊤ :=
      volume_ne_top_of_subset_std Set.diff_subset
    calc ENNReal.ofReal ((1 - (q.hi - q.lo) / stdTriangle.width m'') ^ 2 * (1 / 2))
        ≤ ENNReal.ofReal (plankGap p₂) := ENNReal.ofReal_le_ofReal h1
      _ = volume (stdTriangle.set \ p₂.set) := by
          rw [plankGap, area, ENNReal.ofReal_toReal hfin]
  -- assemble; the Jacobian cancels
  have hΔ : volume (triPre S v) = K * ENNReal.ofReal (1 / 2) := volume_triPre hS v
  rw [hgap, hΔ, ← mul_assoc,
    mul_comm (ENNReal.ofReal ((1 - (q.hi - q.lo) / stdTriangle.width m'') ^ 2)) K,
    mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul_right hstd K

/-- **The wedge form.**  A vertex wedge is a triangle, so a single
plank of relative width `w ≤ 1` leaves at least `(1 − w)²` of it free.
This is the *true* one-strip content behind the rigidity queue's R5;
see this file's header for why R5's own formulation is false. -/
theorem wedge_one_plank {S : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)} (hS : LinearMap.det S ≠ 0)
    (v : ℝ × ℝ) (q : Plank) {m'' : ℝ × ℝ} (hmm : ∀ x, dot m'' (S x) = dot q.u x)
    (hm0 : m'' ≠ 0) (hw : (q.hi - q.lo) / stdTriangle.width m'' ≤ 1) :
    ENNReal.ofReal ((1 - (q.hi - q.lo) / stdTriangle.width m'') ^ 2)
        * volume (triPre S v)
      ≤ volume (triPre S v \ q.set) :=
  one_plank_general_triangle hS v q hmm hm0 hw

end Quant

end
