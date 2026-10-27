/-
# The CAL-w equality cone: `gap = δ²·|D|` for every width distribution

Port of `Dim2N3/KPlankCalwCone.lean` onto the `Plank` vocabulary — the
CAL-w twin of the shared-middle attainment (`stackConfig_gapArea`).

**The configuration** (`calwConfig`): one edge-parallel band along each
edge of `D = conv{(0,0),(1,0),(0,1)}` — normals `(1,0)`, `(0,1)`,
`(1,1)`, windows `[0,r₁]`, `[0,r₂]`, `[1−r₃,1]`.  All three directions
have width `1` over `D`, so the relative widths are exactly
`r₁, r₂, r₃` (`calwConfig_relW`) and `δ = 1 − (r₁+r₂+r₃)`.

★ **The uncovered set is the CENTRAL triangle — determined, not
assumed.**  `calwConfig_uncovered` proves it is the *open* central
triangle `{r₁ < x, r₂ < y, x + y < 1 − r₃}` with both legs exactly `δ`
(open, because the bands are closed; the closed triangle differs by a
null set).  It is not a corner configuration. ★

**What is proved.**  `volume_calwGap` — the uncovered area is
`(1 − (r₁+r₂+r₃))²/2 = δ²·|D|`; `calwConfig_gapArea` — the same in the
ledger's own `Config.gapArea` vocabulary; `volume_calwGap_cone` — the
same at fixed `δ` for *every* admissible distribution, which is the
point: the equality locus carries the two free redistribution
dimensions, so a collar must wrap the **cone**, not a ray;
`deltaSq_mem_gapValues_calw` — `δ²|D| ∈ gapValues` for the
edge-parallel normals, the same shape as `deltaSq_mem_gapValues`, so
`isLeast_gapValues_of_floor` composes with this witness verbatim.

**Hypotheses — both necessary.**  `0 ≤ rᵢ` and `r₁+r₂+r₃ ≤ 1`; exact
counterexamples exist outside each (a band with `lo > hi` is empty and
the uncovered set escapes the central triangle; at `Σr > 1` the gap is
`0` but `δ²/2` is not).  Everything *inside* those walls is in:
`rᵢ = 0`, `δ = 0`, and `δ = 1` are covered by the theorem rather than
excluded.

**Proof route.**  Not the `σ = x+y` sweep of the attainment chapter:
the central triangle is already fibred by the *first coordinate*, so
plain Fubini gives slices `Ioo r₂ (1−r₃−x)` directly, and the profile
is the descending ramp `(Ioc r₁ (1−r₃−r₂)).indicator (x ↦ 1−r₃−r₂−x)`.
`lintegral_ramp_down` is that integral — the mirror of
`lintegral_ramp_smul` with both endpoints free.
-/
module

public import Plank.Proofs.Quant.FlushTilt

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant Proofs.Transport

namespace Quant

/-! ## §1  The descending ramp integral -/

theorem lintegral_ramp_down {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ x, (Ioc a b).indicator (fun s => ENNReal.ofReal (b - s)) x
      = ENNReal.ofReal ((b - a) ^ 2 / 2) := by
  rw [lintegral_indicator measurableSet_Ioc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hab]
    congr 1
    rw [show (fun s : ℝ => b - s) = (fun s : ℝ => (fun x : ℝ => x) (b - s)) from rfl,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => x) b, sub_self, integral_id]
    ring
  · exact ((continuous_const.sub continuous_id).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa using hx.2

/-! ## §2  The barycentric CAL-w configuration -/

variable {r₁ r₂ r₃ : ℝ}

/-- The barycentric CAL-w configuration: one edge-parallel band along
each edge of `D`, of relative widths `r₁, r₂, r₃`. -/
def calwConfig (r₁ r₂ r₃ : ℝ) (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (h₃ : 0 ≤ r₃) :
    Config :=
  ⟨![⟨((1 : ℝ), (0 : ℝ)), 0, r₁, by simp [Prod.ext_iff], h₁⟩,
     ⟨((0 : ℝ), (1 : ℝ)), 0, r₂, by simp [Prod.ext_iff], h₂⟩,
     ⟨((1 : ℝ), (1 : ℝ)), 1 - r₃, 1, by simp [Prod.ext_iff], by linarith⟩]⟩

variable (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (h₃ : 0 ≤ r₃)

/-- ★ **The uncovered set is the CENTRAL triangle** ★ (open), not a
corner configuration: `r₁ < x`, `r₂ < y`, `x + y < 1 − r₃`. -/
theorem calwConfig_uncovered :
    (calwConfig r₁ r₂ r₃ h₁ h₂ h₃).uncovered
      = {p : ℝ × ℝ | r₁ < p.1 ∧ r₂ < p.2 ∧ p.1 + p.2 < 1 - r₃} := by
  ext p
  simp only [Config.uncovered, calwConfig, Set.mem_diff, Set.mem_iUnion,
    stdTriangle_set_eq, Set.mem_setOf_eq, not_exists]
  constructor
  · rintro ⟨⟨hd1, hd2, hd3⟩, hb⟩
    have hb1 := hb 0
    have hb2 := hb 1
    have hb3 := hb 2
    simp only [plank_set_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Set.mem_setOf_eq,
      dot, not_and, not_le] at hb1 hb2 hb3
    refine ⟨?_, ?_, ?_⟩
    · have := hb1 (by linarith)
      linarith
    · have := hb2 (by linarith)
      linarith
    · by_contra hcon
      push_neg at hcon
      have := hb3 (by linarith)
      linarith
  · rintro ⟨ha, hb, hc⟩
    refine ⟨⟨by linarith, by linarith, by linarith⟩, ?_⟩
    intro i
    rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with h | h | h <;>
      subst h <;>
      simp only [plank_set_eq, calwConfig, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Set.mem_setOf_eq,
        dot, not_and, not_le] <;>
      intro _ <;> linarith

/-- ★ **The CAL-w equality cone, as a volume** ★  For *every* width
distribution the uncovered area is exactly `δ²·|D|`. -/
theorem volume_calwGap (ht : r₁ + r₂ + r₃ ≤ 1) :
    volume ((calwConfig r₁ r₂ r₃ h₁ h₂ h₃).uncovered)
      = ENNReal.ofReal ((1 - (r₁ + r₂ + r₃)) ^ 2 / 2) := by
  have hmeas : MeasurableSet
      {p : ℝ × ℝ | r₁ < p.1 ∧ r₂ < p.2 ∧ p.1 + p.2 < 1 - r₃} := by
    have h : {p : ℝ × ℝ | r₁ < p.1 ∧ r₂ < p.2 ∧ p.1 + p.2 < 1 - r₃}
        = {p : ℝ × ℝ | r₁ < p.1} ∩ ({p : ℝ × ℝ | r₂ < p.2}
            ∩ {p : ℝ × ℝ | p.1 + p.2 < 1 - r₃}) := by
      ext p; simp [Set.mem_inter_iff, and_assoc]
    rw [h]
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt (measurable_fst.add measurable_snd) measurable_const))
  rw [calwConfig_uncovered]
  have hslice : ∀ x : ℝ,
      volume (Prod.mk x ⁻¹'
          {p : ℝ × ℝ | r₁ < p.1 ∧ r₂ < p.2 ∧ p.1 + p.2 < 1 - r₃})
        = (Ioc r₁ (1 - r₃ - r₂)).indicator
          (fun s => ENNReal.ofReal ((1 - r₃ - r₂) - s)) x := by
    intro x
    have hset : Prod.mk x ⁻¹'
          {p : ℝ × ℝ | r₁ < p.1 ∧ r₂ < p.2 ∧ p.1 + p.2 < 1 - r₃}
        = if r₁ < x then Ioo r₂ (1 - r₃ - x) else ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      split_ifs with hx
      · simp only [Set.mem_Ioo]
        constructor
        · rintro ⟨-, hy, hxy⟩; exact ⟨hy, by linarith⟩
        · rintro ⟨hy, hxy⟩; exact ⟨hx, hy, by linarith⟩
      · simp only [Set.mem_empty_iff_false, iff_false, not_and]
        intro hcon
        exact absurd hcon hx
    rw [hset]
    split_ifs with hx
    · rw [Real.volume_Ioo]
      rcases le_or_gt x (1 - r₃ - r₂) with hb | hb
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hb⟩)]
        congr 1
        ring
      · have hnot : x ∉ Ioc r₁ (1 - r₃ - r₂) := by
          simp only [Set.mem_Ioc, not_and, not_le]
          intro _
          exact hb
        rw [Set.indicator_of_notMem hnot, ENNReal.ofReal_eq_zero]
        linarith
    · have hnot : x ∉ Ioc r₁ (1 - r₃ - r₂) := by
        simp only [Set.mem_Ioc, not_and, not_le]
        intro hcon
        exact absurd hcon hx
      rw [measure_empty, Set.indicator_of_notMem hnot]
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas,
    lintegral_congr hslice, lintegral_ramp_down (by linarith)]
  congr 1
  ring

/-! ## §3  The cone form, and the ledger vocabulary -/

/-- **Admissibility.**  The three bands' relative widths against `D`
are exactly `r₁, r₂, r₃` — all three normals have width `1`. -/
theorem calwConfig_relW (i : Fin 3) :
    (calwConfig r₁ r₂ r₃ h₁ h₂ h₃).relW i = ![r₁, r₂, r₃] i := by
  rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with h | h | h <;>
    subst h <;>
    simp only [Config.relW, calwConfig, Plank.relWidth, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, stdTriangle_width_eq] <;>
    norm_num

/-- **(CAL-w) in the ledger's own vocabulary**: the gap area is
`δ²·|D|` on the nose. -/
theorem calwConfig_gapArea (ht : r₁ + r₂ + r₃ ≤ 1) :
    (calwConfig r₁ r₂ r₃ h₁ h₂ h₃).gapArea
      = (1 - (r₁ + r₂ + r₃)) ^ 2 / 2 := by
  rw [Config.gapArea, volume_calwGap h₁ h₂ h₃ ht,
    ENNReal.toReal_ofReal (by positivity)]

/-- ★ **The CAL-w equality CONE** ★  At a fixed deficit `δ` the
uncovered area is `δ²·|D|` for *every* admissible width distribution:
the equality locus carries the two free redistribution dimensions, not
just the symmetric ray. -/
theorem volume_calwGap_cone {δ : ℝ} (hδ : 0 ≤ δ) (hsum : r₁ + r₂ + r₃ = 1 - δ) :
    volume ((calwConfig r₁ r₂ r₃ h₁ h₂ h₃).uncovered)
      = ENNReal.ofReal (δ ^ 2 / 2) := by
  rw [volume_calwGap h₁ h₂ h₃ (by linarith), hsum]
  congr 1
  ring

/-- ★ **Composability with (I1)** ★  `δ²|D|` is a value of the gap for
the edge-parallel normals at relative widths `r₁, r₂, r₃` — the same
`gapValues` vocabulary as `deltaSq_mem_gapValues`, so
`isLeast_gapValues_of_floor` composes with this witness too. -/
theorem deltaSq_mem_gapValues_calw (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (h₃ : 0 ≤ r₃)
    (ht : r₁ + r₂ + r₃ ≤ 1) :
    (1 - (r₁ + r₂ + r₃)) ^ 2 / 2
      ∈ gapValues ![((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (1 : ℝ))]
          ![r₁, r₂, r₃] := by
  refine ⟨calwConfig r₁ r₂ r₃ h₁ h₂ h₃, ?_, calwConfig_relW h₁ h₂ h₃,
    (calwConfig_gapArea h₁ h₂ h₃ ht).symm⟩
  intro i
  rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with h | h | h <;>
    subst h <;> rfl

end Quant
