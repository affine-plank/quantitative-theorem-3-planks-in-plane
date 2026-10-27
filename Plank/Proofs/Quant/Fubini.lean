/-
# `hbox` discharged: Fubini for the band region, and (F-CF) as one theorem

Port of `Dim2N3/KPlankFubini.lean` — the last step of the (U1-BOX)
chain's kernel side.  `Slice.lean` reduced the box-density identity to
Fubini plus a `lintegral`-to-`intervalIntegral` conversion; this file
does that, and then discharges the `hbox` hypothesis of `Chart.lean`,
giving

* `volume_bandRegion` — Fubini: the band region's area is the integral
  of the slice length over the `w`-band (empty slices outside it);
* `volume_chartRegion_eq_gTrap_integral` — **`hbox` as a theorem**;
* `tripleD_eq_Ftri` — ★**(F-CF) with no side hypotheses beyond
  geometry**★: unclipped, the cofactor dependency, `λᵢ ≠ 0`,
  `det(u₀,u₁) = λ₂`.

With this the chain is end-to-end kernel:

    jointPhi_eq_pairExcess_sub_triple  →  tripleD_eq_Ftri
      →  Ftri_peak / Ftri_antitone  →  le_Fbox  →  U1_of_boxcap .

No new geometry enters here: the slice length is `volume_slice_gTrap`,
positivity and continuity of the integrand are `gTrap_nonneg` and
`gTrap_continuous`, and the two changes of variables are already
proved.
-/
module

public import Plank.Proofs.Quant.Slice

@[expose] public section


noncomputable section

open MeasureTheory Set

namespace Quant

/-! ## §1  Measurability -/

theorem isClosed_bandRegion (lam₁ A₀ c₁ S A₂ : ℝ) :
    IsClosed (bandRegion lam₁ A₀ c₁ S A₂) := by
  have hset : bandRegion lam₁ A₀ c₁ S A₂
      = {p : ℝ × ℝ | |p.1 - lam₁ * p.2| ≤ A₀} ∩
        ({p : ℝ × ℝ | |p.2| ≤ c₁} ∩ {p : ℝ × ℝ | |p.1 + S| ≤ A₂}) := by
    ext p
    simp only [bandRegion, mem_inter_iff, mem_setOf_eq]
  rw [hset]
  have h₁ : Continuous fun p : ℝ × ℝ => |p.1 - lam₁ * p.2| := by fun_prop
  have h₂ : Continuous fun p : ℝ × ℝ => |p.2| := by fun_prop
  have h₃ : Continuous fun p : ℝ × ℝ => |p.1 + S| := by fun_prop
  exact (isClosed_le h₁ continuous_const).inter
    ((isClosed_le h₂ continuous_const).inter (isClosed_le h₃ continuous_const))

theorem measurableSet_bandRegion (lam₁ A₀ c₁ S A₂ : ℝ) :
    MeasurableSet (bandRegion lam₁ A₀ c₁ S A₂) :=
  (isClosed_bandRegion lam₁ A₀ c₁ S A₂).measurableSet

/-- Outside the `w`-band the slice is empty. -/
theorem bandRegion_slice_empty (lam₁ A₀ c₁ S A₂ w : ℝ) (hw : ¬ |w + S| ≤ A₂) :
    {v : ℝ | (w, v) ∈ bandRegion lam₁ A₀ c₁ S A₂} = ∅ := by
  ext v
  simp only [bandRegion, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨-, -, h⟩
  exact hw h

/-- The `w`-band is an interval. -/
theorem band_eq_Icc (S A₂ : ℝ) :
    {w : ℝ | |w + S| ≤ A₂} = Icc (-S - A₂) (-S + A₂) := by
  ext w
  simp only [mem_setOf_eq, mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-! ## §2  Fubini -/

/-- **Fubini for the band region.**  Its area is the integral of the
slice length over the `w`-band. -/
theorem volume_bandRegion (lam₀ lam₁ c₀ c₁ S A₂ : ℝ) (hlam₀ : lam₀ ≠ 0)
    (hlam₁ : lam₁ ≠ 0) (hA₂ : 0 ≤ A₂) :
    volume (bandRegion lam₁ (|lam₀| * c₀) c₁ S A₂)
      = ENNReal.ofReal (|lam₀| *
          ∫ w in (-S - A₂)..(-S + A₂),
            gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁| w) := by
  have hcont : Continuous (gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁|) :=
    gTrap_continuous _ _ _
  have hnn : ∀ w, 0 ≤ gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁| w :=
    fun w => gTrap_nonneg _ _ _ (abs_nonneg _) w
  have hle : (-S - A₂) ≤ (-S + A₂) := by linarith
  -- Fubini
  rw [Measure.volume_eq_prod ℝ ℝ,
    Measure.prod_apply (measurableSet_bandRegion _ _ _ _ _)]
  -- the integrand is the slice length, supported on the band
  have hslice : ∀ w : ℝ,
      volume (Prod.mk w ⁻¹' bandRegion lam₁ (|lam₀| * c₀) c₁ S A₂)
      = Set.indicator {w : ℝ | |w + S| ≤ A₂}
        (fun w => ENNReal.ofReal
          (|lam₀| * gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁| w)) w := by
    intro w
    by_cases hw : |w + S| ≤ A₂
    · rw [Set.indicator_of_mem (show w ∈ {w : ℝ | |w + S| ≤ A₂} from hw)]
      have : Prod.mk w ⁻¹' bandRegion lam₁ (|lam₀| * c₀) c₁ S A₂
          = {v : ℝ | |w - lam₁ * v| ≤ |lam₀| * c₀ ∧ |v| ≤ c₁} :=
        bandRegion_slice lam₁ (|lam₀| * c₀) c₁ S A₂ w hw
      rw [this, volume_slice_gTrap lam₀ lam₁ c₀ c₁ w hlam₀ hlam₁]
    · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ | |w + S| ≤ A₂} from hw)]
      have : Prod.mk w ⁻¹' bandRegion lam₁ (|lam₀| * c₀) c₁ S A₂ = ∅ :=
        bandRegion_slice_empty lam₁ (|lam₀| * c₀) c₁ S A₂ w hw
      rw [this, measure_empty]
  rw [lintegral_congr hslice, lintegral_indicator
    (by rw [band_eq_Icc]; exact measurableSet_Icc), band_eq_Icc]
  -- the set-lintegral is the interval integral
  have hint : IntegrableOn
      (fun w => |lam₀| * gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁| w)
      (Icc (-S - A₂) (-S + A₂)) :=
    (hcont.const_mul _).integrableOn_Icc
  have hae : 0 ≤ᵐ[volume.restrict (Icc (-S - A₂) (-S + A₂))]
      fun w => |lam₀| * gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁| w :=
    Filter.Eventually.of_forall fun w => by
      have := hnn w; positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hae]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_const_mul]

/-! ## §3  `hbox`, discharged -/

/-- ★ **`hbox` as a theorem** ★ — the box-density identity. -/
theorem volume_chartRegion_eq_gTrap_integral
    (lam₀ lam₁ lam₂ b₀ c₀ b₁ c₁ b₂ A₂ : ℝ)
    (hlam₀ : lam₀ ≠ 0) (hlam₁ : lam₁ ≠ 0) (hA₂ : 0 ≤ A₂) :
    volume (chartRegion lam₀ lam₁ lam₂ b₀ c₀ b₁ c₁ b₂ A₂)
      = ENNReal.ofReal
        (∫ w in (-(lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂) - A₂)..
                (-(lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂) + A₂),
          gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁| w) := by
  have hnn : ∀ w, 0 ≤ gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁| w :=
    fun w => gTrap_nonneg _ _ _ (abs_nonneg _) w
  have hle : (-(lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂) - A₂)
      ≤ (-(lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂) + A₂) := by linarith
  have hIntNN : 0 ≤ ∫ w in (-(lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂) - A₂)..
      (-(lam₀ * b₀ + lam₁ * b₁ + lam₂ * b₂) + A₂),
      gTrap (|lam₀| * c₀) (|lam₁| * c₁) |lam₀ * lam₁| w :=
    intervalIntegral.integral_nonneg hle fun w _ => hnn w
  have habs₀ : (0:ℝ) < |lam₀| := abs_pos.mpr hlam₀
  rw [volume_chartRegion_eq_centered, volume_centered_eq_band _ _ _ _ _ _ hlam₀,
    volume_bandRegion lam₀ lam₁ c₀ c₁ _ A₂ hlam₀ hlam₁ hA₂,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ## §4  (F-CF), composed -/

/-- ★ **(F-CF) as one kernel theorem** ★  On an unclipped configuration
whose directions satisfy the cofactor dependency, the ledger's triple
term is `Ftri` at the concurrency defect. -/
theorem tripleD_eq_Ftri (C : Config) (lam₀ lam₁ lam₂ : ℝ)
    (hlam₀ : lam₀ ≠ 0) (hlam₁ : lam₁ ≠ 0) (hlam₂ : lam₂ ≠ 0)
    (hdet : (C.plank 0).u.1 * (C.plank 1).u.2
      - (C.plank 0).u.2 * (C.plank 1).u.1 = lam₂)
    (hdep : ∀ q : ℝ × ℝ,
      lam₀ * dot (C.plank 0).u q + lam₁ * dot (C.plank 1).u q
        + lam₂ * dot (C.plank 2).u q = 0)
    (hunclip : (C.plank 0).set ∩ (C.plank 1).set ∩ (C.plank 2).set
      ⊆ stdTriangle.set) :
    tripleD C
      = Ftri (|lam₀| * (C.plank 0).halfWidth) (|lam₁| * (C.plank 1).halfWidth)
          (|lam₂| * (C.plank 2).halfWidth) (|lam₀ * lam₁|) |lam₂|
          (lam₀ * (C.plank 0).center + lam₁ * (C.plank 1).center
            + lam₂ * (C.plank 2).center) := by
  have hA₂ : (0:ℝ) ≤ |lam₂| * (C.plank 2).halfWidth := by
    have := halfWidth_nonneg (C.plank 2); positivity
  have hnn : ∀ w, 0 ≤ gTrap (|lam₀| * (C.plank 0).halfWidth)
      (|lam₁| * (C.plank 1).halfWidth) |lam₀ * lam₁| w :=
    fun w => gTrap_nonneg _ _ _ (abs_nonneg _) w
  have hle : (-(lam₀ * (C.plank 0).center + lam₁ * (C.plank 1).center
        + lam₂ * (C.plank 2).center) - |lam₂| * (C.plank 2).halfWidth)
      ≤ (-(lam₀ * (C.plank 0).center + lam₁ * (C.plank 1).center
        + lam₂ * (C.plank 2).center) + |lam₂| * (C.plank 2).halfWidth) := by
    linarith
  exact tripleD_eq_Ftri_of_boxDensity C lam₀ lam₁ lam₂ hlam₂ hdet hdep hunclip
    (intervalIntegral.integral_nonneg hle fun w _ => hnn w)
    (volume_chartRegion_eq_gTrap_integral lam₀ lam₁ lam₂ (C.plank 0).center
      (C.plank 0).halfWidth (C.plank 1).center (C.plank 1).halfWidth
      (C.plank 2).center (|lam₂| * (C.plank 2).halfWidth) hlam₀ hlam₁ hA₂)

end Quant
