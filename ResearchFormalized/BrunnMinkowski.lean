/- Brunn–Minkowski for coordinate functions, transported from TauCeti's Euclidean theorem. -/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace ResearchFormalized

open Set MeasureTheory
open scoped Pointwise

/-- The standard Brunn–Minkowski inequality in finite real coordinates.
The change from the sup norm to the Euclidean norm preserves addition and volume. -/
theorem pi_brunnMinkowski {ι : Type*} [Fintype ι] (hn : Fintype.card ι ≠ 0)
    {A B : Set (ι → ℝ)} (hA : IsCompact A) (hB : IsCompact B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    volume.real A ^ ((Fintype.card ι : ℝ)⁻¹) +
      volume.real B ^ ((Fintype.card ι : ℝ)⁻¹) ≤
        volume.real (A + B) ^ ((Fintype.card ι : ℝ)⁻¹) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  have hv (S : Set (ι → ℝ)) : volume (e '' S) = volume S := by
    change volume ((MeasurableEquiv.toLp 2 (ι → ℝ)) '' S) = volume S
    rw [MeasurableEquiv.image_eq_preimage_symm]
    exact (PiLp.volume_preserving_ofLp ι).measure_preimage_emb
      (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding S
  have hAe := hA.image e.continuous
  have hBe := hB.image e.continuous
  have h := TauCeti.volume_real_rpow_add_volume_real_rpow_le
    (by simpa only [finrank_euclideanSpace] using hn)
    (hneA.image e) hAe.measurableSet.nullMeasurableSet
    (hneB.image e) hBe.measurableSet.nullMeasurableSet (hAe.add hBe).measure_ne_top
  simpa only [finrank_euclideanSpace, ← Set.image_add e, measureReal_def, hv] using h

end ResearchFormalized
