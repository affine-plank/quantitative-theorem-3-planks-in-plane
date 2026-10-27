/- Exact equality in the support-plank homothetic-body reduction. -/
module

public import Plank.Proofs.Quant.PlanarInductionBoundary
public import Plank.Proofs.Quant.PlanarGapAnalysis

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSupportGap

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarInductionBoundary

/-- A contracted subbody beyond a support plank accounts for all remaining
area exactly when the two closed covered sets and the subbody cover K.
The conclusion is pointwise, including the boundary of the body. -/
theorem area_eq_iff_cover {K C U : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (hC : IsCompact C) (hU : IsClosed U) (hCK : C ⊆ K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (lo hi : ℝ)
    (hbeyond : ∀ x ∈ C, hi ≤ f x) :
    (volume (C \ U)).toReal = (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪ U))).toReal ↔
      K ⊆ ({x | lo ≤ f x ∧ f x ≤ hi} ∪ U) ∪ C := by
  let P := {x | lo ≤ f x ∧ f x ≤ hi}
  let G := K \ (P ∪ U)
  let A := (C \ U) \ {x | f x = hi}
  have hP : IsClosed P := (isClosed_le continuous_const (continuous_form f)).inter
    (isClosed_le (continuous_form f) continuous_const)
  have hA : MeasurableSet A := (hC.measurableSet.diff hU.measurableSet).diff
    (isClosed_eq (continuous_form f) continuous_const).measurableSet
  have hsub : A ⊆ G := by
    intro x hx
    refine ⟨hCK hx.1.1,?_⟩
    rintro (hband | hu)
    · exact hx.2 (le_antisymm hband.2 (hbeyond x hx.1.1))
    · exact hx.1.2 hu
  have hnull : volume {x | f x = hi} = 0 := measure_level_zero f hf hi
  have hvolA : volume A = volume (C \ U) := measure_sdiff_null hnull
  have hGfin : volume G ≠ ⊤ := ne_top_of_le_ne_top hK.measure_ne_top (measure_mono sdiff_subset)
  have hAfin : volume A ≠ ⊤ := ne_top_of_le_ne_top hGfin (measure_mono hsub)
  constructor
  · intro he
    have hm : volume A = volume G := (ENNReal.toReal_eq_toReal_iff' hAfin hGfin).mp (by
      rw [hvolA]; exact he)
    have hae := ae_eq_of_subset_of_measure_ge hsub hm.ge hA.nullMeasurableSet hGfin
    have hz : volume (G \ A) = 0 := ae_le_set.mp hae.symm.le
    have hmiss : K \ ((P ∪ U) ∪ C) ⊆ G \ A := by
      intro x hx
      refine ⟨⟨hx.1,fun hh => hx.2 (Or.inl hh)⟩,?_⟩
      intro hh
      exact hx.2 (Or.inr hh.1.1)
    apply (PlanarGapAnalysis.area_sdiff_eq_zero_iff_subset hK hconv hV ((hP.union hU).union hC.isClosed)).mp
    rw [measure_mono_null hmiss hz,ENNReal.toReal_zero]
  · intro hcover
    have hsub' : G ⊆ C \ U := by
      intro x hx
      have hc : x ∈ C := (hcover hx.1).resolve_left hx.2
      exact ⟨hc,fun hu => hx.2 (Or.inr hu)⟩
    exact le_antisymm (area_gap_mono_beyond hK hCK f hf lo hi hbeyond)
      (ENNReal.toReal_mono (ne_top_of_le_ne_top hC.measure_ne_top (measure_mono sdiff_subset))
        (measure_mono hsub'))

/-- Pull a physical window back through a positive homothety. -/
theorem homothety_preimage_band (g : Point →ᵃ[ℝ] ℝ) (a : Point) {q : ℝ}
    (hq : 0 < q) (lo hi : ℝ) :
    (AffineMap.homothety a q) ⁻¹' {x | lo ≤ g x ∧ g x ≤ hi} =
      {x | (lo-(1-q)*g a)/q ≤ g x ∧ g x ≤ (hi-(1-q)*g a)/q} := by
  ext x
  change (lo ≤ g (AffineMap.homothety a q x) ∧ g (AffineMap.homothety a q x) ≤ hi) ↔ _
  rw [form_homothety]
  simp only [mem_ofPred_eq,div_le_iff₀ hq,le_div_iff₀ hq]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith only [h₁,h₂]

/-- This is an identity of actual uncovered areas, not a scalar substitute
for the geometry of the homothetic image. -/
theorem area_homothety_gap (K : Set Point) (g : Point →ᵃ[ℝ] ℝ) (a : Point)
    {q : ℝ} (hq : 0 < q) (lo hi : ℝ) :
    (volume ((AffineMap.homothety a q '' K) \ {x | lo ≤ g x ∧ g x ≤ hi})).toReal =
      q^2*(volume (K \ {x | (lo-(1-q)*g a)/q ≤ g x ∧ g x ≤ (hi-(1-q)*g a)/q})).toReal := by
  rw [← image_sdiff_preimage,homothety_preimage_band g a hq lo hi]
  exact area_homothety _ a q

end Plank.PlanarSupportGap

/-- info: 'Plank.PlanarSupportGap.area_eq_iff_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSupportGap.area_eq_iff_cover
/-- info: 'Plank.PlanarSupportGap.area_homothety_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSupportGap.area_homothety_gap
