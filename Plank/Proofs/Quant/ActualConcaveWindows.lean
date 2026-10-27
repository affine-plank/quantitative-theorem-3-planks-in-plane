/- Connect the concave-density contraction inequality to actual body areas. -/
module

public import Plank.Proofs.Quant.PlanarBodySectionDensity
public import Plank.Proofs.Quant.ConcaveDensity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ActualConcaveWindows

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarSevenCellArea
open PlanarBodySectionDensity intervalIntegral
open Plank.Convex.DeficientHeightTilt

/-- The abstract section density integrates to the actual area of each
window. Its derivative data determine the integration constant because an
affine level has zero area. No extra Fubini hypothesis is assumed. -/
theorem coveredArea_eq_integral {K : Set Point} (hK : IsCompact K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (D : BodySectionDensity K f)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (horder : lo ≤ hi) :
    coveredArea K f lo hi = ∫ x in lo..hi, D.density x := by
  have hft := integral_eq_sub_of_hasDerivAt
    (f := fun x => coveredArea K f (-1) x)
    (fun x hx => D.upper_deriv (-1) x (by
      rw [uIcc_of_le horder] at hx
      linarith only [hlo, hx.1])) (D.continuous.intervalIntegrable lo hi)
  let A := K ∩ plank f (-1) lo
  let B := K ∩ plank f lo hi
  have hu : A ∪ B = K ∩ plank f (-1) hi := by
    ext x
    change ((x ∈ K ∧ -1 ≤ f x ∧ f x ≤ lo) ∨
      (x ∈ K ∧ lo ≤ f x ∧ f x ≤ hi)) ↔ (x ∈ K ∧ -1 ≤ f x ∧ f x ≤ hi)
    constructor
    · rintro (⟨hx, h1, h2⟩ | ⟨hx, h1, h2⟩)
      · exact ⟨hx, h1, h2.trans horder⟩
      · exact ⟨hx, by linarith only [hlo, h1], h2⟩
    · rintro ⟨hx, h1, h2⟩
      rcases le_total (f x) lo with hh | hh
      · exact Or.inl ⟨hx, h1, hh⟩
      · exact Or.inr ⟨hx, hh, h2⟩
  have hz : volume (A ∩ B) = 0 := by
    apply measure_mono_null _ (measure_level_zero f hf lo)
    intro x hx
    exact le_antisymm hx.1.2.2 hx.2.2.1
  have hab := measureReal_union_add_inter (μ := volume) (s := A)
    (hK.measurableSet.inter (isClosed_plank f lo hi).measurableSet)
    (measure_ne_top_of_subset inter_subset_left hK.measure_ne_top)
    (measure_ne_top_of_subset inter_subset_left hK.measure_ne_top)
  change (volume (A ∪ B)).toReal+(volume (A ∩ B)).toReal =
    (volume A).toReal+(volume B).toReal at hab
  rw [hu, hz, ENNReal.toReal_zero, add_zero] at hab
  change coveredArea K f (-1) hi = coveredArea K f (-1) lo+coveredArea K f lo hi at hab
  linarith only [hft, hab]

theorem density_mass {K : Set Point} (hK : IsCompact K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (D : BodySectionDensity K f)
    (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) :
    ConcaveDensity.mass D.density = (volume K).toReal := by
  have hs : K ∩ plank f 0 1 = K := inter_eq_left.mpr hnorm
  rw [ConcaveDensity.mass, ← coveredArea_eq_integral hK f hf D (by norm_num) (by norm_num),
    coveredArea, hs]

/-- Actual covered area satisfies the canonical-window contraction bound.
The centre is a coordinate in the body's unit support interval. -/
theorem coveredArea_contraction {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (D : BodySectionDensity K f)
    (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) (hunit : rangeWidth K f = 1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    coveredArea K f ((1-t*r)*c) (c+(1-c)*(t*r)) ≤
      t^2*coveredArea K f ((1-r)*c) (c+(1-c)*r)+
        2*t*r*(1-t)*(volume K).toReal := by
  have hf : f.linear ≠ 0 := linear_ne_zero_of_rangeWidth_pos hne f (by rw [hunit]; norm_num)
  have hw (s : ℝ) (hs : s ∈ Icc 0 1) :
      0 ≤ (1-s)*c ∧ (1-s)*c ≤ c+(1-c)*s := by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr hs.2) hc.1
    · nlinarith only [hs.1]
  have htr : t*r ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ht.1 hr.1, (mul_le_of_le_one_left hr.1 ht.2).trans hr.2⟩
  rw [coveredArea_eq_integral hK f hf D (hw _ htr).1 (hw _ htr).2,
    coveredArea_eq_integral hK f hf D (hw _ hr).1 (hw _ hr).2]
  have hh := ConcaveDensity.canonical_window_scaling D.density D.continuous
    (D.concave_unit hK hconv hne hnorm hunit) (D.nonnegative 0) (D.nonnegative 1) hc ht hr
  rwa [density_mass hK f hf D hnorm] at hh

end Plank.ActualConcaveWindows
