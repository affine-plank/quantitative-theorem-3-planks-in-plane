/- A continuous concave density with actual interior derivatives for any planar convex body. -/
module

public import Plank.Proofs.Quant.PlanarConvexSectionContinuity
public import Plank.Proofs.Quant.ConcaveDensity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarConvexSectionDensity

open Set MeasureTheory ConvexSections PlanarConvexSectionLength
open PlanarConvexSectionIntegral PlanarConvexSectionContinuity

/-- Constant extension from the closed support interval. It preserves the
actual section values on that interval, including nontrivial support faces. -/
def density (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  length K (max 0 (min 1 t))

theorem density_eq (K : Set (ℝ × ℝ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    density K t = length K t := by
  rw [density,min_eq_right ht.2,max_eq_right ht.1]

theorem continuous_density {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hfull : (interior K).Nonempty)
    (hproj : Prod.fst '' K = Icc (0 : ℝ) 1) : Continuous (density K) := by
  apply (continuousOn_length_unit hK hc hfull hproj).comp_continuous (by fun_prop)
  intro t
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem nonnegative_density (K : Set (ℝ × ℝ)) (t : ℝ) : 0 ≤ density K t :=
  ENNReal.toReal_nonneg

theorem concaveOn_density {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hproj : Prod.fst '' K = Icc (0 : ℝ) 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (density K) := by
  have hh : ConcaveOn ℝ (Icc (0 : ℝ) 1) (length K) := by
    rw [← hproj]
    exact concaveOn_length hK hc
  exact hh.congr fun _ ht => (density_eq K ht).symm

theorem area_slab_eq_integral_density {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (ho : lo ≤ hi) (hhi : hi ≤ 1) :
    (volume (slab K lo hi)).toReal = ∫ t in lo..hi, density K t := by
  rw [area_slab_eq_integral hK ho]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le ho] at ht
  exact (density_eq K ⟨hlo.trans ht.1,ht.2.trans hhi⟩).symm

theorem mass_density {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hproj : Prod.fst '' K = Icc (0 : ℝ) 1) :
    ConcaveDensity.mass (density K) = (volume K).toReal := by
  have hs : slab K 0 1 = K := by
    apply inter_eq_left.mpr
    intro p hp
    have hh : p.1 ∈ Prod.fst '' K := ⟨p,hp,rfl⟩
    rwa [hproj] at hh
  rw [ConcaveDensity.mass,← area_slab_eq_integral_density hK
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1),hs]

/-- The continuously extended density supplies the actual derivative of
the area for every pair of internal cuts. No derivative across a supporting
face is asserted or needed. -/
theorem hasFDerivAt_area_slab_density {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hfull : (interior K).Nonempty)
    (hproj : Prod.fst '' K = Icc (0 : ℝ) 1)
    {lo hi : ℝ} (hlo : 0 < lo) (ho : lo < hi) (hhi : hi < 1) :
    HasFDerivAt (fun p : ℝ × ℝ => (volume (slab K p.1 p.2)).toReal)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (density K hi)-
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (density K lo)) (lo,hi) := by
  rw [density_eq K ⟨(hlo.trans ho).le,hhi.le⟩,
    density_eq K ⟨hlo.le,(ho.trans hhi).le⟩]
  apply hasFDerivAt_area_slab hK hc hfull ho
  · rw [hproj,interior_Icc]
    exact ⟨hlo,ho.trans hhi⟩
  · rw [hproj,interior_Icc]
    exact ⟨hlo.trans ho,hhi⟩

end Plank.PlanarConvexSectionDensity

/-- info: 'Plank.PlanarConvexSectionDensity.continuous_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarConvexSectionDensity.continuous_density
/-- info: 'Plank.PlanarConvexSectionDensity.mass_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarConvexSectionDensity.mass_density
/-- info: 'Plank.PlanarConvexSectionDensity.hasFDerivAt_area_slab_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarConvexSectionDensity.hasFDerivAt_area_slab_density
