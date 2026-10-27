/- The direct sharp bound for any finite parallel family. -/
module

public import Plank.Proofs.Quant.PlanarParallelTranslations

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelBound

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarParallelTranslations
open scoped Pointwise

variable {ι : Type*} [Fintype ι]

theorem uncovered_area_lower_bound {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hR1 : total lo hi < 1) (f : Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0) :
    (1-total lo hi)^2*(volume K).toReal ≤
      (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal := by
  classical
  let core := (1-total lo hi) • K
  have hR : 0 ≤ total lo hi := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (ho i))
  have hc : IsCompact core := hK.image (f := fun x : Point => (1-total lo hi) • x) (by fun_prop)
  have hf : f.linear ≠ 0 := by
    intro hz
    obtain ⟨c,hh⟩ := f.linear_eq_zero_iff_exists_const.mp hz
    have he : f a = f b := by rw [hh]; rfl
    rw [hfa,hfb] at he
    norm_num at he
  have hinside (s : Finset ι) (x : Point) (hx : x ∈ core) : x+translations lo hi a b s ∈ K := by
    rcases hR.eq_or_lt with hz | hp
    · have hs : selected lo hi s = 0 := by
        have hh := selected_bounds lo hi ho s
        linarith only [hh.1,hh.2,hz]
      have hv : translations lo hi a b s = 0 := by simp [translations,← hz,hs]
      rw [hv,add_zero]
      simpa only [core,← hz,sub_zero,one_smul] using hx
    · exact translated_inside hconv lo hi ho hp hR1 a b ha hb s x hx
  have hm := LinearBands.measure_le_closed_gap_of_translations volume
    (fun _ : ι => (f : Point → ℝ)) (fun _ => (continuous_form f).measurable)
    lo hi ho (fun i => measure_level_zero f hf (lo i)) (fun i => measure_level_zero f hf (hi i))
    core hc.measurableSet (translations lo hi a b)
    (fun x _ => weak_assignments lo hi ho f a b hfa hfb x) K hinside
  have hfin : volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i)) ≠ ⊤ :=
    ne_top_of_le_ne_top hK.measure_ne_top (measure_mono sdiff_subset)
  have hr := ENNReal.toReal_mono hfin hm
  have harea : (volume core).toReal = (1-total lo hi)^2*(volume K).toReal := by
    rw [volume.addHaar_smul_of_nonneg (sub_pos.mpr hR1).le,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (sub_pos.mpr hR1).le _)]
    simp only [Module.finrank_pi,Fintype.card_fin]
  rwa [harea] at hr

end Plank.PlanarParallelBound

/-- info: 'Plank.PlanarParallelBound.uncovered_area_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelBound.uncovered_area_lower_bound
