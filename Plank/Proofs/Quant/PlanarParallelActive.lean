/- Zero-width parallel planks can be removed without changing either
the total width or the actual uncovered area. -/
module

public import Plank.Proofs.Quant.PlanarParallelPositive

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelActive

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarParallelTranslations

variable {ι : Type*} [Fintype ι]

abbrev Active (lo hi : ι → ℝ) := {i // lo i < hi i}

attribute [local instance] Classical.propDecidable

theorem total_active (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i) :
    total (fun i : Active lo hi => lo i.1) (fun i => hi i.1) = total lo hi := by
  classical
  have hz : (∑ i : {j : ι // ¬(lo j < hi j)}, (hi i.1-lo i.1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact sub_eq_zero.mpr (le_antisymm (le_of_not_gt i.2) (ho i.1))
  have hh := Fintype.sum_subtype_add_sum_subtype (fun i => lo i < hi i) (fun i => hi i-lo i)
  simpa only [total,widths,Active,hz,add_zero] using hh

theorem active_nonempty (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hR : 0 < total lo hi) : Nonempty (Active lo hi) := by
  by_contra hnone
  have hz (i) : widths lo hi i = 0 := by
    have hh : ¬lo i < hi i := fun hp => hnone ⟨⟨i,hp⟩⟩
    exact sub_eq_zero.mpr (le_antisymm (le_of_not_gt hh) (ho i))
  have ht : total lo hi = 0 := Finset.sum_eq_zero (fun i _ => hz i)
  rw [ht] at hR
  exact lt_irrefl 0 hR

/-- This equality concerns Lebesgue area, so arbitrary null lines are
retained in the original configuration while omitted from its active part. -/
theorem gap_eq_active (K : Set Point) (lo hi : ι → ℝ) (_ho : ∀ i, lo i ≤ hi i)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) :
    volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i)) =
      volume (K \ ⋃ i : Active lo hi, LinearBands.closedBand f (lo i.1) (hi i.1)) := by
  classical
  let bad : Set Point := ⋃ i : {i // ¬lo i < hi i}, {x | f x = lo i.1}
  have hbad : volume bad = 0 := measure_iUnion_null (fun i => measure_level_zero f hf (lo i.1))
  apply measure_congr
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hbad] with x hx
  apply propext
  constructor
  · rintro ⟨hK,hn⟩
    refine ⟨hK,?_⟩
    intro hh
    obtain ⟨i,hi'⟩ := mem_iUnion.mp hh
    exact hn (mem_iUnion.mpr ⟨i.1,hi'⟩)
  · rintro ⟨hK,hn⟩
    refine ⟨hK,?_⟩
    intro hh
    obtain ⟨i,hi'⟩ := mem_iUnion.mp hh
    by_cases hp : lo i < hi i
    · exact hn (mem_iUnion.mpr ⟨⟨i,hp⟩,hi'⟩)
    · apply hx
      refine mem_iUnion.mpr ⟨⟨i,hp⟩,?_⟩
      change f x = lo i
      exact le_antisymm (hi'.2.trans (le_of_not_gt hp)) hi'.1

end Plank.PlanarParallelActive

/-- info: 'Plank.PlanarParallelActive.gap_eq_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelActive.gap_eq_active
