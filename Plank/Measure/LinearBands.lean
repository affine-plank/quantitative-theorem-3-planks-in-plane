/- Exterior cells and null boundaries, with the finite-translation gap bound.
Import LinearBandsCore when only the elementary band and level-set facts are needed. -/
module

public import Plank.Measure.LinearBandsCore
public import Plank.Measure.FiniteTranslations

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.LinearBands

open Set MeasureTheory Function

variable {E ι : Type*}

/-- Weak side assignments give a closed-plank gap bound after deleting finitely
many null translated levels. Widths may vanish, and translations need not be sums. -/
theorem measure_le_closed_gap_of_translations [AddGroup E] [MeasurableSpace E]
    [MeasurableAdd E] [Fintype ι] (μ : Measure E) [μ.IsAddRightInvariant]
    (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i)) (lo hi : ι → ℝ)
    (hwidth : ∀ i, lo i ≤ hi i)
    (hlo : ∀ i, μ {x | f i x = lo i} = 0)
    (hhi : ∀ i, μ {x | f i x = hi i} = 0)
    (core : Set E) (hcore : MeasurableSet core) (v : Finset ι → E)
    (hassign : ∀ t ∈ core, ∃ s, t + v s ∈ weakCell f lo hi s)
    (K : Set E) (hinside : ∀ s t, t ∈ core → t + v s ∈ K) :
    μ core ≤ μ (K \ ⋃ i, closedBand (f i) (lo i) (hi i)) := by
  classical
  let bad : Set E := ⋃ s : Finset ι, ⋃ i : ι,
    {x | f i (x + v s) = lo i} ∪ {x | f i (x + v s) = hi i}
  have hbad : μ bad = 0 := by
    apply measure_iUnion_null
    intro s
    apply measure_iUnion_null
    intro i
    apply measure_union_null
    · change μ ((fun x => x + v s) ⁻¹' {x | f i x = lo i}) = 0
      rw [measure_preimage_add_right, hlo]
    · change μ ((fun x => x + v s) ⁻¹' {x | f i x = hi i}) = 0
      rw [measure_preimage_add_right, hhi]
  have hbadm : MeasurableSet bad := by
    apply MeasurableSet.iUnion
    intro s
    apply MeasurableSet.iUnion
    intro i
    exact (measurableSet_eq_fun ((hf i).comp (measurable_add_const _)) measurable_const).union
      (measurableSet_eq_fun ((hf i).comp (measurable_add_const _)) measurable_const)
  rw [← measure_sdiff_null hbad]
  apply FiniteTranslations.measure_le_of_translations μ (core \ bad) (hcore.diff hbadm) v
    (strictCell f lo hi) (measurableSet_strictCell f hf lo hi)
    (disjoint_strictCells f lo hi hwidth)
  · intro x hx
    obtain ⟨s, hs⟩ := hassign x hx.1
    refine ⟨s, ?_⟩
    intro i
    have h := hs i
    by_cases his : i ∈ s <;> simp only [his, ↓reduceIte] at h ⊢
    · apply lt_of_le_of_ne h
      intro heq
      exact hx.2 (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨i, Or.inr heq.symm⟩⟩)
    · apply lt_of_le_of_ne h
      intro heq
      exact hx.2 (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨i, Or.inl heq⟩⟩)
  · intro s x hx hcell
    exact ⟨hinside s x hx.1, strictCell_subset_gap f lo hi s hcell⟩

end Plank.LinearBands
