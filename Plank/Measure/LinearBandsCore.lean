module
/-
# Exterior cells and null boundaries of finite families of bands

The measure arguments use arbitrary finite index types. In finite-dimensional
real normed spaces, a nonzero continuous linear functional has null level sets.
This includes the zero-width bands that disappear from open-plank formulations.
-/
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Plank.LinearBands

open Set MeasureTheory Function

variable {E ι : Type*}

def closedBand (f : E → ℝ) (lo hi : ℝ) : Set E :=
  {x | lo ≤ f x ∧ f x ≤ hi}

def openBand (f : E → ℝ) (lo hi : ℝ) : Set E :=
  {x | lo < f x ∧ f x < hi}

def strictCell (f : ι → E → ℝ) (lo hi : ι → ℝ) (s : Finset ι) : Set E := by
  classical
  exact {x | ∀ i, if i ∈ s then hi i < f i x else f i x < lo i}

def weakCell (f : ι → E → ℝ) (lo hi : ι → ℝ) (s : Finset ι) : Set E := by
  classical
  exact {x | ∀ i, if i ∈ s then hi i ≤ f i x else f i x ≤ lo i}

theorem disjoint_strictCells (f : ι → E → ℝ) (lo hi : ι → ℝ)
    (hwidth : ∀ i, lo i ≤ hi i) : Pairwise (Disjoint on strictCell f lo hi) := by
  classical
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  apply hst
  ext i
  have hsi := hs i
  have hti := ht i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [his, hit, ↓reduceIte] at hsi hti ⊢
  · linarith [hwidth i]
  · linarith [hwidth i]

theorem disjoint_weakCells (f : ι → E → ℝ) (lo hi : ι → ℝ)
    (hwidth : ∀ i, lo i < hi i) : Pairwise (Disjoint on weakCell f lo hi) := by
  classical
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  apply hst
  ext i
  have hsi := hs i
  have hti := ht i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [his, hit, ↓reduceIte] at hsi hti ⊢
  · linarith [hwidth i]
  · linarith [hwidth i]

theorem strictCell_subset_gap (f : ι → E → ℝ) (lo hi : ι → ℝ) (s : Finset ι) :
    strictCell f lo hi s ⊆ (⋃ i, closedBand (f i) (lo i) (hi i))ᶜ := by
  classical
  intro x hx hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
  have h := hx i
  by_cases his : i ∈ s <;> simp only [his, ↓reduceIte] at h
  · exact (not_lt_of_ge hi.2) h
  · exact (not_lt_of_ge hi.1) h

theorem weakCell_subset_gap (f : ι → E → ℝ) (lo hi : ι → ℝ) (s : Finset ι) :
    weakCell f lo hi s ⊆ (⋃ i, openBand (f i) (lo i) (hi i))ᶜ := by
  classical
  intro x hx hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
  have h := hx i
  by_cases his : i ∈ s <;> simp only [his, ↓reduceIte] at h
  · exact (not_lt_of_ge h) hi.2
  · exact (not_lt_of_ge h) hi.1

/-- Outside null boundary levels, all open and closed bands in a countable
family have the same membership. No measurability of the functions is needed. -/
theorem ae_mem_closedBand_iff_openBand [MeasurableSpace E] [Countable ι]
    (μ : Measure E) (f : ι → E → ℝ) (lo hi : ι → ℝ)
    (hlo : ∀ i, μ {x | f i x = lo i} = 0) (hhi : ∀ i, μ {x | f i x = hi i} = 0) :
    ∀ᵐ x ∂μ, ∀ i, x ∈ closedBand (f i) (lo i) (hi i) ↔
      x ∈ openBand (f i) (lo i) (hi i) := by
  apply ae_all_iff.mpr
  intro i
  have hl : ∀ᵐ x ∂μ, f i x ≠ lo i := by simpa only [ae_iff, not_not] using hlo i
  have hh : ∀ᵐ x ∂μ, f i x ≠ hi i := by simpa only [ae_iff, not_not] using hhi i
  filter_upwards [hl, hh] with x hxl hxh
  exact ⟨fun h => ⟨lt_of_le_of_ne h.1 hxl.symm, lt_of_le_of_ne h.2 hxh⟩,
    fun h => ⟨h.1.le, h.2.le⟩⟩

section Measurable

variable [MeasurableSpace E] [Fintype ι]

theorem measurableSet_strictCell (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i))
    (lo hi : ι → ℝ) (s : Finset ι) : MeasurableSet (strictCell f lo hi s) := by
  classical
  rw [strictCell, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases his : i ∈ s
  · simpa [his] using measurableSet_lt measurable_const (hf i)
  · simpa [his] using measurableSet_lt (hf i) measurable_const

theorem measurableSet_weakCell (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i))
    (lo hi : ι → ℝ) (s : Finset ι) : MeasurableSet (weakCell f lo hi s) := by
  classical
  rw [weakCell, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases his : i ∈ s
  · simpa [his] using measurableSet_le measurable_const (hf i)
  · simpa [his] using measurableSet_le (hf i) measurable_const

/-- Null boundary levels make closed and open plank complements equal in measure,
including zero-width planks. No positivity or nondegeneracy of the body is needed. -/
theorem measure_closed_gap_eq_open_gap (μ : Measure E) (f : ι → E → ℝ)
    (lo hi : ι → ℝ) (hlo : ∀ i, μ {x | f i x = lo i} = 0)
    (hhi : ∀ i, μ {x | f i x = hi i} = 0) (K : Set E) :
    μ (K \ ⋃ i, closedBand (f i) (lo i) (hi i)) =
      μ (K \ ⋃ i, openBand (f i) (lo i) (hi i)) := by
  apply measure_congr
  filter_upwards [ae_mem_closedBand_iff_openBand μ f lo hi hlo hhi] with x hx
  simp only [mem_sdiff, mem_iUnion, hx]

end Measurable

/-- Every affine level of a nonzero functional is Haar-null. -/
theorem measure_level_zero [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E →L[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    μ {x | f x = c} = 0 := by
  classical
  have hker : f.toLinearMap.ker ≠ ⊤ := by
    intro h
    apply hf
    ext x
    exact LinearMap.congr_fun (LinearMap.ker_eq_top.mp h) x
  by_cases hne : ∃ z, f z = c
  · obtain ⟨z, hz⟩ := hne
    have hset : {x | f x = c} =
        (fun x => x + -z) ⁻¹' (f.toLinearMap.ker : Set E) := by
      ext x
      change f x = c ↔ f (x + -z) = 0
      simp only [map_add, map_neg, add_neg_eq_zero, hz]
    rw [hset, measure_preimage_add_right]
    exact Measure.addHaar_submodule μ f.toLinearMap.ker hker
  · have hset : {x | f x = c} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨x, h⟩
    rw [hset, measure_empty]

end Plank.LinearBands
