/- Removing zero-width windows preserves gap measure and relative budget. -/
module

public import GlobalPlankMergeMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ActivePlankRestriction

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]

omit [FiniteDimensional ℝ E] in
theorem budget_restrict (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (ho : ∀ i,lo i≤hi i) :
    budget K (fun i : {i // lo i<hi i} => f i) (fun i => lo i) (fun i => hi i)=
      budget K f lo hi := by
  classical
  unfold budget
  rw [←Finset.sum_subtype (Finset.univ.filter fun i => lo i<hi i) (by simp)
    (fun i => (hi i-lo i)/Body.width K (f i))]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hn
  have hz : hi i=lo i := le_antisymm (le_of_not_gt (by simpa using hn)) (ho i)
  simp [hz]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Only the discarded affine hyperplanes are null; no genericity of
directions, boundary positions or remaining intersections is assumed. -/
theorem gap_restrict_to (p : ι → Prop) [DecidablePred p]
    (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hf : ∀ i,(f i).linear≠0) (hzero : ∀ i,¬p i → hi i≤lo i) :
    μ.real (K\covered (fun i : {i // p i} => f i) (fun i => lo i) (fun i => hi i))=
      μ.real (K\covered f lo hi) := by
  classical
  let bad : Set E := ⋃ i : {i // ¬p i},{x | f i x=lo i}
  have hbad : μ bad=0 := measure_iUnion_null fun i =>
    ConvexExposedSections.measure_affine_level_eq_zero μ (f i) (hf i) (lo i)
  have he : (K\covered (fun i : {i // p i} => f i) (fun i => lo i) (fun i => hi i))\bad=
      (K\covered f lo hi)\bad := by
    ext x
    constructor
    · rintro ⟨⟨hx,hout⟩,hgood⟩
      refine ⟨⟨hx,?_⟩,hgood⟩
      intro hin
      obtain ⟨i,hi'⟩ := mem_iUnion.mp hin
      by_cases hp : p i
      · exact hout (mem_iUnion.mpr ⟨⟨i,hp⟩,hi'⟩)
      · apply hgood
        apply mem_iUnion.mpr
        exact ⟨⟨i,hp⟩,le_antisymm (hi'.2.trans (hzero i hp)) hi'.1⟩
    · rintro ⟨⟨hx,hout⟩,hgood⟩
      refine ⟨⟨hx,?_⟩,hgood⟩
      rintro hin
      obtain ⟨i,hi'⟩ := mem_iUnion.mp hin
      exact hout (mem_iUnion.mpr ⟨i.val,hi'⟩)
  apply congrArg ENNReal.toReal
  exact (measure_sdiff_null hbad).symm.trans ((congrArg μ he).trans (measure_sdiff_null hbad))

theorem gap_restrict (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hf : ∀ i,(f i).linear≠0) :
    μ.real (K\covered (fun i : {i // lo i<hi i} => f i) (fun i => lo i) (fun i => hi i))=
      μ.real (K\covered f lo hi) :=
  gap_restrict_to μ (fun i => lo i<hi i) K f lo hi hf (fun _ h => le_of_not_gt h)

end Plank.ActivePlankRestriction
