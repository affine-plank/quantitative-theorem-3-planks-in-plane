/- Interior geometry and actual Haar measure continuity of convex sections.
The geometric lemmas hold in arbitrary real normed spaces; the measure theorem
uses finite dimensionality, compactness and nonempty ambient interior. -/
module
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ConvexSections

open Set MeasureTheory MeasureTheory.Measure
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An open continuous linear map preserves interiors of convex sets with nonempty interior. -/
theorem image_interior_eq (f : E →L[ℝ] F) (hf : IsOpenMap f)
    {K : Set E} (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    f '' interior K = interior (f '' K) := by
  apply Subset.antisymm (hf.image_interior_subset K)
  have ho : IsOpen (f '' interior K) := hf _ isOpen_interior
  have hconv : Convex ℝ (f '' interior K) := hc.interior.linear_image f.toLinearMap
  have hne : (interior (f '' interior K)).Nonempty := by
    rw [ho.interior_eq]
    exact hi.image f
  have hsub : f '' K ⊆ closure (f '' interior K) := by
    have hk : K ⊆ closure (interior K) := by
      rw [hc.closure_interior_eq_closure_of_nonempty_interior hi]
      exact subset_closure
    exact (image_mono hk).trans
      (image_closure_subset_closure_image f.continuous)
  simpa only [hconv.interior_closure_eq_interior_of_nonempty_interior hne,
    ho.interior_eq] using interior_mono hsub

/-- If an affine slice meets the ambient interior, its own interior is exactly that slice
of the ambient interior. Only continuity is needed for the reverse inclusion. -/
theorem interior_preimage_eq (f : E →ᵃ[ℝ] F) (hf : Continuous f)
    {K : Set F} (hc : Convex ℝ K) (hi : (f ⁻¹' interior K).Nonempty) :
    interior (f ⁻¹' K) = f ⁻¹' interior K := by
  apply Subset.antisymm ?_ (preimage_interior_subset_interior_preimage hf)
  intro y hy
  obtain ⟨x, hx⟩ := hi
  have h := AffineMap.lineMap_apply_one (k := ℝ) x y
  obtain ⟨t, ht1, ht⟩ := AffineMap.lineMap_continuous.tendsto' _ _ h |>.eventually_mem
    (mem_interior_iff_mem_nhds.1 hy) |>.exists_gt
  apply hc.openSegment_interior_self_subset_interior hx ht
  rw [← image_openSegment]
  refine ⟨y, ?_, rfl⟩
  nth_rw 1 [← AffineMap.lineMap_apply_zero (k := ℝ) x y, ← image_openSegment]
  exact ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, ht1⟩, h⟩

def fiber (K : Set (ℝ × E)) (c : ℝ) : Set E := Prod.mk c ⁻¹' K

theorem interior_fiber_eq {K : Set (ℝ × E)} (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) {c : ℝ} (hcint : c ∈ interior (Prod.fst '' K)) :
    interior (fiber K c) = fiber (interior K) c := by
  have hproj : Prod.fst '' interior K = interior (Prod.fst '' K) :=
    image_interior_eq (ContinuousLinearMap.fst ℝ ℝ E) isOpenMap_fst hc hi
  obtain ⟨p, hp, hpc⟩ := hproj.symm ▸ hcint
  let f : E →ᵃ[ℝ] ℝ × E := (AffineMap.const ℝ E c).prod (AffineMap.id ℝ E)
  exact interior_preimage_eq f (continuous_const.prodMk continuous_id) hc
    ⟨p.2, by change (c, p.2) ∈ interior K; rw [← hpc]; exact hp⟩

theorem convex_fiber {K : Set (ℝ × E)} (hc : Convex ℝ K) (c : ℝ) :
    Convex ℝ (fiber K c) :=
  hc.affine_preimage ((AffineMap.const ℝ E c).prod (AffineMap.id ℝ E))

omit [NormedSpace ℝ E] in
theorem compact_fiber {K : Set (ℝ × E)} (hK : IsCompact K) (c : ℝ) :
    IsCompact (fiber K c) := by
  apply (hK.image continuous_snd).of_isClosed_subset
    (hK.isClosed.preimage (continuous_const.prodMk continuous_id))
  intro y hy
  exact ⟨(c, y), hy, rfl⟩

/-- Off the boundary of the limiting fiber, section membership is locally constant in the cut. -/
theorem continuousAt_fiber_indicator {K : Set (ℝ × E)} (hK : IsClosed K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) {c : ℝ}
    (hcint : c ∈ interior (Prod.fst '' K)) {y : E} (hy : y ∉ frontier (fiber K c)) :
    ContinuousAt (fun t => (fiber K t).indicator (fun _ => (1 : ℝ)) y) c := by
  have hpath : Continuous (fun t : ℝ => (t, y)) := continuous_id.prodMk continuous_const
  by_cases hymem : y ∈ fiber K c
  · have hyint : y ∈ interior (fiber K c) :=
      (mem_interior_iff_notMem_frontier hymem).2 hy
    rw [interior_fiber_eq hc hi hcint] at hyint
    have hevent : ∀ᶠ t in 𝓝 c, (t, y) ∈ K :=
      hpath.continuousAt.eventually_mem (mem_interior_iff_mem_nhds.1 hyint)
    apply (show ContinuousAt (fun _ : ℝ => (1 : ℝ)) c from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [hevent] with t ht
    exact indicator_of_mem (show y ∈ fiber K t from ht) _
  · have hevent : ∀ᶠ t in 𝓝 c, (t, y) ∉ K :=
      hpath.continuousAt.eventually_mem (hK.isOpen_compl.mem_nhds hymem)
    apply (show ContinuousAt (fun _ : ℝ => (0 : ℝ)) c from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [hevent] with t ht
    exact indicator_of_notMem (show y ∉ fiber K t from ht) _

section Measure

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- The actual Haar measure of a compact convex section is continuous at every interior cut.
The body may have flat faces; no strict convexity or smoothness is assumed. -/
theorem continuousAt_section_measure {K : Set (ℝ × E)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) {c : ℝ}
    (hcint : c ∈ interior (Prod.fst '' K)) :
    ContinuousAt (fun t => μ.real (fiber K t)) c := by
  let B : Set E := Prod.snd '' K
  have hB : IsCompact B := hK.image continuous_snd
  have hmeas (t : ℝ) : MeasurableSet (fiber K t) := (compact_fiber hK t).measurableSet
  have hnf : ∀ᵐ y ∂μ, y ∉ frontier (fiber K c) :=
    measure_eq_zero_iff_ae_notMem.1 ((convex_fiber hc c).addHaar_frontier μ)
  have hcont : ContinuousAt
      (fun t => ∫ y, (fiber K t).indicator (fun _ => (1 : ℝ)) y ∂μ) c := by
    apply continuousAt_of_dominated (bound := B.indicator (fun _ => (1 : ℝ)))
    · exact Filter.Eventually.of_forall fun t => aestronglyMeasurable_const.indicator (hmeas t)
    · apply Filter.Eventually.of_forall
      intro t
      apply Filter.Eventually.of_forall
      intro y
      by_cases hy : y ∈ fiber K t
      · have hyB : y ∈ B := ⟨(t, y), hy, rfl⟩
        simp [hy, hyB]
      · by_cases hyB : y ∈ B <;> simp [hy, hyB]
    · exact (integrableOn_const hB.measure_ne_top).integrable_indicator hB.measurableSet
    · filter_upwards [hnf] with y hy
      exact continuousAt_fiber_indicator hK.isClosed hc hi hcint hy
  simpa only [integral_indicator_const (1 : ℝ) (hmeas _), smul_eq_mul, mul_one] using hcont

end Measure

end Plank.ConvexSections

#print axioms Plank.ConvexSections.interior_fiber_eq
#print axioms Plank.ConvexSections.continuousAt_section_measure
