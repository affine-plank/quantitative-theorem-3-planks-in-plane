/- Joint continuity of actual exposed sections under finitely many transverse
moving affine bands, in every finite dimension. -/
module
public import Plank.Proofs.Quant.ConvexSections

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ConvexExposedSections

open Set MeasureTheory MeasureTheory.Measure ConvexSections
open scoped Topology

variable {E ι X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def exposed (K : Set (ℝ × E)) (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ)
    (a b : ι → ℝ) (c : ℝ) : Set E :=
  fiber K c \ ⋃ i ∈ s, (f i) ⁻¹' Icc (a i) (b i)

section Topology

variable [TopologicalSpace X]

theorem eventually_le_iff_of_ne {a b : X → ℝ} {x : X}
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hne : a x ≠ b x) :
    ∀ᶠ t in 𝓝 x, a t ≤ b t ↔ a x ≤ b x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · filter_upwards [ha.eventually_lt hb hlt] with t ht
    exact iff_of_true ht.le hlt.le
  · filter_upwards [hb.eventually_lt ha hgt] with t ht
    exact iff_of_false (not_le_of_gt ht) (not_le_of_gt hgt)

theorem eventually_mem_fiber_iff {K : Set (ℝ × E)} (hK : IsClosed K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) {c : X → ℝ} {x : X}
    (hcx : ContinuousAt c x) (hcint : c x ∈ interior (Prod.fst '' K))
    {y : E} (hy : y ∉ frontier (fiber K (c x))) :
    ∀ᶠ t in 𝓝 x, y ∈ fiber K (c t) ↔ y ∈ fiber K (c x) := by
  have hpath : ContinuousAt (fun t => (c t, y)) x := hcx.prodMk continuousAt_const
  by_cases hymem : y ∈ fiber K (c x)
  · have hyint : y ∈ interior (fiber K (c x)) :=
      (mem_interior_iff_notMem_frontier hymem).2 hy
    rw [interior_fiber_eq hc hi hcint] at hyint
    filter_upwards [hpath.eventually_mem (mem_interior_iff_mem_nhds.1 hyint)] with t ht
    exact iff_of_true ht hymem
  · filter_upwards [hpath.eventually_mem (hK.isOpen_compl.mem_nhds hymem)] with t ht
    exact iff_of_false ht hymem

theorem continuousAt_exposed_indicator {K : Set (ℝ × E)} (hK : IsClosed K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) (s : Finset ι)
    (f : ι → E →ᵃ[ℝ] ℝ) {c : X → ℝ} {a b : ι → X → ℝ} {x : X}
    (hcx : ContinuousAt c x) (hcint : c x ∈ interior (Prod.fst '' K))
    (ha : ∀ i ∈ s, ContinuousAt (a i) x) (hb : ∀ i ∈ s, ContinuousAt (b i) x)
    {y : E} (hy : y ∉ frontier (fiber K (c x)))
    (hya : ∀ i ∈ s, f i y ≠ a i x) (hyb : ∀ i ∈ s, f i y ≠ b i x) :
    ContinuousAt
      (fun t => (exposed K s f (fun i => a i t) (fun i => b i t) (c t)).indicator
        (fun _ => (1 : ℝ)) y) x := by
  classical
  have hev : ∀ᶠ t in 𝓝 x, ∀ i ∈ s,
      (f i y ∈ Icc (a i t) (b i t) ↔ f i y ∈ Icc (a i x) (b i x)) := by
    apply (Filter.eventually_all_finset s).2
    intro i hi
    filter_upwards [eventually_le_iff_of_ne (ha i hi) continuousAt_const (hya i hi).symm,
      eventually_le_iff_of_ne continuousAt_const (hb i hi) (hyb i hi)] with t ht₁ ht₂
    exact and_congr ht₁ ht₂
  apply (show ContinuousAt (fun _ : X =>
    (exposed K s f (fun i => a i x) (fun i => b i x) (c x)).indicator
      (fun _ => (1 : ℝ)) y) x from continuousAt_const).congr_of_eventuallyEq
  filter_upwards [eventually_mem_fiber_iff hK hc hi hcx hcint hy, hev] with t ht hti
  have hm : y ∈ exposed K s f (fun i => a i t) (fun i => b i t) (c t) ↔
      y ∈ exposed K s f (fun i => a i x) (fun i => b i x) (c x) := by
    simp only [exposed, mem_sdiff, mem_iUnion, mem_preimage]
    exact and_congr ht (not_congr (exists_congr fun i => exists_congr fun hi => hti i hi))
  simp only [indicator_apply]
  rw [hm]

end Topology

section Measure

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- A proper affine level set is Haar null, including empty levels of constants. -/
theorem measure_affine_level_eq_zero_of_not_forall (f : E →ᵃ[ℝ] ℝ) (r : ℝ)
    (hf : ¬∀ y, f y=r) : μ {y | f y=r}=0 := by
  let H : AffineSubspace ℝ E := (affineSpan ℝ ({r} : Set ℝ)).comap f
  have hH : H≠⊤ := by
    intro htop
    apply hf
    intro y
    have hy : y∈H := by rw [htop]; trivial
    simpa [H] using hy
  have hset : (H : Set E)={y | f y=r} := by ext y; simp [H]
  rw [←hset]
  exact addHaar_affineSubspace μ H hH

/-- A transverse affine level set is Haar null. -/
theorem measure_affine_level_eq_zero (f : E →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (r : ℝ) :
    μ {y | f y = r} = 0 := by
  apply measure_affine_level_eq_zero_of_not_forall μ f r
  intro h
  exact hf (f.linear_eq_zero_iff_exists_const.mpr ⟨r,by ext y; exact h y⟩)

theorem measurableSet_exposed {K : Set (ℝ × E)} (hK : IsCompact K)
    (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ) (a b : ι → ℝ) (c : ℝ) :
    MeasurableSet (exposed K s f a b c) := by
  apply (compact_fiber hK c).measurableSet.diff
  exact s.finite_toSet.measurableSet_biUnion fun i _ =>
    measurableSet_Icc.preimage (f i).continuous_of_finiteDimensional.measurable

/-- Actual exposed-section measure is jointly continuous in the cut and all endpoints.
There is no ordering or disjointness requirement on the bands. -/
theorem continuousAt_exposed_measure_of_null_levels [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ)
    {c : X → ℝ} {a b : ι → X → ℝ} {x : X}
    (hnulla : ∀ i ∈ s, μ {y | f i y=a i x}=0)
    (hnullb : ∀ i ∈ s, μ {y | f i y=b i x}=0)
    (hcx : ContinuousAt c x) (hcint : c x ∈ interior (Prod.fst '' K))
    (ha : ∀ i ∈ s, ContinuousAt (a i) x) (hb : ∀ i ∈ s, ContinuousAt (b i) x) :
    ContinuousAt
      (fun t => μ.real (exposed K s f (fun i => a i t) (fun i => b i t) (c t))) x := by
  let B : Set E := Prod.snd '' K
  have hB : IsCompact B := hK.image continuous_snd
  have hmeas (t : X) : MeasurableSet
      (exposed K s f (fun i => a i t) (fun i => b i t) (c t)) :=
    measurableSet_exposed hK s f _ _ _
  have hnf : ∀ᵐ y ∂μ, y ∉ frontier (fiber K (c x)) :=
    measure_eq_zero_iff_ae_notMem.1 ((convex_fiber hc (c x)).addHaar_frontier μ)
  have hna : ∀ᵐ y ∂μ, ∀ i ∈ s, f i y ≠ a i x := by
    apply (Filter.eventually_all_finset s).2
    intro i hi
    exact measure_eq_zero_iff_ae_notMem.1 (hnulla i hi)
  have hnb : ∀ᵐ y ∂μ, ∀ i ∈ s, f i y ≠ b i x := by
    apply (Filter.eventually_all_finset s).2
    intro i hi
    exact measure_eq_zero_iff_ae_notMem.1 (hnullb i hi)
  have hcont : ContinuousAt
      (fun t => ∫ y, (exposed K s f (fun i => a i t) (fun i => b i t) (c t)).indicator
        (fun _ => (1 : ℝ)) y ∂μ) x := by
    apply continuousAt_of_dominated (bound := B.indicator (fun _ => (1 : ℝ)))
    · exact Filter.Eventually.of_forall fun t => aestronglyMeasurable_const.indicator (hmeas t)
    · apply Filter.Eventually.of_forall
      intro t
      apply Filter.Eventually.of_forall
      intro y
      by_cases hy : y ∈ exposed K s f (fun i => a i t) (fun i => b i t) (c t)
      · have hyB : y ∈ B := ⟨(c t, y), hy.1, rfl⟩
        simp [hy, hyB]
      · by_cases hyB : y ∈ B <;> simp [hy, hyB]
    · exact (integrableOn_const hB.measure_ne_top).integrable_indicator hB.measurableSet
    · filter_upwards [hnf, hna, hnb] with y hy hya hyb
      exact continuousAt_exposed_indicator hK.isClosed hc hi s f hcx hcint ha hb hy hya hyb
  simpa only [integral_indicator_const (1 : ℝ) (hmeas _), smul_eq_mul, mul_one] using hcont

/-- Transverse bands are a special case of null boundary levels. -/
theorem continuousAt_exposed_measure [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ)
    (hf : ∀ i ∈ s, (f i).linear ≠ 0) {c : X → ℝ} {a b : ι → X → ℝ} {x : X}
    (hcx : ContinuousAt c x) (hcint : c x ∈ interior (Prod.fst '' K))
    (ha : ∀ i ∈ s, ContinuousAt (a i) x) (hb : ∀ i ∈ s, ContinuousAt (b i) x) :
    ContinuousAt
      (fun t => μ.real (exposed K s f (fun i => a i t) (fun i => b i t) (c t))) x :=
  continuousAt_exposed_measure_of_null_levels μ hK hc hi s f
    (fun i hi => measure_affine_level_eq_zero μ (f i) (hf i hi) _)
    (fun i hi => measure_affine_level_eq_zero μ (f i) (hf i hi) _)
    hcx hcint ha hb

end Measure

end Plank.ConvexExposedSections

#print axioms Plank.ConvexExposedSections.continuousAt_exposed_measure
