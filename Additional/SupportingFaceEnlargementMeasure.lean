/- The actual volume added outside the supporting-face cylinder is o(ε).
This is a measured statement about the convex-hull enlargement itself. -/
module
public import SupportingFaceEnlargement
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SupportingFaceEnlargement

open Set Filter MeasureTheory ConvexSections
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def outsideFace (K : Set (ℝ × E)) (b : ℝ) (A : Set E) (ε : ℝ) : Set (ℝ × E) :=
  (enlargement K b A ε\K)\(univ×ˢfiber K b)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem cap_cylinder_subset_added {K : Set (ℝ × E)} {b ε : ℝ}
    (htop : ∀ p∈K,p.1≤b) {A : Set E} (hA : A⊆fiber K b) :
    Ioc b (b+ε)×ˢA ⊆ enlargement K b A ε\K := by
  rintro ⟨t,y⟩ ⟨ht,hy⟩
  have hc' : Convex ℝ {r : ℝ | (r,y)∈enlargement K b A ε} :=
    (convex_enlargement K b A ε).affine_preimage
      ((AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ y))
  have hb : (b,y)∈enlargement K b A ε := subset_enlargement K b A ε (hA hy)
  have hbε : (b+ε,y)∈enlargement K b A ε := subset_convexHull ℝ _ (Or.inr ⟨y,hy,rfl⟩)
  exact ⟨hc'.ordConnected.out hb hbε ⟨ht.1.le,ht.2⟩,fun h => ht.1.not_ge (htop _ h)⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem added_subset_face_cylinder_union_outside {K : Set (ℝ × E)} (hc : Convex ℝ K)
    {b ε : ℝ} (htop : ∀ p∈K,p.1≤b) {A : Set E} (hA : A⊆fiber K b) (hε : 0≤ε) :
    enlargement K b A ε\K ⊆ (Ioc b (b+ε)×ˢfiber K b)∪outsideFace K b A ε := by
  rintro ⟨t,y⟩ ⟨ht,hnot⟩
  by_cases hy : y∈fiber K b
  · obtain ⟨s,hs,hps⟩ := enlargement_vertical_bound hc hA hε _ ht
    have hup := htop _ hps
    refine Or.inl ⟨⟨?_,by dsimp at hup; linarith [hs.2]⟩,hy⟩
    by_contra hn
    have hc' : Convex ℝ {r : ℝ | (r,y)∈K} :=
      hc.affine_preimage ((AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ y))
    exact hnot (hc'.ordConnected.out hps hy ⟨by linarith [hs.1],not_lt.mp hn⟩)
  · exact Or.inr ⟨⟨ht,hnot⟩,fun h => hy h.2⟩

omit [BorelSpace E] in
/-- Bounds for the actual added volume. The upper error is the actual
outside-cylinder volume; its ratio to ε tends to zero in the next theorem. -/
theorem added_volume_bounds (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    {b ε : ℝ} (htop : ∀ p∈K,p.1≤b) {A : Set E} (hA : IsCompact A)
    (hAc : Convex ℝ A) (hAF : A⊆fiber K b) (hε : 0≤ε) :
    ε*ν.real A≤(volume.prod ν).real (enlargement K b A ε\K) ∧
      (volume.prod ν).real (enlargement K b A ε\K)≤ε*ν.real (fiber K b)+
        (volume.prod ν).real (outsideFace K b A ε) := by
  let μ : Measure (ℝ × E) := volume.prod ν
  have hC : μ (enlargement K b A ε\K)≠∞ :=
    measure_ne_top_of_subset sdiff_subset (compact_enlargement hK hc b hA hAc ε).measure_ne_top
  have hO : μ (outsideFace K b A ε)≠∞ := measure_ne_top_of_subset sdiff_subset hC
  have hF : μ (Ioc b (b+ε)×ˢfiber K b)≠∞ :=
    measure_ne_top_of_subset (prod_mono Ioc_subset_Icc_self Subset.rfl)
      (isCompact_Icc.prod (compact_fiber hK b)).measure_ne_top
  have hp (S : Set E) : μ.real (Ioc b (b+ε)×ˢS)=ε*ν.real S := by
    rw [measureReal_prod_prod]
    simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hε]
  constructor
  · rw [←hp A]
    exact measureReal_mono (cap_cylinder_subset_added htop hAF) hC
  · calc μ.real (enlargement K b A ε\K) ≤
          μ.real ((Ioc b (b+ε)×ˢfiber K b)∪outsideFace K b A ε) :=
            measureReal_mono (added_subset_face_cylinder_union_outside hc htop hAF hε)
              (measure_union_lt_top hF.lt_top hO.lt_top).ne
         _ ≤ μ.real (Ioc b (b+ε)×ˢfiber K b)+μ.real (outsideFace K b A ε) := measureReal_union_le _ _
         _ = _ := by rw [hp]

/-- Lifting an inner cap adds only o(ε) volume outside the face cylinder.
No polyhedral description, convex extension or fixed-width assumption occurs. -/
theorem tendsto_outside_volume_div (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty)
    {b : ℝ} (htop : ∀ p∈K,p.1≤b) {A : Set E} (hA : IsCompact A) (hAc : Convex ℝ A)
    (hAi : A⊆interior (fiber K b)) :
    Tendsto (fun ε : ℝ => (volume.prod ν).real (outsideFace K b A ε)/ε)
      (𝓝[>] 0) (𝓝 0) := by
  let D := Prod.snd '' K
  have hD : IsCompact D := hK.image continuous_snd
  have hm (ε : ℝ) : MeasurableSet (outsideFace K b A ε) :=
    ((compact_enlargement hK hc b hA hAc ε).measurableSet.diff hK.measurableSet).diff
      (MeasurableSet.univ.prod (compact_fiber hK b).measurableSet)
  let F : ℝ → E → ℝ≥0∞ := fun ε y => (ENNReal.ofReal ε)⁻¹*
    volume ((fun t : ℝ => (t,y)) ⁻¹' outsideFace K b A ε)
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),∀ᵐ y ∂ν,F ε y≤D.indicator (fun _ => 1) y := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply Eventually.of_forall
    intro y
    by_cases hy : y∈D
    · rw [indicator_of_mem hy]
      have hs : ((fun t : ℝ => (t,y)) ⁻¹' outsideFace K b A ε)⊆
          {t | (t,y)∈enlargement K b A ε\K} := fun _ h => h.1
      have hh := (measure_mono hs).trans
        (volume_added_fiber_le hK hc (hAi.trans interior_subset) hε.le y)
      calc F ε y ≤ (ENNReal.ofReal ε)⁻¹*ENNReal.ofReal ε := by
             simpa only [F,mul_comm] using mul_le_mul_left hh ((ENNReal.ofReal ε)⁻¹)
           _ = 1 := ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top
    · have hz : ((fun t : ℝ => (t,y)) ⁻¹' outsideFace K b A ε)=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        obtain ⟨s,_,hs⟩ := enlargement_vertical_bound hc (hAi.trans interior_subset) hε.le _ ht.1.1
        exact hy ⟨(t-s,y),hs,rfl⟩
      simp [F,hz,hy]
  have hlim : ∀ᵐ y ∂ν,Tendsto (fun ε => F ε y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    filter_upwards [ae_eventually_vertical_fiber_eq ν hK hc hi htop hA hAi] with y hy
    apply tendsto_const_nhds.congr'
    by_cases hyF : y∈fiber K b
    · apply Eventually.of_forall
      intro ε
      have hz : ((fun t : ℝ => (t,y)) ⁻¹' outsideFace K b A ε)=∅ := by
        ext t
        simp [outsideFace,hyF]
      simp [F,hz]
    · filter_upwards [(hy hyF).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with ε hε hεpos
      have hz : ((fun t : ℝ => (t,y)) ⁻¹' outsideFace K b A ε)=∅ := by
        ext t
        simp [outsideFace,hε hεpos.le t]
      simp [F,hz]
  have hh := tendsto_lintegral_filter_of_dominated_convergence
    (μ := ν) (F := F) (f := fun _ => 0) (D.indicator (fun _ => 1))
    (Eventually.of_forall fun ε => measurable_const.mul
      (measurable_measure_prodMk_right (hm ε))) hbound
    (by rw [lintegral_indicator hD.measurableSet]
        simpa only [lintegral_const,one_mul,Measure.restrict_apply_univ] using hD.measure_ne_top (μ := ν)) hlim
  have he (ε : ℝ) : (∫⁻ y,F ε y ∂ν)=
      (ENNReal.ofReal ε)⁻¹*(volume.prod ν) (outsideFace K b A ε) := by
    dsimp only [F]
    rw [lintegral_const_mul _ (measurable_measure_prodMk_right (hm ε)),
      ←Measure.prod_apply_symm (hm ε)]
  simp only [he,lintegral_zero] at hh
  have hr := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞)≠∞)).tendsto.comp hh
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal hε.le,
    div_eq_mul_inv,mul_comm,Measure.real]

end Plank.SupportingFaceEnlargement
