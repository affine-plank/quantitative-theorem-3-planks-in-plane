/- Uncovered volume in thin cylinders over an actual supporting face. -/
module
public import SupportingFaceEnlargementMeasure
public import Plank.Proofs.Quant.ConvexExposedSections

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SupportingFaceResidual

open Set Filter MeasureTheory ConvexSections ConvexExposedSections
open SupportingFaceEnlargement
open scoped Topology ENNReal

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The thin-cylinder limit needs only an almost everywhere locally constant
vertical coverage trace. No boundary regularity of the base is required. -/
theorem tendsto_cylinder_residual_div (ν : Measure E) [ν.IsAddHaarMeasure]
    {F : Set E} (hF : IsCompact F) {U : Set (ℝ × E)} (hU : MeasurableSet U) (b : ℝ)
    (htrace : ∀ᵐ y ∂ν,∀ᶠ t in 𝓝 b,(t,y)∈U ↔ (b,y)∈U) :
    Tendsto (fun ε : ℝ => (volume.prod ν).real ((Ioc b (b+ε)×ˢF)\U)/ε)
      (𝓝[>] 0) (𝓝 (ν.real (F\Prod.mk b ⁻¹' U))) := by
  let S : ℝ → Set (ℝ × E) := fun ε => (Ioc b (b+ε)×ˢF)\U
  let D := F\Prod.mk b ⁻¹' U
  have hD : MeasurableSet D := hF.measurableSet.diff
    (hU.preimage (continuous_const.prodMk continuous_id).measurable)
  have hm (ε : ℝ) : MeasurableSet (S ε) :=
    (measurableSet_Ioc.prod hF.measurableSet).diff hU
  let G : ℝ → E → ℝ≥0∞ := fun ε y => (ENNReal.ofReal ε)⁻¹*
    volume ((fun t : ℝ => (t,y)) ⁻¹' S ε)
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),∀ᵐ y ∂ν,G ε y≤F.indicator (fun _ => 1) y := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply Eventually.of_forall
    intro y
    by_cases hy : y∈F
    · rw [indicator_of_mem hy]
      have hs : ((fun t : ℝ => (t,y)) ⁻¹' S ε)⊆Ioc b (b+ε) := fun _ h => h.1.1
      have hh : volume ((fun t : ℝ => (t,y)) ⁻¹' S ε)≤ENNReal.ofReal ε := by
        simpa using measure_mono (μ := volume) hs
      calc G ε y≤(ENNReal.ofReal ε)⁻¹*ENNReal.ofReal ε := by
             simpa only [G,mul_comm] using mul_le_mul_left hh ((ENNReal.ofReal ε)⁻¹)
           _ = 1 := ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top
    · have hz : ((fun t : ℝ => (t,y)) ⁻¹' S ε)=∅ := by ext t; simp [S,hy]
      simp [G,hz,hy]
  have hlim : ∀ᵐ y ∂ν,Tendsto (fun ε => G ε y) (𝓝[>] (0 : ℝ))
      (𝓝 (D.indicator (fun _ => 1) y)) := by
    filter_upwards [htrace] with y hy
    obtain ⟨l,u,⟨hl,hu⟩,hs⟩ := hy.exists_Ioo_subset
    apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ)<u-b by linarith)),
      self_mem_nhdsWithin] with ε hεu hε
    change ε<u-b at hεu
    have he (t : ℝ) (ht : t∈Ioc b (b+ε)) : (t,y)∈U ↔ (b,y)∈U :=
      hs ⟨by linarith [ht.1],by linarith [ht.2]⟩
    by_cases hyF : y∈F
    · by_cases hyU : (b,y)∈U
      · have hz : ((fun t : ℝ => (t,y)) ⁻¹' S ε)=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact ht.2 ((he t ht.1.1).mpr hyU)
        simp [G,hz,D,hyU]
      · have hz : ((fun t : ℝ => (t,y)) ⁻¹' S ε)=Ioc b (b+ε) := by
          ext t
          exact ⟨fun h => h.1.1,fun ht => ⟨⟨ht,hyF⟩,fun h => hyU ((he t ht).mp h)⟩⟩
        simp [G,hz,D,hyF,hyU,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top]
    · have hz : ((fun t : ℝ => (t,y)) ⁻¹' S ε)=∅ := by ext t; simp [S,hyF]
      simp [G,hz,D,hyF]
  have hh := tendsto_lintegral_filter_of_dominated_convergence
    (μ := ν) (F := G) (f := D.indicator (fun _ => 1)) (F.indicator (fun _ => 1))
    (Eventually.of_forall fun ε => measurable_const.mul
      (measurable_measure_prodMk_right (hm ε))) hbound
    (by rw [lintegral_indicator hF.measurableSet]
        simpa only [lintegral_const,one_mul,Measure.restrict_apply_univ] using hF.measure_ne_top (μ := ν)) hlim
  have he (ε : ℝ) : (∫⁻ y,G ε y ∂ν)=(ENNReal.ofReal ε)⁻¹*(volume.prod ν) (S ε) := by
    dsimp only [G]
    rw [lintegral_const_mul _ (measurable_measure_prodMk_right (hm ε)),←Measure.prod_apply_symm (hm ε)]
  have hd : (∫⁻ y,D.indicator (fun _ => (1 : ℝ≥0∞)) y ∂ν)=ν D := by
    rw [lintegral_indicator hD,lintegral_const,one_mul,Measure.restrict_apply_univ]
  simp only [he,hd] at hh
  have hr := (ENNReal.continuousAt_toReal (measure_ne_top_of_subset sdiff_subset hF.measure_ne_top)).tendsto.comp hh
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal hε.le,
    div_eq_mul_inv,mul_comm,Measure.real,S]

/-- A finite union of affine planks has locally constant vertical membership
almost everywhere when no boundary hyperplane contains the entire section. -/
theorem ae_eventually_plank_mem_iff (ν : Measure E) [ν.IsAddHaarMeasure]
    (b : ℝ) (s : Finset ι) (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hsep : ∀ j∈s,(¬∀ y,f j (b,y)=lo j) ∧ (¬∀ y,f j (b,y)=hi j)) :
    ∀ᵐ y ∂ν,∀ᶠ t in 𝓝 b,
      (t,y)∈(⋃ i∈s,(f i) ⁻¹' Icc (lo i) (hi i)) ↔
        (b,y)∈(⋃ i∈s,(f i) ⁻¹' Icc (lo i) (hi i)) := by
  classical
  have hn (j : ι) (v : ℝ) (hv : ¬∀ y,f j (b,y)=v) : ∀ᵐ y ∂ν,f j (b,y)≠v := by
    let g : E →ᵃ[ℝ] ℝ := (f j).comp ((AffineMap.const ℝ E b).prod (AffineMap.id ℝ E))
    exact measure_eq_zero_iff_ae_notMem.mp (measure_affine_level_eq_zero_of_not_forall ν g v hv)
  have hna : ∀ᵐ y ∂ν,∀ j∈s,f j (b,y)≠lo j :=
    (Filter.eventually_all_finset s).mpr fun j hj => hn j _ (hsep j hj).1
  have hnb : ∀ᵐ y ∂ν,∀ j∈s,f j (b,y)≠hi j :=
    (Filter.eventually_all_finset s).mpr fun j hj => hn j _ (hsep j hj).2
  filter_upwards [hna,hnb] with y hya hyb
  have hev : ∀ᶠ t in 𝓝 b,∀ j∈s,
      f j (t,y)∈Icc (lo j) (hi j) ↔ f j (b,y)∈Icc (lo j) (hi j) := by
    apply (Filter.eventually_all_finset s).mpr
    intro j hj
    have hf : ContinuousAt (fun t : ℝ => f j (t,y)) b :=
      ((f j).continuous_of_finiteDimensional.comp (continuous_id.prodMk continuous_const)).continuousAt
    filter_upwards [eventually_le_iff_of_ne continuousAt_const hf (hya j hj).symm,
      eventually_le_iff_of_ne hf continuousAt_const (hyb j hj)] with t hl hu
    exact and_congr hl hu
  filter_upwards [hev] with t ht
  simp only [mem_iUnion,mem_preimage]
  exact exists_congr fun j => exists_congr fun hj => ht j hj

/-- The actual uncovered thin-cylinder volume converges to the uncovered
section area for any finite family of noncoincident affine plank boundaries. -/
theorem tendsto_plank_cylinder_residual_div (ν : Measure E) [ν.IsAddHaarMeasure]
    {F : Set E} (hF : IsCompact F) (b : ℝ) (s : Finset ι)
    (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hsep : ∀ j∈s,(¬∀ y,f j (b,y)=lo j) ∧ (¬∀ y,f j (b,y)=hi j)) :
    Tendsto (fun ε : ℝ => (volume.prod ν).real
      ((Ioc b (b+ε)×ˢF)\(⋃ i∈s,(f i) ⁻¹' Icc (lo i) (hi i)))/ε)
      (𝓝[>] 0) (𝓝 (ν.real (F\Prod.mk b ⁻¹' (⋃ i∈s,(f i) ⁻¹' Icc (lo i) (hi i))))) := by
  apply tendsto_cylinder_residual_div ν hF
    (s.finite_toSet.measurableSet_biUnion fun i _ =>
      measurableSet_Icc.preimage (f i).continuous_of_finiteDimensional.measurable) b
  exact ae_eventually_plank_mem_iff ν b s f lo hi hsep

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Actual added uncovered volume is bounded by the uncovered face cylinder
plus the entire outside-cylinder error. -/
theorem added_residual_le (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    {b ε : ℝ} (htop : ∀ p∈K,p.1≤b) {A : Set E} (hA : IsCompact A)
    (hAc : Convex ℝ A) (hAF : A⊆fiber K b) (hε : 0≤ε) (U : Set (ℝ × E)) :
    (volume.prod ν).real ((enlargement K b A ε\K)\U)≤
      (volume.prod ν).real ((Ioc b (b+ε)×ˢfiber K b)\U)+
        (volume.prod ν).real (outsideFace K b A ε) := by
  let μ : Measure (ℝ × E) := volume.prod ν
  have hO : μ (outsideFace K b A ε)≠∞ := measure_ne_top_of_subset
    (sdiff_subset.trans sdiff_subset) (compact_enlargement hK hc b hA hAc ε).measure_ne_top
  have hF : μ ((Ioc b (b+ε)×ˢfiber K b)\U)≠∞ := measure_ne_top_of_subset
    (sdiff_subset.trans (prod_mono Ioc_subset_Icc_self Subset.rfl))
    (isCompact_Icc.prod (compact_fiber hK b)).measure_ne_top
  have hs : (enlargement K b A ε\K)\U⊆
      ((Ioc b (b+ε)×ˢfiber K b)\U)∪outsideFace K b A ε := by
    intro p hp
    rcases added_subset_face_cylinder_union_outside hc htop hAF hε hp.1 with h | h
    · exact Or.inl ⟨h,hp.2⟩
    · exact Or.inr h
  exact (measureReal_mono hs (measure_union_lt_top hF.lt_top hO.lt_top).ne).trans
    (measureReal_union_le _ _)

/-- A linear lower bound on the actual enlargement's uncovered volume
forces the same lower bound on the original supporting section. -/
theorem le_section_of_added_lower (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty)
    {b : ℝ} (htop : ∀ p∈K,p.1≤b) {A : Set E} (hA : IsCompact A)
    (hAc : Convex ℝ A) (hAi : A⊆interior (fiber K b))
    {U : Set (ℝ × E)} (hU : MeasurableSet U)
    (htrace : ∀ᵐ y ∂ν,∀ᶠ t in 𝓝 b,(t,y)∈U ↔ (b,y)∈U)
    {a : ℝ} (hlower : ∀ ε>0,a*ε≤(volume.prod ν).real ((enlargement K b A ε\K)\U)) :
    a≤ν.real (fiber (K\U) b) := by
  have ht := (tendsto_cylinder_residual_div ν (compact_fiber hK b) hU b htrace).add
    (tendsto_outside_volume_div ν hK hc hi htop hA hAc hAi)
  simp only [add_zero] at ht
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [←add_div]
  apply (le_div_iff₀ hε).mpr
  exact (hlower ε hε).trans (added_residual_le ν hK hc htop hA hAc (hAi.trans interior_subset) hε.le U)

/-- Compact convex inner copies recover the full measure of a compact
convex face, including faces with empty interior and zero measure. -/
theorem le_of_forall_inner_caps (ν : Measure E) [ν.IsAddHaarMeasure]
    {F : Set E} (hF : IsCompact F) (hc : Convex ℝ F) {q z : ℝ}
    (hbound : ∀ A : Set E,IsCompact A → Convex ℝ A → A⊆interior F → q*ν.real A≤z) :
    q*ν.real F≤z := by
  by_cases hi : (interior F).Nonempty
  · obtain ⟨x,hx⟩ := hi
    have hv (r : ℝ) : ν.real (AffineMap.homothety x r '' F)=
        abs (r^Module.finrank ℝ E)*ν.real F := by
      rw [Measure.real,Measure.addHaar_image_homothety,ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg _)]
      rfl
    have ht : Tendsto (fun r : ℝ => q*(abs (r^Module.finrank ℝ E)*ν.real F))
        (𝓝[<] 1) (𝓝 (q*ν.real F)) := by
      simpa using ((show Continuous (fun r : ℝ => q*(abs (r^Module.finrank ℝ E)*ν.real F)) from by fun_prop).tendsto 1).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ)<1 by norm_num)),
      self_mem_nhdsWithin] with r hr hr1
    rw [←hv]
    apply hbound _ (hF.image (AffineMap.homothety x r).continuous_of_finiteDimensional)
      (hc.affine_image (AffineMap.homothety x r))
    rintro _ ⟨y,hy,rfl⟩
    rw [AffineMap.homothety_eq_lineMap,AffineMap.lineMap_apply_module]
    exact hc.combo_interior_self_mem_interior hx hy (sub_pos.mpr hr1) hr.le (by ring)
  · have hz : ν F=0 := by
      simpa [frontier,hF.isClosed.closure_eq,not_nonempty_iff_eq_empty.mp hi] using hc.addHaar_frontier ν
    simpa [Measure.real,hz] using hbound ∅ isCompact_empty convex_empty (empty_subset _)

end Plank.SupportingFaceResidual
