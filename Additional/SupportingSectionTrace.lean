/- One-sided traces at a supporting hyperplane of an arbitrary convex body.
The auxiliary cylinder is measurable and compact, not asserted convex. -/
module
public import MovingAffineCut

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SupportingSectionTrace

open Set Filter MeasureTheory ConvexSections ConvexExposedSections
open NoncoincidentCutDerivatives MovingAffineCut
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An interior point of the top section has a vertical segment entering K.
Only convexity and one point below the section are needed. -/
theorem exists_vertical_segment {K : Set (ℝ × E)} (hc : Convex ℝ K)
    {b : ℝ} (hbelow : ∃ p∈K,p.1<b) {y : E} (hy : y∈interior (fiber K b)) :
    ∃ a<b,∀ t∈Icc a b,(t,y)∈K := by
  obtain ⟨p,hp,hpb⟩ := hbelow
  have he : ∀ᶠ u : ℝ in 𝓝 0,y+u • (y-p.2)∈fiber K b := by
    have ht : Tendsto (fun u : ℝ => y+u • (y-p.2)) (𝓝 0) (𝓝 y) := by
      simpa using (show Continuous (fun u : ℝ => y+u • (y-p.2)) from by fun_prop).tendsto 0
    exact ht.eventually_mem (mem_interior_iff_mem_nhds.mp hy)
  obtain ⟨u,hu,hw⟩ := he.exists_gt
  let c : ℝ := 1/(u+1)
  let a : ℝ := (c*u)*p.1+c*b
  have hden : 0<u+1 := by linarith
  have hcpos : 0<c := one_div_pos.mpr hden
  have hsum : c*u+c=1 := by dsimp [c]; field_simp
  have hpoint : (a,y)=(c*u) • p+c • (b,y+u • (y-p.2)) := by
    apply Prod.ext
    · rfl
    · change y=(c*u) • p.2+c • (y+u • (y-p.2))
      rw [smul_add,smul_smul,smul_sub]
      have hs : c • y+(c*u) • y=y := by rw [←add_smul,add_comm,hsum,one_smul]
      exact hs.symm.trans (by abel)
  have haK : (a,y)∈K := by
    rw [hpoint]
    exact hc hp hw (mul_nonneg hcpos.le hu.le) hcpos.le hsum
  have hab : a<b := by
    dsimp [a]
    nlinarith only [mul_pos (mul_pos hcpos hu) (sub_pos.mpr hpb),
      congrArg (fun r : ℝ => r*b) hsum]
  have hl : Convex ℝ {t : ℝ | (t,y)∈K} :=
    hc.affine_preimage ((AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ y))
  have hbK : (b,y)∈K := (show y∈fiber K b from interior_subset hy)
  exact ⟨a,hab,fun t ht => hl.ordConnected.out haK hbK ht⟩

/-- Fill above the supporting section only to make a two-sided analytic trace.
No convexity claim is made for this auxiliary set. -/
def traceExtension (K : Set (ℝ × E)) (b : ℝ) : Set (ℝ × E) :=
  K∪(Icc b (b+1) ×ˢ fiber K b)

omit [NormedSpace ℝ E] in
theorem compact_traceExtension {K : Set (ℝ × E)} (hK : IsCompact K) (b : ℝ) :
    IsCompact (traceExtension K b) :=
  hK.union (isCompact_Icc.prod (compact_fiber hK b))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem fiber_traceExtension (K : Set (ℝ × E)) (b : ℝ) :
    fiber (traceExtension K b) b=fiber K b := by
  ext y
  simp [fiber,traceExtension]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A nonnegative inward cut never sees the added cylinder. -/
theorem cut_traceExtension (K : Set (ℝ × E)) (b : ℝ)
    (h : E → ℝ) (hh : ∀ y∈fiber K b,0≤h y) {t : ℝ} (ht : t≤0) :
    cut (traceExtension K b) h b t=cut K h b t := by
  ext p
  constructor
  · rintro ⟨hp,hcut⟩
    refine ⟨?_,hcut⟩
    rcases hp with hp | ⟨⟨hl,_⟩,hy⟩
    · exact hp
    · change p.1≤b+t*h p.2 at hcut
      have he : p.1=b := le_antisymm (by linarith [mul_nonpos_of_nonpos_of_nonneg ht (hh p.2 hy)]) hl
      have hp' : (b,p.2)=p := Prod.ext he.symm rfl
      change (b,p.2)∈K at hy
      rwa [hp'] at hy
  · rintro ⟨hp,ht⟩
    exact ⟨Or.inl hp,ht⟩

/-- The artificial extension's vertical trace is locally constant away from
the boundary of the actual supporting section. -/
theorem eventually_mem_traceExtension_iff {K : Set (ℝ × E)} (hK : IsClosed K)
    (hc : Convex ℝ K) {b : ℝ} (hbelow : ∃ p∈K,p.1<b)
    {y : E} (hy : y∉frontier (fiber K b)) :
    ∀ᶠ t in 𝓝 b,(t,y)∈traceExtension K b ↔ (b,y)∈K := by
  by_cases hm : y∈fiber K b
  · obtain ⟨a,hab,ha⟩ := exists_vertical_segment hc hbelow
      ((mem_interior_iff_notMem_frontier hm).mpr hy)
    filter_upwards [Ioo_mem_nhds hab (show b<b+1 by linarith)] with t ht
    apply iff_of_true ?_ hm
    by_cases htb : t≤b
    · exact Or.inl (ha t ⟨ht.1.le,htb⟩)
    · exact Or.inr ⟨⟨(not_le.mp htb).le,ht.2.le⟩,hm⟩
  · have hev : ∀ᶠ t in 𝓝 b,(t,y)∉K :=
      (continuous_id.prodMk continuous_const).continuousAt.eventually_mem
        (hK.isOpen_compl.mem_nhds hm)
    filter_upwards [hev] with t ht
    exact iff_of_false (by simpa [traceExtension,hm] using ht) hm

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (ν : Measure E) [ν.IsAddHaarMeasure]

theorem ae_continuousAt_traceExtension_indicator {K : Set (ℝ × E)}
    (hK : IsCompact K) (hc : Convex ℝ K) (b : ℝ) (hbelow : ∃ p∈K,p.1<b) :
    ∀ᵐ y ∂ν,ContinuousAt (fun t =>
      (traceExtension K b).indicator (fun _ => (1 : ℝ)) (t,y)) b := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp ((convex_fiber hc b).addHaar_frontier ν)] with y hy
  apply (continuousAt_const : ContinuousAt (fun _ : ℝ => K.indicator (fun _ => (1 : ℝ)) (b,y)) b).congr_of_eventuallyEq
  filter_upwards [eventually_mem_traceExtension_iff hK.isClosed hc hbelow hy] with t ht
  by_cases hm : (b,y)∈K
  · simp [ht.mpr hm,hm]
  · simp [show (t,y)∉traceExtension K b from mt ht.mp hm,hm]

/-- Noncoincident plank levels give the same continuous artificial trace for
the actual residual. The original body need not have a convex extension. -/
theorem ae_continuousAt_residual_trace {K : Set (ℝ × E)}
    (hK : IsCompact K) (hc : Convex ℝ K) (b : ℝ) (hbelow : ∃ p∈K,p.1<b)
    (s : Finset ι) (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hsep : ∀ j∈s,(¬∀ y,f j (b,y)=lo j) ∧ (¬∀ y,f j (b,y)=hi j)) :
    ∀ᵐ y ∂ν,ContinuousAt (fun t =>
      (residual (traceExtension K b) s f lo hi).indicator (fun _ => (1 : ℝ)) (t,y)) b := by
  classical
  have hn (j : ι) (v : ℝ) (hv : ¬∀ y,f j (b,y)=v) : ∀ᵐ y ∂ν,f j (b,y)≠v := by
    let g : E →ᵃ[ℝ] ℝ := (f j).comp ((AffineMap.const ℝ E b).prod (AffineMap.id ℝ E))
    exact measure_eq_zero_iff_ae_notMem.mp (measure_affine_level_eq_zero_of_not_forall ν g v hv)
  have hna : ∀ᵐ y ∂ν,∀ j∈s,f j (b,y)≠lo j :=
    (Filter.eventually_all_finset s).mpr fun j hj => hn j _ (hsep j hj).1
  have hnb : ∀ᵐ y ∂ν,∀ j∈s,f j (b,y)≠hi j :=
    (Filter.eventually_all_finset s).mpr fun j hj => hn j _ (hsep j hj).2
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp ((convex_fiber hc b).addHaar_frontier ν),hna,hnb]
    with y hy hya hyb
  have hev : ∀ᶠ t in 𝓝 b,∀ j∈s,
      (lo j≤f j (t,y) ∧ f j (t,y)≤hi j) ↔ (lo j≤f j (b,y) ∧ f j (b,y)≤hi j) := by
    apply (Filter.eventually_all_finset s).mpr
    intro j hj
    have hf : ContinuousAt (fun t : ℝ => f j (t,y)) b :=
      ((f j).continuous_of_finiteDimensional.comp (continuous_id.prodMk continuous_const)).continuousAt
    filter_upwards [eventually_le_iff_of_ne continuousAt_const hf (hya j hj).symm,
      eventually_le_iff_of_ne hf continuousAt_const (hyb j hj)] with t hl hu
    exact and_congr hl hu
  apply (continuousAt_const : ContinuousAt (fun _ : ℝ =>
    (residual K s f lo hi).indicator (fun _ => (1 : ℝ)) (b,y)) b).congr_of_eventuallyEq
  filter_upwards [eventually_mem_traceExtension_iff hK.isClosed hc hbelow hy,hev] with t ht hj
  have hm : (t,y)∈residual (traceExtension K b) s f lo hi ↔ (b,y)∈residual K s f lo hi := by
    simp only [NoncoincidentCutDerivatives.residual,Set.mem_sdiff,mem_iUnion,mem_ofPred_eq]
    exact and_congr ht (not_congr (exists_congr fun j => exists_congr fun hj' => hj j hj'))
  by_cases hz : (b,y)∈NoncoincidentCutDerivatives.residual K s f lo hi
  · simp [hm.mpr hz,hz]
  · simp [show (t,y)∉NoncoincidentCutDerivatives.residual (traceExtension K b) s f lo hi from mt hm.mp hz,hz]

end Plank.SupportingSectionTrace
