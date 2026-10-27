/- Inward convex section-moment comparison at an arbitrary supporting plane.
No convex extension and no polyhedral representation is assumed. -/
module
public import SupportingSectionTrace
public import SupportingCutVariation

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.GlobalSupportingCut

open Set MeasureTheory Filter PrunedPlankCounterexample GlobalPlankBodyMinimum
open MovingAffineCut SupportingSectionTrace GlobalBodyTiltEquilibrium
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

omit [BorelSpace E] [Fintype ι] in
/-- A positive-volume body lying below a plane has a point strictly below it. -/
theorem below_of_positive_volume (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hV : 0<(volume.prod ν).real K) {b : ℝ}
    (htop : ∀ p∈K,p.1≤b) : ∃ p∈K,p.1<b := by
  by_contra! hn
  have hs : K⊆({b} ×ˢ (univ : Set E)) := by
    intro p hp
    exact ⟨le_antisymm (htop p hp) (hn p hp),mem_univ _⟩
  have hz : (volume.prod ν) ({b} ×ˢ (univ : Set E))=0 := by
    rw [Measure.prod_prod]
    simp
  have hKz := measure_mono_null hs hz
  simp [Measure.real,hKz] at hV

/-- Every nonnegative continuous convex test function satisfies the section
comparison at an actual supporting plane, even without a convex extension.
Both selected extrema still need witnesses strictly below the plane. -/
theorem convex_moment_le (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    (b : ℝ) (htop : ∀ p∈K,p.1≤b) (y : E) (hyK : (b,y)∈K)
    (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i,lo i≤hi i)
    (hV : 0<(volume.prod ν).real K) (hW : ∀ i,0<Body.width K (f i))
    (P Q : ι → ℝ × E) (hP : ∀ i,P i∈K) (hQ : ∀ i,Q i∈K)
    (hmax : ∀ i,∀ x∈K,f i x≤f i (P i)) (hmin : ∀ i,∀ x∈K,f i (Q i)≤f i x)
    (hPb : ∀ i,(P i).1<b) (hQb : ∀ i,(Q i).1<b)
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum (volume.prod ν) K f lo hi d B)
    (h : E → ℝ) (hh : Continuous h) (hnonneg : ∀ y,(b,y)∈K → 0≤h y)
    (hconv : ConvexOn ℝ univ h) :
    (∫ y in Prod.mk b ⁻¹' (K\covered f lo hi),h y ∂ν)≤
      (volume.prod ν).real (K\covered f lo hi)/(volume.prod ν).real K*
        ∫ y in Prod.mk b ⁻¹' K,h y ∂ν := by
  classical
  let T := traceExtension K b
  have hT : IsCompact T := compact_traceExtension hK b
  have hbelow := below_of_positive_volume ν hV htop
  let C : ℝ → Set (ℝ × E) := cut T h b
  have hCe {t : ℝ} (ht : t≤0) : C t=cut K h b t :=
    cut_traceExtension K b h hnonneg ht
  let q := (volume.prod ν).real (K\covered f lo hi)/(volume.prod ν).real K
  have hC0 : C 0=K := by
    rw [hCe le_rfl]
    ext p
    simp only [cut,zero_mul,add_zero,mem_inter_iff,mem_ofPred_eq]
    exact ⟨And.left,fun hp => ⟨hp,htop p hp⟩⟩
  have hsep (j) : (¬∀ z,f j (b,z)=lo j) ∧ (¬∀ z,f j (b,z)=hi j) :=
    ⟨GlobalBodyCutEquilibrium.nonconstant_on_cut (f j) hyK (hW j)
      (hP j) (hQ j) (hmax j) (hmin j) (hPb j) (hQb j) _,
     GlobalBodyCutEquilibrium.nonconstant_on_cut (f j) hyK (hW j)
      (hP j) (hQ j) (hmax j) (hmin j) (hPb j) (hQb j) _⟩
  have hD := hasDerivAt_compact_area ν hT hT.measurableSet Subset.rfl hh b
    (ae_continuousAt_traceExtension_indicator ν hK hc b hbelow)
  have hR := hasDerivAt_compact_area ν hT
    (NoncoincidentCutDerivatives.measurable_residual hT.measurableSet Finset.univ f lo hi)
    sdiff_subset hh b
    (ae_continuousAt_residual_trace ν hK hc b hbelow Finset.univ f lo hi (fun j _ => hsep j))
  have hgap (t : ℝ) : C t\covered f lo hi=
      cut (NoncoincidentCutDerivatives.residual T Finset.univ f lo hi) h b t := by
    ext p
    simp only [C,cut,covered,NoncoincidentCutDerivatives.residual,
      mem_inter_iff,Set.mem_sdiff,mem_iUnion,Finset.mem_univ,exists_const]
    tauto
  have hG : HasDerivAt (fun t => (volume.prod ν).real (C t\covered f lo hi))
      (∫ z in Prod.mk b ⁻¹' NoncoincidentCutDerivatives.residual T Finset.univ f lo hi,
        h z ∂ν) 0 :=
    hR.congr_of_eventuallyEq (Eventually.of_forall fun t => congrArg (volume.prod ν).real (hgap t))
  have hpos : ∀ᶠ t in 𝓝 0,0<(volume.prod ν).real (C t) :=
    hD.continuousAt.eventually (Ioi_mem_nhds (by change 0<(volume.prod ν).real (C 0); rwa [hC0]))
  have hpoints : ∀ᶠ t in 𝓝 0,∀ i,P i∈C t ∧ Q i∈C t := by
    apply Filter.eventually_all.2
    intro i
    have hp : ∀ᶠ t : ℝ in 𝓝 0,(P i).1<b+t*h (P i).2 :=
      (show Continuous (fun t : ℝ => b+t*h (P i).2) from by fun_prop).continuousAt.eventually
        (Ioi_mem_nhds (by simpa using hPb i))
    have hq : ∀ᶠ t : ℝ in 𝓝 0,(Q i).1<b+t*h (Q i).2 :=
      (show Continuous (fun t : ℝ => b+t*h (Q i).2) from by fun_prop).continuousAt.eventually
        (Ioi_mem_nhds (by simpa using hQb i))
    have hPL : P i∈T := Or.inl (hP i)
    have hQL : Q i∈T := Or.inl (hQ i)
    filter_upwards [hp,hq] with t ht hu
    exact ⟨⟨hPL,ht.le⟩,⟨hQL,hu.le⟩⟩
  have hzero : (volume.prod ν).real (C 0\covered f lo hi)-q*(volume.prod ν).real (C 0)=0 := by
    rw [hC0]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hV.ne').symm
  have hlocal : ∀ᶠ t in 𝓝 (0 : ℝ),t≤0 → 0≤(volume.prod ν).real (C t\covered f lo hi)-
      q*(volume.prod ν).real (C t) := by
    filter_upwards [hpos,hpoints] with t ht hp
    intro ht0
    apply sub_nonneg.mpr
    have hw (i) : Body.width K (f i)≤Body.width (C t) (f i) := by
      rw [Body.width_eq_of_realisers (hP i) (hQ i) (hmax i) (hmin i)]
      exact Body.sub_le_width (compact_cut_continuous hT h hh b t) (f i).continuous_of_finiteDimensional
        (hp i).1 (hp i).2
    exact (le_div_iff₀ ht).mp (ratio_le_of_width_le (volume.prod ν)
      (compact_cut_continuous hT h hh b t)
      (by change Convex ℝ (C t); rw [hCe ht0]; exact convex_cut_of_convex hc h hconv b ht0)
      ht f lo hi horder hW hw d hbudget hglobal)
  have hz : (∫ z in Prod.mk b ⁻¹' NoncoincidentCutDerivatives.residual T Finset.univ f lo hi,
      h z ∂ν)-q*(∫ z in Prod.mk b ⁻¹' T,h z ∂ν)≤0 := by
    apply le_of_tendsto (hG.sub (hD.const_mul q)).tendsto_slope_zero_left
    filter_upwards [hlocal.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht ht0
    simp only [zero_add,smul_eq_mul]
    change t⁻¹*((volume.prod ν).real (C t\covered f lo hi)-q*(volume.prod ν).real (C t)-
      ((volume.prod ν).real (C 0\covered f lo hi)-q*(volume.prod ν).real (C 0)))≤0
    rw [hzero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr ht0.le) (ht ht0.le)
  have hs : Prod.mk b ⁻¹' K=Prod.mk b ⁻¹' T := (fiber_traceExtension K b).symm
  have hr : Prod.mk b ⁻¹' (K\covered f lo hi)=
      Prod.mk b ⁻¹' NoncoincidentCutDerivatives.residual T Finset.univ f lo hi := by
    simp only [preimage_sdiff,hs,NoncoincidentCutDerivatives.residual,
      covered,Finset.mem_univ,iUnion_true]
  rw [hr,hs]
  exact sub_nonpos.mp hz

end Plank.GlobalSupportingCut
