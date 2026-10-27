/- Almost-everywhere continuity at internal convex cuts, including bodies
with empty ambient interior. -/
module
public import MovingAffineCut
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.InternalCutTrace

open Set MeasureTheory Filter ConvexSections
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A proper affine subspace containing a point off a cut cannot contain
the whole cut hyperplane. -/
theorem comap_cut_ne_top (A : AffineSubspace ℝ (ℝ × E)) (hA : A≠⊤)
    {p : ℝ × E} (hp : p∈A) {b : ℝ} (hb : p.1≠b) :
    A.comap ((AffineMap.const ℝ E b).prod (AffineMap.id ℝ E))≠⊤ := by
  intro he
  have hall (y : E) : (b,y)∈A := by
    have hy : y∈A.comap ((AffineMap.const ℝ E b).prod (AffineMap.id ℝ E)) := by
      rw [he]
      exact AffineSubspace.mem_top ℝ E y
    exact hy
  apply hA
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨p,hp⟩).mp
  apply top_unique
  intro w _
  have hv : (p.1-b,(0 : E))∈A.direction := by
    have hh := AffineSubspace.vsub_mem_direction hp (hall p.2)
    change (p.1-b,p.2-p.2)∈A.direction at hh
    simpa only [sub_self] using hh
  have hy : ((0 : ℝ),w.2)∈A.direction := by
    have hh := AffineSubspace.vsub_mem_direction (hall w.2) (hall 0)
    change (b-b,w.2-0)∈A.direction at hh
    simpa only [sub_self,sub_zero] using hh
  have hw : w=(w.1/(p.1-b)) • (p.1-b,(0 : E))+(0,w.2) := by
    ext <;> simp [div_mul_cancel₀ _ (sub_ne_zero.mpr hb)]
  rw [hw]
  exact A.direction.add_mem (A.direction.smul_mem _ hv) hy

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure]

/-- If a convex body has empty ambient interior, every internal section
has zero transverse Haar measure. -/
theorem measure_fiber_eq_zero_of_empty_interior {K : Set (ℝ × E)}
    (hc : Convex ℝ K) (hthin : ¬(interior K).Nonempty) {b : ℝ}
    (hcut : b∈interior (Prod.fst '' K)) : ν (fiber K b)=0 := by
  have hnear : ∀ᶠ t in 𝓝 b,t∈Prod.fst '' K := mem_interior_iff_mem_nhds.mp hcut
  obtain ⟨t,hbt,p,hp,hpt⟩ := hnear.exists_gt
  have hspan : affineSpan ℝ K≠⊤ := fun he =>
    hthin (hc.interior_nonempty_iff_affineSpan_eq_top.mpr he)
  have hproper := comap_cut_ne_top (affineSpan ℝ K) hspan
    (subset_affineSpan ℝ K hp) (show p.1≠b by rw [hpt]; exact ne_of_gt hbt)
  apply measure_mono_null (t := ((affineSpan ℝ K).comap
    ((AffineMap.const ℝ E b).prod (AffineMap.id ℝ E)) : Set E))
  · intro y hy
    exact subset_affineSpan ℝ K hy
  · exact MeasureTheory.Measure.addHaar_affineSubspace ν _ hproper

/-- The actual vertical indicator is almost everywhere continuous at an
internal cut. No nonempty-interior hypothesis is required. -/
theorem ae_continuousAt_indicator {K : Set (ℝ × E)} (hK : IsClosed K)
    (hc : Convex ℝ K) {b : ℝ} (hcut : b∈interior (Prod.fst '' K)) :
    ∀ᵐ y ∂ν, ContinuousAt (fun t : ℝ => K.indicator (fun _ => (1 : ℝ)) (t,y)) b := by
  by_cases hfull : (interior K).Nonempty
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1
      ((convex_fiber hc b).addHaar_frontier ν)] with y hy
    have hh := continuousAt_fiber_indicator hK hc hfull hcut hy
    apply hh.congr_of_eventuallyEq
    exact Eventually.of_forall fun t => by
      by_cases hy : (t,y)∈K <;> simp [fiber,hy]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (measure_fiber_eq_zero_of_empty_interior ν hc hfull hcut)] with y hy
    have hpath : Continuous (fun t : ℝ => (t,y)) := continuous_id.prodMk continuous_const
    have he : ∀ᶠ t in 𝓝 b,(t,y)∉K :=
      hpath.continuousAt.eventually_mem (hK.isOpen_compl.mem_nhds hy)
    apply (show ContinuousAt (fun _ : ℝ => (0 : ℝ)) b from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with t ht
    exact indicator_of_notMem ht _

open ConvexExposedSections NoncoincidentCutDerivatives

/-- An unequal affine boundary has null contact with the cut if its
coefficient in the cut direction is nonzero. -/
theorem ae_ne_level (H : (ℝ × E) →ᵃ[ℝ] ℝ) (hH : H.linear (1,0)≠0)
    (b d : ℝ) (hne : {p : ℝ × E | p.1=b}≠{p | H p=d}) :
    ∀ᵐ y ∂ν,H (b,y)≠d := by
  have hn : ¬∀ y,H (b,y)=d := by
    intro hall
    apply hne
    ext p
    change p.1=b ↔ H p=d
    have hh := hall p.2
    rw [affine_eval] at hh
    rw [affine_eval]
    constructor
    · intro hp; rwa [hp]
    · intro hp
      apply mul_left_cancel₀ hH
      linarith only [hp,hh]
  have hz : ν {y | transverseForm H y=d-H.linear (1,0)*b}=0 := by
    apply measure_affine_level_eq_zero_of_not_forall
    intro he
    apply hn
    intro y
    rw [affine_eval,he y]
    ring
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with y hy
  intro he
  apply hy
  rw [affine_eval] at he
  linarith only [he]

/-- Constant affine forms and planks parallel to the cut direction need
no exceptional-set argument: their membership is unchanged along each fiber. -/
theorem ae_eventually_mem_band_iff (H : (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi b : ℝ)
    (hl : {p : ℝ × E | p.1=b}≠{p | H p=lo})
    (hu : {p : ℝ × E | p.1=b}≠{p | H p=hi}) :
    ∀ᵐ y ∂ν,∀ᶠ t in 𝓝 b,
      (lo≤H (t,y) ∧ H (t,y)≤hi) ↔ (lo≤H (b,y) ∧ H (b,y)≤hi) := by
  by_cases hH : H.linear (1,0)=0
  · exact Eventually.of_forall fun y => Eventually.of_forall fun t => by
      simp only [affine_eval,hH,zero_mul,add_zero]
  · filter_upwards [ae_ne_level ν H hH b lo hl,ae_ne_level ν H hH b hi hu]
      with y hylo hyhi
    have hh : ContinuousAt (fun t : ℝ => H (t,y)) b :=
      H.continuous_of_finiteDimensional.continuousAt.comp
        (continuousAt_id.prodMk continuousAt_const)
    filter_upwards [eventually_le_iff_of_ne continuousAt_const hh hylo.symm,
      eventually_le_iff_of_ne hh continuousAt_const hyhi] with t ht₁ ht₂
    exact and_congr ht₁ ht₂

/-- Almost-everywhere continuity for the actual residual, with only unequal
boundary hyperplanes. Empty-interior bodies and constant forms are allowed. -/
theorem ae_continuousAt_residual_indicator {ι : Type*} {K : Set (ℝ × E)}
    (hK : IsClosed K) (hc : Convex ℝ K)
    (s : Finset ι) (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) {b : ℝ}
    (hcut : b∈interior (Prod.fst '' K))
    (hline : ∀ j∈s,∀ d∈({lo j,hi j} : Set ℝ),
      {p : ℝ × E | p.1=b}≠{p | H j p=d}) :
    ∀ᵐ y ∂ν,ContinuousAt (fun t : ℝ =>
      (residual K s H lo hi).indicator (fun _ => (1 : ℝ)) (t,y)) b := by
  classical
  have hev : ∀ᵐ y ∂ν,∀ j∈s,∀ᶠ t in 𝓝 b,
      (lo j≤H j (t,y) ∧ H j (t,y)≤hi j) ↔
        (lo j≤H j (b,y) ∧ H j (b,y)≤hi j) :=
    (Filter.eventually_all_finset s).2 fun j hj =>
      ae_eventually_mem_band_iff ν (H j) (lo j) (hi j) b
        (hline j hj _ (by simp)) (hline j hj _ (by simp))
  filter_upwards [ae_continuousAt_indicator ν hK hc hcut,hev] with y hy hye
  let U : Set (ℝ × E) := ⋃ j∈s,{p | lo j≤H j p ∧ H j p≤hi j}
  have he : ∀ᶠ t in 𝓝 b,(t,y)∈U ↔ (b,y)∈U := by
    filter_upwards [(Filter.eventually_all_finset s).2 hye] with t ht
    simp only [U,mem_iUnion,mem_ofPred_eq]
    exact exists_congr fun j => exists_congr fun hj => ht j hj
  by_cases hb : (b,y)∈U
  · apply (show ContinuousAt (fun _ : ℝ => (0 : ℝ)) b from
      continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with t ht
    have hn : (t,y)∉residual K s H lo hi := fun hp => hp.2 (ht.mpr hb)
    exact indicator_of_notMem hn _
  · apply hy.congr_of_eventuallyEq
    filter_upwards [he] with t ht
    have hn : (t,y)∉U := fun hp => hb (ht.mp hp)
    by_cases hp : (t,y)∈K <;> simp [NoncoincidentCutDerivatives.residual,show (t,y)∉⋃ j∈s,
      {p | lo j≤H j p ∧ H j p≤hi j} from hn,hp]

/-- The actual residual-section volume is continuous at every internal
noncoincident cut, without a full-dimensionality or nonconstant-form premise. -/
theorem continuousAt_residual_density {ι : Type*} {K : Set (ℝ × E)}
    (hK : IsCompact K) (hc : Convex ℝ K)
    (s : Finset ι) (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) {b : ℝ}
    (hcut : b∈interior (Prod.fst '' K))
    (hline : ∀ j∈s,∀ d∈({lo j,hi j} : Set ℝ),
      {p : ℝ × E | p.1=b}≠{p | H j p=d}) :
    ContinuousAt (MovingCutArea.density ν (residual K s H lo hi)) b := by
  let R := residual K s H lo hi
  let D := Prod.snd '' K
  have hD : IsCompact D := hK.image continuous_snd
  have hR : MeasurableSet R := measurable_residual hK.measurableSet s H lo hi
  have hm (t : ℝ) : MeasurableSet (Prod.mk t ⁻¹' R) :=
    hR.preimage (measurable_const.prodMk measurable_id)
  have he (t : ℝ) : (fun y => R.indicator (fun _ => (1 : ℝ)) (t,y))=
      (Prod.mk t ⁻¹' R).indicator (fun _ => (1 : ℝ)) := by
    funext y
    by_cases hy : (t,y)∈R <;> simp [hy]
  have ht : ContinuousAt (fun t => ∫ y,R.indicator (fun _ => (1 : ℝ)) (t,y) ∂ν) b := by
    apply continuousAt_of_dominated (bound := D.indicator (fun _ => (1 : ℝ)))
    · exact Eventually.of_forall fun t => by
        rw [he]
        exact aestronglyMeasurable_const.indicator (hm t)
    · exact Eventually.of_forall fun t => Eventually.of_forall fun y => by
        by_cases hy : (t,y)∈R
        · have hyD : y∈D := ⟨(t,y),hy.1,rfl⟩
          simp [hy,hyD]
        · by_cases hyD : y∈D <;> simp [hy,hyD]
    · exact (integrableOn_const hD.measure_ne_top).integrable_indicator hD.measurableSet
    · exact ae_continuousAt_residual_indicator ν hK.isClosed hc s H lo hi hcut hline
  change ContinuousAt (fun t => ν.real (Prod.mk t ⁻¹' R)) b
  simpa only [he,integral_indicator_const (1 : ℝ) (hm _),smul_eq_mul,mul_one] using ht

end Plank.InternalCutTrace
