/- Tilted cuts by direct differentiation under the integral.
No interval-fiber representation or cell decomposition is used. -/
module
public import NoncoincidentCutDerivatives
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.MovingAffineCut

open Set MeasureTheory Filter
open ConvexSections ConvexExposedSections NoncoincidentCutDerivatives
open scoped Topology

variable {E : Type*} [MeasurableSpace E] (ν : Measure E) [SFinite ν]

def cut (S : Set (ℝ × E)) (h : E → ℝ) (b t : ℝ) : Set (ℝ × E) :=
  S ∩ {p | p.1 ≤ b+t*h p.2}

def cumulative (S : Set (ℝ × E)) (h : E → ℝ) (b t : ℝ) (y : E) : ℝ :=
  ∫ x in Iic (b+t*h y), S.indicator (fun _ => (1 : ℝ)) (x,y)

omit [SFinite ν] in
theorem measurable_cut {S : Set (ℝ × E)} (hS : MeasurableSet S)
    {h : E → ℝ} (hh : Measurable h) (b t : ℝ) : MeasurableSet (cut S h b t) :=
  hS.inter (measurableSet_le measurable_fst
    (measurable_const.add (measurable_const.mul (hh.comp measurable_snd))))

omit [MeasurableSpace E] in
theorem cumulative_eq (S : Set (ℝ × E)) (h : E → ℝ) (b t : ℝ) (y : E) :
    cumulative S h b t y = ∫ x, (cut S h b t).indicator (fun _ => (1 : ℝ)) (x,y) := by
  rw [cumulative, ←integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : (x,y)∈S <;> by_cases ht : x≤b+t*h y <;> simp [cut,hx,ht]

theorem integrable_cumulative {S : Set (ℝ × E)} (hS : MeasurableSet S)
    (hfin : (volume.prod ν) S≠⊤) {h : E → ℝ} (hh : Measurable h) (b t : ℝ) :
    Integrable (cumulative S h b t) ν := by
  have hi : Integrable ((cut S h b t).indicator (fun _ => (1 : ℝ))) (volume.prod ν) :=
    (integrableOn_const (measure_ne_top_of_subset inter_subset_left hfin)).integrable_indicator
      (measurable_cut hS hh b t)
  change Integrable (fun y => cumulative S h b t y) ν
  simp_rw [cumulative_eq]
  exact hi.integral_prod_right

theorem area_eq_integral {S : Set (ℝ × E)} (hS : MeasurableSet S)
    (hfin : (volume.prod ν) S≠⊤) {h : E → ℝ} (hh : Measurable h) (b t : ℝ) :
    (volume.prod ν).real (cut S h b t)=∫ y,cumulative S h b t y ∂ν := by
  have hm := measurable_cut hS hh b t
  have hi : Integrable ((cut S h b t).indicator (fun _ => (1 : ℝ))) (volume.prod ν) :=
    (integrableOn_const (measure_ne_top_of_subset inter_subset_left hfin)).integrable_indicator hm
  rw [←integral_indicator_one hm]
  change (∫ x,(cut S h b t).indicator (fun _ => (1 : ℝ)) x ∂volume.prod ν)=_
  rw [integral_prod_symm _ hi]
  simp only [cumulative_eq]

omit [MeasurableSpace E] in
theorem cumulative_lipschitz (S : Set (ℝ × E)) (h : E → ℝ) (b : ℝ) (y : E)
    (hi : Integrable (fun x : ℝ => S.indicator (fun _ => (1 : ℝ)) (x,y))) :
    LipschitzWith (Real.nnabs (h y)) (fun t => cumulative S h b t y) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  simp only [Real.dist_eq, Real.coe_nnabs]
  rw [cumulative,cumulative,intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := b+u*h y) (b := b+t*h y)
    (C := (1 : ℝ)) (f := fun x => S.indicator (fun _ => (1 : ℝ)) (x,y))
    (fun x _ => by by_cases hx : (x,y)∈S <;> simp [hx])
  simpa only [Real.norm_eq_abs,one_mul,mul_one,
    show (b+t*h y)-(b+u*h y)=(t-u)*h y by ring,abs_mul,mul_comm] using hh

omit [MeasurableSpace E] in
theorem hasDerivAt_cumulative (S : Set (ℝ × E)) (h : E → ℝ) (b : ℝ) (y : E)
    (hi : Integrable (fun x : ℝ => S.indicator (fun _ => (1 : ℝ)) (x,y)))
    (hc : ContinuousAt (fun x : ℝ => S.indicator (fun _ => (1 : ℝ)) (x,y)) b) :
    HasDerivAt (fun t => cumulative S h b t y)
      (S.indicator (fun _ => (1 : ℝ)) (b,y)*h y) 0 := by
  have hd := intervalIntegral.integral_hasDerivAt_right
    (a := b) hi.intervalIntegrable hi.aestronglyMeasurable.stronglyMeasurableAtFilter hc
  have hp : HasDerivAt (fun t : ℝ => b+t*h y) (h y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (h y)).const_add b
  have hd' : HasDerivAt (fun u => ∫ x in b..u,S.indicator (fun _ => (1 : ℝ)) (x,y))
      (S.indicator (fun _ => (1 : ℝ)) (b,y)) (b+0*h y) := by simpa using hd
  have he := (hd'.comp 0 hp).add_const (cumulative S h b 0 y)
  apply he.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro t
  dsimp only [Function.comp_def]
  have hh := intervalIntegral.integral_Iic_sub_Iic (a := b) (b := b+t*h y)
    hi.integrableOn hi.integrableOn
  simp only [cumulative,zero_mul,add_zero]
  linarith only [hh]

/-- Actual measured derivative for any finite-measure measurable set with
almost-everywhere continuous trace, and any integrable measurable cut speed. -/
theorem hasDerivAt_area {S : Set (ℝ × E)} (hS : MeasurableSet S)
    (hfin : (volume.prod ν) S≠⊤) {h : E → ℝ} (hh : Measurable h) (hi : Integrable h ν)
    (b : ℝ) (hc : ∀ᵐ y ∂ν,
      ContinuousAt (fun x : ℝ => S.indicator (fun _ => (1 : ℝ)) (x,y)) b) :
    HasDerivAt (fun t => (volume.prod ν).real (cut S h b t))
      (∫ y in Prod.mk b ⁻¹' S,h y ∂ν) 0 := by
  have hint : Integrable (S.indicator (fun _ => (1 : ℝ))) (volume.prod ν) :=
    (integrableOn_const hfin).integrable_indicator hS
  let D : E → ℝ := fun y => S.indicator (fun _ => (1 : ℝ)) (b,y)*h y
  have hm : Measurable D :=
    ((measurable_const.indicator hS).comp (measurable_const.prodMk measurable_id)).mul hh
  have hd := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := ν) (F := cumulative S h b) (F' := D) (bound := h) (s := univ)
    (x₀ := (0 : ℝ)) (univ_mem : univ∈𝓝 (0 : ℝ))
    (Eventually.of_forall fun t => (integrable_cumulative ν hS hfin hh b t).aestronglyMeasurable)
    (integrable_cumulative ν hS hfin hh b 0) hm.aestronglyMeasurable
    (hint.prod_left_ae.mono fun y hy => (cumulative_lipschitz S h b y hy).lipschitzOnWith)
    hi ((hint.prod_left_ae.and hc).mono fun y hy => hasDerivAt_cumulative S h b y hy.1 hy.2)
  have he : (∫ y,D y ∂ν)=∫ y in Prod.mk b ⁻¹' S,h y ∂ν := by
    have hs : MeasurableSet (Prod.mk b ⁻¹' S) :=
      hS.preimage (measurable_const.prodMk measurable_id)
    rw [←integral_indicator hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by by_cases hy : (b,y)∈S <;> simp [D,hy]
  rw [he] at hd
  exact hd.2.congr_of_eventuallyEq (Eventually.of_forall (area_eq_integral ν hS hfin hh b))

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [ν.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A compact enclosing body supplies the integrable cut speed. The speed
may be any continuous function; affine speeds later give convex variations. -/
theorem hasDerivAt_compact_area {L S : Set (ℝ × E)} (hL : IsCompact L)
    (hS : MeasurableSet S) (hSL : S⊆L) {h : E → ℝ} (hh : Continuous h)
    (b : ℝ) (hc : ∀ᵐ y ∂ν,
      ContinuousAt (fun x : ℝ => S.indicator (fun _ => (1 : ℝ)) (x,y)) b) :
    HasDerivAt (fun t => (volume.prod ν).real (cut S h b t))
      (∫ y in Prod.mk b ⁻¹' S,h y ∂ν) 0 := by
  let D := Prod.snd '' L
  have hD : IsCompact D := hL.image continuous_snd
  have hi : Integrable (D.indicator h) ν :=
    (hh.continuousOn.integrableOn_compact hD).integrable_indicator hD.measurableSet
  have hd := hasDerivAt_area ν hS (measure_ne_top_of_subset hSL hL.measure_ne_top)
    (hh.measurable.indicator hD.measurableSet) hi b hc
  have he (t : ℝ) : cut S (D.indicator h) b t=cut S h b t := by
    ext p
    by_cases hp : p∈S
    · have hpD : p.2∈D := ⟨p,hSL hp,rfl⟩
      simp [cut,hp,indicator_of_mem hpD]
    · simp [cut,hp]
  have hmoment : (∫ y in Prod.mk b ⁻¹' S,D.indicator h y ∂ν)=
      ∫ y in Prod.mk b ⁻¹' S,h y ∂ν := by
    apply setIntegral_congr_fun (hS.preimage (measurable_const.prodMk measurable_id))
    intro y hy
    exact indicator_of_mem (show y∈D from ⟨(b,y),hSL hy,rfl⟩) _
  simpa only [he,hmoment] using hd

variable {ι : Type*}

omit [SFinite ν] in
/-- Convexity and noncoincident affine boundary levels prove the required
almost-everywhere continuity of the actual residual indicator. -/
theorem ae_continuousAt_residual_indicator {L : Set (ℝ × E)} (hL : IsCompact L)
    (hc : Convex ℝ L) (hfull : (interior L).Nonempty)
    (s : Finset ι) (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (b : ℝ)
    (hcut : b∈interior (Prod.fst '' L))
    (hsep : ∀ j∈s,(¬∀ y,H j (b,y)=lo j) ∧ (¬∀ y,H j (b,y)=hi j)) :
    ∀ᵐ y ∂ν, ContinuousAt (fun x : ℝ =>
      (NoncoincidentCutDerivatives.residual L s H lo hi).indicator
        (fun _ => (1 : ℝ)) (x,y)) b := by
    have hnf : ∀ᵐ y ∂ν,y∉frontier (fiber L b) :=
      measure_eq_zero_iff_ae_notMem.1 ((convex_fiber hc b).addHaar_frontier ν)
    have hn (j : ι) (u : ℝ) (hh : ¬∀ y,H j (b,y)=u) :
        ∀ᵐ y ∂ν,transverseForm (H j) y≠u-(H j).linear (1,0)*b := by
      apply (measure_eq_zero_iff_ae_notMem (s :=
        {y | transverseForm (H j) y = u - (H j).linear (1, 0) * b})).1
      apply measure_affine_level_eq_zero_of_not_forall ν
      intro he
      apply hh
      intro y
      rw [affine_eval,he y]
      ring
    have hna : ∀ᵐ y ∂ν,∀ j∈s,
        transverseForm (H j) y≠lo j-(H j).linear (1,0)*b :=
      (Filter.eventually_all_finset s).2 fun j hj => hn j (lo j) (hsep j hj).1
    have hnb : ∀ᵐ y ∂ν,∀ j∈s,
        transverseForm (H j) y≠hi j-(H j).linear (1,0)*b :=
      (Filter.eventually_all_finset s).2 fun j hj => hn j (hi j) (hsep j hj).2
    filter_upwards [hnf,hna,hnb] with y hy hya hyb
    have hh := continuousAt_exposed_indicator hL.isClosed hc hfull s
      (fun j => transverseForm (H j)) (c := fun t : ℝ => t)
      (a := fun j t => lo j-(H j).linear (1,0)*t)
      (b := fun j t => hi j-(H j).linear (1,0)*t)
      continuousAt_id hcut (fun _ _ => by fun_prop) (fun _ _ => by fun_prop) hy hya hyb
    simp_rw [←fiber_residual] at hh
    apply hh.congr_of_eventuallyEq
    exact Eventually.of_forall fun t => by
      by_cases hy : (t,y)∈NoncoincidentCutDerivatives.residual L s H lo hi <;>
        simp [fiber,hy]

/-- Whole-body version, using only nullity of a convex section's boundary. -/
theorem hasDerivAt_body_area_continuous {L : Set (ℝ × E)} (hL : IsCompact L)
    (hc : Convex ℝ L) (hfull : (interior L).Nonempty) (b : ℝ)
    (hcut : b∈interior (Prod.fst '' L)) (h : E → ℝ) (hh : Continuous h) :
    HasDerivAt (fun t => (volume.prod ν).real (cut L h b t))
      (∫ y in Prod.mk b ⁻¹' L,h y ∂ν) 0 := by
  apply hasDerivAt_compact_area ν hL hL.measurableSet Subset.rfl
    hh b
  filter_upwards [measure_eq_zero_iff_ae_notMem.1
    ((convex_fiber hc b).addHaar_frontier ν)] with y hy
  have hh := continuousAt_fiber_indicator hL.isClosed hc hfull hcut hy
  apply hh.congr_of_eventuallyEq
  exact Eventually.of_forall fun t => by
    by_cases hy : (t,y)∈L <;> simp [fiber,hy]

/-- The actual moving-cut derivative for a compact convex body after any
finite plank family. All analytic trace hypotheses are proved geometrically. -/
theorem hasDerivAt_residual_area_continuous {L : Set (ℝ × E)} (hL : IsCompact L)
    (hc : Convex ℝ L) (hfull : (interior L).Nonempty)
    (s : Finset ι) (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (b : ℝ)
    (hcut : b∈interior (Prod.fst '' L))
    (hsep : ∀ j∈s,(¬∀ y,H j (b,y)=lo j) ∧ (¬∀ y,H j (b,y)=hi j))
    (h : E → ℝ) (hh : Continuous h) :
    HasDerivAt (fun t => (volume.prod ν).real
      (cut (NoncoincidentCutDerivatives.residual L s H lo hi) h b t))
      (∫ y in Prod.mk b ⁻¹' NoncoincidentCutDerivatives.residual L s H lo hi,h y ∂ν) 0 :=
  hasDerivAt_compact_area ν hL
    (NoncoincidentCutDerivatives.measurable_residual hL.measurableSet s H lo hi)
    sdiff_subset hh b
    (ae_continuousAt_residual_indicator ν hL hc hfull s H lo hi b hcut hsep)

/-- Affine-speed specialization of the continuous-speed body derivative. -/
theorem hasDerivAt_body_area {L : Set (ℝ × E)} (hL : IsCompact L)
    (hc : Convex ℝ L) (hfull : (interior L).Nonempty) (b : ℝ)
    (hcut : b∈interior (Prod.fst '' L)) (h : E →ᵃ[ℝ] ℝ) :
    HasDerivAt (fun t => (volume.prod ν).real (cut L h b t))
      (∫ y in Prod.mk b ⁻¹' L,h y ∂ν) 0 :=
  hasDerivAt_body_area_continuous ν hL hc hfull b hcut h
    h.continuous_of_finiteDimensional

/-- Affine-speed specialization of the continuous-speed residual derivative. -/
theorem hasDerivAt_residual_area {L : Set (ℝ × E)} (hL : IsCompact L)
    (hc : Convex ℝ L) (hfull : (interior L).Nonempty)
    (s : Finset ι) (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (b : ℝ)
    (hcut : b∈interior (Prod.fst '' L))
    (hsep : ∀ j∈s,(¬∀ y,H j (b,y)=lo j) ∧ (¬∀ y,H j (b,y)=hi j))
    (h : E →ᵃ[ℝ] ℝ) :
    HasDerivAt (fun t => (volume.prod ν).real
      (cut (NoncoincidentCutDerivatives.residual L s H lo hi) h b t))
      (∫ y in Prod.mk b ⁻¹' NoncoincidentCutDerivatives.residual L s H lo hi,h y ∂ν) 0 :=
  hasDerivAt_residual_area_continuous ν hL hc hfull s H lo hi b hcut hsep h
    h.continuous_of_finiteDimensional

end Plank.MovingAffineCut
