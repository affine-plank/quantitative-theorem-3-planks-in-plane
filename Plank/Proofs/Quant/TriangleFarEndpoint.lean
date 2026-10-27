/- Endpoint differentiability for a unique far-edge-parallel triangle plank. -/
module
public import Plank.Proofs.Quant.TriangleTiedMaximum
public import Plank.Proofs.Quant.PlanarGapSectionDerivatives
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleFarEndpoint
open Set MeasureTheory MeasureTheory.Measure
open Plank.PlanarGapSectionDerivatives Plank.PlanarPolygonHalfplanes
open scoped Topology BigOperators

def chart (z : Fin 2 → ℝ) : ℝ × ℝ := (z 0-z 1,z 1)

theorem chart_preserves_volume : MeasurePreserving chart volume volume := by
  have h : MeasurePreserving (fun z : ℝ × ℝ => (z.1-z.2,z.2)) volume volume := by
    convert measurePreserving_swap.comp
      (measurePreserving_prod_neg_add_swap (volume : Measure ℝ) volume) using 1 <;>
      first | rfl | (funext z; ext <;> simp [sub_eq_add_neg,add_comm])
  convert h.comp (volume_preserving_finTwoArrow ℝ) using 1
  rfl

def form (p : Plank) : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ :=
  (p.u.1 • (LinearMap.proj 0)+(p.u.2-p.u.1) • (LinearMap.proj 1) :
    (Fin 2 → ℝ) →ₗ[ℝ] ℝ).toAffineMap

theorem form_apply (p : Plank) (z : Fin 2 → ℝ) : form p z=dot p.u (chart z) := by
  change p.u.1*z 0+(p.u.2-p.u.1)*z 1=p.u.1*(z 0-z 1)+p.u.2*z 1
  ring

theorem form_second (p : Plank) : (form p).linear (Pi.single 1 1)=p.u.2-p.u.1 := by
  simp [form]

def gap (C : Config) (t : ℝ) : Set (ℝ × ℝ) :=
  stdTriangle.set \ ((C.plank 0).set ∪ (C.plank 1).set ∪
    {z | (C.plank 2).lo ≤ z.1+z.2 ∧ z.1+z.2 ≤ t})

theorem gap_measurable (C : Config) (t : ℝ) : MeasurableSet (gap C t) := by
  apply Proofs.Quant.measurableSet_stdTriangle.diff
  apply (Proofs.Quant.measurableSet_plank (C.plank 0) |>.union
    (Proofs.Quant.measurableSet_plank (C.plank 1))).union
  exact (isClosed_le continuous_const (continuous_fst.add continuous_snd)).measurableSet.inter
    (isClosed_le (continuous_fst.add continuous_snd) continuous_const).measurableSet

theorem gap_original (C : Config) (hu : (C.plank 2).u=(1,1)) :
    gap C (C.plank 2).hi=C.uncovered := by
  have hband : {z : ℝ × ℝ | (C.plank 2).lo ≤ z.1+z.2 ∧ z.1+z.2 ≤ (C.plank 2).hi} =
      (C.plank 2).set := by
    ext z
    change ((C.plank 2).lo ≤ z.1+z.2 ∧ z.1+z.2 ≤ (C.plank 2).hi) ↔
      ((C.plank 2).lo ≤ dot (C.plank 2).u z ∧ dot (C.plank 2).u z ≤ (C.plank 2).hi)
    simp only [hu,dot,one_mul]
  unfold gap Config.uncovered
  rw [hband]
  congr 1
  ext z
  simp only [mem_union,mem_iUnion,Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
  tauto

theorem chart_triangle : chart ⁻¹' stdTriangle.set =
    boxedRegion 0 1 0 1 (fun _ : Unit => -1) (fun _ => 1) (fun _ => 0) := by
  ext z
  rw [mem_preimage,Proofs.Quant.stdTriangle_set_eq]
  change (0 ≤ z 0-z 1 ∧ 0 ≤ z 1 ∧ (z 0-z 1)+z 1 ≤ 1) ↔
    (z 0 ∈ Icc 0 1 ∧ z 1 ∈ Icc 0 1 ∧ ∀ _ : Unit, -1*z 0+1*z 1 ≤ 0)
  constructor
  · rintro ⟨h0,h1,h2⟩
    refine ⟨⟨by linarith,by linarith⟩,⟨h1,by linarith⟩,?_⟩
    intro _
    linarith
  · rintro ⟨hx,hy,h⟩
    have hh := h ()
    exact ⟨by linarith,hy.1,by linarith only [hx.2]⟩

theorem chart_gap (C : Config) (t : ℝ) : chart ⁻¹' gap C t =
    verticalGap 0 1 0 1 (fun _ : Unit => -1) (fun _ => 1) (fun _ => 0)
      (fun i : Fin 2 => form (C.plank i.castSucc))
      (fun i => (C.plank i.castSucc).lo) (fun i => (C.plank i.castSucc).hi)
      (C.plank 2).lo t := by
  have hp (p : Plank) : chart ⁻¹' p.set = {z | p.lo ≤ form p z ∧ form p z ≤ p.hi} := by
    ext z
    change (p.lo ≤ dot p.u (chart z) ∧ dot p.u (chart z) ≤ p.hi) ↔ _
    rw [← form_apply]
    rfl
  have he : chart ⁻¹' {z : ℝ × ℝ | (C.plank 2).lo ≤ z.1+z.2 ∧ z.1+z.2 ≤ t} =
      {z : Fin 2 → ℝ | (C.plank 2).lo ≤ z 0 ∧ z 0 ≤ t} := by
    ext z
    simp [chart]
  rw [gap,preimage_sdiff,preimage_union,preimage_union,chart_triangle,hp,hp,he]
  unfold verticalGap boxedGap
  ext z
  simp only [mem_sdiff,mem_union,mem_iUnion,Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
  tauto

theorem gap_derivative (C : Config) (hl : 0 < (C.plank 2).lo)
    (hw : (C.plank 2).lo < (C.plank 2).hi) (hh : (C.plank 2).hi < 1)
    (hn : ∀ i : Fin 2, (C.plank i.castSucc).u.1 ≠ (C.plank i.castSucc).u.2) :
    ∃ d : ℝ, HasDerivAt (fun t => (volume (gap C t)).toReal) d (C.plank 2).hi := by
  have hf (i : Fin 2) : (form (C.plank i.castSucc)).linear (Pi.single 1 1) ≠ 0 := by
    rw [form_second]
    exact sub_ne_zero.mpr (Ne.symm (hn i))
  have hd := hasDerivAt_area_verticalGap_upper hl hw hh 0 1
    (fun _ : Unit => -1) (fun _ => 1) (fun _ => 0)
    (fun i : Fin 2 => form (C.plank i.castSucc)) (by intro _; norm_num) hf
    (fun i => (C.plank i.castSucc).lo) (fun i => (C.plank i.castSucc).hi)
    (fun i => (C.plank i.castSucc).lo_le_hi)
  refine ⟨_,hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => ?_))⟩
  dsimp only
  rw [← chart_gap C t,chart_preserves_volume.measure_preimage (gap_measurable C t).nullMeasurableSet]

def replaceUpper (C : Config) (t : ℝ) (ht : (C.plank 2).lo ≤ t) : Config :=
  ⟨![C.plank 0,C.plank 1,
    ⟨(C.plank 2).u,(C.plank 2).lo,t,(C.plank 2).u_ne_zero,ht⟩]⟩

theorem replaceUpper_normals (C : Config) (t : ℝ) (ht : (C.plank 2).lo ≤ t) (i : Fin 3) :
    ((replaceUpper C t ht).plank i).u=(C.plank i).u := by
  fin_cases i <;> rfl

theorem replaceUpper_gap (C : Config) (hu : (C.plank 2).u=(1,1))
    (t : ℝ) (ht : (C.plank 2).lo ≤ t) : (replaceUpper C t ht).uncovered=gap C t := by
  rw [← gap_original (replaceUpper C t ht) hu]
  rfl

theorem replaceUpper_deficit (C : Config) (hu : (C.plank 2).u=(1,1))
    (t : ℝ) (ht : (C.plank 2).lo ≤ t) :
    (replaceUpper C t ht).deficit=C.deficit-(t-(C.plank 2).hi) := by
  have hw : C.relW 2=(C.plank 2).hi-(C.plank 2).lo := by
    simp [Config.relW,Plank.relWidth,hu,Proofs.Transport.stdTriangle_width_eq]
  have hw' : (replaceUpper C t ht).relW 2=t-(C.plank 2).lo := by
    simp [replaceUpper,Config.relW,Plank.relWidth,hu,Proofs.Transport.stdTriangle_width_eq]
  simp only [Config.deficit,Config.sumRelW,Fin.sum_univ_three,hw,hw']
  change 1-(C.relW 0+C.relW 1+(t-(C.plank 2).lo)) =
    1-(C.relW 0+C.relW 1+((C.plank 2).hi-(C.plank 2).lo))-(t-(C.plank 2).hi)
  ring

theorem gap_bound (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hu2 : (C.plank 2).u=(1,1)) (t : ℝ) (ht : (C.plank 2).lo ≤ t) :
    (max 0 (C.deficit-(t-(C.plank 2).hi)))^2/2 ≤ (volume (gap C t)).toReal := by
  have hh := CommonVertex.config_positive_square_bound (replaceUpper C t ht)
    (fun i => by rw [replaceUpper_normals]; exact hu i)
  rwa [replaceUpper_deficit C hu2,Config.gapArea,replaceUpper_gap C hu2] at hh

theorem upper_le_one (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hu2 : (C.plank 2).u=(1,1)) (hw : (C.plank 2).lo < (C.plank 2).hi)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C) :
    (C.plank 2).hi ≤ 1 := by
  by_contra hn
  have hh : 1 < (C.plank 2).hi := lt_of_not_ge hn
  let t := max (C.plank 2).lo 1
  have ht : (C.plank 2).lo ≤ t := le_max_left _ _
  have ht1 : 1 ≤ t := le_max_right _ _
  have hth : t < (C.plank 2).hi := max_lt hw hh
  have hgap : gap C t=gap C (C.plank 2).hi := by
    ext z
    by_cases hz : z ∈ stdTriangle.set
    · have hz1 := (Proofs.Quant.stdTriangle_set_eq ▸ hz).2.2
      have heq : z.1+z.2 ≤ t := hz1.trans ht1
      have heq' : z.1+z.2 ≤ (C.plank 2).hi := hz1.trans hh.le
      simp only [gap,mem_sdiff,mem_union,mem_ofPred_eq,hz,heq,heq',and_true]
    · simp only [gap,mem_sdiff,hz,false_and]
  have hb := gap_bound C hu hu2 t ht
  rw [hgap,gap_original C hu2] at hb
  change (max 0 (C.deficit-(t-(C.plank 2).hi)))^2/2 ≤ C.gapArea at hb
  have hd' : 0 ≤ C.deficit-(t-(C.plank 2).hi) := by linarith only [hδ,hth]
  rw [max_eq_right hd',he,max_eq_right hδ.le] at hb
  nlinarith only [hb,hδ,hth,sq_nonneg (t-(C.plank 2).hi)]

theorem lower_pos (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hu2 : (C.plank 2).u=(1,1)) (hw : 0 < C.relW 2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C) :
    0 < (C.plank 2).lo := by
  by_contra hn
  have hl : (C.plank 2).lo ≤ 0 := le_of_not_gt hn
  have hempty : C.uncovered=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hh := TriangleTiedMaximum.gap_below C hu hδ he 2 (by rw [hu2]) hw hz
    have hzt := Proofs.Quant.stdTriangle_set_eq ▸ hz.1
    simp only [hu2,dot,one_mul] at hh
    linarith only [hh,hl,hzt.1,hzt.2.1]
  have hz : C.gapArea=0 := by simp [Config.gapArea,hempty]
  rw [TriangleEqualityReductions.Equality,max_eq_right hδ.le,hz] at he
  nlinarith only [he,sq_pos_of_pos hδ]

theorem gap_constant_right (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hu2 : (C.plank 2).u=(1,1)) (hw : 0 < C.relW 2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C)
    (t : ℝ) (ht : (C.plank 2).hi ≤ t) : gap C t=gap C (C.plank 2).hi := by
  ext z
  constructor
  · rintro ⟨hz,hn⟩
    refine ⟨hz,?_⟩
    rintro (hp | hp)
    · exact hn (Or.inl hp)
    · exact hn (Or.inr ⟨hp.1,hp.2.trans ht⟩)
  · intro hz
    have hz' : z ∈ C.uncovered := by rwa [gap_original C hu2] at hz
    have hl := TriangleTiedMaximum.gap_below C hu hδ he 2 (by rw [hu2]) hw hz'
    simp only [hu2,dot,one_mul] at hl
    refine ⟨hz.1,?_⟩
    rintro (hp | hp)
    · exact hz.2 (Or.inl hp)
    · exact not_le_of_gt hl hp.1

/-- If the other two normals are transverse to the far edge, sharpness
forces the original positive edge band's upper boundary onto that edge.
No placement or support-containment premise is supplied. -/
theorem upper_eq_one (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hu2 : (C.plank 2).u=(1,1)) (hw : 0 < C.relW 2)
    (hn : ∀ i : Fin 2, (C.plank i.castSucc).u.1 ≠ (C.plank i.castSucc).u.2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C) :
    (C.plank 2).hi=1 := by
  have hw' : (C.plank 2).lo < (C.plank 2).hi := by
    have hew : C.relW 2=(C.plank 2).hi-(C.plank 2).lo := by
      simp [Config.relW,Plank.relWidth,hu2,Proofs.Transport.stdTriangle_width_eq]
    rw [hew] at hw
    exact sub_pos.mp hw
  have hle := upper_le_one C hu hu2 hw' hδ he
  apply le_antisymm hle
  by_contra hnot
  have hh : (C.plank 2).hi < 1 := lt_of_not_ge hnot
  obtain ⟨d,hd⟩ := gap_derivative C (lower_pos C hu hu2 hw hδ he) hw' hh hn
  have hc (t) (ht : t ∈ Ici (C.plank 2).hi) :
      (volume (gap C t)).toReal=(volume (gap C (C.plank 2).hi)).toReal := by
    rw [gap_constant_right C hu hu2 hw hδ he t ht]
  have hz : HasDerivWithinAt (fun t => (volume (gap C t)).toReal) 0
      (Ici (C.plank 2).hi) (C.plank 2).hi := by
    apply (hasDerivAt_const (C.plank 2).hi ((volume (gap C (C.plank 2).hi)).toReal)).hasDerivWithinAt.congr
    · exact hc
    · rfl
  have hd0 : d=0 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici _) hd.hasDerivWithinAt hz
  subst d
  let M := fun t : ℝ => (volume (gap C t)).toReal-(C.deficit-(t-(C.plank 2).hi))^2/2
  have hM0 : M (C.plank 2).hi=0 := by
    dsimp only [M]
    rw [gap_original C hu2]
    change C.gapArea-_=0
    rw [he,max_eq_right hδ.le]
    ring
  have hmin : IsLocalMin M (C.plank 2).hi := by
    change ∀ᶠ t in 𝓝 (C.plank 2).hi, M (C.plank 2).hi ≤ M t
    filter_upwards [Ioi_mem_nhds hw',Iio_mem_nhds (show (C.plank 2).hi < (C.plank 2).hi+C.deficit by linarith only [hδ])]
      with t ht htδ
    change t < (C.plank 2).hi+C.deficit at htδ
    rw [hM0]
    apply sub_nonneg.mpr
    have hb := gap_bound C hu hu2 t ht.le
    rwa [max_eq_right (show 0 ≤ C.deficit-(t-(C.plank 2).hi) by linarith only [htδ])] at hb
  have hq : HasDerivAt (fun t : ℝ => (C.deficit-(t-(C.plank 2).hi))^2/2)
      (-C.deficit) (C.plank 2).hi := by
    convert! ((((hasDerivAt_id (C.plank 2).hi).sub_const (C.plank 2).hi).const_sub C.deficit).pow 2).div_const 2 using 1 <;> norm_num <;> ring
  have hdM : HasDerivAt M C.deficit (C.plank 2).hi := by
    convert! hd.sub hq using 1 <;> simp [M]
  have hzero := hmin.hasDerivAt_eq_zero hdM
  linarith only [hzero,hδ]

end Quant.TriangleFarEndpoint

/-- info: 'Quant.TriangleFarEndpoint.gap_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleFarEndpoint.gap_derivative

/-- info: 'Quant.TriangleFarEndpoint.upper_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleFarEndpoint.upper_eq_one
