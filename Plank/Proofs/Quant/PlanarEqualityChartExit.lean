/- Extend an actual equality line to a chart or window boundary. -/
module

public import Plank.Proofs.Quant.PlanarEqualityFlatDirection

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarEqualityChartExit

open Set MeasureTheory Topology PlanarQuantitative PlanarParameterDomain
  PlanarPolygonCharts PlanarEqualityFlatDirection
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero ray from an interior point of a compact set has a positive
last parameter in the set, and that endpoint is not interior. -/
theorem exists_ray_endpoint {S : Set E} (hS : IsCompact S) (p z : E)
    (hp : p ∈ interior S) (hz : z ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ p+t • z ∈ S ∧ p+t • z ∉ interior S := by
  let L := fun t : ℝ => p+t • z
  have hemb : IsClosedEmbedding L :=
    (Homeomorph.addLeft p).isClosedEmbedding.comp (isClosedEmbedding_smul_left hz)
  have hT : IsCompact (L ⁻¹' S) := hemb.isCompact_preimage hS
  have hU : IsOpen (L ⁻¹' interior S) := isOpen_interior.preimage hemb.continuous
  have hsub : L ⁻¹' interior S ⊆ L ⁻¹' S := preimage_mono interior_subset
  have h0 : (0 : ℝ) ∈ interior (L ⁻¹' S) :=
    (interior_maximal hsub hU) (by simpa only [mem_preimage,L,zero_smul,add_zero] using hp)
  obtain ⟨t,ht,hmax⟩ := hT.exists_isMaxOn ⟨0,interior_subset h0⟩ continuous_id.continuousOn
  have hbound : L ⁻¹' S ⊆ Iic t := fun x hx => hmax hx
  have htpos : 0 < t := by
    have hh := interior_mono hbound h0
    simpa only [interior_Iic,mem_Iio] using hh
  refine ⟨t,htpos,ht,?_⟩
  intro hi
  have hti : t ∈ interior (L ⁻¹' S) := (interior_maximal hsub hU) hi
  have hh := interior_mono hbound hti
  have hlt : t < t := by simpa only [interior_Iic,mem_Iio] using hh
  exact lt_irrefl t hlt

/-- Equality can be moved all the way to a chart boundary or a zero/support
window, with the same body and directions and without increasing total
relative width. Budget one is excluded by the original positive deficit.
The chart may change after this endpoint; no continuation through its
boundary is claimed by this theorem. -/
theorem exists_boundary_equality {K : Set Point} {f : Fin 2 → Point →ᵃ[ℝ] ℝ}
    (ch : OpenChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hp : ch.point ∈ interior (domain K f)) (hR : budget K f ch.point < 1)
    (heq : gapArea K f ch.point = (1-budget K f ch.point)^2*(volume K).toReal) :
    ∃ q : Endpoints 2, q ≠ ch.point ∧ q ∈ domain K f ∧ budget K f q ≤ budget K f ch.point ∧
      gapArea K f q = (1-budget K f q)^2*(volume K).toReal ∧
      (q ∈ frontier ch.region ∨ ∃ i, q.1 i = 0 ∨ q.1 i = q.2 i ∨ q.2 i = 1) := by
  obtain ⟨z,hzne,hdpos,hline⟩ := ch.exists_flat_equality_line hK hconv hne hV hW hp hR heq
  have hpc : ch.point ∈ interior (closure ch.region) := by
    apply interior_mono subset_closure
    rw [ch.open_region.interior_eq]
    exact ch.point_mem
  have hpi : ch.point ∈ interior (domain K f ∩ closure ch.region) := by
    rw [interior_inter]
    exact ⟨hp,hpc⟩
  obtain ⟨t,ht,hq,hqnot⟩ := exists_ray_endpoint
    ((isCompact_domain K f).inter_right isClosed_closure) ch.point z hpi hzne
  let q := ch.point+t • z
  have hqne : q ≠ ch.point := by
    intro he
    have hz0 : t • z = 0 := add_left_cancel (he.trans (add_zero ch.point).symm)
    exact (smul_ne_zero ht.ne' hzne) hz0
  have hb : budget K f q ≤ budget K f ch.point := by
    have hh := affine_eval_line (deficit K f 1) ch.point z t
    simp only [deficit_apply] at hh
    have hprod := mul_nonneg ht.le hdpos
    change budget K f (ch.point+t • z) ≤ budget K f ch.point
    linarith only [hh,hprod]
  refine ⟨q,hqne,hq.1,hb,hline t hq.2 (fun i => (hq.1.1 i).2.1),?_⟩
  by_cases hi : q ∈ interior (domain K f)
  · left
    change q ∈ closure ch.region ∧ q ∉ interior ch.region
    refine ⟨hq.2,?_⟩
    intro hh
    apply hqnot
    rw [interior_inter]
    exact ⟨hi,interior_mono subset_closure hh⟩
  · right
    rcases boundary_cases K f hq.1 hi with hbad | hh
    · exact (not_lt_of_ge hb (hbad ▸ hR)).elim
    · exact hh

end Plank.PlanarEqualityChartExit

/-- info: 'Plank.PlanarEqualityChartExit.exists_boundary_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarEqualityChartExit.exists_boundary_equality
