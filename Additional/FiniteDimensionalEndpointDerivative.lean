/- Differentiability of actual uncovered volume under a physical endpoint
variation in any finite dimension, including separated parallel boundaries. -/
module
public import PhysicalCutSections
public import PrunedPlankCounterexample

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalEndpointDerivative

open Set MeasureTheory PrunedPlankCounterexample FiniteDimensionalCutCoordinates
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

def gap (K : Set E) (g : E →ᵃ[ℝ] ℝ) (f : ι → E →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (a b : ℝ) : Set E :=
  (K\covered f lo hi)\{x | a≤g x ∧ g x≤b}

theorem measurable_gap {K : Set E} (hK : MeasurableSet K)
    (g : E →ᵃ[ℝ] ℝ) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (a b : ℝ) :
    MeasurableSet (gap K g f lo hi a b) := by
  have hcov : MeasurableSet (covered f lo hi) := MeasurableSet.iUnion fun i =>
    measurableSet_Icc.preimage (f i).continuous_of_finiteDimensional.measurable
  exact (hK.diff hcov).diff
    (measurableSet_Icc.preimage g.continuous_of_finiteDimensional.measurable)

omit [Fintype ι] in
/-- The actual upper-endpoint derivative, with its exposed section rate.
No positive-volume hypothesis or nonconstant fixed form is required. -/
theorem hasDerivAt_residual_upper (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (g : E →ᵃ[ℝ] ℝ) (v : E) (hv : g.linear v=1)
    (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) {a b : ℝ} (hab : a<b)
    (hleft : ∃ x∈K,g x<b) (hright : ∃ y∈K,b<g y)
    (hsep : ∀ j∈s,∀ d∈({lo j,hi j} : Set ℝ),¬∀ x,g x=b → f j x=d) :
    HasDerivAt (fun t => μ.real (PhysicalCutSections.residual K s f lo hi\
      {x | a≤g x ∧ g x≤t}))
      (-PhysicalCutSections.rate μ K g v hv s f lo hi b) b := by
  let F := split g.linear v hv
  let ν : Measure g.linear.ker := Measure.addHaar
  let C := F ⁻¹' K
  let H (j : ι) := (f j).comp F.toAffineMap
  let S := NoncoincidentCutDerivatives.residual C s H lo hi
  have hC : IsCompact C := PhysicalCutSections.compact_chart hK g v hv
  have hCc : Convex ℝ C := hc.linear_preimage F.toLinearMap
  have hcut := PhysicalCutSections.internal_cut hc g v hv hleft hright
  have hdensity := InternalCutTrace.continuousAt_residual_density ν hC hCc s H lo hi hcut
    (fun j hj d hd => PhysicalCutSections.noncoincident_chart g (f j) v hv b d (hsep j hj d hd))
  have hder := MovingCutArea.hasDerivAt_gapArea_upper ν
    (NoncoincidentCutDerivatives.measurable_residual hC.measurableSet s H lo hi)
    (measure_ne_top_of_subset sdiff_subset hC.measure_ne_top)
    (sub_lt_sub_right hab (g 0)) hdensity
  have hgap (t : ℝ) : μ.real (PhysicalCutSections.residual K s f lo hi\
      {x | a≤g x ∧ g x≤t})=
      PhysicalCutSections.scale μ g v hv*MovingCutArea.gapArea ν S (a-g 0) (t-g 0) := by
    have hm : MeasurableSet {x | a≤g x ∧ g x≤t} :=
      measurableSet_Icc.preimage g.continuous_of_finiteDimensional.measurable
    rw [PhysicalCutSections.volume_eq μ g v hv
      ((PhysicalCutSections.measurable_residual hK.measurableSet s f lo hi).diff
        hm)]
    congr 2
    ext p
    have hgF := affine_split g v hv p
    simp only [PhysicalCutSections.residual,S,C,
      NoncoincidentCutDerivatives.residual,mem_preimage,mem_sdiff,mem_iUnion,
      mem_ofPred_eq,mem_prod,mem_Icc,mem_univ,and_true,H,
      AffineMap.comp_apply,LinearMap.coe_toAffineMap,LinearEquiv.coe_coe,F,hgF,
      sub_le_iff_le_add,le_sub_iff_add_le]
  have hd := ((hder.comp b ((hasDerivAt_id b).sub_const (g 0))).const_mul
    (PhysicalCutSections.scale μ g v hv)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hgap)
  have he : PhysicalCutSections.sectionSet K g v hv s f lo hi b=Prod.mk (b-g 0) ⁻¹' S := by
    ext y
    simp [PhysicalCutSections.sectionSet,PhysicalCutSections.residual,
      NoncoincidentCutDerivatives.residual,S,C,H,F]
  simpa only [PhysicalCutSections.rate,he,MovingCutArea.density,mul_one,mul_neg] using hd

/-- The endpoints lie inside the body's projection and no other boundary
contains the moving cut. The assertion concerns physical Haar volume. -/
theorem differentiableAt_upper (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (_hV : 0<μ.real K)
    (g : E →ᵃ[ℝ] ℝ) (hg : g.linear≠0) (f : ι → E →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) {a b : ℝ} (hab : a<b)
    (hleft : ∃ x∈K,g x<b) (hright : ∃ y∈K,b<g y)
    (hsep : ∀ j, (¬{x | g x=b}⊆{x | f j x=lo j}) ∧
      (¬{x | g x=b}⊆{x | f j x=hi j})) :
    DifferentiableAt ℝ (fun t => μ.real (gap K g f lo hi a t)) b := by
  obtain ⟨v,hv⟩ := exists_unit_vector g.linear hg
  have hd := hasDerivAt_residual_upper μ hK hc g v hv Finset.univ f lo hi hab hleft hright (by
    intro j _ d hd
    rcases hd with rfl | rfl
    · exact (hsep j).1
    · exact (hsep j).2)
  simpa only [PhysicalCutSections.residual,gap,covered,Finset.mem_univ,iUnion_true] using
    hd.differentiableAt

end Plank.FiniteDimensionalEndpointDerivative
