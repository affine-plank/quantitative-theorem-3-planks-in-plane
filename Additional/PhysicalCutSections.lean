/- Actual exposed sections in a physical affine coordinate, in any dimension. -/
module
public import InternalCutTrace
public import FiniteDimensionalCutCoordinates

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PhysicalCutSections

open Set MeasureTheory FiniteDimensionalCutCoordinates
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def scale (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1) : ℝ :=
  (exists_volume_factor μ f.linear v hv).choose

theorem scale_pos (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1) : 0<scale μ f v hv :=
  (exists_volume_factor μ f.linear v hv).choose_spec.1

theorem volume_eq (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1)
    {S : Set E} (hS : MeasurableSet S) :
    μ.real S=scale μ f v hv*(volume.prod (Measure.addHaar : Measure f.linear.ker)).real
      (split f.linear v hv ⁻¹' S) :=
  (exists_volume_factor μ f.linear v hv).choose_spec.2 S hS

def residual (K : Set E) (s : Finset ι) (H : ι → E →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) : Set E := K\⋃ j∈s,{x | lo j≤H j x ∧ H j x≤hi j}

def sectionSet (K : Set E) (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1)
    (s : Finset ι) (H : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (a : ℝ) :
    Set f.linear.ker :=
  {y | split f.linear v hv (a-f 0,y)∈residual K s H lo hi}

def rate (μ : Measure E) [μ.IsAddHaarMeasure] (K : Set E)
    (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1)
    (s : Finset ι) (H : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (a : ℝ) : ℝ :=
  scale μ f v hv*(Measure.addHaar : Measure f.linear.ker).real
    (sectionSet K f v hv s H lo hi a)

/-- Physical transverse first moment, including the Haar change-of-coordinates factor. -/
def moment (μ : Measure E) [μ.IsAddHaarMeasure] (K : Set E)
    (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1)
    (s : Finset ι) (H : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (g : E →ᵃ[ℝ] ℝ) (a : ℝ) : ℝ :=
  scale μ f v hv*∫ y in sectionSet K f v hv s H lo hi a,
    g (y : E) ∂(Measure.addHaar : Measure f.linear.ker)

theorem measurable_residual {K : Set E} (hK : MeasurableSet K)
    (s : Finset ι) (H : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    MeasurableSet (residual K s H lo hi) :=
  hK.diff (s.finite_toSet.measurableSet_biUnion fun j _ =>
    measurableSet_Icc.preimage (H j).continuous_of_finiteDimensional.measurable)

theorem measurable_section {K : Set E} (hK : MeasurableSet K)
    (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1)
    (s : Finset ι) (H : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (a : ℝ) :
    MeasurableSet (sectionSet K f v hv s H lo hi a) :=
  (measurable_residual hK s H lo hi).preimage
    (((split f.linear v hv).toContinuousLinearEquiv.continuous.comp
      (continuous_const.prodMk continuous_id)).measurable)

theorem moment_one (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1)
    (s : Finset ι) (H : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (a : ℝ) :
    moment μ K f v hv s H lo hi (AffineMap.const ℝ E 1) a=
      rate μ K f v hv s H lo hi a := by
  simp [moment,rate,integral_const,Measure.real]

omit [MeasurableSpace E] [BorelSpace E] in
theorem compact_chart {K : Set E} (hK : IsCompact K)
    (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1) :
    IsCompact (split f.linear v hv ⁻¹' K) :=
  (split f.linear v hv).toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr hK

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem internal_cut {K : Set E} (hc : Convex ℝ K)
    (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1) {a : ℝ}
    (ha : ∃ x∈K,f x<a) (hb : ∃ y∈K,a<f y) :
    a-f 0∈interior (Prod.fst '' (split f.linear v hv ⁻¹' K)) := by
  let F := split f.linear v hv
  obtain ⟨x,hx,hxa⟩ := ha
  obtain ⟨y,hy,hay⟩ := hb
  have hfirst (z : E) : (F.symm z).1=f z-f 0 := by
    have he := affine_split f v hv (F.symm z)
    rw [F.apply_symm_apply] at he
    linarith only [he]
  have hxC : (F.symm x).1∈Prod.fst '' (F ⁻¹' K) :=
    ⟨F.symm x,by simpa using hx,rfl⟩
  have hyC : (F.symm y).1∈Prod.fst '' (F ⁻¹' K) :=
    ⟨F.symm y,by simpa using hy,rfl⟩
  have hinterval := ((hc.linear_preimage F.toLinearMap).linear_image
    (LinearMap.fst ℝ ℝ f.linear.ker)).ordConnected.out hxC hyC
  apply interior_mono hinterval
  rw [interior_Icc,hfirst,hfirst]
  constructor <;> linarith only [hxa,hay]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem noncoincident_chart (f H : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1)
    (a b : ℝ) (hsep : ¬∀ x,f x=a → H x=b) :
    {p : ℝ × f.linear.ker | p.1=a-f 0}≠
      {p | H (split f.linear v hv p)=b} := by
  let F := split f.linear v hv
  intro he
  apply hsep
  intro x hx
  have hfirst : (F.symm x).1=a-f 0 := by
    have hh := affine_split f v hv (F.symm x)
    rw [F.apply_symm_apply,hx] at hh
    linarith only [hh]
  have hh := (Set.ext_iff.mp he (F.symm x)).mp hfirst
  simpa [F] using hh

end Plank.PhysicalCutSections
