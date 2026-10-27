/- Assemble the actual continuous endpoint partials directly into C1 regularity. -/
module

public import Plank.Proofs.Quant.PlanarParameterDerivatives
public import Plank.Proofs.Quant.FinitePartialCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarChartRegularity

open Set MeasureTheory PlanarQuantitative PlanarPlankCellCharts PlanarPolygonCharts
open PlanarParameterDerivatives
open scoped Topology

variable {κ : Type*} [Fintype κ]

/-- The candidate full derivative assembled from the endpoint partials. -/
def endpointGradient (dl dh : κ → ℝ) : EndpointSpace κ →L[ℝ] ℝ :=
  ∑ i, (dl i • (loMap i).linear.toContinuousLinearMap +
    dh i • (hiMap i).linear.toContinuousLinearMap)

theorem endpointGradient_apply (dl dh : κ → ℝ) (z : EndpointSpace κ) :
    endpointGradient dl dh z = ∑ i, (dl i*z.1 i+dh i*z.2 i) := by
  simp [endpointGradient, loMap, hiMap]

theorem endpointGradient_lower [DecidableEq κ] (dl dh : κ → ℝ) (i : κ) :
    endpointGradient dl dh (Pi.single i 1, 0) = dl i := by
  simp [endpointGradient_apply, Pi.single_apply]

theorem endpointGradient_upper [DecidableEq κ] (dl dh : κ → ℝ) (i : κ) :
    endpointGradient dl dh (0, Pi.single i 1) = dh i := by
  simp [endpointGradient_apply, Pi.single_apply]

theorem continuous_endpointGradient (dl dh : κ → EndpointSpace κ → ℝ)
    (hl : ∀ i, Continuous (dl i)) (hh : ∀ i, Continuous (dh i)) :
    Continuous (fun e => endpointGradient (fun i => dl i e) (fun i => dh i e)) := by
  unfold endpointGradient
  apply continuous_finsetSum
  intro i _
  exact ((hl i).smul continuous_const).add ((hh i).smul continuous_const)

theorem endpoint_linear_ext [DecidableEq κ] (D E : EndpointSpace κ →L[ℝ] ℝ)
    (hl : ∀ i, D (Pi.single i 1, 0) = E (Pi.single i 1, 0))
    (hh : ∀ i, D (0, Pi.single i 1) = E (0, Pi.single i 1)) : D = E := by
  exact ContinuousLinearMap.prod_ext
    (ContinuousLinearMap.coe_injective ((Pi.basisFun ℝ κ).ext (by simpa using hl)))
    (ContinuousLinearMap.coe_injective ((Pi.basisFun ℝ κ).ext (by simpa using hh)))

/-- Whenever the full derivative exists, the independently constructed
actual endpoint partials determine it uniquely. -/
theorem derivative_eq_endpointGradient [DecidableEq κ]
    (G : EndpointSpace κ → ℝ) (e : EndpointSpace κ) (D : EndpointSpace κ →L[ℝ] ℝ)
    (dl dh : κ → ℝ) (hD : HasFDerivAt G D e)
    (hl : ∀ i, HasDerivAt (fun t => G (Function.update e.1 i t, e.2)) (dl i) (e.1 i))
    (hh : ∀ i, HasDerivAt (fun t => G (e.1, Function.update e.2 i t)) (dh i) (e.2 i)) :
    D = endpointGradient dl dh := by
  apply endpoint_linear_ext
  · intro i
    rw [endpointGradient_lower]
    have hp := (hasDerivAt_update e.1 i (e.1 i)).prodMk (hasDerivAt_const (e.1 i) e.2)
    have hd := hD.comp_hasDerivAt_of_eq (e.1 i) hp (by simp)
    exact hd.unique (hl i)
  · intro i
    rw [endpointGradient_upper]
    have hp := (hasDerivAt_const (e.2 i) e.1).prodMk (hasDerivAt_update e.2 i (e.2 i))
    have hd := hD.comp_hasDerivAt_of_eq (e.2 i) hp (by simp)
    exact hd.unique (hh i)

theorem hasFDerivWithinAt_finite_iUnion {σ E : Type*} [Fintype σ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → ℝ) (D : E →L[ℝ] ℝ) (x : E) (S : σ → Set E)
    (h : ∀ i, HasFDerivWithinAt G D (S i) x) :
    HasFDerivWithinAt G D (⋃ i, S i) x := by
  classical
  have hs (s : Finset σ) : HasFDerivWithinAt G D (⋃ i ∈ s, S i) x := by
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih => simpa only [Finset.set_biUnion_insert] using (h i).union ih
  simpa only [Finset.mem_univ, iUnion_true] using hs Finset.univ

theorem mem_closure_inter_of_open {E : Type*} [TopologicalSpace E]
    {S U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ closure S) (hxu : x ∈ U) :
    x ∈ closure (S ∩ U) := by
  exact hU.closure_inter ⟨hx, hxu⟩

/-- Continuous partials agree with each smooth chart's full derivative
on its closure. Finite closed-cover gluing then proves actual C1 regularity,
including all incidence walls. No full differentiability is assumed. -/
theorem contDiffOn_of_charts_and_partials {σ : Type*} [Fintype σ] [DecidableEq κ]
    (G : EndpointSpace κ → ℝ) (U : Set (EndpointSpace κ)) (hU : IsOpen U)
    (C : σ → Set (EndpointSpace κ)) (hC : ∀ i, IsOpen (C i))
    (hcover : (⋃ i, closure (C i)) = univ)
    (q : σ → EndpointSpace κ → ℝ) (hq : ∀ i, ContDiff ℝ 1 (q i))
    (hvalue : ∀ i, ∀ e ∈ closure (C i) ∩ U, G e = q i e)
    (dl dh : κ → EndpointSpace κ → ℝ)
    (hlc : ∀ i, Continuous (dl i)) (hhc : ∀ i, Continuous (dh i))
    (hpartials : ∀ e ∈ U, ∀ i,
      HasDerivAt (fun t => G (Function.update e.1 i t, e.2)) (dl i e) (e.1 i) ∧
      HasDerivAt (fun t => G (e.1, Function.update e.2 i t)) (dh i e) (e.2 i)) :
    ContDiffOn ℝ 1 G U := by
  let D (e : EndpointSpace κ) := endpointGradient (fun i => dl i e) (fun i => dh i e)
  have hD : Continuous D := continuous_endpointGradient dl dh hlc hhc
  have hfd (i : σ) (e : EndpointSpace κ) : HasFDerivAt (q i) (fderiv ℝ (q i) e) e :=
    ((hq i).differentiable (by norm_num) e).hasFDerivAt
  have hmatch (i : σ) : ∀ e ∈ C i ∩ U, fderiv ℝ (q i) e = D e := by
    intro e he
    have heq : G =ᶠ[nhds e] q i := by
      filter_upwards [((hC i).inter hU).mem_nhds he] with x hx
      exact hvalue i x ⟨subset_closure hx.1, hx.2⟩
    exact derivative_eq_endpointGradient G e _ _ _ ((hfd i e).congr_of_eventuallyEq heq)
      (fun j => (hpartials e he.2 j).1) (fun j => (hpartials e he.2 j).2)
  have hclosed (i : σ) : ∀ e ∈ closure (C i) ∩ U, fderiv ℝ (q i) e = D e := by
    intro e he
    exact Set.EqOn.closure (hmatch i) ((hq i).continuous_fderiv (by norm_num)) hD
      (hU.closure_inter he)
  have hglobal (e : EndpointSpace κ) (he : e ∈ U) : HasFDerivAt G (D e) e := by
    have hpiece (i : σ) : HasFDerivWithinAt G (D e) (closure (C i) ∩ U) e := by
      by_cases hmem : e ∈ closure (C i)
      · exact (((hfd i e).congr_fderiv (hclosed i e ⟨hmem, he⟩)).hasFDerivWithinAt).congr'
          (hvalue i) ⟨hmem, he⟩
      · apply HasFDerivWithinAt.of_notMem_closure
        intro hx
        apply hmem
        have hc := closure_mono (inter_subset_left : closure (C i) ∩ U ⊆ closure (C i)) hx
        simpa only [closure_closure] using hc
    have hall := hasFDerivWithinAt_finite_iUnion G (D e) e (fun i => closure (C i) ∩ U) hpiece
    have hunion : (⋃ i, closure (C i) ∩ U) = U := by rw [← iUnion_inter, hcover, univ_inter]
    rw [hunion] at hall
    exact hall.hasFDerivAt (hU.mem_nhds he)
  intro e he
  exact (contDiffAt_one_iff.mpr ⟨D, U, hU.mem_nhds he, hD.continuousOn, hglobal⟩).contDiffWithinAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem contDiff_affine (f : E →ᵃ[ℝ] ℝ) : ContDiff ℝ 1 f := by
  rw [f.decomp]
  exact f.linear.toContinuousLinearMap.contDiff.add contDiff_const

theorem contDiff_quadratic (q : QuadraticFormula E) : ContDiff ℝ 1 q.eval := by
  apply ContDiff.sum
  intro i _
  exact (contDiff_affine (q.left i)).mul (contDiff_affine (q.right i))

theorem contDiffOn_area_of_transverse_halfplanes_nonempty {ι : Type*} [Fintype ι]
    [Nonempty κ] [DecidableEq κ]
    (K : Set Point) (hcompact : IsCompact K) (hne : K.Nonempty)
    (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (hK : K = {x | ∀ j, F j x ≤ C j})
    (f : κ → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, 0 < Plank.Convex.DeficientHeightTilt.rangeWidth K (f i))
    (hbody : ∀ i j, PlanarDirectionDerivatives.cross (f i) (F j) ≠ 0)
    (hpairs : ∀ i j, i ≠ j → PlanarDirectionDerivatives.cross (f i) (f j) ≠ 0) :
    ContDiffOn ℝ 1 (area K f) {e : EndpointSpace κ | ∀ i, e.1 i < e.2 i} := by
  classical
  have hfn (i) := PlanarGapCells.linear_ne_zero_of_rangeWidth_pos hne (f i) (hf i)
  obtain ⟨dl, dh, hcont, hpartials⟩ := exists_continuous_partials K hcompact F C hK
    f hfn hbody hpairs
  have hopen : IsOpen {e : EndpointSpace κ | ∀ i, e.1 i < e.2 i} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt
      ((continuous_apply i).comp continuous_fst) ((continuous_apply i).comp continuous_snd))
  exact FinitePartialCalculus.contDiffOn_one_fintype_prod_of_continuousOn_partials hopen
    (fun i => (hcont i).1.continuousOn) (fun i => (hcont i).2.continuousOn)
    (fun e he i => (hpartials e he i).1) (fun e he i => (hpartials e he i).2)

/-- The actual uncovered area of a compact finite-half-plane body is C1
on strictly ordered endpoints when plank directions are pairwise transverse
and each body boundary direction is transverse to every plank. The actual
continuous partials give the full derivative without constructing area charts.
This holds for any finite number of planks, including zero. -/
theorem contDiffOn_area_of_transverse_halfplanes {ι : Type*} [Fintype ι] [DecidableEq κ]
    (K : Set Point) (hcompact : IsCompact K) (hne : K.Nonempty)
    (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (hK : K = {x | ∀ j, F j x ≤ C j})
    (f : κ → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, 0 < Plank.Convex.DeficientHeightTilt.rangeWidth K (f i))
    (hbody : ∀ i j, PlanarDirectionDerivatives.cross (f i) (F j) ≠ 0)
    (hpairs : ∀ i j, i ≠ j → PlanarDirectionDerivatives.cross (f i) (f j) ≠ 0) :
    ContDiffOn ℝ 1 (area K f) {e : EndpointSpace κ | ∀ i, e.1 i < e.2 i} := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · let := hκ
    have heq : area K f = fun _ => (volume K).toReal := by
      funext e
      simp [area]
    rw [heq]
    exact contDiff_const.contDiffOn
  · let := hκ
    exact contDiffOn_area_of_transverse_halfplanes_nonempty K hcompact hne F C hK f hf hbody hpairs

end Plank.PlanarChartRegularity
