/- Actual polygonal section lengths and derivatives of moving cuts. -/
module

public import Plank.Proofs.Quant.PlanarPolygonHalfplanes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Lattice

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSectionDerivatives

open Set MeasureTheory PlanarQuantitative PlanarPolygonSlabs PlanarPolygonHalfplanes
open scoped Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

/-- The bottom of a section is the largest of its lower bounds. -/
def lowerEnvelope (ls lc : ι → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ls i*x+lc i)

/-- The top of a section is the smallest of its upper bounds. -/
def upperEnvelope (us uc : κ → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => us i*x+uc i)

theorem lowerEnvelope_le_iff (ls lc : ι → ℝ) (x y : ℝ) :
    lowerEnvelope ls lc x ≤ y ↔ ∀ i, ls i*x+lc i ≤ y := by
  simp [lowerEnvelope, Finset.sup'_le_iff]

theorem le_upperEnvelope_iff (us uc : κ → ℝ) (x y : ℝ) :
    y ≤ upperEnvelope us uc x ↔ ∀ i, y ≤ us i*x+uc i := by
  simp [upperEnvelope, Finset.le_inf'_iff]

/-- The actual length of a section, also when its bounds are reversed. -/
def sectionLength (ls lc : ι → ℝ) (us uc : κ → ℝ) (x : ℝ) : ℝ :=
  max 0 (upperEnvelope us uc x-lowerEnvelope ls lc x)

theorem sectionLength_nonneg (ls lc : ι → ℝ) (us uc : κ → ℝ) (x : ℝ) :
    0 ≤ sectionLength ls lc us uc x := le_max_left _ _

/-- All offsets and the section level may vary together. Incidences and
changes of the active lower or upper edge need no separate cases. -/
theorem continuous_sectionLength {E : Type*} [TopologicalSpace E]
    (ls : ι → ℝ) (lc : ι → E → ℝ) (us : κ → ℝ) (uc : κ → E → ℝ)
    (x : E → ℝ) (hlc : ∀ i, Continuous (lc i)) (huc : ∀ j, Continuous (uc j))
    (hx : Continuous x) :
    Continuous (fun e => sectionLength ls (fun i => lc i e) us (fun j => uc j e) (x e)) := by
  apply continuous_const.max
  exact (Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun j _ => (continuous_const.mul hx).add (huc j))).sub
    (Continuous.finset_sup'_apply Finset.univ_nonempty
      (fun i _ => (continuous_const.mul hx).add (hlc i)))

theorem continuous_sectionLength_level (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    Continuous (sectionLength ls lc us uc) :=
  continuous_sectionLength ls (fun i _ => lc i) us (fun j _ => uc j)
    id (fun _ => continuous_const) (fun _ => continuous_const) continuous_id

theorem slab_eq_between_envelopes (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    slab a b ls lc us uc = between a b (lowerEnvelope ls lc) (upperEnvelope us uc) := by
  ext p
  simp only [slab, between, mem_ofPred_eq, mem_Icc, lowerEnvelope_le_iff,
    le_upperEnvelope_iff]

/-- Fubini identifies the actual closed polygon slab area with the integral
of its continuously varying section length. The integrand is constructed. -/
theorem area_closedSlab_eq_integral {a b : ℝ} (hab : a ≤ b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    (volume (closedSlab a b ls lc us uc)).toReal =
      ∫ x in a..b, sectionLength ls lc us uc x := by
  have hl : Continuous (lowerEnvelope ls lc) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty (fun _ _ => by fun_prop)
  have hu : Continuous (upperEnvelope us uc) :=
    Continuous.finset_inf'_apply Finset.univ_nonempty (fun _ _ => by fun_prop)
  have hc := continuous_sectionLength_level ls lc us uc
  have hint : IntegrableOn (sectionLength ls lc us uc) (Ioc a b) volume :=
    hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] sectionLength ls lc us uc :=
    Filter.Eventually.of_forall (sectionLength_nonneg ls lc us uc)
  rw [measure_closedSlab, measure_coordinateSlab, slab_eq_between_envelopes,
    measure_between a b hl.measurable hu.measurable]
  have heq : (fun x => ENNReal.ofReal (upperEnvelope us uc x-lowerEnvelope ls lc x)) =
      fun x => ENNReal.ofReal (sectionLength ls lc us uc x) := by
    funext x
    simp [sectionLength, ENNReal.ofReal_max]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg),
    ← intervalIntegral.integral_of_le hab]

/-- The derivative with respect to the right cut is its actual section
length, even when the cut passes through vertices or multiple incidences. -/
theorem hasDerivAt_area_closedSlab_right {a b : ℝ} (hab : a < b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    HasDerivAt (fun t => (volume (closedSlab a t ls lc us uc)).toReal)
      (sectionLength ls lc us uc b) b := by
  have hc := continuous_sectionLength_level ls lc us uc
  apply (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a b)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hab] with t ht
  exact area_closedSlab_eq_integral ht.le ls lc us uc

/-- Moving the left cut removes area at the section-length rate. -/
theorem hasDerivAt_area_closedSlab_left {a b : ℝ} (hab : a < b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    HasDerivAt (fun t => (volume (closedSlab t b ls lc us uc)).toReal)
      (-sectionLength ls lc us uc a) a := by
  have hc := continuous_sectionLength_level ls lc us uc
  apply (intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable a b)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hab] with t ht
  exact area_closedSlab_eq_integral ht.le ls lc us uc

/-- Both cuts can move at once. The derivative is constructed directly
from actual section lengths rather than from a selected area chart. -/
theorem hasFDerivAt_area_closedSlab {a b : ℝ} (hab : a < b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => (volume (closedSlab p.1 p.2 ls lc us uc)).toReal)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (sectionLength ls lc us uc b) -
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (sectionLength ls lc us uc a)) (a, b) := by
  have hc := continuous_sectionLength_level ls lc us uc
  apply (intervalIntegral.integral_hasFDerivAt (hc.intervalIntegrable a b)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    hc.continuousAt).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_fst continuous_snd).mem_nhds hab] with p hp
  exact area_closedSlab_eq_integral hp.le ls lc us uc

/-- The derivative formula for a box clipped by any finite collection of
nonvertical half-planes. No ordering or genericity of their intersections is
required; all the other half-plane offsets may be used as parameters. -/
theorem hasDerivAt_area_boxedRegion_right {η : Type*} [Fintype η]
    {a b : ℝ} (hab : a < b) (c d : ℝ) (A B C : η → ℝ) (hB : ∀ i, B i ≠ 0) :
    HasDerivAt (fun t => (volume (boxedRegion a t c d A B C)).toReal)
      (sectionLength
        (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
        (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d) b) b := by
  simpa only [boxedRegion_eq_closedSlab _ _ _ _ _ _ _ hB] using
    hasDerivAt_area_closedSlab_right hab
      (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
      (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d)

theorem hasDerivAt_area_boxedRegion_left {η : Type*} [Fintype η]
    {a b : ℝ} (hab : a < b) (c d : ℝ) (A B C : η → ℝ) (hB : ∀ i, B i ≠ 0) :
    HasDerivAt (fun t => (volume (boxedRegion t b c d A B C)).toReal)
      (-sectionLength
        (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
        (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d) a) a := by
  simpa only [boxedRegion_eq_closedSlab _ _ _ _ _ _ _ hB] using
    hasDerivAt_area_closedSlab_left hab
      (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
      (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d)

/-- The section length in the boxed half-plane representation. -/
def boxedSectionLength {η : Type*} [Fintype η]
    (c d : ℝ) (A B C : η → ℝ) (x : ℝ) : ℝ :=
  sectionLength
    (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
    (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d) x

theorem continuous_boxedSectionLength {η E : Type*} [Fintype η] [TopologicalSpace E]
    (c d : E → ℝ) (A B : η → ℝ) (C : η → E → ℝ) (x : E → ℝ)
    (hc : Continuous c) (hd : Continuous d) (hC : ∀ i, Continuous (C i))
    (hx : Continuous x) :
    Continuous (fun e => boxedSectionLength (c e) (d e) A B (fun i => C i e) (x e)) := by
  apply continuous_sectionLength
  · intro i
    cases i with
    | none => exact hc
    | some i => exact (hC i).div_const (B i)
  · intro i
    cases i with
    | none => exact hd
    | some i => exact (hC i).div_const (B i)
  · exact hx

theorem isCompact_boxedRegion {η : Type*}
    (a b c d : ℝ) (A B C : η → ℝ) : IsCompact (boxedRegion a b c d A B C) := by
  have hbox : {x : Point | x 0 ∈ Icc a b ∧ x 1 ∈ Icc c d} =
      Icc ![a, c] ![b, d] := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc, Pi.le_def, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  have hclosed : IsClosed {x : Point | ∀ i, A i*x 0+B i*x 1 ≤ C i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun _ => isClosed_le (by fun_prop) continuous_const)
  have heq : boxedRegion a b c d A B C =
      {x : Point | x 0 ∈ Icc a b ∧ x 1 ∈ Icc c d} ∩
        {x | ∀ i, A i*x 0+B i*x 1 ≤ C i} := by
    ext x
    simp [boxedRegion, and_assoc]
  rw [heq, hbox]
  exact isCompact_Icc.inter_right hclosed

end Plank.PlanarSectionDerivatives
