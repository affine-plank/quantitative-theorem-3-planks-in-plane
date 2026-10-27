/- Endpoint derivatives of actual uncovered polygonal sections. -/
module

public import Plank.Proofs.Quant.PlanarSectionDerivatives
public import Plank.Proofs.Quant.PlanarPlankCellCharts

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarGapSectionDerivatives

open Set MeasureTheory PlanarQuantitative PlanarPolygonHalfplanes PlanarSectionDerivatives
open PlanarGapCells PlanarPlankCellCharts
open scoped Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The portion of a boxed polygon left after the given closed planks. -/
def boxedGap (a b c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (lo hi : κ → ℝ) : Set Point :=
  boxedRegion a b c d A B C \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}

omit [Fintype ι] in
theorem measurableSet_boxedGap (a b c d : ℝ) (A B C : ι → ℝ)
    (f : κ → Point →ᵃ[ℝ] ℝ) (lo hi : κ → ℝ) :
    MeasurableSet (boxedGap a b c d A B C f lo hi) :=
  (isCompact_boxedRegion a b c d A B C).measurableSet.diff
    (MeasurableSet.iUnion (fun i =>
      (measurableSet_le measurable_const (continuous_form (f i)).measurable).inter
        (measurableSet_le (continuous_form (f i)).measurable measurable_const)))

omit [Fintype ι] [Fintype κ] in
theorem measure_boxedGap_ne_top (a b c d : ℝ) (A B C : ι → ℝ)
    (f : κ → Point →ᵃ[ℝ] ℝ) (lo hi : κ → ℝ) :
    volume (boxedGap a b c d A B C f lo hi) ≠ ⊤ :=
  measure_ne_top_of_subset sdiff_subset (isCompact_boxedRegion a b c d A B C).measure_ne_top

/-- Sum of the lengths of the exterior sign-cell sections. Endpoints may
be unordered in this definition; the area identity uses ordered windows. -/
def residualSectionLength (c d : ℝ) (A B C : ι → ℝ)
    (f : κ → Point →ᵃ[ℝ] ℝ) (e : EndpointSpace κ) (x : ℝ) : ℝ :=
  ∑ s : Finset κ, boxedSectionLength c d (cellA A f s) (cellB B f s)
    (fun i => cellC C f s i e) x

/-- Residual section lengths are jointly continuous in every plank
endpoint and the section level, including all incidences. -/
theorem continuous_residualSectionLength (c d : ℝ) (A B C : ι → ℝ)
    (f : κ → Point →ᵃ[ℝ] ℝ) :
    Continuous (fun p : EndpointSpace κ × ℝ =>
      residualSectionLength c d A B C f p.1 p.2) := by
  classical
  apply continuous_finsetSum
  intro s _
  apply continuous_boxedSectionLength
  · exact continuous_const
  · exact continuous_const
  · intro i
    exact (PlanarPolygonCharts.continuous_affine (cellC C f s i)).comp continuous_fst
  · exact continuous_snd

omit [Fintype ι] [Fintype κ] in
theorem cellB_ne_zero (B : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hB : ∀ i, B i ≠ 0) (hf : ∀ i, (f i).linear (Pi.single 1 1) ≠ 0)
    (s : Finset κ) : ∀ i, cellB B f s i ≠ 0 := by
  classical
  intro i
  cases i with
  | inl i => exact hB i
  | inr i =>
    by_cases his : i ∈ s <;> simp [cellB, his, hf i]

omit [Fintype ι] in
theorem area_boxedGap_eq_sum (a b c d : ℝ) (A B C : ι → ℝ)
    (f : κ → Point →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : κ → ℝ) (hwidth : ∀ i, lo i ≤ hi i) :
    (volume (boxedGap a b c d A B C f lo hi)).toReal =
      ∑ s : Finset κ, (volume (boxedRegion a b c d
        (cellA A f s) (cellB B f s) (fun i => cellC C f s i (lo, hi)))).toReal := by
  have hK := isCompact_boxedRegion a b c d A B C
  have heq := measure_gap_eq_sum_signCells hK.measurableSet f hf lo hi hwidth
  change (volume (boxedGap a b c d A B C f lo hi)) = _ at heq
  rw [heq, ENNReal.toReal_sum (fun s _ => (isCompact_signCell hK f lo hi s).measure_ne_top)]
  exact Finset.sum_congr rfl (fun s _ => congrArg (fun T => (volume T).toReal)
    (signCell_eq_boxedRegion a b c d A B C f (lo, hi) s))

/-- Moving the right cut of the actual gap has derivative equal to the
residual section length. Other plank directions must be transverse to the
cut; the body half-planes here satisfy the same explicit condition. -/
theorem hasDerivAt_area_boxedGap_right {a b : ℝ} (hab : a < b)
    (c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hB : ∀ i, B i ≠ 0) (hf : ∀ i, (f i).linear (Pi.single 1 1) ≠ 0)
    (lo hi : κ → ℝ) (hwidth : ∀ i, lo i ≤ hi i) :
    HasDerivAt (fun t => (volume (boxedGap a t c d A B C f lo hi)).toReal)
      (residualSectionLength c d A B C f (lo, hi) b) b := by
  classical
  have hne (i) : (f i).linear ≠ 0 := by
    intro h
    exact hf i (by rw [h]; rfl)
  have hd (s : Finset κ) (_ : s ∈ Finset.univ) :=
    hasDerivAt_area_boxedRegion_right hab c d (cellA A f s) (cellB B f s)
      (fun i => cellC C f s i (lo, hi)) (cellB_ne_zero B f hB hf s)
  apply (HasDerivAt.fun_sum hd).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => area_boxedGap_eq_sum a t c d A B C f hne lo hi hwidth)

theorem hasDerivAt_area_boxedGap_left {a b : ℝ} (hab : a < b)
    (c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hB : ∀ i, B i ≠ 0) (hf : ∀ i, (f i).linear (Pi.single 1 1) ≠ 0)
    (lo hi : κ → ℝ) (hwidth : ∀ i, lo i ≤ hi i) :
    HasDerivAt (fun t => (volume (boxedGap t b c d A B C f lo hi)).toReal)
      (-residualSectionLength c d A B C f (lo, hi) a) a := by
  classical
  have hne (i) : (f i).linear ≠ 0 := by
    intro h
    exact hf i (by rw [h]; rfl)
  have hd (s : Finset κ) (_ : s ∈ Finset.univ) :=
    hasDerivAt_area_boxedRegion_left hab c d (cellA A f s) (cellB B f s)
      (fun i => cellC C f s i (lo, hi)) (cellB_ne_zero B f hB hf s)
  have hsum := HasDerivAt.fun_sum hd
  simp only [Finset.sum_neg_distrib] at hsum
  apply hsum.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => area_boxedGap_eq_sum t b c d A B C f hne lo hi hwidth)

/-- Add one closed vertical plank to the given family. -/
def verticalGap (a b c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (lo hi : κ → ℝ) (ell h : ℝ) : Set Point :=
  boxedGap a b c d A B C f lo hi \ {x | ell ≤ x 0 ∧ x 0 ≤ h}

omit [Fintype ι] [Fintype κ] in
theorem verticalGap_eq_union {a b ell h : ℝ}
    (hell : a ≤ ell) (horder : ell ≤ h) (hh : h ≤ b)
    (c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ) (lo hi : κ → ℝ) :
    verticalGap a b c d A B C f lo hi ell h =
      (boxedGap a ell c d A B C f lo hi \ {x | x 0 = ell}) ∪
      (boxedGap h b c d A B C f lo hi \ {x | x 0 = h}) := by
  ext x
  constructor
  · rintro ⟨⟨hx, hout⟩, hnot⟩
    by_cases hl : x 0 < ell
    · exact Or.inl ⟨⟨⟨⟨hx.1.1, hl.le⟩, hx.2⟩, hout⟩, ne_of_lt hl⟩
    · have hu : h < x 0 := by
        apply lt_of_not_ge
        intro hu
        exact hnot ⟨le_of_not_gt hl, hu⟩
      exact Or.inr ⟨⟨⟨⟨hu.le, hx.1.2⟩, hx.2⟩, hout⟩, ne_of_gt hu⟩
  · rintro (⟨⟨hx, hout⟩, hneq⟩ | ⟨⟨hx, hout⟩, hneq⟩)
    · refine ⟨⟨⟨⟨hx.1.1, hx.1.2.trans (horder.trans hh)⟩, hx.2⟩, hout⟩, ?_⟩
      exact fun hv => hneq (le_antisymm hx.1.2 hv.1)
    · refine ⟨⟨⟨⟨(hell.trans horder).trans hx.1.1, hx.1.2⟩, hx.2⟩, hout⟩, ?_⟩
      exact fun hv => hneq (le_antisymm hv.2 hx.1.1)

omit [Fintype ι] in
/-- Closing the two residual cut edges changes no area. The decomposition
also includes a zero-width vertical plank. -/
theorem area_verticalGap_eq_sum {a b ell h : ℝ}
    (hell : a ≤ ell) (horder : ell ≤ h) (hh : h ≤ b)
    (c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ) (lo hi : κ → ℝ) :
    (volume (verticalGap a b c d A B C f lo hi ell h)).toReal =
      (volume (boxedGap a ell c d A B C f lo hi)).toReal +
      (volume (boxedGap h b c d A B C f lo hi)).toReal := by
  have hdis : Disjoint
      (boxedGap a ell c d A B C f lo hi \ {x | x 0 = ell})
      (boxedGap h b c d A B C f lo hi \ {x | x 0 = h}) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hlx : x 0 < ell := lt_of_le_of_ne hx.1.1.1.2 hx.2
    exact (not_lt_of_ge (horder.trans hy.1.1.1.1)) hlx
  have hm : MeasurableSet (boxedGap h b c d A B C f lo hi \ {x | x 0 = h}) :=
    (measurableSet_boxedGap h b c d A B C f lo hi).diff
      (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [verticalGap_eq_union hell horder hh, measure_union hdis hm,
    measure_sdiff_null (measure_vertical_line ell), measure_sdiff_null (measure_vertical_line h),
    ENNReal.toReal_add (measure_boxedGap_ne_top a ell c d A B C f lo hi)
      (measure_boxedGap_ne_top h b c d A B C f lo hi)]

/-- Lower-endpoint derivative for an actual plank in an actual uncovered
set. All remaining plank endpoints are free parameters of the continuous
residual-section expression. -/
theorem hasDerivAt_area_verticalGap_lower {a b ell h : ℝ}
    (hell : a < ell) (horder : ell < h) (hh : h < b)
    (c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hB : ∀ i, B i ≠ 0) (hf : ∀ i, (f i).linear (Pi.single 1 1) ≠ 0)
    (lo hi : κ → ℝ) (hwidth : ∀ i, lo i ≤ hi i) :
    HasDerivAt (fun t => (volume (verticalGap a b c d A B C f lo hi t h)).toReal)
      (residualSectionLength c d A B C f (lo, hi) ell) ell := by
  have hd := (hasDerivAt_area_boxedGap_right hell c d A B C f hB hf lo hi hwidth).add_const
    (volume (boxedGap h b c d A B C f lo hi)).toReal
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hell, Iio_mem_nhds horder] with t ht₁ ht₂
  exact area_verticalGap_eq_sum ht₁.le ht₂.le hh.le c d A B C f lo hi

/-- The upper endpoint removes area at the residual-section rate. -/
theorem hasDerivAt_area_verticalGap_upper {a b ell h : ℝ}
    (hell : a < ell) (horder : ell < h) (hh : h < b)
    (c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hB : ∀ i, B i ≠ 0) (hf : ∀ i, (f i).linear (Pi.single 1 1) ≠ 0)
    (lo hi : κ → ℝ) (hwidth : ∀ i, lo i ≤ hi i) :
    HasDerivAt (fun t => (volume (verticalGap a b c d A B C f lo hi ell t)).toReal)
      (-residualSectionLength c d A B C f (lo, hi) h) h := by
  have hd := (hasDerivAt_area_boxedGap_left hh c d A B C f hB hf lo hi hwidth).const_add
    (volume (boxedGap a ell c d A B C f lo hi)).toReal
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds horder, Iio_mem_nhds hh] with t ht₁ ht₂
  exact area_verticalGap_eq_sum hell.le ht₁.le ht₂.le c d A B C f lo hi

end Plank.PlanarGapSectionDerivatives
