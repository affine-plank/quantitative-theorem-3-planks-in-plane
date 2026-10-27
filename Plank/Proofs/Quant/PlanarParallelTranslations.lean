/- Equality for parallel planks forces a closed cover by correctly sided
homothetic pieces. The construction works on every planar convex body. -/
module

public import Plank.Proofs.Quant.PlanarParallelSections
public import Plank.Algebra.MonotoneSubset

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelTranslations

open Set MeasureTheory Function PlanarQuantitative PlanarGapCells PlanarParallelSections
open scoped Pointwise

variable {ι : Type*} [Fintype ι]

def widths (lo hi : ι → ℝ) (i : ι) := hi i-lo i
def total (lo hi : ι → ℝ) := ∑ i, widths lo hi i
def selected (lo hi : ι → ℝ) (s : Finset ι) := ∑ i ∈ s, widths lo hi i

def translations (lo hi : ι → ℝ) (a b : Point) (s : Finset ι) : Point :=
  total lo hi • b+selected lo hi s • (a-b)

def center (lo hi : ι → ℝ) (a b : Point) (s : Finset ι) : Point :=
  (1-selected lo hi s/total lo hi) • b+(selected lo hi s/total lo hi) • a

theorem selected_bounds (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i) (s : Finset ι) :
    0 ≤ selected lo hi s ∧ selected lo hi s ≤ total lo hi := by
  have hr (i) : 0 ≤ widths lo hi i := sub_nonneg.mpr (ho i)
  exact ⟨Finset.sum_nonneg (fun i _ => hr i),Finset.sum_le_univ_sum_of_nonneg hr⟩

theorem translations_eq (lo hi : ι → ℝ) (a b : Point) (s : Finset ι)
    (hR : total lo hi ≠ 0) : translations lo hi a b s = total lo hi • center lo hi a b s := by
  ext i
  change total lo hi*b i+selected lo hi s*(a i-b i) =
    total lo hi*((1-selected lo hi s/total lo hi)*b i+(selected lo hi s/total lo hi)*a i)
  field_simp
  ring

theorem center_level (lo hi : ι → ℝ) (f : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (hfa : f a = 1) (hfb : f b = 0) (s : Finset ι) :
    f (center lo hi a b s) = selected lo hi s/total lo hi := by
  rw [center,map_combo,hfa,hfb,mul_zero,mul_one,zero_add]

theorem translated_level (lo hi : ι → ℝ) (f : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (hfa : f a = 1) (hfb : f b = 0) (s : Finset ι) (x : Point) :
    f (x+translations lo hi a b s) = f (x+total lo hi • b)+selected lo hi s := by
  have hl : f.linear (a-b) = 1 := by
    have hh := f.linearMap_vsub a b
    simpa only [vsub_eq_sub,hfa,hfb,sub_zero] using hh
  rw [affine_eval f (x+translations lo hi a b s),affine_eval f (x+total lo hi • b)]
  simp only [translations,map_add,map_smul,smul_eq_mul,hl,mul_one]
  ring

theorem weak_assignments (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (hfa : f a = 1) (hfb : f b = 0) (x : Point) :
    ∃ s, x+translations lo hi a b s ∈ LinearBands.weakCell (fun _ => f) lo hi s := by
  classical
  obtain ⟨s,hh,hl⟩ := MonotoneSubset.exists_side_assignment
    (fun _ : ι => f (x+total lo hi • b)) (fun j _ => widths lo hi j)
    (fun j _ => sub_nonneg.mpr (ho j)) lo hi (fun _ => le_rfl)
  refine ⟨s,fun i => ?_⟩
  by_cases his : i ∈ s <;> simp only [his,↓reduceIte]
  · rw [translated_level lo hi f a b hfa hfb]
    exact (hh i his).le
  · rw [translated_level lo hi f a b hfa hfb]
    exact hl i his

theorem translated_inside {K : Set Point} (hconv : Convex ℝ K)
    (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i) (hR : 0 < total lo hi)
    (hR1 : total lo hi < 1) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (s : Finset ι) (x : Point) (hx : x ∈ (1-total lo hi) • K) :
    x+translations lo hi a b s ∈ K := by
  obtain ⟨y,hy,rfl⟩ := hx
  have hs := selected_bounds lo hi ho s
  have hr : selected lo hi s/total lo hi ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hR.le,(div_le_one hR).mpr hs.2⟩
  have hc : center lo hi a b s ∈ K :=
    hconv hb ha (sub_nonneg.mpr hr.2) hr.1 (sub_add_cancel 1 _)
  rw [translations_eq lo hi a b s hR.ne']
  exact hconv hy hc (sub_pos.mpr hR1).le hR.le (sub_add_cancel 1 _)

def closedCover (K : Set Point) (lo hi : ι → ℝ) (f : Point →ᵃ[ℝ] ℝ) (a b : Point) : Set Point :=
  (⋃ i, LinearBands.closedBand f (lo i) (hi i)) ∪
    ⋃ s : Finset ι, ((fun x => x-translations lo hi a b s) ⁻¹' ((1-total lo hi) • K)) ∩
      LinearBands.weakCell (fun _ => f) lo hi s

omit [Fintype ι] in
theorem isClosed_weakCell (lo hi : ι → ℝ) (f : Point →ᵃ[ℝ] ℝ) (s : Finset ι) :
    IsClosed (LinearBands.weakCell (fun _ => f) lo hi s) := by
  classical
  have he : LinearBands.weakCell (fun _ => f) lo hi s =
      ⋂ i, {x | if i ∈ s then hi i ≤ f x else f x ≤ lo i} := by
    ext x
    simp [LinearBands.weakCell]
  rw [he]
  apply isClosed_iInter
  intro i
  by_cases his : i ∈ s
  · simpa only [his,↓reduceIte] using isClosed_le continuous_const (continuous_form f)
  · simpa only [his,↓reduceIte] using isClosed_le (continuous_form f) continuous_const

/-- Actual equality gives a closed, pointwise cover by the planks and the
correctly sided homothetic pieces, on arbitrary positive-area convex bodies. -/
theorem equality_implies_closedCover {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hR : 0 < total lo hi) (hR1 : total lo hi < 1)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0)
    (he : (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
      (1-total lo hi)^2*(volume K).toReal) : K ⊆ closedCover K lo hi f a b := by
  let core := (1-total lo hi) • K
  let v := translations lo hi a b
  let cells := LinearBands.strictCell (fun _ : ι => f) lo hi
  let gap := K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i)
  have hc : IsCompact core := hK.image (f := fun x : Point => (1-total lo hi) • x) (by fun_prop)
  have hgfin : volume gap ≠ ⊤ := ne_top_of_le_ne_top hK.measure_ne_top (measure_mono sdiff_subset)
  have hf : f.linear ≠ 0 := by
    intro hz
    obtain ⟨c,hh⟩ := f.linear_eq_zero_iff_exists_const.mp hz
    have h : f a = f b := by rw [hh]; rfl
    rw [hfa,hfb] at h
    norm_num at h
  have harea : (volume core).toReal = (1-total lo hi)^2*(volume K).toReal := by
    rw [volume.addHaar_smul_of_nonneg (sub_pos.mpr hR1).le,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (sub_pos.mpr hR1).le _)]
    simp only [Module.finrank_pi,Fintype.card_fin]
  have hmeasure : volume core = volume gap :=
    (ENNReal.toReal_eq_toReal_iff' hc.measure_ne_top hgfin).mp (harea.trans he.symm)
  have hp := (Quant.TranslationEquality.closed_gap_measure_eq_iff volume
    (fun _ : ι => f) (fun _ => (continuous_form f).measurable) lo hi ho
    (fun i => measure_level_zero f hf (lo i)) (fun i => measure_level_zero f hf (hi i))
    core hc.measurableSet v (fun x _ => weak_assignments lo hi ho f a b hfa hfb x)
    K hK.measure_ne_top (translated_inside hconv lo hi ho hR hR1 a b ha hb)).mp hmeasure
  let U := ⋃ s, Quant.TranslationEquality.targetPiece core v cells s
  have hnull : volume (gap \ U) = 0 := ae_le_set.mp hp.2.symm.le
  have hclosed : IsClosed (closedCover K lo hi f a b) := by
    apply IsClosed.union
    · apply isClosed_iUnion_of_finite
      intro i
      exact (isClosed_le continuous_const (continuous_form f)).inter
        (isClosed_le (continuous_form f) continuous_const)
    · apply isClosed_iUnion_of_finite
      intro s
      exact (hc.isClosed.preimage (by fun_prop)).inter (isClosed_weakCell lo hi f s)
  have hsub : K \ closedCover K lo hi f a b ⊆ gap \ U := by
    intro x hx
    refine ⟨⟨hx.1,fun hh => hx.2 (Or.inl hh)⟩,?_⟩
    intro hu
    obtain ⟨s,hs⟩ := mem_iUnion.mp hu
    apply hx.2
    right
    refine mem_iUnion.mpr ⟨s,hs.1,fun i => ?_⟩
    have hh := hs.2 i
    by_cases his : i ∈ s <;> simp only [his,↓reduceIte] at hh ⊢ <;> exact hh.le
  apply (PlanarGapAnalysis.area_sdiff_eq_zero_iff_subset hK hconv hV hclosed).mp
  rw [measure_mono_null hsub hnull,ENNReal.toReal_zero]

end Plank.PlanarParallelTranslations

/-- info: 'Plank.PlanarParallelTranslations.equality_implies_closedCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelTranslations.equality_implies_closedCover
