/- A calibrated diagonal cut cannot amplify the maximum oblique section. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralObliqueSections
public import Plank.Proofs.Quant.CrossedQuadrilateralCaps

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCalibratedSections
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralObliqueSections
open scoped Pointwise

theorem fiber_homothet (A : Set Point) (η δ k q : ℝ) (hδ : δ ≠ 0) :
    fiber ((fun z : Point => (0,η)+δ • z) '' A) k q =
      (fun y : ℝ => η+δ*y) '' fiber A k ((q-k*η)/δ) := by
  ext y
  constructor
  · rintro ⟨z,hz,he⟩
    have hx : δ*z.1 = q-k*y := by
      simpa only [Prod.fst_add,Prod.smul_fst,smul_eq_mul,zero_add] using congrArg Prod.fst he
    have hy : η+δ*z.2 = y := congrArg Prod.snd he
    have hx' : z.1+k*z.2 = (q-k*η)/δ := by
      apply (eq_div_iff hδ).mpr
      linear_combination hx+k*hy
    have hcoord : (q-k*η)/δ-k*z.2 = z.1 := by linarith only [hx']
    refine ⟨z.2,?_,hy⟩
    change ((q-k*η)/δ-k*z.2,z.2) ∈ A
    simpa only [hcoord] using hz
  · rintro ⟨y,hy,rfl⟩
    refine ⟨((q-k*η)/δ-k*y,y),hy,?_⟩
    ext
    · change 0+δ*((q-k*η)/δ-k*y) = q-k*(η+δ*y)
      field_simp [hδ]
      ring
    · rfl

theorem length_translate_scale (A : Set ℝ) (η δ : ℝ) (hδ : 0 ≤ δ) :
    (volume ((fun y : ℝ => η+δ*y) '' A)).toReal = δ*(volume A).toReal := by
  have he : (fun y : ℝ => η+δ*y) '' A = (fun y : ℝ => η+y) '' (δ • A) := by
    rw [← Set.image_smul,Set.image_image]
    rfl
  rw [he,Set.image_add_left,measure_preimage_add,Measure.addHaar_smul_of_nonneg volume hδ]
  simp only [Module.finrank_self,pow_one,ENNReal.toReal_mul,ENNReal.toReal_ofReal hδ]

theorem cap_length (S : Shape) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (j : Bool) (k q : ℝ) :
    sectionLength (CrossedQuadrilateralCaps.cap S r j) k q =
      (1-r)*sectionLength (CrossedQuadrilateralCaps.half S j) k ((q-k*(S.Y j*r))/(1-r)) := by
  rw [CrossedQuadrilateralCaps.cap_eq_image S hr hr1,sectionLength,
    fiber_homothet _ _ _ _ _ (sub_pos.mpr hr1).ne',
    length_translate_scale _ _ _ (sub_pos.mpr hr1).le]
  rfl

theorem half_false (S : Shape) : CrossedQuadrilateralCaps.half S false = lower S := by
  ext z
  change (z ∈ S.body ∧ 0 ≤ z.2/(-S.d)) ↔ (z ∈ S.body ∧ z.2 ≤ 0)
  rw [le_div_iff_of_neg (neg_neg_of_pos S.hd),zero_mul]

theorem half_true (S : Shape) : CrossedQuadrilateralCaps.half S true = upper S := by
  ext z
  change (z ∈ S.body ∧ 0 ≤ z.2/S.b) ↔ (z ∈ S.body ∧ 0 ≤ z.2)
  rw [le_div_iff₀ S.hb,zero_mul]

def closedResidual (S : Shape) (r : ℝ) : Set Point :=
  CrossedQuadrilateralCaps.cap S r false ∪ CrossedQuadrilateralCaps.cap S r true

theorem compact_residual (S : Shape) (r : ℝ) : IsCompact (closedResidual S r) :=
  (CrossedQuadrilateralCaps.compact_cap S r false).union
    (CrossedQuadrilateralCaps.compact_cap S r true)

theorem residual_subset (S : Shape) (r : ℝ) : closedResidual S r ⊆ S.body :=
  union_subset inter_subset_left inter_subset_left

theorem residual_length_le (S : Shape) (r k q : ℝ) :
    sectionLength (closedResidual S r) k q ≤
      sectionLength (CrossedQuadrilateralCaps.cap S r false) k q+
        sectionLength (CrossedQuadrilateralCaps.cap S r true) k q := by
  have hf (j) := compact_section S (CrossedQuadrilateralCaps.compact_cap S r j).isClosed
    inter_subset_left k q
  have hu : fiber (closedResidual S r) k q =
      fiber (CrossedQuadrilateralCaps.cap S r false) k q ∪
        fiber (CrossedQuadrilateralCaps.cap S r true) k q := rfl
  unfold sectionLength
  rw [hu]
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨(hf false).measure_ne_top (μ := volume),(hf true).measure_ne_top (μ := volume)⟩)
    (measure_union_le (fiber (CrossedQuadrilateralCaps.cap S r false) k q)
      (fiber (CrossedQuadrilateralCaps.cap S r true) k q))
  simpa only [ENNReal.toReal_add (hf false).measure_ne_top (hf true).measure_ne_top] using hh

/-- Every section left by the calibrated band packs into a section of the
original body after the exact scale factor `1-r` is removed. -/
theorem section_packing (S : Shape) {r k : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hk : 0 ≤ k) (q : ℝ) :
    ∃ s : ℝ, sectionLength (closedResidual S r) k q ≤ (1-r)*sectionLength S.body k s := by
  have ht := sub_pos.mpr hr1
  have ho : (q-k*(S.Y true*r))/(1-r) ≤ (q-k*(S.Y false*r))/(1-r) := by
    rw [div_le_div_iff_of_pos_right ht]
    simp only [Shape.Y,if_true,Bool.false_eq_true,if_false]
    have hp : 0 ≤ k*((S.b+S.d)*r) :=
      mul_nonneg hk (mul_nonneg (add_pos S.hb S.hd).le hr)
    nlinarith only [hp]
  obtain ⟨s,hs⟩ := separated_sections S hk ho
  refine ⟨s,(residual_length_le S r k q).trans ?_⟩
  rw [cap_length S hr hr1,cap_length S hr hr1,half_false,half_true,← mul_add]
  exact mul_le_mul_of_nonneg_left hs ht.le

end Quant.CrossedQuadrilateralCalibratedSections

/-- info: 'Quant.CrossedQuadrilateralCalibratedSections.section_packing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCalibratedSections.section_packing
