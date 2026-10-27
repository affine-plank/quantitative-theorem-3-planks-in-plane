/- Actual residual bounds after two calibrated diagonal cuts. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralFourCornerPacking

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralDoublePacking
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralObliqueSections
open CrossedQuadrilateralCoreProfiles CrossedQuadrilateralCornerSections
open CrossedQuadrilateralReflections CrossedQuadrilateralObliquePeak
open Plank.Convex.DeficientHeightTilt

def gap (S : Shape) (r s : ℝ) : Set Point := S.body \
  (CrossedQuadrilateralPlacement.band false (-S.c*r) (S.a*r) ∪
    CrossedQuadrilateralPlacement.band true (-S.d*s) (S.b*s))

theorem corner_flipX (S : Shape) (r s : ℝ) (i j : Bool) :
    corner (flippedX S) r s (!i) j = flipX '' corner S r s i j := by
  ext z
  rw [image_mem]
  cases i <;> cases j <;>
    simp [corner,flippedX,Shape.X,Shape.Y,div_neg,neg_div]

theorem closed_flipX (S : Shape) (r s : ℝ) :
    closedCorners (flippedX S) r s = flipX '' closedCorners S r s := by
  rw [closedCorners,closedCorners,image_iUnion]
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨⟨i,j⟩,hz⟩
    refine ⟨(!i,j),?_⟩
    rwa [← corner_flipX,Bool.not_not]
  · rintro ⟨⟨i,j⟩,hz⟩
    refine ⟨(!i,j),?_⟩
    rwa [corner_flipX]

theorem closed_flip_length (S : Shape) (r s k q : ℝ) :
    sectionLength (closedCorners (flippedX S) r s) (-k) (-q) =
      sectionLength (closedCorners S r s) k q := by
  rw [closed_flipX,sectionLength,CrossedQuadrilateralCalibratedPacking.flip_fiber]
  rfl

theorem closed_section_packing (S : Shape) {r s k : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r+s < 1) (hk : k ≠ 0) (q : ℝ) :
    ∃ v : ℝ, sectionLength (closedCorners S r s) k q ≤ (1-r-s)*sectionLength S.body k v := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · obtain ⟨v,hv⟩ := CrossedQuadrilateralFourCornerPacking.section_packing
      (flippedX S) hr hs hrs (neg_pos.mpr hk) (-q)
    refine ⟨-v,?_⟩
    rw [closed_flip_length] at hv
    have hb : sectionLength (flippedX S).body (-k) v = sectionLength S.body k (-v) := by
      simpa only [neg_neg] using CrossedQuadrilateralCalibratedPacking.flip_body_length S k (-v)
    rwa [hb] at hv
  · exact CrossedQuadrilateralFourCornerPacking.section_packing S hr hs hrs hk q

theorem closed_subset (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    closedCorners S r s ⊆ S.body := by
  intro z hz
  obtain ⟨e,he⟩ := mem_iUnion.mp hz
  exact core_subset_body S e.1 e.2 (corner_subset_core S hr hs e.1 e.2 he)

theorem compact_closed (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    IsCompact (closedCorners S r s) :=
  (compact_body S).of_isClosed_subset
    (isClosed_iUnion_of_finite (fun e : Bool × Bool => closed_corner S r s e.1 e.2))
    (closed_subset S hr hs)

theorem gap_subset (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    gap S r s ⊆ closedCorners S r s := by
  change gap S r s ⊆ ⋃ e : Bool × Bool, corner S r s e.1 e.2
  rw [← open_gap_eq_corners S hr hs]
  intro z hz
  refine ⟨hz.1,?_⟩
  rintro (hx | hy)
  · exact hz.2 (Or.inl ⟨hx.1.le,hx.2.le⟩)
  · exact hz.2 (Or.inr ⟨hy.1.le,hy.2.le⟩)

theorem actual_section_packing (S : Shape) {r s k : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r+s < 1) (hk : k ≠ 0) (q : ℝ) :
    ∃ v : ℝ, sectionLength (gap S r s) k q ≤ (1-r-s)*sectionLength S.body k v := by
  obtain ⟨v,hv⟩ := closed_section_packing S hr hs hrs hk q
  refine ⟨v,le_trans ?_ hv⟩
  exact ENNReal.toReal_mono
    (compact_section S (compact_closed S hr hs).isClosed (closed_subset S hr hs) k q).measure_ne_top
    (measure_mono (fun _ hy => gap_subset S hr hs hy))

/-- Every fixed non-diagonal direction retains strict area efficiency after
both calibrated cuts. Their widths may vary throughout the whole subcritical simplex. -/
theorem strict_covered_bound (S : Shape) {k : ℝ} (hk : k ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ M < 2*(volume S.body).toReal ∧
      ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → r+s < 1 → ∀ lo hi : ℝ, lo ≤ hi →
        (volume (gap S r s ∩ CrossedQuadrilateralResidualArea.band k lo hi)).toReal ≤
          (1-r-s)*M*((hi-lo)/rangeWidth S.body (direction (1,k))) := by
  obtain ⟨M,hM,hm,hbound⟩ := strict_original_bound S hk
  let w := rangeWidth S.body (direction (1,k))
  have hw : 0 < w := direction_width_pos S (by
    intro he; have hh := congrArg Prod.fst he; norm_num at hh)
  refine ⟨M*w,mul_nonneg hM hw.le,hm,?_⟩
  intro r s hr hs hrs lo hi ho
  have ht : 0 ≤ 1-r-s := by linarith only [hrs]
  have hclosed (q) : sectionLength (closedCorners S r s) k q ≤ (1-r-s)*M := by
    obtain ⟨v,hv⟩ := closed_section_packing S hr hs hrs hk q
    exact hv.trans (mul_le_mul_of_nonneg_left (hbound v) ht)
  have ha := CrossedQuadrilateralResidualArea.area_band_le
    (compact_closed S hr hs) k ((1-r-s)*M) hclosed ho
  have hmono : (volume (gap S r s ∩ CrossedQuadrilateralResidualArea.band k lo hi)).toReal ≤
      (volume (closedCorners S r s ∩ CrossedQuadrilateralResidualArea.band k lo hi)).toReal := by
    exact ENNReal.toReal_mono
      (measure_ne_top_of_subset inter_subset_left (compact_closed S hr hs).measure_ne_top)
      (measure_mono (fun _ hz => ⟨gap_subset S hr hs hz.1,hz.2⟩))
  refine (hmono.trans ha).trans_eq ?_
  change (hi-lo)*((1-r-s)*M) = (1-r-s)*(M*w)*((hi-lo)/w)
  field_simp [hw.ne']

end Quant.CrossedQuadrilateralDoublePacking

/-- info: 'Quant.CrossedQuadrilateralDoublePacking.strict_covered_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralDoublePacking.strict_covered_bound
