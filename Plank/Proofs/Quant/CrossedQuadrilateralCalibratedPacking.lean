/- Actual residual sections after a calibrated band, in every oblique direction. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCalibratedSections

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCalibratedPacking
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralPlacement
open CrossedQuadrilateralObliqueSections CrossedQuadrilateralCalibratedSections
open CrossedQuadrilateralReflections

def gap (S : Shape) (r : ℝ) : Set Point := S.body \ band true (-S.d*r) (S.b*r)

theorem gap_subset (S : Shape) (r : ℝ) : gap S r ⊆ closedResidual S r := by
  intro z hz
  have hn : ¬(-S.d*r ≤ z.2 ∧ z.2 ≤ S.b*r) := hz.2
  by_cases hy : z.2 ≤ -S.d*r
  · left
    refine ⟨hz.1,?_⟩
    change r ≤ z.2/(-S.d)
    apply (le_div_iff_of_neg (neg_lt_zero.mpr S.hd)).mpr
    nlinarith only [hy]
  · right
    have hhigh : S.b*r < z.2 := lt_of_not_ge (fun h => hn ⟨(lt_of_not_ge hy).le,h⟩)
    refine ⟨hz.1,?_⟩
    change r ≤ z.2/S.b
    apply (le_div_iff₀ S.hb).mpr
    nlinarith only [hhigh]

theorem nonnegative_packing (S : Shape) {r k : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hk : 0 ≤ k) (q : ℝ) :
    ∃ s : ℝ, sectionLength (gap S r) k q ≤ (1-r)*sectionLength S.body k s := by
  obtain ⟨s,hs⟩ := section_packing S hr hr1 hk q
  refine ⟨s,le_trans ?_ hs⟩
  exact ENNReal.toReal_mono
    (compact_section S (compact_residual S r).isClosed (residual_subset S r) k q).measure_ne_top
    (measure_mono (fun _ hy => gap_subset S r hy))

theorem flip_fiber (A : Set Point) (k q : ℝ) :
    fiber (flipX '' A) (-k) (-q) = fiber A k q := by
  ext y
  change (-q-(-k)*y,y) ∈ flipX '' A ↔ (q-k*y,y) ∈ A
  rw [image_mem]
  change (-(-q-(-k)*y),y) ∈ A ↔ (q-k*y,y) ∈ A
  have h : -(-q-(-k)*y) = q-k*y := by ring
  rw [h]

theorem flip_band (l u : ℝ) : flipX '' band true l u = band true l u := by
  ext z
  rw [image_mem]
  rfl

theorem flip_gap (S : Shape) (r : ℝ) : gap (flippedX S) r = flipX '' gap S r := by
  change (flippedX S).body \ band true (-S.d*r) (S.b*r) =
    flipX '' (S.body \ band true (-S.d*r) (S.b*r))
  rw [body_flipX,Set.image_sdiff flipX.injective,flip_band]

theorem flip_gap_length (S : Shape) (r k q : ℝ) :
    sectionLength (gap (flippedX S) r) (-k) (-q) = sectionLength (gap S r) k q := by
  rw [flip_gap,sectionLength,flip_fiber]
  rfl

theorem flip_body_length (S : Shape) (k q : ℝ) :
    sectionLength (flippedX S).body (-k) (-q) = sectionLength S.body k q := by
  rw [body_flipX,sectionLength,flip_fiber]
  rfl

/-- This is an unconditional bound for actual remaining section lengths.
It covers every real slope, every section level and every calibrated width below one. -/
theorem actual_section_packing (S : Shape) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (k q : ℝ) :
    ∃ s : ℝ, sectionLength (gap S r) k q ≤ (1-r)*sectionLength S.body k s := by
  rcases le_total 0 k with hk | hk
  · exact nonnegative_packing S hr hr1 hk q
  · obtain ⟨s,hs⟩ := nonnegative_packing (flippedX S) hr hr1 (neg_nonneg.mpr hk) (-q)
    refine ⟨-s,?_⟩
    rw [flip_gap_length] at hs
    have hh : sectionLength (flippedX S).body (-k) s = sectionLength S.body k (-s) := by
      simpa only [neg_neg] using flip_body_length S k (-s)
    rwa [hh] at hs

end Quant.CrossedQuadrilateralCalibratedPacking

/-- info: 'Quant.CrossedQuadrilateralCalibratedPacking.actual_section_packing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCalibratedPacking.actual_section_packing
