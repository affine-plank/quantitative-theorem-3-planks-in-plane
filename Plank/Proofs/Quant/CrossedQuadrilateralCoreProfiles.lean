/- Actual oblique sections of the two mixed-sign triangular cores. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralThinExtension

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCoreProfiles
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralObliqueSections
open CrossedQuadrilateralReflections

theorem nw_fiber (S : Shape) {k : ℝ} (hk : 0 < k) (q : ℝ) :
    fiber (core S false true) k q = Icc (max 0 (q/k)) (S.b*(S.c+q)/(S.c+k*S.b)) := by
  have hD : 0 < S.c+k*S.b := add_pos S.hc (mul_pos hk S.hb)
  ext y
  have hx : 0 ≤ (q-k*y)/(-S.c) ↔ q/k ≤ y := by
    rw [le_div_iff_of_neg (neg_lt_zero.mpr S.hc),zero_mul,div_le_iff₀ hk]
    constructor <;> intro h <;> nlinarith only [h]
  have hy : 0 ≤ y/S.b ↔ 0 ≤ y := by rw [le_div_iff₀ S.hb,zero_mul]
  have hid : (q-k*y)/(-S.c)+y/S.b = ((S.c+k*S.b)*y-S.b*q)/(S.b*S.c) := by
    field_simp [S.hb.ne',S.hc.ne']
    ring
  have hz : (q-k*y)/(-S.c)+y/S.b ≤ 1 ↔ y ≤ S.b*(S.c+q)/(S.c+k*S.b) := by
    rw [hid,div_le_iff₀ (mul_pos S.hb S.hc),le_div_iff₀ hD]
    constructor <;> intro h <;> nlinarith only [h]
  change (0 ≤ (q-k*y)/(-S.c) ∧ 0 ≤ y/S.b ∧ (q-k*y)/(-S.c)+y/S.b ≤ 1) ↔ _
  rw [hx,hy,hz]
  simp only [mem_Icc,max_le_iff]
  tauto

theorem nw_length (S : Shape) {k : ℝ} (hk : 0 < k) (q : ℝ) :
    sectionLength (core S false true) k q =
      max 0 (S.b*(S.c+q)/(S.c+k*S.b)-max 0 (q/k)) := by
  rw [sectionLength,nw_fiber S hk]
  change volume.real (Icc _ _) = _
  rw [Real.volume_real_Icc,max_comm]

theorem nw_negative (S : Shape) {k q : ℝ} (hk : 0 < k) (hq : q ≤ 0) :
    sectionLength (core S false true) k q = max 0 (S.b*(S.c+q)/(S.c+k*S.b)) := by
  rw [nw_length S hk,max_eq_left (div_nonpos_of_nonpos_of_nonneg hq hk.le),sub_zero]

theorem nw_positive (S : Shape) {k q : ℝ} (hk : 0 < k) (hq : 0 ≤ q) :
    sectionLength (core S false true) k q = max 0 (S.c*(S.b-q/k)/(S.c+k*S.b)) := by
  rw [nw_length S hk,max_eq_right (div_nonneg hq hk.le)]
  congr 1
  have hD : S.c+k*S.b ≠ 0 := (add_pos S.hc (mul_pos hk S.hb)).ne'
  apply (eq_div_iff hD).mpr
  rw [sub_mul,div_mul_cancel₀ _ hD]
  field_simp [hk.ne']
  ring

theorem nw_monotone (S : Shape) {k : ℝ} (hk : 0 < k) :
    MonotoneOn (sectionLength (core S false true) k) (Iic 0) := by
  intro a ha b hb hab
  rw [nw_negative S hk ha,nw_negative S hk hb]
  apply max_le_max le_rfl
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hab) S.hb.le)
    (add_pos S.hc (mul_pos hk S.hb)).le

theorem nw_antitone (S : Shape) {k : ℝ} (hk : 0 < k) :
    AntitoneOn (sectionLength (core S false true) k) (Ici 0) := by
  intro a ha b hb hab
  rw [nw_positive S hk ha,nw_positive S hk hb]
  apply max_le_max le_rfl
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (sub_le_sub_left (div_le_div_of_nonneg_right hab hk.le) S.b) S.hc.le)
    (add_pos S.hc (mul_pos hk S.hb)).le

theorem nw_le_zero (S : Shape) {k : ℝ} (hk : 0 < k) (q : ℝ) :
    sectionLength (core S false true) k q ≤ sectionLength (core S false true) k 0 := by
  rcases le_total q 0 with hq | hq
  · exact nw_monotone S hk hq (by simp) hq
  · exact nw_antitone S hk (by simp) hq hq

theorem antipode_fiber (A : Set Point) (k q : ℝ) :
    fiber (antipode '' A) k q = Neg.neg ⁻¹' fiber A k (-q) := by
  ext y
  change (q-k*y,y) ∈ antipode '' A ↔ (-q-k*(-y),-y) ∈ A
  rw [image_mem]
  change (-(q-k*y),-y) ∈ A ↔ (-q-k*(-y),-y) ∈ A
  have hh : -(q-k*y) = -q-k*(-y) := by ring
  rw [hh]

theorem antipode_length (A : Set Point) (k q : ℝ) :
    sectionLength (antipode '' A) k q = sectionLength A k (-q) := by
  rw [sectionLength,antipode_fiber,Measure.measure_preimage_neg]
  rfl

theorem opposite_core (S : Shape) (i j : Bool) :
    core (opposite S) (!i) (!j) = antipode '' core S i j := by
  ext z
  rw [image_mem]
  cases i <;> cases j <;>
    simp [core,opposite,Shape.X,Shape.Y,antipode_apply,div_neg,neg_div]

theorem se_length (S : Shape) (k q : ℝ) :
    sectionLength (core S true false) k q =
      sectionLength (core (opposite S) false true) k (-q) := by
  have hh := antipode_length (core S true false) k (-q)
  rw [← opposite_core S true false,neg_neg] at hh
  exact hh.symm

theorem se_monotone (S : Shape) {k : ℝ} (hk : 0 < k) :
    MonotoneOn (sectionLength (core S true false) k) (Iic 0) := by
  intro a ha b hb hab
  rw [se_length,se_length]
  exact nw_antitone (opposite S) hk
    (by change 0 ≤ -b; exact neg_nonneg.mpr hb)
    (by change 0 ≤ -a; exact neg_nonneg.mpr ha) (neg_le_neg hab)

theorem se_antitone (S : Shape) {k : ℝ} (hk : 0 < k) :
    AntitoneOn (sectionLength (core S true false) k) (Ici 0) := by
  intro a ha b hb hab
  rw [se_length,se_length]
  exact nw_monotone (opposite S) hk
    (by change -b ≤ 0; exact neg_nonpos.mpr hb)
    (by change -a ≤ 0; exact neg_nonpos.mpr ha) (neg_le_neg hab)

theorem se_le_zero (S : Shape) {k : ℝ} (hk : 0 < k) (q : ℝ) :
    sectionLength (core S true false) k q ≤ sectionLength (core S true false) k 0 := by
  rw [se_length,se_length,neg_zero]
  exact nw_le_zero (opposite S) hk (-q)

theorem ne_zero (S : Shape) {k q : ℝ} (hk : 0 < k) (hq : q ≤ 0) :
    sectionLength (core S true true) k q = 0 := by
  have hs : fiber (core S true true) k q ⊆ ({0} : Set ℝ) := by
    intro y hy
    have hx : 0 ≤ (q-k*y)/S.a := hy.1
    have hy' : 0 ≤ y/S.b := hy.2.1
    rw [le_div_iff₀ S.ha,zero_mul] at hx
    rw [le_div_iff₀ S.hb,zero_mul] at hy'
    change y=0
    nlinarith only [hx,hy',hq,hk]
  rw [sectionLength,measure_mono_null hs (measure_singleton 0),ENNReal.toReal_zero]

theorem sw_zero (S : Shape) {k q : ℝ} (hk : 0 < k) (hq : 0 ≤ q) :
    sectionLength (core S false false) k q = 0 := by
  have hh := antipode_length (core S false false) k (-q)
  rw [← opposite_core S false false,neg_neg] at hh
  rw [← hh]
  exact ne_zero (opposite S) hk (neg_nonpos.mpr hq)

end Quant.CrossedQuadrilateralCoreProfiles

/-- info: 'Quant.CrossedQuadrilateralCoreProfiles.nw_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCoreProfiles.nw_le_zero
/-- info: 'Quant.CrossedQuadrilateralCoreProfiles.se_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCoreProfiles.se_le_zero
