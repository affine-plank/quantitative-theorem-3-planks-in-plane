/- All four shifted corner profiles pack into one original section. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCornerSections

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralFourCornerPacking
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralObliqueSections
open CrossedQuadrilateralCoreProfiles CrossedQuadrilateralCornerSections
open scoped BigOperators

def offset (S : Shape) (r s k : ℝ) (e : Bool × Bool) : ℝ :=
  S.X e.1*r+k*(S.Y e.2*s)

theorem offset_bounds (S : Shape) {r s k : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hk : 0 ≤ k)
    (e : Bool × Bool) :
    offset S r s k (false,false) ≤ offset S r s k e ∧
      offset S r s k e ≤ offset S r s k (true,true) := by
  have hx (i : Bool) : -S.c ≤ S.X i ∧ S.X i ≤ S.a := by
    cases i
    · exact ⟨le_rfl,by change -S.c ≤ S.a; linarith [S.ha,S.hc]⟩
    · exact ⟨by change -S.c ≤ S.a; linarith [S.ha,S.hc],le_rfl⟩
  have hy (i : Bool) : -S.d ≤ S.Y i ∧ S.Y i ≤ S.b := by
    cases i
    · exact ⟨le_rfl,by change -S.d ≤ S.b; linarith [S.hb,S.hd]⟩
    · exact ⟨by change -S.d ≤ S.b; linarith [S.hb,S.hd],le_rfl⟩
  exact ⟨add_le_add (mul_le_mul_of_nonneg_right (hx e.1).1 hr)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hy e.2).1 hs) hk),
    add_le_add (mul_le_mul_of_nonneg_right (hx e.1).2 hr)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hy e.2).2 hs) hk)⟩

/-- One common original level works for every corner: the translated north-east
level, the translated south-west level, or zero between those two levels. -/
theorem profiles_pack (S : Shape) {r s k : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r+s < 1) (hk : 0 < k) (q : ℝ) :
    ∃ v : ℝ, ∀ e : Bool × Bool,
      sectionLength (core S e.1 e.2) k ((q-offset S r s k e)/(1-r-s)) ≤
        sectionLength (core S e.1 e.2) k v := by
  have ht : 0 < 1-r-s := by linarith only [hrs]
  by_cases hN : q ≤ offset S r s k (false,false)
  · let v := (q-offset S r s k (false,false))/(1-r-s)
    have hv : v ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hN) ht.le
    have harg (e : Bool × Bool) : (q-offset S r s k e)/(1-r-s) ≤ v :=
      div_le_div_of_nonneg_right (sub_le_sub_left (offset_bounds S hr hs hk.le e).1 q) ht.le
    refine ⟨v,?_⟩
    rintro ⟨i,j⟩
    cases i <;> cases j
    · exact le_rfl
    · exact nw_monotone S hk ((harg (false,true)).trans hv) hv (harg (false,true))
    · exact se_monotone S hk ((harg (true,false)).trans hv) hv (harg (true,false))
    · rw [ne_zero S hk ((harg (true,true)).trans hv),ne_zero S hk hv]
  · by_cases hP : offset S r s k (true,true) ≤ q
    · let v := (q-offset S r s k (true,true))/(1-r-s)
      have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hP) ht.le
      have harg (e : Bool × Bool) : v ≤ (q-offset S r s k e)/(1-r-s) :=
        div_le_div_of_nonneg_right (sub_le_sub_left (offset_bounds S hr hs hk.le e).2 q) ht.le
      refine ⟨v,?_⟩
      rintro ⟨i,j⟩
      cases i <;> cases j
      · rw [sw_zero S hk (hv.trans (harg (false,false))),sw_zero S hk hv]
      · exact nw_antitone S hk hv (hv.trans (harg (false,true))) (harg (false,true))
      · exact se_antitone S hk hv (hv.trans (harg (true,false))) (harg (true,false))
      · exact le_rfl
    · refine ⟨0,?_⟩
      rintro ⟨i,j⟩
      cases i <;> cases j
      · rw [sw_zero S hk (div_nonneg (sub_nonneg.mpr (le_of_not_ge hN)) ht.le),sw_zero S hk le_rfl]
      · exact nw_le_zero S hk _
      · exact se_le_zero S hk _
      · rw [ne_zero S hk (div_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (le_of_not_ge hP)) ht.le),ne_zero S hk le_rfl]

theorem section_packing (S : Shape) {r s k : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r+s < 1) (hk : 0 < k) (q : ℝ) :
    ∃ v : ℝ, sectionLength (closedCorners S r s) k q ≤ (1-r-s)*sectionLength S.body k v := by
  obtain ⟨v,hv⟩ := profiles_pack S hr hs hrs hk q
  refine ⟨v,(corners_length_le S r s k q).trans ?_⟩
  simp_rw [length_corner S hrs]
  rw [← Finset.mul_sum,body_length_sum S hk.ne' v]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e _ => hv e))
    (by linarith only [hrs])

end Quant.CrossedQuadrilateralFourCornerPacking

/-- info: 'Quant.CrossedQuadrilateralFourCornerPacking.section_packing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralFourCornerPacking.section_packing
