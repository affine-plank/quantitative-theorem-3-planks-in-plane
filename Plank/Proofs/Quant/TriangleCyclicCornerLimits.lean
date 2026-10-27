/- Elementary one-sided limits and inward perturbations at a triangle corner. -/
module
public import Plank.Proofs.Quant.TriangleCyclicCornerAssignments

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicCornerLimits
open Set Filter
open scoped Topology

theorem ab_limit {a c q r s t x y w : ℝ}
    (ha : 0 < a ∧ a < 1) (hc : 0 < c)
    (H : ∀ ε : ℝ, 0 < ε → ∃ e, 0 < e ∧ e < ε ∧
      ((q < x+e ∧ -s < y+a*e ∧ w+c*e < 0) ∨
        (x+e < q ∧ r-s < y+a*e ∧ w+c*e < t))) :
    (q ≤ x ∧ -s ≤ y ∧ w < 0) ∨ (x < q ∧ r-s ≤ y ∧ w < t) := by
  by_cases hx : x < q
  · right
    have hw : w < t := by
      obtain ⟨e,he,he',h⟩ := H ((q-x)/2) (by linarith only [hx])
      rcases h with h | h
      · linarith only [h.1,he',hx]
      · nlinarith only [h.2.2,mul_pos hc he]
    refine ⟨hx,?_,hw⟩
    by_contra hy
    have hy' : y < r-s := lt_of_not_ge hy
    obtain ⟨e,he,he',h⟩ := H (min (q-x) (r-s-y)/2)
      (div_pos (lt_min (by linarith only [hx]) (by linarith only [hy'])) (by norm_num))
    have hq := min_le_left (q-x) (r-s-y)
    have hr := min_le_right (q-x) (r-s-y)
    rcases h with h | h
    · linarith only [h.1,he',hq,hx]
    · nlinarith only [h.2.1,he',hr,mul_lt_mul_of_pos_right ha.2 he,hy']
  · left
    have hx' : q ≤ x := le_of_not_gt hx
    have hw : w < 0 := by
      obtain ⟨e,he,_,h⟩ := H 1 zero_lt_one
      rcases h with h | h
      · nlinarith only [h.2.2,mul_pos hc he]
      · linarith only [h.1,hx',he]
    refine ⟨hx',?_,hw⟩
    by_contra hy
    have hy' : y < -s := lt_of_not_ge hy
    obtain ⟨e,he,he',h⟩ := H ((-s-y)/2) (by linarith only [hy'])
    rcases h with h | h
    · nlinarith only [h.2.1,he',mul_lt_mul_of_pos_right ha.2 he,hy']
    · linarith only [h.1,hx',he]

theorem bc_limit {a b p q r s t u x y w : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : b < 1)
    (H : ∀ ε : ℝ, 0 < ε → ∃ e, 0 < e ∧ e < ε ∧
      ((x+(1-b)*e < p ∧ y-(1-a)*e < r ∧ t-u < w+e) ∨
        (x+(1-b)*e < p+q ∧ y-(1-a)*e < r-s ∧ w+e < t-u))) :
    (x < p ∧ y ≤ r ∧ t-u ≤ w) ∨ (x < p+q ∧ y ≤ r-s ∧ w < t-u) := by
  by_cases hw : w < t-u
  · right
    have hx : x < p+q := by
      obtain ⟨e,he,he',h⟩ := H ((t-u-w)/2) (by linarith only [hw])
      rcases h with h | h
      · linarith only [h.2.2,he',hw]
      · nlinarith only [h.1,mul_pos (sub_pos.mpr hb) he]
    refine ⟨hx,?_,hw⟩
    by_contra hy
    have hy' : r-s < y := lt_of_not_ge hy
    obtain ⟨e,he,he',h⟩ := H (min (t-u-w) (y-(r-s))/2)
      (div_pos (lt_min (by linarith only [hw]) (by linarith only [hy'])) (by norm_num))
    have ht := min_le_left (t-u-w) (y-(r-s))
    have hr := min_le_right (t-u-w) (y-(r-s))
    rcases h with h | h
    · linarith only [h.2.2,he',ht,hw]
    · nlinarith only [h.2.1,he',hr,mul_pos ha.1 he,hy']
  · left
    have hw' : t-u ≤ w := le_of_not_gt hw
    have hx : x < p := by
      obtain ⟨e,he,_,h⟩ := H 1 zero_lt_one
      rcases h with h | h
      · nlinarith only [h.1,mul_pos (sub_pos.mpr hb) he]
      · linarith only [h.2.2,hw',he]
    refine ⟨hx,?_,hw'⟩
    by_contra hy
    have hy' : r < y := lt_of_not_ge hy
    obtain ⟨e,he,he',h⟩ := H ((y-r)/2) (by linarith only [hy'])
    rcases h with h | h
    · nlinarith only [h.2.1,he',mul_pos ha.1 he,hy']
    · linarith only [h.2.2,hw',he]

theorem affine_pos_near_right {x v : ℝ} (hx : 0 ≤ x) (hv : x=0 → 0 < v) :
    ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < x+v*e := by
  rcases hx.eq_or_lt with he | he
  · have hx0 : x=0 := he.symm
    have hh : ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < e := self_mem_nhdsWithin
    filter_upwards [hh] with e he
    rw [hx0,zero_add]
    exact mul_pos (hv hx0) he
  · have hcont : ContinuousAt (fun e : ℝ => x+v*e) 0 := by fun_prop
    have hpos : ∀ᶠ e : ℝ in 𝓝 0, 0 < x+v*e :=
      hcont.eventually_const_lt (by simpa only [mul_zero,add_zero] using he)
    exact hpos.filter_mono nhdsWithin_le_nhds

/-- A small inward ray can make the three box coordinates strict. The
middle coordinate can move either way; the other two increase inward. -/
theorem inward_box {a b c d x y w xl xu yl yu wl wu : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hd : 0 < d) (hx : xl ≤ x ∧ x < xu) (hy : yl ≤ y ∧ y ≤ yu)
    (hyu : yl < yu) (hw : wl ≤ w ∧ w < wu) :
    ∃ e k : ℝ, 0 < e ∧ e < d ∧ 0 < k ∧ k < 1 ∧
      (xl < x+(1-b*k)*e ∧ x+(1-b*k)*e < xu) ∧
      (yl < y+(a-k)*e ∧ y+(a-k)*e < yu) ∧
      (wl < w+(c+(1-c)*k)*e ∧ w+(c+(1-c)*k)*e < wu) := by
  have hk : ∃ k : ℝ, 0 < k ∧ k < 1 ∧ (y=yl → k<a) ∧ (y=yu → a<k) := by
    by_cases hyl : y=yl
    · refine ⟨a/2,by linarith only [ha.1],by linarith only [ha.1,ha.2],?_,?_⟩
      · intro _; linarith only [ha.1]
      · intro hy'; linarith only [hyl,hy',hyu]
    · by_cases hy' : y=yu
      · refine ⟨(a+1)/2,by linarith only [ha.1],by linarith only [ha.2],?_,?_⟩
        · exact fun hh => (hyl hh).elim
        · intro _; linarith only [ha.2]
      · exact ⟨a,ha.1,ha.2,fun hh => (hyl hh).elim,fun hh => (hy' hh).elim⟩
  obtain ⟨k,hk0,hk1,hkl,hku⟩ := hk
  have hdx : 0 < 1-b*k := by nlinarith only [hb.2,mul_lt_mul_of_pos_left hk1 hb.1]
  have hdw : 0 < c+(1-c)*k := add_pos hc.1 (mul_pos (sub_pos.mpr hc.2) hk0)
  have hxl := affine_pos_near_right (sub_nonneg.mpr hx.1) (fun _ => hdx)
  have hxu := affine_pos_near_right (v := -(1-b*k)) (sub_nonneg.mpr hx.2.le)
    (fun hh => False.elim (by linarith only [hh,hx.2]))
  have hyl := affine_pos_near_right (v := a-k) (sub_nonneg.mpr hy.1)
    (fun hh => sub_pos.mpr (hkl (by linarith only [hh])))
  have hyu' := affine_pos_near_right (v := -(a-k)) (sub_nonneg.mpr hy.2)
    (fun hh => by have ht := hku (by linarith only [hh]); linarith only [ht])
  have hwl := affine_pos_near_right (sub_nonneg.mpr hw.1) (fun _ => hdw)
  have hwu := affine_pos_near_right (v := -(c+(1-c)*k)) (sub_nonneg.mpr hw.2.le)
    (fun hh => False.elim (by linarith only [hh,hw.2]))
  have he0 : ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < e := self_mem_nhdsWithin
  have hed : ∀ᶠ e : ℝ in 𝓝[>] 0, e < d :=
    (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds
  obtain ⟨e,he0,hed,hxl,hxu,hyl,hyu',hwl,hwu⟩ :=
    (he0.and (hed.and (hxl.and (hxu.and (hyl.and (hyu'.and (hwl.and hwu))))))).exists
  exact ⟨e,k,he0,hed,hk0,hk1,⟨by linarith only [hxl],by linarith only [hxu]⟩,
    ⟨by linarith only [hyl],by linarith only [hyu']⟩,
    ⟨by linarith only [hwl],by linarith only [hwu]⟩⟩

/-- The two adjoining source edges must meet through the single middle
switch. Each other pairing creates two strict assignments just inside. -/
theorem corner_middle {a b c d p q r s t u x y w : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hd : 0 < d) (hr : 0 < r) (hs : 0 < s)
    (hAB : (q ≤ x ∧ -s ≤ y ∧ w < 0) ∨ (x < q ∧ r-s ≤ y ∧ w < t))
    (hBC : (x < p ∧ y ≤ r ∧ t-u ≤ w) ∨ (x < p+q ∧ y ≤ r-s ∧ w < t-u))
    (hno : ∀ e k : ℝ, 0 < e → e < d → 0 < k → k < 1 →
      let X := x+(1-b*k)*e
      let Y := y+(a-k)*e
      let W := w+(c+(1-c)*k)*e
      ¬ (((q < X ∧ -s < Y ∧ W < 0) ∧ (X < p ∧ Y < r ∧ t-u < W)) ∨
        ((q < X ∧ -s < Y ∧ W < 0) ∧ (X < p+q ∧ Y < r-s ∧ W < t-u)) ∨
        ((X < q ∧ r-s < Y ∧ W < t) ∧ (X < p ∧ Y < r ∧ t-u < W)))) :
    y=r-s := by
  rcases hAB with hA | hB <;> rcases hBC with hC | hD
  · obtain ⟨e,k,he,hed,hk,hk1,hx,hy,hw⟩ := inward_box ha hb hc hd
      ⟨hA.1,hC.1⟩ ⟨hA.2.1,hC.2.1⟩ (by linarith only [hr,hs]) ⟨hC.2.2,hA.2.2⟩
    exact (hno e k he hed hk hk1 (Or.inl
      ⟨⟨hx.1,hy.1,hw.2⟩,⟨hx.2,hy.2,hw.1⟩⟩)).elim
  · obtain ⟨e,k,he,hed,hk,hk1,hx,hy,hw⟩ := inward_box ha hb hc hd
      ⟨hA.1,hD.1⟩ ⟨hA.2.1,hD.2.1⟩ (by linarith only [hr])
      (wl := w-1) ⟨by linarith,lt_min hA.2.2 hD.2.2⟩
    exact (hno e k he hed hk hk1 (Or.inr (Or.inl
      ⟨⟨hx.1,hy.1,hw.2.trans_le (min_le_left _ _)⟩,
        ⟨hx.2,hy.2,hw.2.trans_le (min_le_right _ _)⟩⟩))).elim
  · obtain ⟨e,k,he,hed,hk,hk1,hx,hy,hw⟩ := inward_box ha hb hc hd
      (xl := x-1) ⟨by linarith,lt_min hB.1 hC.1⟩
      ⟨hB.2.1,hC.2.1⟩ (by linarith only [hs]) ⟨hC.2.2,hB.2.2⟩
    exact (hno e k he hed hk hk1 (Or.inr (Or.inr
      ⟨⟨hx.2.trans_le (min_le_left _ _),hy.1,hw.2⟩,
        ⟨hx.2.trans_le (min_le_right _ _),hy.2,hw.1⟩⟩))).elim
  · exact le_antisymm hD.2.1 hB.2.1

end Quant.TriangleCyclicCornerLimits
