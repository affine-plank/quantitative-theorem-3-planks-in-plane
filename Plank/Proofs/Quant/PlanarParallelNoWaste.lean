/- A tight finite parallel family cannot spend positive width outside the
body's support interval. Uses only the direct parallel bound. -/
module

public import Plank.Proofs.Quant.PlanarParallelBound

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelNoWaste

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarParallelTranslations

private def clip (x : ℝ) : ℝ := max 0 (min 1 x)

private theorem monotone_clip : Monotone clip := by
  intro x y h
  exact max_le_max le_rfl (min_le_min le_rfl h)

private theorem clip_sub_le {lo hi : ℝ} (h : lo ≤ hi) : clip hi-clip lo ≤ hi-lo := by
  by_cases hh : hi ≤ 0
  · have hc : clip hi = 0 := max_eq_left ((min_le_right 1 hi).trans hh)
    have hl : clip lo = 0 := max_eq_left ((min_le_right 1 lo).trans (h.trans hh))
    rw [hc,hl]
    linarith only [h]
  by_cases hl : 1 ≤ lo
  · simp only [clip,min_eq_left hl,min_eq_left (hl.trans h),max_eq_right (by norm_num : (0:ℝ) ≤ 1),sub_self]
    exact sub_nonneg.mpr h
  have hc : clip hi = min 1 hi := max_eq_right (le_min (by norm_num) (le_of_not_ge hh))
  have hc' : clip lo = max 0 lo := by rw [clip,min_eq_right (le_of_not_ge hl)]
  rw [hc,hc']
  linarith only [min_le_right (1:ℝ) hi,le_max_right (0:ℝ) lo]

private theorem clip_length_eq_iff {lo hi : ℝ} (h : lo < hi) :
    clip hi-clip lo = hi-lo ↔ 0 ≤ lo ∧ hi ≤ 1 := by
  constructor
  · intro he
    by_cases hh : hi ≤ 0
    · have hc : clip hi = 0 := max_eq_left ((min_le_right 1 hi).trans hh)
      have hl : clip lo = 0 := max_eq_left ((min_le_right 1 lo).trans (h.le.trans hh))
      rw [hc,hl] at he
      linarith only [h,he]
    by_cases hl : 1 ≤ lo
    · have hc : clip lo = 1 := by simp [clip,min_eq_left hl]
      have hc' : clip hi = 1 := by simp [clip,min_eq_left (hl.trans h.le)]
      rw [hc,hc'] at he
      linarith only [h,he]
    have hc : clip hi = min 1 hi := max_eq_right (le_min (by norm_num) (le_of_not_ge hh))
    have hc' : clip lo = max 0 lo := by rw [clip,min_eq_right (le_of_not_ge hl)]
    rw [hc,hc'] at he
    constructor
    · linarith [min_le_right (1:ℝ) hi,le_max_left (0:ℝ) lo]
    · linarith [min_le_left (1:ℝ) hi,le_max_right (0:ℝ) lo]
  · rintro ⟨hl,hh⟩
    simp [clip,min_eq_right hh,min_eq_right (h.le.trans hh),max_eq_right hl,max_eq_right (hl.trans h.le)]

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private theorem gap_clip (K : Set Point) (lo hi : ι → ℝ) (f : Point →ᵃ[ℝ] ℝ)
    (hf : f.linear ≠ 0) (hn : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) :
    volume (K \ ⋃ i, LinearBands.closedBand f (clip (lo i)) (clip (hi i))) =
      volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i)) := by
  have hz := measure_union_null (measure_level_zero f hf 0) (measure_level_zero f hf 1)
  apply measure_congr
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hz] with x hx
  apply propext
  change (x ∈ K \ ⋃ i, LinearBands.closedBand f (clip (lo i)) (clip (hi i))) ↔
    (x ∈ K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))
  by_cases hK : x ∈ K
  · have h0 : 0 < f x := lt_of_le_of_ne (hn x hK).1 (fun he => hx (Or.inl he.symm))
    have h1 : f x < 1 := lt_of_le_of_ne (hn x hK).2 (fun he => hx (Or.inr he))
    have he (i) : x ∈ LinearBands.closedBand f (clip (lo i)) (clip (hi i)) ↔
        x ∈ LinearBands.closedBand f (lo i) (hi i) := by
      simp only [LinearBands.closedBand,mem_ofPred_eq,clip,max_le_iff,min_le_iff,
        le_max_iff,le_min_iff,not_le.mpr h0,not_le.mpr h1,h0.le,h1.le,false_or,true_and]
    simp only [mem_sdiff,mem_iUnion,hK,true_and,he]
  · simp only [mem_sdiff,hK,false_and]

/-- Every positive window of a tight finite parallel family lies inside
the normalized support interval. Null windows have unrestricted positions. -/
theorem positive_window_no_waste {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hR1 : total lo hi < 1) (f : Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (he : (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
      (1-total lo hi)^2*(volume K).toReal) (i : ι) (hp : lo i < hi i) :
    0 ≤ lo i ∧ hi i ≤ 1 := by
  have hlinear : f.linear ≠ 0 := by
    intro hz
    obtain ⟨c,hh⟩ := f.linear_eq_zero_iff_exists_const.mp hz
    have ht : f a = f b := by rw [hh]; rfl
    rw [hfa,hfb] at ht
    norm_num at ht
  let cl := fun i => clip (lo i)
  let ch := fun i => clip (hi i)
  have hle : total cl ch ≤ total lo hi := Finset.sum_le_sum (fun i _ => clip_sub_le (ho i))
  have hbound := PlanarParallelBound.uncovered_area_lower_bound hK hconv cl ch
    (fun i => monotone_clip (ho i)) (hle.trans_lt hR1) f a b ha hb hfa hfb
  rw [gap_clip K lo hi f hlinear hf,he] at hbound
  have hsq := (mul_le_mul_iff_left₀ hV).mp hbound
  have hlin := (sq_le_sq₀ (by linarith only [hle,hR1]) (by linarith only [hR1])).mp hsq
  have hsum : total cl ch = total lo hi := by linarith only [hlin,hle]
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => clip_sub_le (ho j))).mp hsum i (Finset.mem_univ i)
  exact (clip_length_eq_iff hp).mp heq

end Plank.PlanarParallelNoWaste

/-- info: 'Plank.PlanarParallelNoWaste.positive_window_no_waste' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelNoWaste.positive_window_no_waste
