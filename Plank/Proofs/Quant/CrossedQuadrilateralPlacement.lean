/- Removing the origin-containment restriction from diagonal band placement. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralNecessity

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralPlacement
open Set MeasureTheory
open Quant.CrossedQuadrilateralAttainment Quant.CrossedQuadrilateralNecessity
open scoped BigOperators Pointwise Function

local instance : (volume : Measure Point).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℝ × ℝ)).IsAddHaarMeasure)

def coord (i : Bool) (z : Point) : ℝ := if i then z.2 else z.1
def vector (i : Bool) (t : ℝ) : Point := if i then (0,t) else (t,0)
def band (i : Bool) (l u : ℝ) : Set Point := {z | l ≤ coord i z ∧ coord i z ≤ u}

@[simp] theorem vector_zero (i : Bool) : vector i 0 = 0 := by cases i <;> rfl

@[simp] theorem coord_vector_add (i : Bool) (t : ℝ) (z : Point) :
    coord i (vector i t+z) = t+coord i z := by cases i <;> rfl

@[simp] theorem other_coord_vector_add (i : Bool) (t : ℝ) (z : Point) :
    coord (!i) (vector i t+z) = coord (!i) z := by cases i <;> simp [coord,vector]

theorem measurable_band (i : Bool) (l u : ℝ) : MeasurableSet (band i l u) := by
  have hc : Measurable (coord i) := by
    cases i
    · exact measurable_fst
    · exact measurable_snd
  exact (measurableSet_le measurable_const hc).inter (measurableSet_le hc measurable_const)

theorem zero_x_mem (S : Shape) {z : Point} (hz : z ∈ S.body) : (0,z.2) ∈ S.body := by
  rw [body_eq_cores] at hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  obtain ⟨j,hj⟩ := mem_iUnion.mp hi
  apply core_subset_body S i j
  refine ⟨by simp,hj.2.1,?_⟩
  simp only [zero_div,zero_add]
  linarith [hj.1,hj.2.2]

theorem zero_y_mem (S : Shape) {z : Point} (hz : z ∈ S.body) : (z.1,0) ∈ S.body := by
  rw [body_eq_cores] at hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  obtain ⟨j,hj⟩ := mem_iUnion.mp hi
  apply core_subset_body S i j
  refine ⟨hj.1,by simp,?_⟩
  simp only [zero_div,add_zero]
  linarith [hj.2.1,hj.2.2]

theorem contract_x_mem (S : Shape) {z : Point} (hz : z ∈ S.body)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : (t*z.1,z.2) ∈ S.body := by
  have h := (convex_body S) (zero_x_mem S hz) hz (a := 1-t) (b := t)
    (sub_nonneg.mpr ht₁) ht₀ (by ring)
  convert h using 1
  ext <;> simp
  all_goals ring

theorem contract_y_mem (S : Shape) {z : Point} (hz : z ∈ S.body)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : (z.1,t*z.2) ∈ S.body := by
  have h := (convex_body S) (zero_y_mem S hz) hz (a := 1-t) (b := t)
    (sub_nonneg.mpr ht₁) ht₀ (by ring)
  convert h using 1
  ext <;> simp
  all_goals ring

theorem contract_mem (S : Shape) (i : Bool) {z : Point} (hz : z ∈ S.body)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    vector i ((t-1)*coord i z)+z ∈ S.body := by
  cases i
  · convert contract_x_mem S hz ht₀ ht₁ using 1
    ext <;> simp [vector,coord]
    all_goals ring
  · convert contract_y_mem S hz ht₀ ht₁ using 1
    ext <;> simp [vector,coord]
    all_goals ring

/-- Move only bands disjoint from zero, until their nearest endpoint reaches zero. -/
def shift (l u : ℝ) : ℝ := if 0 < l then l else if u < 0 then u else 0

theorem shifted_contains_zero {l u : ℝ} (h : l ≤ u) :
    l-shift l u ≤ 0 ∧ 0 ≤ u-shift l u := by
  by_cases hl : 0 < l
  · simp [shift,hl]; linarith
  · by_cases hu : u < 0
    · simp [shift,hl,hu]; linarith
    · simp [shift,hl,hu]
      exact ⟨le_of_not_gt hl,le_of_not_gt hu⟩

theorem slide_mem (S : Shape) (i : Bool) {l u : ℝ} {z : Point}
    (hz : z ∈ S.body) (hb : z ∈ band i l u) :
    vector i (-shift l u)+z ∈ S.body := by
  by_cases hl : 0 < l
  · have hp : 0 < coord i z := hl.trans_le hb.1
    have ht₀ : 0 ≤ (coord i z-l)/coord i z := div_nonneg (sub_nonneg.mpr hb.1) hp.le
    have ht₁ : (coord i z-l)/coord i z ≤ 1 := (div_le_one hp).mpr (by linarith)
    have he : ((coord i z-l)/coord i z-1)*coord i z = -l := by
      field_simp [ne_of_gt hp]; ring
    simpa [shift,hl,he] using contract_mem S i hz ht₀ ht₁
  · by_cases hu : u < 0
    · have hp : coord i z < 0 := hb.2.trans_lt hu
      have ht₀ : 0 ≤ (coord i z-u)/coord i z :=
        div_nonneg_of_nonpos (sub_nonpos.mpr hb.2) hp.le
      have ht₁ : (coord i z-u)/coord i z ≤ 1 := (div_le_one_of_neg hp).mpr (by linarith)
      have he : ((coord i z-u)/coord i z-1)*coord i z = -u := by
        field_simp [ne_of_lt hp]; ring
      simpa [shift,hl,hu,he] using contract_mem S i hz ht₀ ht₁
    · simpa [shift,hl,hu] using hz

/-- The covered portion outside the other band can be translated injectively
into the new covered portion. Thus sliding an exterior band inward cannot
increase the actual uncovered volume. -/
theorem slide_gap_le (S : Shape) (i : Bool) (l u p q : ℝ) :
    volume (S.body \ (band i (l-shift l u) (u-shift l u) ∪ band (!i) p q)) ≤
      volume (S.body \ (band i l u ∪ band (!i) p q)) := by
  let U := S.body \ band (!i) p q
  let A := band i l u
  let B := band i (l-shift l u) (u-shift l u)
  have hmap : (fun z : Point => vector i (-shift l u)+z) '' (U ∩ A) ⊆ U ∩ B := by
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨⟨slide_mem S i hz.1.1 hz.2,?_⟩,?_⟩
    · intro hh
      apply hz.1.2
      simpa only [band,mem_ofPred_eq,other_coord_vector_add] using hh
    · change l-shift l u ≤ coord i (vector i (-shift l u)+z) ∧
        coord i (vector i (-shift l u)+z) ≤ u-shift l u
      rw [coord_vector_add]
      exact ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hcovered : volume (U ∩ A) ≤ volume (U ∩ B) := by
    calc
      _ = volume ((fun z : Point => vector i (-shift l u)+z) '' (U ∩ A)) := by
        rw [Set.image_add_left,measure_preimage_add]
      _ ≤ _ := measure_mono hmap
  have hfinite (T : Set Point) : volume (U ∩ T) ≠ ⊤ :=
    ne_top_of_le_ne_top (compact_body S).measure_ne_top
      (measure_mono (inter_subset_left.trans sdiff_subset))
  have ha : volume (U \ A) = volume U-volume (U ∩ A) :=
    ENNReal.eq_sub_of_add_eq (hfinite A) (measure_sdiff_add_inter U (measurable_band i l u))
  have hb : volume (U \ B) = volume U-volume (U ∩ B) :=
    ENNReal.eq_sub_of_add_eq (hfinite B)
      (measure_sdiff_add_inter U (measurable_band i _ _))
  have hc : volume (U \ B) ≤ volume (U \ A) := by
    rw [ha,hb]
    exact tsub_le_tsub_left hcovered _
  simpa only [U,A,B,Set.sdiff_sdiff,Set.union_comm] using hc

theorem weighted_hinge_lower_bound {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {m : ℝ} (hm : 0 ≤ m)
    (hmean : ∑ i, w i*x i = m*∑ i, w i) :
    m^2*∑ i, w i ≤ ∑ i, w i*(max 0 (x i))^2 := by
  have ht (i : ι) : m^2+2*m*(x i-m) ≤ (max 0 (x i))^2 := by
    nlinarith [sq_nonneg (max 0 (x i)-m),
      mul_nonneg hm (sub_nonneg.mpr (le_max_right 0 (x i)))]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => mul_le_mul_of_nonneg_left (ht i) (hw i))
  have he : (∑ i, w i*(m^2+2*m*(x i-m))) = m^2*∑ i, w i := by
    calc
      _ = 2*m*(∑ i, w i*x i)-m^2*(∑ i, w i) := by
        simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hmean]; ring
  rwa [he] at h

theorem calibrated_chart_lower_bound (S : Shape) (r s : Bool → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j)
    (hbudget : xWidth S r+yWidth S s < 1) :
    (1-xWidth S r-yWidth S s)^2*(volume S.body).toReal ≤
      (volume (S.body \ (xBand S r ∪ yBand S s))).toReal := by
  have h := weighted_hinge_lower_bound (weight S) (fun e => 1-r e.1-s e.2)
    (fun e => (weight_pos S e).le) (by linarith) (weighted_deficit_mean S r s)
  rw [area_gap S r s hr hs,area_body,← mul_assoc]
  exact mul_le_mul_of_nonneg_right h ENNReal.toReal_nonneg

theorem endpoint_lower_bound (S : Shape) (lx ux ly uy : ℝ)
    (hlx : lx ≤ 0) (hux : 0 ≤ ux) (hly : ly ≤ 0) (huy : 0 ≤ uy)
    (hbudget : (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (1-(ux-lx)/(S.a+S.c)-(uy-ly)/(S.b+S.d))^2*(volume S.body).toReal ≤
      (volume (S.body \ (band false lx ux ∪ band true ly uy))).toReal := by
  let r : Bool → ℝ := fun i => if i then ux/S.a else -lx/S.c
  let s : Bool → ℝ := fun j => if j then uy/S.b else -ly/S.d
  have hr : ∀ i, 0 ≤ r i := by
    intro i; cases i
    · exact div_nonneg (neg_nonneg.mpr hlx) S.hc.le
    · exact div_nonneg hux S.ha.le
  have hs : ∀ j, 0 ≤ s j := by
    intro j; cases j
    · exact div_nonneg (neg_nonneg.mpr hly) S.hd.le
    · exact div_nonneg huy S.hb.le
  have hxr : xWidth S r = (ux-lx)/(S.a+S.c) := by
    dsimp [xWidth,r]
    field_simp [ne_of_gt S.ha,ne_of_gt S.hc,ne_of_gt (add_pos S.ha S.hc)]
    ring
  have hys : yWidth S s = (uy-ly)/(S.b+S.d) := by
    dsimp [yWidth,s]
    field_simp [ne_of_gt S.hb,ne_of_gt S.hd,ne_of_gt (add_pos S.hb S.hd)]
    ring
  have hxb : xBand S r = band false lx ux := by
    ext z
    simp [xBand,r,band,coord,mul_div_cancel₀,ne_of_gt S.ha,ne_of_gt S.hc]
  have hyb : yBand S s = band true ly uy := by
    ext z
    simp [yBand,s,band,coord,mul_div_cancel₀,ne_of_gt S.hb,ne_of_gt S.hd]
  have h := calibrated_chart_lower_bound S r s hr hs (by rwa [hxr,hys])
  simpa only [hxb,hyb,hxr,hys] using h

theorem both_slides_gap_le (S : Shape) (lx ux ly uy : ℝ) :
    volume (S.body \ (band false (lx-shift lx ux) (ux-shift lx ux) ∪
        band true (ly-shift ly uy) (uy-shift ly uy))) ≤
      volume (S.body \ (band false lx ux ∪ band true ly uy)) := by
  have hx := slide_gap_le S false lx ux ly uy
  have hy := slide_gap_le S true ly uy (lx-shift lx ux) (ux-shift lx ux)
  simp only [Bool.not_false] at hx
  simp only [Bool.not_true] at hy
  apply le_trans ?_ hx
  simpa only [Set.union_comm] using hy

theorem balanced_shift_iff {a c l u : ℝ} (ha : 0 < a) (hc : 0 < c) (hlu : l ≤ u) :
    (u-shift l u)/a = -(l-shift l u)/c ↔ u = l ∨ u/a = -l/c := by
  constructor
  · intro h
    by_cases hl : 0 < l
    · left
      have hz : (u-l)/a = 0 := by simpa [shift,hl] using h
      exact sub_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right (ne_of_gt ha))
    · by_cases hu : u < 0
      · left
        have hz : (u-l)/c = 0 := by simpa [shift,hl,hu] using h.symm
        exact sub_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right (ne_of_gt hc))
      · right
        simpa [shift,hl,hu] using h
  · rintro (h | h)
    · subst u
      by_cases hl : 0 < l
      · simp [shift,hl]
      · by_cases hu : l < 0
        · simp [shift,hl,hu]
        · have hz : l = 0 := by linarith
          simp [hz,shift]
    · have hl : ¬ 0 < l := by
        intro hp
        have hleft := div_pos (hp.trans_le hlu) ha
        have hright := div_neg_of_neg_of_pos (neg_lt_zero.mpr hp) hc
        linarith
      have hu : ¬ u < 0 := by
        intro hn
        have hleft := div_neg_of_neg_of_pos hn ha
        have hright := div_pos (neg_pos.mpr (hlu.trans_lt hn)) hc
        linarith
      simpa [shift,hl,hu] using h

theorem balanced_contains_zero {a c l u : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hlu : l ≤ u) (h : u/a = -l/c) : l ≤ 0 ∧ 0 ≤ u := by
  constructor
  · by_contra hn
    have hp : 0 < l := lt_of_not_ge hn
    have hleft := div_pos (hp.trans_le hlu) ha
    have hright := div_neg_of_neg_of_pos (neg_lt_zero.mpr hp) hc
    linarith
  · by_contra hn
    have hp : u < 0 := lt_of_not_ge hn
    have hleft := div_neg_of_neg_of_pos hp ha
    have hright := div_pos (neg_pos.mpr (hlu.trans_lt hp)) hc
    linarith

theorem volume_band_null (i : Bool) (t : ℝ) : volume (band i t t) = 0 := by
  have he : band i t t = {z | coord i z = t} := by
    ext z
    exact ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩
  rw [he]
  cases i
  · simpa [coord,dot] using volume_line (by norm_num : ((1,0) : Point) ≠ 0) t
  · simpa [coord,dot] using volume_line (by norm_num : ((0,1) : Point) ≠ 0) t

theorem slide_gap_eq (S : Shape) (i : Bool) (l u p q : ℝ)
    (h : u = l ∨ (l ≤ 0 ∧ 0 ≤ u)) :
    volume (S.body \ (band i (l-shift l u) (u-shift l u) ∪ band (!i) p q)) =
      volume (S.body \ (band i l u ∪ band (!i) p q)) := by
  rcases h with rfl | h
  · rw [Set.union_comm (band i _ _) (band (!i) p q),← Set.sdiff_sdiff,
      measure_sdiff_null (volume_band_null i _),
      Set.union_comm (band i _ _) (band (!i) p q),← Set.sdiff_sdiff,
      measure_sdiff_null (volume_band_null i _)]
  · simp [shift,not_lt_of_ge h.1,not_lt_of_ge h.2]

theorem shifted_gap_lower_bound (S : Shape) (lx ux ly uy : ℝ)
    (hx : lx ≤ ux) (hy : ly ≤ uy)
    (hbudget : (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (1-(ux-lx)/(S.a+S.c)-(uy-ly)/(S.b+S.d))^2*(volume S.body).toReal ≤
      (volume (S.body \ (band false (lx-shift lx ux) (ux-shift lx ux) ∪
        band true (ly-shift ly uy) (uy-shift ly uy)))).toReal := by
  obtain ⟨hlx,hux⟩ := shifted_contains_zero hx
  obtain ⟨hly,huy⟩ := shifted_contains_zero hy
  have hwx : (ux-shift lx ux)-(lx-shift lx ux) = ux-lx := by ring
  have hwy : (uy-shift ly uy)-(ly-shift ly uy) = uy-ly := by ring
  have h := endpoint_lower_bound S _ _ _ _ hlx hux hly huy (by rwa [hwx,hwy])
  simpa only [hwx,hwy] using h

theorem shifted_area_le (S : Shape) (lx ux ly uy : ℝ) :
    (volume (S.body \ (band false (lx-shift lx ux) (ux-shift lx ux) ∪
        band true (ly-shift ly uy) (uy-shift ly uy)))).toReal ≤
      (volume (S.body \ (band false lx ux ∪ band true ly uy))).toReal :=
  ENNReal.toReal_mono (ne_top_of_le_ne_top (compact_body S).measure_ne_top
    (measure_mono sdiff_subset)) (both_slides_gap_le S lx ux ly uy)

/-- The square lower bound for arbitrary placements in the two diagonal directions. -/
theorem arbitrary_placement_lower_bound (S : Shape) (lx ux ly uy : ℝ)
    (hx : lx ≤ ux) (hy : ly ≤ uy)
    (hbudget : (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (1-(ux-lx)/(S.a+S.c)-(uy-ly)/(S.b+S.d))^2*(volume S.body).toReal ≤
      (volume (S.body \ (band false lx ux ∪ band true ly uy))).toReal :=
  (shifted_gap_lower_bound S lx ux ly uy hx hy hbudget).trans (shifted_area_le S lx ux ly uy)

/-- Complete placement iff for two diagonal-parallel bands. Positive-width bands
must have the calibrated crossed placement. Zero-width bands may be anywhere. -/
theorem arbitrary_placement_equality_iff (S : Shape) (lx ux ly uy : ℝ)
    (hx : lx ≤ ux) (hy : ly ≤ uy)
    (hbudget : (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (volume (S.body \ (band false lx ux ∪ band true ly uy))).toReal =
        (1-(ux-lx)/(S.a+S.c)-(uy-ly)/(S.b+S.d))^2*(volume S.body).toReal ↔
      (ux = lx ∨ ux/S.a = -lx/S.c) ∧ (uy = ly ∨ uy/S.b = -ly/S.d) := by
  obtain ⟨hlx,hux⟩ := shifted_contains_zero hx
  obtain ⟨hly,huy⟩ := shifted_contains_zero hy
  have hwx : (ux-shift lx ux)-(lx-shift lx ux) = ux-lx := by ring
  have hwy : (uy-shift ly uy)-(ly-shift ly uy) = uy-ly := by ring
  have hiff := endpoint_equality_iff S _ _ _ _ hlx hux hly huy (by rwa [hwx,hwy])
  change (volume (S.body \ (band false _ _ ∪ band true _ _))).toReal = _ ↔ _ at hiff
  rw [hwx,hwy,balanced_shift_iff S.ha S.hc hx,balanced_shift_iff S.hb S.hd hy] at hiff
  constructor
  · intro he
    apply hiff.mp
    apply le_antisymm
    · exact (shifted_area_le S lx ux ly uy).trans he.le
    · exact shifted_gap_lower_bound S lx ux ly uy hx hy hbudget
  · intro he
    have heq := hiff.mpr he
    have hxc : ux = lx ∨ (lx ≤ 0 ∧ 0 ≤ ux) :=
      he.1.imp id (balanced_contains_zero S.ha S.hc hx)
    have hyc : uy = ly ∨ (ly ≤ 0 ∧ 0 ≤ uy) :=
      he.2.imp id (balanced_contains_zero S.hb S.hd hy)
    have hxs := slide_gap_eq S false lx ux ly uy hxc
    have hys := slide_gap_eq S true ly uy (lx-shift lx ux) (ux-shift lx ux) hyc
    simp only [Bool.not_false] at hxs
    simp only [Bool.not_true] at hys
    have hvol : volume (S.body \ (band false (lx-shift lx ux) (ux-shift lx ux) ∪
        band true (ly-shift ly uy) (uy-shift ly uy))) =
        volume (S.body \ (band false lx ux ∪ band true ly uy)) := by
      calc
        _ = volume (S.body \ (band false (lx-shift lx ux) (ux-shift lx ux) ∪ band true ly uy)) := by
          simpa only [Set.union_comm] using hys
        _ = _ := hxs
    rwa [hvol] at heq

theorem arbitrary_placement_with_null_iff (S : Shape) (lx ux ly uy : ℝ)
    (hx : lx ≤ ux) (hy : ly ≤ uy)
    (hbudget : (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1)
    (n : Plank) (hn : n.lo = n.hi) :
    (volume (S.body \ (band false lx ux ∪ band true ly uy ∪ n.set))).toReal =
        (1-(ux-lx)/(S.a+S.c)-(uy-ly)/(S.b+S.d))^2*(volume S.body).toReal ↔
      (ux = lx ∨ ux/S.a = -lx/S.c) ∧ (uy = ly ∨ uy/S.b = -ly/S.d) := by
  rw [← Set.sdiff_sdiff,measure_sdiff_null (null_plank_volume n hn)]
  exact arbitrary_placement_equality_iff S lx ux ly uy hx hy hbudget

theorem arbitrary_split_equality_iff (S : Shape) (lx ux ly uy t : ℝ)
    (ht₀ : lx ≤ t) (ht₁ : t ≤ ux) (hy : ly ≤ uy)
    (hbudget : (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (volume (S.body \ (band false lx t ∪ band false t ux ∪ band true ly uy))).toReal =
        (1-(ux-lx)/(S.a+S.c)-(uy-ly)/(S.b+S.d))^2*(volume S.body).toReal ↔
      (ux = lx ∨ ux/S.a = -lx/S.c) ∧ (uy = ly ∨ uy/S.b = -ly/S.d) := by
  have hu : band false lx t ∪ band false t ux = band false lx ux := by
    exact congrArg (fun A : Set ℝ => Prod.fst ⁻¹' A) (Set.Icc_union_Icc_eq_Icc ht₀ ht₁)
  rw [hu]
  exact arbitrary_placement_equality_iff S lx ux ly uy (ht₀.trans ht₁) hy hbudget

def axisPlank (i : Bool) (l u : ℝ) (h : l ≤ u) : Plank where
  u := vector i 1
  lo := l
  hi := u
  u_ne_zero := by cases i <;> norm_num [vector]
  lo_le_hi := h

@[simp] theorem axisPlank_set (i : Bool) (l u : ℝ) (h : l ≤ u) :
    (axisPlank i l u h).set = band i l u := by
  cases i <;> ext z <;> simp [axisPlank,band,coord,vector,Plank.set,Membership.mem,dot]

theorem axisPlank_relative_width (S : Shape) (lx ux ly uy : ℝ)
    (hx : lx ≤ ux) (hy : ly ≤ uy) :
    relativeWidth S (axisPlank false lx ux hx) = (ux-lx)/(S.a+S.c) ∧
      relativeWidth S (axisPlank true ly uy hy) = (uy-ly)/(S.b+S.d) := by
  simp [relativeWidth,axisPlank,vector,(coordinate_widths S).1,(coordinate_widths S).2]

def physicalFamily (lx ux ly uy : ℝ) (hx : lx ≤ ux) (hy : ly ≤ uy) (n : Plank) :
    Fin 3 → Plank := ![axisPlank false lx ux hx,axisPlank true ly uy hy,n]

theorem physicalFamily_union (lx ux ly uy : ℝ) (hx : lx ≤ ux) (hy : ly ≤ uy) (n : Plank) :
    (⋃ i, (physicalFamily lx ux ly uy hx hy n i).set) =
      band false lx ux ∪ band true ly uy ∪ n.set := by
  ext z
  simp only [mem_iUnion,mem_union]
  constructor
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact Or.inl (Or.inl (by simpa [physicalFamily] using hi))
    · exact Or.inl (Or.inr (by simpa [physicalFamily] using hi))
    · exact Or.inr hi
  · rintro ((hx | hy) | hn)
    · exact ⟨0,by simpa [physicalFamily] using hx⟩
    · exact ⟨1,by simpa [physicalFamily] using hy⟩
    · exact ⟨2,hn⟩

/-- The iff stated for three physical planks and their actual directional widths. -/
theorem physicalFamily_equality_iff (S : Shape) (lx ux ly uy : ℝ)
    (hx : lx ≤ ux) (hy : ly ≤ uy)
    (hbudget : (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1)
    (n : Plank) (hn : n.lo = n.hi) :
    (volume (S.body \ ⋃ i, (physicalFamily lx ux ly uy hx hy n i).set)).toReal =
        (1-∑ i, relativeWidth S (physicalFamily lx ux ly uy hx hy n i))^2*
          (volume S.body).toReal ↔
      (ux = lx ∨ ux/S.a = -lx/S.c) ∧ (uy = ly ∨ uy/S.b = -ly/S.d) := by
  have hw := axisPlank_relative_width S lx ux ly uy hx hy
  have hnw : relativeWidth S n = 0 := by simp [relativeWidth,hn]
  rw [physicalFamily_union]
  simpa [physicalFamily,Fin.sum_univ_three,hw.1,hw.2,hnw,sub_add_eq_sub_sub] using
    arbitrary_placement_with_null_iff S lx ux ly uy hx hy hbudget n hn

end Quant.CrossedQuadrilateralPlacement

/-- info: 'Quant.CrossedQuadrilateralPlacement.physicalFamily_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralPlacement.physicalFamily_equality_iff
