/- Triangular caps for the remaining parallel-pair placement cases. -/
module
public import Plank.Proofs.Quant.ParallelProductPlane

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCaps
open Set MeasureTheory
open Quant.CrossedQuadrilateralAttainment Quant.CrossedQuadrilateralNecessity
open Quant.CrossedQuadrilateralPlacement
open scoped BigOperators Pointwise Function

local instance : (volume : Measure Point).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℝ × ℝ)).IsAddHaarMeasure)

def half (S : Shape) (j : Bool) : Set Point := S.body ∩ {z | 0 ≤ z.2/S.Y j}
def cap (S : Shape) (s : ℝ) (j : Bool) : Set Point := S.body ∩ {z | s ≤ z.2/S.Y j}

theorem half_eq_cores (S : Shape) (j : Bool) :
    half S j = core S false j ∪ core S true j := by
  ext z
  constructor
  · rintro ⟨hz,hy⟩
    have hs := hz
    rw [body_eq_cores] at hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp hi
    have hh : z ∈ core S i j := ⟨hk.1,hy,body_support S i j hs⟩
    cases i
    · exact Or.inl hh
    · exact Or.inr hh
  · rintro (hz | hz)
    · exact ⟨core_subset_body S false j hz,hz.2.1⟩
    · exact ⟨core_subset_body S true j hz,hz.2.1⟩

theorem compact_cap (S : Shape) (s : ℝ) (j : Bool) : IsCompact (cap S s j) :=
  (compact_body S).inter_right
    (isClosed_le continuous_const (continuous_snd.div_const (S.Y j)))

theorem convex_cap (S : Shape) (s : ℝ) (j : Bool) : Convex ℝ (cap S s j) := by
  have he : {z : Point | s ≤ z.2/S.Y j} =
      (((S.Y j)⁻¹ • LinearMap.snd ℝ ℝ ℝ) ⁻¹' Ici s) := by
    ext z
    simp [div_eq_mul_inv,mul_comm]
  exact (convex_body S).inter (he ▸ (convex_Ici s).linear_preimage _)

theorem area_half (S : Shape) (j : Bool) :
    (volume (half S j)).toReal = (S.a+S.c)*|S.Y j| * (volume unitCorner).toReal := by
  have hfin (i : Bool) : volume (core S i j) ≠ ⊤ :=
    ne_top_of_le_ne_top (compact_body S).measure_ne_top (measure_mono (core_subset_body S i j))
  rw [half_eq_cores,measure_union₀ (measurable_core S true j).nullMeasurableSet
    (core_aedisjoint S (show (false,j) ≠ (true,j) by simp)),ENNReal.toReal_add (hfin false) (hfin true),
    area_core,area_core]
  simp [Shape.X,abs_of_pos S.ha,abs_of_pos S.hc]
  ring

theorem cap_eq_corners (S : Shape) {s : ℝ} (hs : 0 ≤ s) (j : Bool) :
    cap S s j = corner S 0 s false j ∪ corner S 0 s true j := by
  ext z
  constructor
  · rintro ⟨hz,hy⟩
    have hsupport := hz
    rw [body_eq_cores] at hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp hi
    have hh : z ∈ corner S 0 s i j := ⟨hk.1,hy,body_support S i j hsupport⟩
    cases i
    · exact Or.inl hh
    · exact Or.inr hh
  · rintro (hz | hz)
    · exact ⟨core_subset_body S false j (corner_subset_core S le_rfl hs false j hz),hz.2.1⟩
    · exact ⟨core_subset_body S true j (corner_subset_core S le_rfl hs true j hz),hz.2.1⟩

theorem cap_eq_image (S : Shape) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (j : Bool) :
    cap S s j = (fun z : Point => (0,S.Y j*s)+(1-s) • z) '' half S j := by
  rw [cap_eq_corners S hs,corner_eq_image S (by linarith : 0+s < 1),
    corner_eq_image S (by linarith : 0+s < 1),half_eq_cores,Set.image_union]
  simp only [mul_zero,sub_zero]

theorem area_cap (S : Shape) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (j : Bool) :
    (volume (cap S s j)).toReal = (1-s)^2*((S.a+S.c)*|S.Y j| * (volume unitCorner).toReal) := by
  rw [cap_eq_image S hs hs1,volume_translate_smul _ (sub_pos.mpr hs1).le,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _),area_half]

theorem x_vertex_mem_half (S : Shape) (i j : Bool) : (S.X i,0) ∈ half S j :=
  ⟨vertexX_mem S i,by simp⟩

theorem cap_x_vertex_mem (S : Shape) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (i j : Bool) : ((1-s)*S.X i,S.Y j*s) ∈ cap S s j := by
  rw [cap_eq_image S hs hs1]
  refine ⟨(S.X i,0),x_vertex_mem_half S i j,?_⟩
  ext <;> simp

theorem cap_x_bounds (S : Shape) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (j : Bool) {z : Point} (hz : z ∈ cap S s j) :
    -(1-s)*S.c ≤ z.1 ∧ z.1 ≤ (1-s)*S.a := by
  rw [cap_eq_image S hs hs1] at hz
  obtain ⟨p,hp,rfl⟩ := hz
  have hb := (coordinate_box S hp.1).1
  change -(1-s)*S.c ≤ 0+(1-s)*p.1 ∧ 0+(1-s)*p.1 ≤ (1-s)*S.a
  constructor
  · have hh := mul_le_mul_of_nonneg_left hb.1 (sub_pos.mpr hs1).le
    nlinarith only [hh]
  · simpa using mul_le_mul_of_nonneg_left hb.2 (sub_pos.mpr hs1).le

def capForm (S : Shape) (s : ℝ) : Point →ᵃ[ℝ] ℝ :=
  ((1-s)*(S.a+S.c))⁻¹ • (direction (1,0)-AffineMap.const ℝ Point (-(1-s)*S.c))

@[simp] theorem capForm_apply (S : Shape) (s : ℝ) (z : Point) :
    capForm S s z = (z.1+(1-s)*S.c)/((1-s)*(S.a+S.c)) := by
  change ((1-s)*(S.a+S.c))⁻¹*(1*z.1+0*z.2-(-(1-s)*S.c)) = _
  rw [div_eq_mul_inv]
  ring

theorem capForm_realisers (S : Shape) {s : ℝ} (hs1 : s < 1) (j : Bool) :
    capForm S s ((1-s)*S.a,S.Y j*s) = 1 ∧
      capForm S s (-(1-s)*S.c,S.Y j*s) = 0 := by
  rw [capForm_apply,capForm_apply]
  constructor
  · field_simp [ne_of_gt (sub_pos.mpr hs1),ne_of_gt (add_pos S.ha S.hc)]
  · have hz : -(1-s)*S.c+(1-s)*S.c = 0 := by ring
    rw [hz,zero_div]

theorem capForm_bounds (S : Shape) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (j : Bool) {z : Point} (hz : z ∈ cap S s j) :
    0 ≤ capForm S s z ∧ capForm S s z ≤ 1 := by
  have hb := cap_x_bounds S hs hs1 j hz
  have hp := mul_pos (sub_pos.mpr hs1) (add_pos S.ha S.hc)
  rw [capForm_apply]
  exact ⟨div_nonneg (by linarith) hp.le,(div_le_one hp).mpr (by nlinarith)⟩

def parallelBudget (S : Shape) (lo hi : Bool → ℝ) : ℝ :=
  (∑ i, (hi i-lo i))/(S.a+S.c)

theorem parallelBudget_nonneg (S : Shape) (lo hi : Bool → ℝ) (ho : ∀ i, lo i ≤ hi i) :
    0 ≤ parallelBudget S lo hi :=
  div_nonneg (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (ho i)) (add_pos S.ha S.hc).le

def normalizedEndpoint (S : Shape) (s t : ℝ) : ℝ :=
  (t+(1-s)*S.c)/((1-s)*(S.a+S.c))

theorem normalized_total (S : Shape) {s : ℝ} (hs1 : s < 1) (lo hi : Bool → ℝ) :
    (∑ i, (normalizedEndpoint S s (hi i)-normalizedEndpoint S s (lo i))) =
      parallelBudget S lo hi/(1-s) := by
  simp [normalizedEndpoint,parallelBudget]
  field_simp [ne_of_gt (sub_pos.mpr hs1),ne_of_gt (add_pos S.ha S.hc)]
  ring

theorem normalized_band (S : Shape) {s : ℝ} (hs1 : s < 1) (l u : ℝ) :
    Plank.LinearBands.closedBand (capForm S s) (normalizedEndpoint S s l)
      (normalizedEndpoint S s u) = band false l u := by
  ext z
  simp only [Plank.LinearBands.closedBand,band,mem_ofPred_eq,capForm_apply,normalizedEndpoint]
  simp only [div_le_div_iff_of_pos_right (mul_pos (sub_pos.mpr hs1) (add_pos S.ha S.hc)),
    add_le_add_iff_right,coord,Bool.false_eq_true,if_false]

theorem cap_parallel_bound (S : Shape) (lo hi : Bool → ℝ) (ho : ∀ i, lo i ≤ hi i)
    {s : ℝ} (hs : 0 ≤ s) (j : Bool) (hsmall : parallelBudget S lo hi < 1-s) :
    (1-s-parallelBudget S lo hi)^2*((S.a+S.c)*|S.Y j| * (volume unitCorner).toReal) ≤
        (volume (cap S s j \ ⋃ i, band false (lo i) (hi i))).toReal ∧
      ((∀ i, lo i < hi i) → hi false < lo true →
        (1-s-parallelBudget S lo hi)^2*((S.a+S.c)*|S.Y j| * (volume unitCorner).toReal) <
          (volume (cap S s j \ ⋃ i, band false (lo i) (hi i))).toReal) := by
  have hr := parallelBudget_nonneg S lo hi ho
  have hδ : 0 < 1-s := hr.trans_lt hsmall
  have hs1 : s < 1 := by linarith
  have hD := mul_pos hδ (add_pos S.ha S.hc)
  let nl := fun i => normalizedEndpoint S s (lo i)
  let nh := fun i => normalizedEndpoint S s (hi i)
  have hno (i : Bool) : nl i ≤ nh i :=
    (div_le_div_iff_of_pos_right hD).mpr (by linarith [ho i])
  have hR : (∑ i, (nh i-nl i)) < 1 := by
    rw [normalized_total S hs1]
    exact (div_lt_one hδ).mpr hsmall
  have ha : ((1-s)*S.a,S.Y j*s) ∈ cap S s j := by
    simpa [Shape.X] using cap_x_vertex_mem S hs hs1 true j
  have hb : (-(1-s)*S.c,S.Y j*s) ∈ cap S s j := by
    have hX : -(1-s)*S.c = (1-s)*S.X false := by simp [Shape.X]; ring
    rw [hX]
    exact cap_x_vertex_mem S hs hs1 false j
  have hf := capForm_realisers S hs1 j
  have hgap : (⋃ i, Plank.LinearBands.closedBand (capForm S s) (nl i) (nh i)) =
      ⋃ i, band false (lo i) (hi i) :=
    iUnion_congr fun i => normalized_band S hs1 (lo i) (hi i)
  have harea : (1-parallelBudget S lo hi/(1-s))^2*(volume (cap S s j)).toReal =
      (1-s-parallelBudget S lo hi)^2*((S.a+S.c)*|S.Y j| * (volume unitCorner).toReal) := by
    rw [area_cap S hs hs1]
    field_simp [ne_of_gt hδ]
  have hbound := ParallelProductPlane.parallel_lower_bound (compact_cap S s j) (convex_cap S s j)
    nl nh hno hR (capForm S s) _ _ ha hb hf.1 hf.2
  rw [hgap,normalized_total S hs1,harea] at hbound
  refine ⟨hbound,?_⟩
  intro hp hsep
  have hnp (i : Bool) : nl i < nh i :=
    (div_lt_div_iff_of_pos_right hD).mpr (by linarith [hp i])
  have hnsep : nh false < nl true :=
    (div_lt_div_iff_of_pos_right hD).mpr (by linarith)
  have hV : 0 < (volume (cap S s j)).toReal := by
    rw [area_cap S hs hs1]
    exact mul_pos (sq_pos_of_pos hδ)
      (mul_pos (mul_pos (add_pos S.ha S.hc) (abs_pos.mpr (S.Y_ne j))) (unitCorner_area_pos S))
  have hne := ParallelProductPlane.separated_pair_not_equality (compact_cap S s j) (convex_cap S s j)
    hV nl nh hnp hnsep hR (capForm S s) _ _ ha hb hf.1 hf.2
      (fun z hz => capForm_bounds S hs hs1 j hz)
  rw [hgap,normalized_total S hs1,harea] at hne
  exact lt_of_le_of_ne hbound hne.symm

theorem cap_hinge_lower_bound (S : Shape) (lo hi : Bool → ℝ) (ho : ∀ i, lo i ≤ hi i)
    {s : ℝ} (hs : 0 ≤ s) (j : Bool) :
    (max 0 (1-s-parallelBudget S lo hi))^2*((S.a+S.c)*|S.Y j| * (volume unitCorner).toReal) ≤
      (volume (cap S s j \ ⋃ i, band false (lo i) (hi i))).toReal := by
  by_cases hsmall : parallelBudget S lo hi < 1-s
  · rw [max_eq_right (by linarith)]
    exact (cap_parallel_bound S lo hi ho hs j hsmall).1
  · rw [max_eq_left (by linarith)]
    simp

theorem mem_cap_false (S : Shape) (s : ℝ) (z : Point) :
    z ∈ cap S s false ↔ z ∈ S.body ∧ z.2 ≤ -S.d*s := by
  change (z ∈ S.body ∧ s ≤ z.2/(-S.d)) ↔ _
  rw [le_div_iff_of_neg (neg_lt_zero.mpr S.hd)]
  simp only [mul_comm s (-S.d)]

theorem mem_cap_true (S : Shape) (s : ℝ) (z : Point) :
    z ∈ cap S s true ↔ z ∈ S.body ∧ S.b*s ≤ z.2 := by
  change (z ∈ S.body ∧ s ≤ z.2/S.b) ↔ _
  rw [le_div_iff₀ S.hb]
  simp only [mul_comm s S.b]

/-- Exact decomposition after removing the transverse band; boundary lines
have zero area. The other removed set may be any union of vertical bands. -/
theorem gap_area_eq_caps (S : Shape) (lo hi s : Bool → ℝ) (hs : ∀ j, 0 ≤ s j) :
    (volume (S.body \ ((⋃ i, band false (lo i) (hi i)) ∪ yBand S s))).toReal =
      ∑ j : Bool, (volume (cap S (s j) j \ ⋃ i, band false (lo i) (hi i))).toReal := by
  let X := ⋃ i, band false (lo i) (hi i)
  have hnull₀ : volume {z : Point | z.2 = -S.d*s false} = 0 := by
    simpa [dot] using volume_line (by norm_num : ((0,1) : Point) ≠ 0) (-S.d*s false)
  have hnull₁ : volume {z : Point | z.2 = S.b*s true} = 0 := by
    simpa [dot] using volume_line (by norm_num : ((0,1) : Point) ≠ 0) (S.b*s true)
  have hopen : volume (S.body \ (X ∪ yBand S s)) =
      volume (S.body \ (X ∪ {z : Point | -S.d*s false < z.2 ∧ z.2 < S.b*s true})) := by
    apply measure_congr
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hnull₀,
      (measure_eq_zero_iff_ae_notMem).mp hnull₁] with z hz₀ hz₁
    apply propext
    have hb : (-S.d*s false ≤ z.2 ∧ z.2 ≤ S.b*s true) ↔
        (-S.d*s false < z.2 ∧ z.2 < S.b*s true) := by
      constructor
      · intro hh
        exact ⟨lt_of_le_of_ne hh.1 (Ne.symm hz₀),lt_of_le_of_ne hh.2 hz₁⟩
      · exact fun hh => ⟨hh.1.le,hh.2.le⟩
    change (z ∈ S.body ∧ ¬ (z ∈ X ∨ (-S.d*s false ≤ z.2 ∧ z.2 ≤ S.b*s true))) ↔
      (z ∈ S.body ∧ ¬ (z ∈ X ∨ (-S.d*s false < z.2 ∧ z.2 < S.b*s true)))
    rw [hb]
  have hset : S.body \ (X ∪ {z : Point | -S.d*s false < z.2 ∧ z.2 < S.b*s true}) =
      (cap S (s false) false \ X) ∪ (cap S (s true) true \ X) := by
    ext z
    simp only [mem_sdiff,mem_union,mem_ofPred_eq,mem_cap_false,mem_cap_true,
      not_or,not_and_or,not_lt]
    tauto
  have hd : AEDisjoint volume (cap S (s false) false \ X) (cap S (s true) true \ X) := by
    apply measure_mono_null (t := {z : Point | z.2 = 0})
    · intro z hz
      have hlo := (mem_cap_false S (s false) z).mp hz.1.1
      have hhi := (mem_cap_true S (s true) z).mp hz.2.1
      change z.2 = 0
      have hleft : -S.d*s false ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr S.hd.le) (hs false)
      have hright : 0 ≤ S.b*s true := mul_nonneg S.hb.le (hs true)
      linarith [hlo.2,hhi.2]
    · simpa [dot] using volume_line (by norm_num : ((0,1) : Point) ≠ 0) 0
  have hm : MeasurableSet (cap S (s true) true \ X) :=
    (compact_cap S _ _).measurableSet.diff (MeasurableSet.iUnion fun i => measurable_band false _ _)
  have hfin (j : Bool) : volume (cap S (s j) j \ X) ≠ ⊤ :=
    ne_top_of_le_ne_top (compact_body S).measure_ne_top
      (measure_mono (sdiff_subset.trans inter_subset_left))
  change (volume (S.body \ (X ∪ yBand S s))).toReal = _
  rw [hopen,hset,measure_union₀ hm.nullMeasurableSet hd,ENNReal.toReal_add (hfin false) (hfin true)]
  simp [X,add_comm]

theorem cap_deficit_mean (S : Shape) (s : Bool → ℝ) (r : ℝ) :
    (∑ j, |S.Y j| * (1-s j-r)) = (1-r-yWidth S s)*(∑ j, |S.Y j|) := by
  simp [Shape.Y,abs_of_pos S.hb,abs_of_pos S.hd,yWidth]
  field_simp [ne_of_gt (add_pos S.hb S.hd)]
  ring

theorem cap_hinges_lower_bound (S : Shape) (s : Bool → ℝ) (r : ℝ)
    (hbudget : r+yWidth S s < 1) :
    (1-r-yWidth S s)^2*(volume S.body).toReal ≤
      ∑ j, (max 0 (1-s j-r))^2*((S.a+S.c)*|S.Y j| * (volume unitCorner).toReal) := by
  have h := weighted_hinge_lower_bound (fun j => |S.Y j|) (fun j => 1-s j-r)
    (fun j => abs_nonneg _) (by linarith) (cap_deficit_mean S s r)
  have hsum : (∑ j, |S.Y j|) = S.b+S.d := by
    simp [Shape.Y,abs_of_pos S.hb,abs_of_pos S.hd]
  rw [hsum] at h
  have hh := mul_le_mul_of_nonneg_right h
    (mul_nonneg (add_pos S.ha S.hc).le (unitCorner_area_pos S).le)
  calc
    _ = (1-r-yWidth S s)^2*(S.b+S.d)*((S.a+S.c)*(volume unitCorner).toReal) := by
      rw [area_body,sum_weight]
      ring
    _ ≤ (∑ j, |S.Y j| * (max 0 (1-s j-r))^2)*((S.a+S.c)*(volume unitCorner).toReal) := hh
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem exists_cap_with_budget (S : Shape) (s : Bool → ℝ) (r : ℝ)
    (hbudget : r+yWidth S s < 1) : ∃ j, r < 1-s j := by
  have hm := cap_deficit_mean S s r
  have hw : 0 < ∑ j, |S.Y j| :=
    Finset.sum_pos (fun j _ => abs_pos.mpr (S.Y_ne j)) Finset.univ_nonempty
  have hpos : 0 < ∑ j, |S.Y j| * (1-s j-r) := by
    rw [hm]
    exact mul_pos (by linarith) hw
  by_contra hn
  push Not at hn
  have hnonpos : (∑ j, |S.Y j| * (1-s j-r)) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (by linarith [hn j])
  linarith

/-- A separated positive parallel pair gives strict inequality, even when one
of the two transverse caps is empty or completely covered. -/
theorem separated_pair_strict (S : Shape) (lo hi s : Bool → ℝ)
    (ho : ∀ i, lo i < hi i) (hsep : hi false < lo true) (hs : ∀ j, 0 ≤ s j)
    (hbudget : parallelBudget S lo hi+yWidth S s < 1) :
    (1-parallelBudget S lo hi-yWidth S s)^2*(volume S.body).toReal <
      (volume (S.body \ ((⋃ i, band false (lo i) (hi i)) ∪ yBand S s))).toReal := by
  have hb (j : Bool) := cap_hinge_lower_bound S lo hi (fun i => (ho i).le) (hs j) j
  obtain ⟨j,hj⟩ := exists_cap_with_budget S s (parallelBudget S lo hi) hbudget
  have hstrict := (cap_parallel_bound S lo hi (fun i => (ho i).le) (hs j) j hj).2 ho hsep
  have hsum : (∑ k, (max 0 (1-s k-parallelBudget S lo hi))^2*
      ((S.a+S.c)*|S.Y k| * (volume unitCorner).toReal)) <
      ∑ k, (volume (cap S (s k) k \ ⋃ i, band false (lo i) (hi i))).toReal := by
    apply Finset.sum_lt_sum (fun k _ => hb k)
    refine ⟨j,Finset.mem_univ j,?_⟩
    rwa [max_eq_right (by linarith)]
  rw [gap_area_eq_caps S lo hi s hs]
  exact (cap_hinges_lower_bound S s (parallelBudget S lo hi) hbudget).trans_lt hsum

theorem transverse_slide_gap_le (S : Shape) (lo hi : Bool → ℝ) (l u : ℝ) :
    volume (S.body \ ((⋃ i, band false (lo i) (hi i)) ∪
      band true (l-shift l u) (u-shift l u))) ≤
      volume (S.body \ ((⋃ i, band false (lo i) (hi i)) ∪ band true l u)) := by
  let X := ⋃ i, band false (lo i) (hi i)
  let U := S.body \ X
  let A := band true l u
  let B := band true (l-shift l u) (u-shift l u)
  have hmap : (fun z : Point => vector true (-shift l u)+z) '' (U ∩ A) ⊆ U ∩ B := by
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨⟨slide_mem S true hz.1.1 hz.2,?_⟩,?_⟩
    · intro hh
      obtain ⟨i,hi⟩ := mem_iUnion.mp hh
      apply hz.1.2
      exact mem_iUnion.mpr ⟨i,by simpa [band,coord,vector] using hi⟩
    · change l-shift l u ≤ coord true (vector true (-shift l u)+z) ∧
        coord true (vector true (-shift l u)+z) ≤ u-shift l u
      rw [coord_vector_add]
      exact ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hcovered : volume (U ∩ A) ≤ volume (U ∩ B) := by
    calc
      _ = volume ((fun z : Point => vector true (-shift l u)+z) '' (U ∩ A)) := by
        rw [Set.image_add_left,measure_preimage_add]
      _ ≤ _ := measure_mono hmap
  have hfinite (T : Set Point) : volume (U ∩ T) ≠ ⊤ :=
    ne_top_of_le_ne_top (compact_body S).measure_ne_top
      (measure_mono (inter_subset_left.trans sdiff_subset))
  have ha : volume (U \ A) = volume U-volume (U ∩ A) :=
    ENNReal.eq_sub_of_add_eq (hfinite A) (measure_sdiff_add_inter U (measurable_band true l u))
  have hb : volume (U \ B) = volume U-volume (U ∩ B) :=
    ENNReal.eq_sub_of_add_eq (hfinite B)
      (measure_sdiff_add_inter U (measurable_band true _ _))
  have hc : volume (U \ B) ≤ volume (U \ A) := by
    rw [ha,hb]
    exact tsub_le_tsub_left hcovered _
  simpa only [U,X,A,B,Set.sdiff_sdiff] using hc

/-- The strict separated-pair obstruction without any restriction on the
position of the transverse band, including null transverse bands. -/
theorem separated_pair_arbitrary_transverse_strict (S : Shape) (lo hi : Bool → ℝ)
    (ho : ∀ i, lo i < hi i) (hsep : hi false < lo true) (l u : ℝ) (hu : l ≤ u)
    (hbudget : parallelBudget S lo hi+(u-l)/(S.b+S.d) < 1) :
    (1-parallelBudget S lo hi-(u-l)/(S.b+S.d))^2*(volume S.body).toReal <
      (volume (S.body \ ((⋃ i, band false (lo i) (hi i)) ∪ band true l u))).toReal := by
  let s : Bool → ℝ := fun j => if j then (u-shift l u)/S.b else -(l-shift l u)/S.d
  have hc := shifted_contains_zero hu
  have hs (j : Bool) : 0 ≤ s j := by
    cases j
    · exact div_nonneg (neg_nonneg.mpr hc.1) S.hd.le
    · exact div_nonneg hc.2 S.hb.le
  have hw : yWidth S s = (u-l)/(S.b+S.d) := by
    dsimp [yWidth,s]
    field_simp [ne_of_gt S.hb,ne_of_gt S.hd,ne_of_gt (add_pos S.hb S.hd)]
    ring
  have hb : yBand S s = band true (l-shift l u) (u-shift l u) := by
    ext z
    simp [yBand,s,band,coord,mul_div_cancel₀,ne_of_gt S.hb,ne_of_gt S.hd]
  have hstrict := separated_pair_strict S lo hi s ho hsep hs (by rwa [hw])
  rw [hw,hb] at hstrict
  have hle := ENNReal.toReal_mono (ne_top_of_le_ne_top (compact_body S).measure_ne_top
    (measure_mono sdiff_subset)) (transverse_slide_gap_le S lo hi l u)
  exact hstrict.trans_le hle

end Quant.CrossedQuadrilateralCaps
