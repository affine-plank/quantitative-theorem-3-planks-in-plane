/- Placement rigidity for diagonal bands on a genuine quadrilateral. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralAttainment

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CrossedQuadrilateralNecessity
open Set MeasureTheory
open Quant.CrossedQuadrilateralAttainment
open scoped BigOperators Pointwise Function

local instance : (volume : Measure Point).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℝ × ℝ)).IsAddHaarMeasure)

def unitCorner : Set Point := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ 1}

def diagonal (x y : ℝ) : Point →ₗ[ℝ] Point :=
  (x • LinearMap.fst ℝ ℝ ℝ).prod (y • LinearMap.snd ℝ ℝ ℝ)

@[simp] theorem diagonal_apply (x y : ℝ) (z : Point) :
    diagonal x y z = (x*z.1,y*z.2) := rfl

theorem diagonal_det (x y : ℝ) : LinearMap.det (diagonal x y) = x*y := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,diagonal,Module.Basis.finTwoProd]

theorem core_eq_diagonal (S : Shape) (i j : Bool) :
    core S i j = diagonal (S.X i) (S.Y j) '' unitCorner := by
  ext z
  constructor
  · intro hz
    refine ⟨(z.1/S.X i,z.2/S.Y j),hz,?_⟩
    ext <;> simp [mul_div_cancel₀, S.X_ne i,S.Y_ne j]
  · rintro ⟨p,hp,rfl⟩
    simpa [core,unitCorner,S.X_ne i,S.Y_ne j] using hp

theorem area_core (S : Shape) (i j : Bool) :
    (volume (core S i j)).toReal =
      |S.X i| * |S.Y j| * (volume unitCorner).toReal := by
  rw [core_eq_diagonal,Measure.addHaar_image_linearMap,diagonal_det,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _),abs_mul]

theorem volume_corner_all (S : Shape) (r s : ℝ) (i j : Bool) :
    volume (corner S r s i j) =
      ENNReal.ofReal ((max 0 (1-r-s))^2)*volume (core S i j) := by
  by_cases h : r+s < 1
  · rw [max_eq_right (by linarith)]
    exact volume_corner S h i j
  · have hle : 1-r-s ≤ 0 := by linarith
    rw [max_eq_left hle]
    simp only [zero_pow (by norm_num : 2 ≠ 0),ENNReal.ofReal_zero,zero_mul]
    apply measure_mono_null (t := {z : Point | dot ((S.X i)⁻¹,(S.Y j)⁻¹) z = 1})
    · intro z hz
      change (S.X i)⁻¹*z.1+(S.Y j)⁻¹*z.2 = 1
      have hsum : z.1/S.X i+z.2/S.Y j = 1 := by
        apply le_antisymm hz.2.2
        linarith [hz.1,hz.2.1]
      simpa [div_eq_mul_inv,mul_comm] using hsum
    · apply volume_line
      intro hn
      have hx := congrArg Prod.fst hn
      exact (inv_ne_zero (S.X_ne i)) hx

theorem area_corner (S : Shape) (r s : ℝ) (i j : Bool) :
    (volume (corner S r s i j)).toReal =
      (max 0 (1-r-s))^2*(|S.X i| * |S.Y j| * (volume unitCorner).toReal) := by
  rw [volume_corner_all,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _),area_core]

def weight (S : Shape) (e : Bool × Bool) : ℝ := |S.X e.1| * |S.Y e.2|

theorem weight_pos (S : Shape) (e : Bool × Bool) : 0 < weight S e :=
  mul_pos (abs_pos.mpr (S.X_ne e.1)) (abs_pos.mpr (S.Y_ne e.2))

theorem sum_weight (S : Shape) :
    ∑ e : Bool × Bool, weight S e = (S.a+S.c)*(S.b+S.d) := by
  simp [Fintype.sum_prod_type,weight,Shape.X,Shape.Y,
    abs_of_pos S.ha,abs_of_pos S.hb,abs_of_pos S.hc,abs_of_pos S.hd]
  ring

theorem area_body (S : Shape) :
    (volume S.body).toReal = (∑ e : Bool × Bool, weight S e)*(volume unitCorner).toReal := by
  rw [volume_body_eq_sum,ENNReal.toReal_sum]
  · simp only [area_core,weight,Finset.sum_mul]
  · intro e _
    exact ne_top_of_le_ne_top (compact_body S).measure_ne_top
      (measure_mono (core_subset_body S e.1 e.2))

theorem unitCorner_area_pos (S : Shape) : 0 < (volume unitCorner).toReal := by
  have hp := area_body_pos S
  rw [area_body] at hp
  exact pos_of_mul_pos_right hp (Finset.sum_nonneg fun e _ => (weight_pos S e).le)

private theorem hinge_remainder_nonneg {m x : ℝ} (hm : 0 < m) :
    0 ≤ (max 0 x)^2-2*m*x+m^2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx]
    nlinarith [sq_nonneg (x-m)]
  · rw [max_eq_left (le_of_not_ge hx)]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hm.le (le_of_not_ge hx),sq_nonneg m]

private theorem hinge_remainder_eq_zero {m x : ℝ} (hm : 0 < m) :
    (max 0 x)^2-2*m*x+m^2 = 0 ↔ x = m := by
  constructor
  · intro h
    by_cases hx : 0 ≤ x
    · rw [max_eq_right hx] at h
      have he : (x-m)^2 = 0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp he)
    · rw [max_eq_left (le_of_not_ge hx)] at h
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hm.le (le_of_not_ge hx),sq_pos_of_pos hm]
  · rintro rfl
    rw [max_eq_right hm.le]
    ring

/-- Strict equality criterion for the positive-part square, with positive weights.
The mean must be positive; values below zero are permitted. -/
theorem weighted_hinge_equality {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 < w i) {m : ℝ} (hm : 0 < m)
    (hmean : ∑ i, w i*x i = m*∑ i, w i) :
    (∑ i, w i*(max 0 (x i))^2) = m^2*∑ i, w i ↔ ∀ i, x i = m := by
  classical
  constructor
  · intro he
    have hn (i : ι) : 0 ≤ w i*((max 0 (x i))^2-2*m*x i+m^2) :=
      mul_nonneg (hw i).le (hinge_remainder_nonneg hm)
    have hz : ∑ i, w i*((max 0 (x i))^2-2*m*x i+m^2) = 0 := by
      calc
        _ = (∑ i, w i*(max 0 (x i))^2)-2*m*(∑ i, w i*x i)+m^2*(∑ i, w i) := by
          simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by rw [he,hmean]; ring
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hz i (Finset.mem_univ i)
    exact (hinge_remainder_eq_zero hm).mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (hw i)))
  · intro he
    simp only [he,max_eq_right hm.le,← Finset.sum_mul,mul_comm (∑ i, w i)]

def xBand (S : Shape) (r : Bool → ℝ) : Set Point :=
  {z | -S.c*r false ≤ z.1 ∧ z.1 ≤ S.a*r true}

def yBand (S : Shape) (s : Bool → ℝ) : Set Point :=
  {z | -S.d*s false ≤ z.2 ∧ z.2 ≤ S.b*s true}

def xWidth (S : Shape) (r : Bool → ℝ) : ℝ :=
  (S.a*r true+S.c*r false)/(S.a+S.c)

def yWidth (S : Shape) (s : Bool → ℝ) : ℝ :=
  (S.b*s true+S.d*s false)/(S.b+S.d)

theorem actual_widths (S : Shape) (r s : Bool → ℝ) :
    (S.a*r true-(-S.c*r false))/
        Plank.Convex.DeficientHeightTilt.rangeWidth S.body (direction (1,0)) = xWidth S r ∧
    (S.b*s true-(-S.d*s false))/
        Plank.Convex.DeficientHeightTilt.rangeWidth S.body (direction (0,1)) = yWidth S s := by
  simp [xWidth,yWidth,(coordinate_widths S).1,(coordinate_widths S).2]

private theorem exterior_iff {p n x : ℝ} (hp : 0 < p) (hn : 0 < n)
    (r : Bool → ℝ) :
    ¬ (-n*r false < x ∧ x < p*r true) ↔
      ∃ i : Bool, r i ≤ x/(if i then p else -n) := by
  constructor
  · intro h
    by_cases hx : -n*r false < x
    · have hh : p*r true ≤ x := le_of_not_gt (fun hh => h ⟨hx,hh⟩)
      exact ⟨true,(le_div_iff₀ hp).mpr (by simpa [mul_comm] using hh)⟩
    · have hh : x ≤ -n*r false := le_of_not_gt hx
      exact ⟨false,(le_div_iff_of_neg (neg_lt_zero.mpr hn)).mpr
        (by simpa [mul_comm] using hh)⟩
  · rintro ⟨i,hi⟩ hx
    cases i
    · have hh := (le_div_iff_of_neg (neg_lt_zero.mpr hn)).mp hi
      nlinarith [hx.1]
    · have hh := (le_div_iff₀ hp).mp hi
      nlinarith [hx.2]

theorem open_gap_eq_corners (S : Shape) (r s : Bool → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) :
    S.body \ ({z : Point | -S.c*r false < z.1 ∧ z.1 < S.a*r true} ∪
      {z : Point | -S.d*s false < z.2 ∧ z.2 < S.b*s true}) =
      ⋃ e : Bool × Bool, corner S (r e.1) (s e.2) e.1 e.2 := by
  ext z
  constructor
  · rintro ⟨hz,hn⟩
    obtain ⟨i,hi⟩ := (exterior_iff S.ha S.hc r).mp (fun h => hn (Or.inl h))
    obtain ⟨j,hj⟩ := (exterior_iff S.hb S.hd s).mp (fun h => hn (Or.inr h))
    exact mem_iUnion.mpr ⟨(i,j),hi,hj,body_support S i j hz⟩
  · intro hz
    obtain ⟨e,he⟩ := mem_iUnion.mp hz
    refine ⟨core_subset_body S _ _ (corner_subset_core S (hr _) (hs _) _ _ he),?_⟩
    rintro (hx | hy)
    · exact (exterior_iff S.ha S.hc r).mpr ⟨e.1,he.1⟩ hx
    · exact (exterior_iff S.hb S.hd s).mpr ⟨e.2,he.2.1⟩ hy

theorem volume_closed_eq_open (S : Shape) (r s : Bool → ℝ) :
    volume (S.body \ (xBand S r ∪ yBand S s)) =
      volume (S.body \ ({z : Point | -S.c*r false < z.1 ∧ z.1 < S.a*r true} ∪
        {z : Point | -S.d*s false < z.2 ∧ z.2 < S.b*s true})) := by
  let f : Bool → Point → ℝ := fun i => if i then Prod.snd else Prod.fst
  let lo : Bool → ℝ := fun i => if i then -S.d*s false else -S.c*r false
  let hi : Bool → ℝ := fun i => if i then S.b*s true else S.a*r true
  have hnull (i : Bool) (t : ℝ) : volume {z | f i z = t} = 0 := by
    cases i
    · simpa [f,dot] using volume_line (by norm_num : ((1,0) : Point) ≠ 0) t
    · simpa [f,dot] using volume_line (by norm_num : ((0,1) : Point) ≠ 0) t
  have hb (A : Bool → Set Point) : (⋃ i, A i) = A false ∪ A true := by
    ext z
    simp only [mem_iUnion,mem_union]
    constructor
    · rintro ⟨i,hi⟩; cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hh | hh)
      · exact ⟨false,hh⟩
      · exact ⟨true,hh⟩
  have he := Plank.LinearBands.measure_closed_gap_eq_open_gap volume f lo hi
    (fun i => hnull i _) (fun i => hnull i _) S.body
  rw [hb,hb] at he
  exact he

/-- Exact area for arbitrary diagonal bands containing the diagonal intersection.
The positive part includes all clipped and collapsed exterior corners. -/
theorem area_gap (S : Shape) (r s : Bool → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) :
    (volume (S.body \ (xBand S r ∪ yBand S s))).toReal =
      (∑ e : Bool × Bool, weight S e*(max 0 (1-r e.1-s e.2))^2)*
        (volume unitCorner).toReal := by
  have hd : Pairwise (AEDisjoint volume on
      fun e : Bool × Bool => corner S (r e.1) (s e.2) e.1 e.2) := by
    intro e f hef
    exact measure_mono_null (Set.inter_subset_inter
      (corner_subset_core S (hr _) (hs _) _ _) (corner_subset_core S (hr _) (hs _) _ _))
      (core_aedisjoint S hef)
  rw [volume_closed_eq_open,open_gap_eq_corners S r s hr hs,
    volume_union _ (fun e => measurable_corner S _ _ e.1 e.2) hd,
    ENNReal.toReal_sum]
  · simp only [area_corner,Finset.sum_mul,weight]
    apply Finset.sum_congr rfl
    intro e _
    ring
  · intro e _
    exact ne_top_of_le_ne_top (compact_body S).measure_ne_top
      (measure_mono ((corner_subset_core S (hr _) (hs _) _ _).trans
        (core_subset_body S _ _)))

theorem weighted_deficit_mean (S : Shape) (r s : Bool → ℝ) :
    (∑ e : Bool × Bool, weight S e*(1-r e.1-s e.2)) =
      (1-xWidth S r-yWidth S s)*∑ e : Bool × Bool, weight S e := by
  rw [sum_weight]
  simp [Fintype.sum_prod_type,weight,Shape.X,Shape.Y,
    abs_of_pos S.ha,abs_of_pos S.hb,abs_of_pos S.hc,abs_of_pos S.hd,xWidth,yWidth]
  field_simp [ne_of_gt (add_pos S.ha S.hc),ne_of_gt (add_pos S.hb S.hd)]
  ring

theorem xWidth_const (S : Shape) (r : ℝ) : xWidth S (fun _ => r) = r := by
  dsimp [xWidth]
  field_simp [ne_of_gt (add_pos S.ha S.hc)]

theorem yWidth_const (S : Shape) (s : ℝ) : yWidth S (fun _ => s) = s := by
  dsimp [yWidth]
  field_simp [ne_of_gt (add_pos S.hb S.hd)]

theorem calibrated_iff_constant_deficit (S : Shape) (r s : Bool → ℝ) :
    (∀ e : Bool × Bool, 1-r e.1-s e.2 = 1-xWidth S r-yWidth S s) ↔
      r true = r false ∧ s true = s false := by
  constructor
  · intro h
    have htt := h (true,true)
    have hft := h (false,true)
    have htf := h (true,false)
    exact ⟨by linarith,by linarith⟩
  · rintro ⟨hr,hs⟩
    have hre : r = fun _ => r true := by funext i; cases i <;> simp [hr]
    have hse : s = fun _ => s true := by funext j; cases j <;> simp [hs]
    rw [hre,hse,xWidth_const,yWidth_const]
    intro e
    rfl

/-- Exhaustive placement classification within the two diagonal directions,
when both closed bands contain the diagonal intersection and the budget is
strictly below one. There is no assumption that every exterior corner survives. -/
theorem equality_iff_calibrated (S : Shape) (r s : Bool → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j)
    (hbudget : xWidth S r+yWidth S s < 1) :
    (volume (S.body \ (xBand S r ∪ yBand S s))).toReal =
        (1-xWidth S r-yWidth S s)^2*(volume S.body).toReal ↔
      r true = r false ∧ s true = s false := by
  have hm : 0 < 1-xWidth S r-yWidth S s := by linarith
  have hC := ne_of_gt (unitCorner_area_pos S)
  rw [area_gap S r s hr hs,area_body,← mul_assoc]
  constructor
  · intro h
    have he := mul_right_cancel₀ hC h
    exact (calibrated_iff_constant_deficit S r s).mp
      ((weighted_hinge_equality (weight S) (fun e => 1-r e.1-s e.2)
        (weight_pos S) hm (weighted_deficit_mean S r s)).mp he)
  · intro h
    have he := (weighted_hinge_equality (weight S) (fun e => 1-r e.1-s e.2)
      (weight_pos S) hm (weighted_deficit_mean S r s)).mpr
        ((calibrated_iff_constant_deficit S r s).mpr h)
    rw [he]

/-- A third plank of zero width has arbitrary direction and location. -/
theorem equality_with_null_iff_calibrated (S : Shape) (r s : Bool → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j)
    (hbudget : xWidth S r+yWidth S s < 1) (n : Plank) (hn : n.lo = n.hi) :
    (volume (S.body \ (xBand S r ∪ yBand S s ∪ n.set))).toReal =
        (1-xWidth S r-yWidth S s)^2*(volume S.body).toReal ↔
      r true = r false ∧ s true = s false := by
  rw [← Set.sdiff_sdiff,measure_sdiff_null (null_plank_volume n hn)]
  exact equality_iff_calibrated S r s hr hs hbudget

/-- Adjacent subdivision gives an exhaustive iff in this three-band chart. -/
theorem equality_split_iff_calibrated (S : Shape) (r s : Bool → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j)
    (hbudget : xWidth S r+yWidth S s < 1) {t : ℝ}
    (ht₀ : -S.c*r false ≤ t) (ht₁ : t ≤ S.a*r true) :
    (volume (S.body \ ({z : Point | -S.c*r false ≤ z.1 ∧ z.1 ≤ t} ∪
      {z : Point | t ≤ z.1 ∧ z.1 ≤ S.a*r true} ∪ yBand S s))).toReal =
        (1-xWidth S r-yWidth S s)^2*(volume S.body).toReal ↔
      r true = r false ∧ s true = s false := by
  have hu : {z : Point | -S.c*r false ≤ z.1 ∧ z.1 ≤ t} ∪
      {z : Point | t ≤ z.1 ∧ z.1 ≤ S.a*r true} = xBand S r := by
    exact congrArg (fun A : Set ℝ => Prod.fst ⁻¹' A)
      (Set.Icc_union_Icc_eq_Icc ht₀ ht₁)
  rw [hu]
  exact equality_iff_calibrated S r s hr hs hbudget

/-- The same classification in the original four band endpoints. The ratios
on the right say that opposite sides are shrunk by the same factor. -/
theorem endpoint_equality_iff (S : Shape) (lx ux ly uy : ℝ)
    (hlx : lx ≤ 0) (hux : 0 ≤ ux) (hly : ly ≤ 0) (huy : 0 ≤ uy)
    (hbudget : (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (volume (S.body \ ({z : Point | lx ≤ z.1 ∧ z.1 ≤ ux} ∪
      {z : Point | ly ≤ z.2 ∧ z.2 ≤ uy}))).toReal =
        (1-(ux-lx)/(S.a+S.c)-(uy-ly)/(S.b+S.d))^2*(volume S.body).toReal ↔
      ux/S.a = -lx/S.c ∧ uy/S.b = -ly/S.d := by
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
  have hxb : xBand S r = {z : Point | lx ≤ z.1 ∧ z.1 ≤ ux} := by
    ext z
    simp [xBand,r,mul_div_cancel₀,ne_of_gt S.ha,ne_of_gt S.hc]
  have hyb : yBand S s = {z : Point | ly ≤ z.2 ∧ z.2 ≤ uy} := by
    ext z
    simp [yBand,s,mul_div_cancel₀,ne_of_gt S.hb,ne_of_gt S.hd]
  have h := equality_iff_calibrated S r s hr hs (by rwa [hxr,hys])
  simpa [hxb,hyb,hxr,hys,r,s] using h

end Quant.CrossedQuadrilateralNecessity

/-- info: 'Quant.CrossedQuadrilateralNecessity.equality_with_null_iff_calibrated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralNecessity.equality_with_null_iff_calibrated
