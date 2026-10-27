/- Exact sharpness for two crossing bands on a four-vertex body. -/
module
public import Plank.Plane
public import Plank.Convex.AffineRangeWidth
public import Plank.Measure.LinearBands
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralAttainment
open Set MeasureTheory
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Pointwise Function

abbrev Point := ℝ × ℝ

local instance : (volume : Measure Point).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℝ × ℝ)).IsAddHaarMeasure)

structure Shape where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  hd : 0 < d

def Shape.X (S : Shape) (i : Bool) : ℝ := if i then S.a else -S.c
def Shape.Y (S : Shape) (j : Bool) : ℝ := if j then S.b else -S.d
def Shape.vertices (S : Shape) : Set Point :=
  {(S.a,0),(0,S.b),(-S.c,0),(0,-S.d)}
def Shape.body (S : Shape) : Set Point := convexHull ℝ S.vertices

theorem Shape.X_ne (S : Shape) (i : Bool) : S.X i ≠ 0 := by
  cases i <;> simp [Shape.X,ne_of_gt S.ha,ne_of_gt S.hc]
theorem Shape.Y_ne (S : Shape) (i : Bool) : S.Y i ≠ 0 := by
  cases i <;> simp [Shape.Y,ne_of_gt S.hb,ne_of_gt S.hd]

def form (u : Point) : Point →L[ℝ] ℝ :=
  u.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + u.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem form_apply (u z : Point) : form u z = dot u z := rfl

theorem vertexX_mem (S : Shape) (i : Bool) : (S.X i,0) ∈ S.body := by
  apply subset_convexHull
  cases i <;> simp [Shape.vertices,Shape.X]
theorem vertexY_mem (S : Shape) (i : Bool) : (0,S.Y i) ∈ S.body := by
  apply subset_convexHull
  cases i <;> simp [Shape.vertices,Shape.Y]

theorem convex_body (S : Shape) : Convex ℝ S.body := convex_convexHull _ _
theorem compact_body (S : Shape) : IsCompact S.body := by
  apply Set.Finite.isCompact_convexHull
  simp [Shape.vertices]

theorem zero_mem (S : Shape) : (0 : Point) ∈ S.body := by
  have h := convex_body S (vertexX_mem S true) (vertexX_mem S false)
    (div_nonneg S.hc.le (add_pos S.ha S.hc).le)
    (div_nonneg S.ha.le (add_pos S.ha S.hc).le)
    (show S.c/(S.a+S.c)+S.a/(S.a+S.c)=1 by
      rw [← add_div,add_comm S.c S.a,div_self (ne_of_gt (add_pos S.ha S.hc))])
  convert h using 1
  ext <;> simp [Shape.X]
  ring

def core (S : Shape) (i j : Bool) : Set Point :=
  {z | 0 ≤ z.1/S.X i ∧ 0 ≤ z.2/S.Y j ∧ z.1/S.X i+z.2/S.Y j ≤ 1}

theorem core_subset_body (S : Shape) (i j : Bool) : core S i j ⊆ S.body := by
  intro z hz
  let w : Fin 3 → ℝ := ![1-z.1/S.X i-z.2/S.Y j,z.1/S.X i,z.2/S.Y j]
  let v : Fin 3 → Point := ![0,(S.X i,0),(0,S.Y j)]
  have hw : ∀ k ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w k := by
    intro k _; fin_cases k <;> dsimp [w] <;> linarith [hz.1,hz.2.1,hz.2.2]
  have hv : ∀ k ∈ (Finset.univ : Finset (Fin 3)), v k ∈ S.body := by
    intro k _; fin_cases k
    · exact zero_mem S
    · exact vertexX_mem S i
    · exact vertexY_mem S j
  have h := (convex_body S).sum_mem hw
    (show ∑ k ∈ (Finset.univ : Finset (Fin 3)), w k = 1 by simp [w,Fin.sum_univ_three]; ring) hv
  convert h using 1
  ext <;> simp [v,w,Fin.sum_univ_three,div_mul_cancel₀ _ (S.X_ne i),div_mul_cancel₀ _ (S.Y_ne j)]

theorem body_support (S : Shape) (i j : Bool) {z : Point} (hz : z ∈ S.body) :
    z.1/S.X i+z.2/S.Y j ≤ 1 := by
  have hh : S.body ⊆ (form ((S.X i)⁻¹,(S.Y j)⁻¹)) ⁻¹' Iic 1 := by
    apply convexHull_min _ ((convex_Iic (1 : ℝ)).linear_preimage (form _).toLinearMap)
    intro p hp
    have hca := S.ha.le
    have hcb := S.hb.le
    have hcc := S.hc.le
    have hcd := S.hd.le
    rcases hp with rfl | rfl | rfl | rfl <;> cases i <;> cases j <;>
      simp [form_apply,dot,Shape.X,Shape.Y,ne_of_gt S.ha,ne_of_gt S.hb,
        ne_of_gt S.hc,ne_of_gt S.hd] <;>
      nlinarith [mul_nonneg (inv_nonneg.mpr S.hc.le) S.ha.le,
        mul_nonneg (inv_nonneg.mpr S.ha.le) S.hc.le,
        mul_nonneg (inv_nonneg.mpr S.hd.le) S.hb.le,
        mul_nonneg (inv_nonneg.mpr S.hb.le) S.hd.le]
  simpa [dot,div_eq_mul_inv,mul_comm] using hh hz

theorem body_eq_cores (S : Shape) : S.body = ⋃ i, ⋃ j, core S i j := by
  apply Set.Subset.antisymm
  · intro z hz
    have chooseSign (x p n : ℝ) (hp : 0 < p) (hn : 0 < n) :
        ∃ i : Bool, 0 ≤ x/(if i then p else -n) := by
      by_cases hx : 0 ≤ x
      · exact ⟨true,div_nonneg hx hp.le⟩
      · exact ⟨false,div_nonneg_of_nonpos (le_of_not_ge hx) (neg_nonpos.mpr hn.le)⟩
    obtain ⟨i,hi⟩ := chooseSign z.1 S.a S.c S.ha S.hc
    obtain ⟨j,hj⟩ := chooseSign z.2 S.b S.d S.hb S.hd
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,hi,hj,body_support S i j hz⟩⟩
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    obtain ⟨j,hj⟩ := mem_iUnion.mp hi
    exact core_subset_body S i j hj

theorem measurable_core (S : Shape) (i j : Bool) : MeasurableSet (core S i j) := by
  exact (measurableSet_le measurable_const (measurable_fst.div_const _)).inter
    ((measurableSet_le measurable_const (measurable_snd.div_const _)).inter
      (measurableSet_le ((measurable_fst.div_const _).add
        (measurable_snd.div_const _)) measurable_const))

def corner (S : Shape) (r s : ℝ) (i j : Bool) : Set Point :=
  {z | r ≤ z.1/S.X i ∧ s ≤ z.2/S.Y j ∧ z.1/S.X i+z.2/S.Y j ≤ 1}

theorem measurable_corner (S : Shape) (r s : ℝ) (i j : Bool) :
    MeasurableSet (corner S r s i j) := by
  exact (measurableSet_le measurable_const (measurable_fst.div_const _)).inter
    ((measurableSet_le measurable_const (measurable_snd.div_const _)).inter
      (measurableSet_le ((measurable_fst.div_const _).add
        (measurable_snd.div_const _)) measurable_const))

theorem corner_eq_image (S : Shape) {r s : ℝ} (h : r+s < 1) (i j : Bool) :
    corner S r s i j =
      (fun z : Point => (S.X i*r,S.Y j*s)+(1-r-s) • z) '' core S i j := by
  have hd : 0 < 1-r-s := by linarith
  have hx := S.X_ne i
  have hy := S.Y_ne j
  have coord (x u t : ℝ) (hu : u ≠ 0) :
      (u*t+(1-r-s)*x)/u = t+(1-r-s)*(x/u) := by field_simp
  apply Set.Subset.antisymm
  · intro z hz
    let q : Point := ((z.1-S.X i*r)/(1-r-s),(z.2-S.Y j*s)/(1-r-s))
    have hqx : q.1/S.X i = (z.1/S.X i-r)/(1-r-s) := by
      dsimp [q]; field_simp
    have hqy : q.2/S.Y j = (z.2/S.Y j-s)/(1-r-s) := by
      dsimp [q]; field_simp
    refine ⟨q,?_,?_⟩
    · change 0 ≤ q.1/S.X i ∧ 0 ≤ q.2/S.Y j ∧ q.1/S.X i+q.2/S.Y j ≤ 1
      rw [hqx,hqy]
      exact ⟨div_nonneg (sub_nonneg.mpr hz.1) hd.le,
        div_nonneg (sub_nonneg.mpr hz.2.1) hd.le,
        by rw [← add_div,div_le_one hd]; linarith [hz.2.2]⟩
    · ext <;> dsimp [q] <;> field_simp <;> ring
  · rintro _ ⟨z,hz,rfl⟩
    change r ≤ (S.X i*r+(1-r-s)*z.1)/S.X i ∧
      s ≤ (S.Y j*s+(1-r-s)*z.2)/S.Y j ∧ _
    simp only [coord _ _ _ hx,coord _ _ _ hy]
    refine ⟨by nlinarith [hz.1],by nlinarith [hz.2.1],?_⟩
    change (S.X i*r+(1-r-s)*z.1)/S.X i+
      (S.Y j*s+(1-r-s)*z.2)/S.Y j ≤ 1
    rw [coord _ _ _ hx,coord _ _ _ hy]
    nlinarith [hz.2.2]

theorem volume_translate_smul (v : Point) {δ : ℝ} (hδ : 0 ≤ δ) (A : Set Point) :
    volume ((fun z => v+δ • z) '' A) = ENNReal.ofReal (δ^2)*volume A := by
  have he : (fun z => v+δ • z) '' A = (fun z => v+z) '' (δ • A) := by
    rw [← Set.image_smul,Set.image_image]
  rw [he,Set.image_add_left,measure_preimage_add,Measure.addHaar_smul_of_nonneg volume hδ]
  simp

theorem volume_corner (S : Shape) {r s : ℝ} (h : r+s < 1) (i j : Bool) :
    volume (corner S r s i j) = ENNReal.ofReal ((1-r-s)^2)*volume (core S i j) := by
  rw [corner_eq_image S h,volume_translate_smul _ (by linarith)]

theorem form_ne_zero {u : Point} (hu : u ≠ 0) : form u ≠ 0 := by
  intro hf
  apply hu
  have hx := congrArg (fun f : Point →L[ℝ] ℝ => f (1,0)) hf
  have hy := congrArg (fun f : Point →L[ℝ] ℝ => f (0,1)) hf
  simpa [dot,Prod.ext_iff] using And.intro hx hy

theorem volume_line {u : Point} (hu : u ≠ 0) (t : ℝ) :
    volume {z | dot u z = t} = 0 :=
  Plank.LinearBands.measure_level_zero volume (form u) (form_ne_zero hu) t

private theorem opposite_zero {p n x : ℝ} (hp : 0 < p) (hn : 0 < n)
    (hx : 0 ≤ x/p) (hy : 0 ≤ x/(-n)) : x = 0 := by
  have hx' : 0 ≤ x := by
    simpa [div_mul_cancel₀ _ (ne_of_gt hp)] using mul_nonneg hx hp.le
  have hy' : x ≤ 0 := by
    simpa only [div_mul_cancel₀ _ (neg_ne_zero.mpr (ne_of_gt hn))] using
      mul_nonpos_of_nonneg_of_nonpos hy (neg_nonpos.mpr hn.le)
  exact le_antisymm hy' hx'

private theorem signed_zero {p n x : ℝ} (hp : 0 < p) (hn : 0 < n)
    {i j : Bool} (hne : i ≠ j)
    (hi : 0 ≤ x/(if i then p else -n))
    (hj : 0 ≤ x/(if j then p else -n)) : x = 0 := by
  cases i <;> cases j
  · exact False.elim (hne rfl)
  · exact opposite_zero hp hn hj hi
  · exact opposite_zero hp hn hi hj
  · exact False.elim (hne rfl)

theorem core_aedisjoint (S : Shape) :
    Pairwise (AEDisjoint volume on fun e : Bool × Bool => core S e.1 e.2) := by
  intro e f hne
  by_cases hx : e.1 = f.1
  · have hy : e.2 ≠ f.2 := fun hy => hne (Prod.ext hx hy)
    apply measure_mono_null (t := {z : Point | dot (0,1) z = 0})
    · intro z hz
      simpa [dot] using signed_zero S.hb S.hd hy hz.1.2.1 hz.2.2.1
    · exact volume_line (by norm_num : ((0,1) : Point) ≠ 0) 0
  · apply measure_mono_null (t := {z : Point | dot (1,0) z = 0})
    · intro z hz
      simpa [dot] using signed_zero S.ha S.hc hx hz.1.1 hz.2.1
    · exact volume_line (by norm_num : ((1,0) : Point) ≠ 0) 0

theorem corner_subset_core (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (i j : Bool) : corner S r s i j ⊆ core S i j :=
  fun _ h => ⟨hr.trans h.1,hs.trans h.2.1,h.2.2⟩

theorem corner_aedisjoint (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Pairwise (AEDisjoint volume on fun e : Bool × Bool => corner S r s e.1 e.2) := by
  intro e f hef
  exact measure_mono_null (Set.inter_subset_inter (corner_subset_core S hr hs _ _)
    (corner_subset_core S hr hs _ _)) (core_aedisjoint S hef)

theorem volume_union (A : Bool × Bool → Set Point) (hm : ∀ e, MeasurableSet (A e))
    (hd : Pairwise (AEDisjoint volume on A)) :
    volume (⋃ e, A e) = ∑ e, volume (A e) := by
  simpa using measure_biUnion_finset₀ (μ := volume) (s := Finset.univ)
    (f := A) (fun _ _ _ _ h => hd h) (fun e _ => (hm e).nullMeasurableSet)

theorem volume_body_eq_sum (S : Shape) :
    volume S.body = ∑ e : Bool × Bool, volume (core S e.1 e.2) := by
  rw [body_eq_cores]
  simpa only [iUnion_prod'] using
    volume_union _ (fun e => measurable_core S e.1 e.2) (core_aedisjoint S)

private theorem exterior_iff {p n t x : ℝ} (hp : 0 < p) (hn : 0 < n) :
    ¬ (-n*t < x ∧ x < p*t) ↔ ∃ i : Bool, t ≤ x/(if i then p else -n) := by
  constructor
  · intro h
    by_cases hx : x < p*t
    · refine ⟨false,?_⟩
      have hlow : x ≤ -n*t := le_of_not_gt (fun hl => h ⟨hl,hx⟩)
      exact (le_div_iff_of_neg (neg_neg_of_pos hn)).mpr (by nlinarith)
    · exact ⟨true,(le_div_iff₀ hp).mpr (by nlinarith [le_of_not_gt hx])⟩
  · rintro ⟨i,hi⟩ ⟨hl,hh⟩
    cases i
    · have h := (le_div_iff_of_neg (neg_neg_of_pos hn)).mp hi
      nlinarith
    · have h := (le_div_iff₀ hp).mp hi
      nlinarith

theorem open_gap_eq_corners (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    S.body \ ({z : Point | -S.c*r < z.1 ∧ z.1 < S.a*r} ∪
      {z : Point | -S.d*s < z.2 ∧ z.2 < S.b*s}) =
      ⋃ e : Bool × Bool, corner S r s e.1 e.2 := by
  ext z
  constructor
  · rintro ⟨hz,hn⟩
    obtain ⟨i,hi⟩ := (exterior_iff S.ha S.hc).mp (fun h => hn (Or.inl h))
    obtain ⟨j,hj⟩ := (exterior_iff S.hb S.hd).mp (fun h => hn (Or.inr h))
    exact mem_iUnion.mpr ⟨(i,j),hi,hj,body_support S i j hz⟩
  · intro hz
    obtain ⟨e,he⟩ := mem_iUnion.mp hz
    refine ⟨core_subset_body S _ _ (corner_subset_core S hr hs _ _ he),?_⟩
    rintro (hx | hy)
    · exact (exterior_iff S.ha S.hc).mpr ⟨e.1,he.1⟩ hx
    · exact (exterior_iff S.hb S.hd).mpr ⟨e.2,he.2.1⟩ hy

theorem volume_closed_eq_open (S : Shape) (r s : ℝ) :
    volume (S.body \ ({z : Point | -S.c*r ≤ z.1 ∧ z.1 ≤ S.a*r} ∪
      {z : Point | -S.d*s ≤ z.2 ∧ z.2 ≤ S.b*s})) =
    volume (S.body \ ({z : Point | -S.c*r < z.1 ∧ z.1 < S.a*r} ∪
      {z : Point | -S.d*s < z.2 ∧ z.2 < S.b*s})) := by
  let f : Bool → Point → ℝ := fun i => if i then Prod.snd else Prod.fst
  let lo : Bool → ℝ := fun i => if i then -S.d*s else -S.c*r
  let hi : Bool → ℝ := fun i => if i then S.b*s else S.a*r
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

/-- Exact actual Lebesgue-volume attainment by the two crossing closed bands. -/
theorem volume_gap_two (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : r+s < 1) :
    volume (S.body \ ({z : Point | -S.c*r ≤ z.1 ∧ z.1 ≤ S.a*r} ∪
      {z : Point | -S.d*s ≤ z.2 ∧ z.2 ≤ S.b*s})) =
      ENNReal.ofReal ((1-r-s)^2)*volume S.body := by
  rw [volume_closed_eq_open,open_gap_eq_corners S hr hs,
    volume_union _ (fun e => measurable_corner S r s e.1 e.2)
      (corner_aedisjoint S hr hs)]
  simp only [volume_corner S h,← Finset.mul_sum,← volume_body_eq_sum]

theorem null_plank_volume (n : Plank) (hn : n.lo = n.hi) : volume n.set = 0 := by
  apply measure_mono_null (t := {z | dot n.u z = n.lo})
  · intro z hz
    exact le_antisymm (by simpa [← hn] using hz.2) hz.1
  · exact volume_line n.u_ne_zero n.lo

/-- The third zero-width plank may have any nonzero normal and any location. -/
theorem volume_gap_with_null (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : r+s < 1) (n : Plank) (hn : n.lo = n.hi) :
    volume (S.body \ ({z : Point | -S.c*r ≤ z.1 ∧ z.1 ≤ S.a*r} ∪
      {z : Point | -S.d*s ≤ z.2 ∧ z.2 ≤ S.b*s} ∪ n.set)) =
      ENNReal.ofReal ((1-r-s)^2)*volume S.body := by
  rw [← Set.sdiff_sdiff,measure_sdiff_null (null_plank_volume n hn)]
  exact volume_gap_two S hr hs h

theorem area_gap_with_null (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : r+s < 1) (n : Plank) (hn : n.lo = n.hi) :
    (volume (S.body \ ({z : Point | -S.c*r ≤ z.1 ∧ z.1 ≤ S.a*r} ∪
      {z : Point | -S.d*s ≤ z.2 ∧ z.2 ≤ S.b*s} ∪ n.set))).toReal =
      (1-r-s)^2*(volume S.body).toReal := by
  rw [volume_gap_with_null S hr hs h n hn,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)]

theorem mem_body_iff_support (S : Shape) (z : Point) :
    z ∈ S.body ↔ ∀ i j, z.1/S.X i+z.2/S.Y j ≤ 1 := by
  constructor
  · exact fun hz i j => body_support S i j hz
  · intro h
    have chooseSign (x p n : ℝ) (hp : 0 < p) (hn : 0 < n) :
        ∃ i : Bool, 0 ≤ x/(if i then p else -n) := by
      by_cases hx : 0 ≤ x
      · exact ⟨true,div_nonneg hx hp.le⟩
      · exact ⟨false,div_nonneg_of_nonpos (le_of_not_ge hx) (neg_nonpos.mpr hn.le)⟩
    obtain ⟨i,hi⟩ := chooseSign z.1 S.a S.c S.ha S.hc
    obtain ⟨j,hj⟩ := chooseSign z.2 S.b S.d S.hb S.hd
    exact core_subset_body S i j ⟨hi,hj,h i j⟩

/-- The body has genuinely positive finite Lebesgue area. -/
theorem area_body_pos (S : Shape) : 0 < (volume S.body).toReal := by
  let U : Set Point := {z | ∀ i j, z.1/S.X i+z.2/S.Y j < 1}
  have hopen : IsOpen U := by
    simp only [U,Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt ((continuous_fst.div_const _).add (continuous_snd.div_const _))
      continuous_const
  have hne : U.Nonempty := ⟨0,by simp [U]⟩
  have hsub : U ⊆ S.body := fun z hz => (mem_body_iff_support S z).mpr
    (fun i j => (hz i j).le)
  exact ENNReal.toReal_pos (ne_of_gt ((hopen.measure_pos volume hne).trans_le
    (measure_mono hsub))) (compact_body S).measure_ne_top

theorem coordinate_box (S : Shape) :
    S.body ⊆ Icc (-S.c) S.a ×ˢ Icc (-S.d) S.b := by
  apply convexHull_min _ ((convex_Icc _ _).prod (convex_Icc _ _))
  intro z hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [Set.mem_prod,Set.mem_Icc] <;>
    constructor <;> constructor <;> linarith [S.ha,S.hb,S.hc,S.hd]

theorem coordinate_ranges (S : Shape) :
    Prod.fst '' S.body = Icc (-S.c) S.a ∧
      Prod.snd '' S.body = Icc (-S.d) S.b := by
  constructor
  · apply Set.Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (coordinate_box S hz).1
    · have : OrdConnected (Prod.fst '' S.body) :=
        ((convex_body S).linear_image (LinearMap.fst ℝ ℝ ℝ)).ordConnected
      exact Set.Icc_subset _ ⟨(-S.c,0),vertexX_mem S false,rfl⟩
        ⟨(S.a,0),vertexX_mem S true,rfl⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (coordinate_box S hz).2
    · have : OrdConnected (Prod.snd '' S.body) :=
        ((convex_body S).linear_image (LinearMap.snd ℝ ℝ ℝ)).ordConnected
      exact Set.Icc_subset _ ⟨(0,-S.d),vertexY_mem S false,rfl⟩
        ⟨(0,S.b),vertexY_mem S true,rfl⟩

def direction (u : Point) : Point →ᵃ[ℝ] ℝ := (form u).toLinearMap.toAffineMap

@[simp] theorem direction_apply (u z : Point) : direction u z = dot u z := rfl

theorem coordinate_widths (S : Shape) :
    rangeWidth S.body (direction (1,0)) = S.a+S.c ∧
      rangeWidth S.body (direction (0,1)) = S.b+S.d := by
  have hx : (direction (1,0) : Point → ℝ) = Prod.fst := by ext z; simp [dot]
  have hy : (direction (0,1) : Point → ℝ) = Prod.snd := by ext z; simp [dot]
  simp only [rangeWidth,Plank.Body.width,hx,hy,(coordinate_ranges S).1,(coordinate_ranges S).2]
  rw [csSup_Icc (by linarith [S.ha,S.hc]),csInf_Icc (by linarith [S.ha,S.hc]),
    csSup_Icc (by linarith [S.hb,S.hd]),csInf_Icc (by linarith [S.hb,S.hd])]
  simp

theorem direction_width_pos (S : Shape) {u : Point} (hu : u ≠ 0) :
    0 < rangeWidth S.body (direction u) := by
  have hc := (compact_body S).image (form u).continuous
  have hbound (z : Point) (hz : z ∈ S.body) :
      sInf (form u '' S.body) ≤ form u z ∧ form u z ≤ sSup (form u '' S.body) :=
    ⟨csInf_le hc.bddBelow ⟨z,hz,rfl⟩,le_csSup hc.bddAbove ⟨z,hz,rfl⟩⟩
  have hzero := hbound 0 (zero_mem S)
  have hX := hbound (S.a,0) (vertexX_mem S true)
  have hY := hbound (0,S.b) (vertexY_mem S true)
  change 0 < sSup (form u '' S.body)-sInf (form u '' S.body)
  by_contra hh
  have hx : u.1*S.a = 0 := by simp [dot] at hzero hX; linarith
  have hy : u.2*S.b = 0 := by simp [dot] at hzero hY; linarith
  apply hu
  ext
  · exact (mul_eq_zero.mp hx).resolve_right (ne_of_gt S.ha)
  · exact (mul_eq_zero.mp hy).resolve_right (ne_of_gt S.hb)

def xPlank (S : Shape) (r : ℝ) (hr : 0 ≤ r) : Plank :=
  ⟨(1,0),-S.c*r,S.a*r,by norm_num,by nlinarith [S.ha,S.hc]⟩
def yPlank (S : Shape) (s : ℝ) (hs : 0 ≤ s) : Plank :=
  ⟨(0,1),-S.d*s,S.b*s,by norm_num,by nlinarith [S.hb,S.hd]⟩

/-- Relative width uses the actual full directional range of this body. -/
def relativeWidth (S : Shape) (p : Plank) : ℝ :=
  (p.hi-p.lo)/rangeWidth S.body (direction p.u)

theorem relative_widths (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (n : Plank) (hn : n.lo = n.hi) :
    relativeWidth S (xPlank S r hr) = r ∧
    relativeWidth S (yPlank S s hs) = s ∧ relativeWidth S n = 0 := by
  simp only [relativeWidth,xPlank,yPlank,(coordinate_widths S).1,
    (coordinate_widths S).2,hn,sub_self,zero_div,and_true]
  constructor
  · field_simp [ne_of_gt (add_pos S.ha S.hc)]; ring
  · field_simp [ne_of_gt (add_pos S.hb S.hd)]; ring

def family (S : Shape) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (n : Plank) :
    Fin 3 → Plank := ![xPlank S r hr,yPlank S s hs,n]

theorem family_union (S : Shape) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (n : Plank) :
    (⋃ i, (family S r s hr hs n i).set) =
    {z : Point | -S.c*r ≤ z.1 ∧ z.1 ≤ S.a*r} ∪
      {z : Point | -S.d*s ≤ z.2 ∧ z.2 ≤ S.b*s} ∪ n.set := by
  ext z
  simp only [mem_iUnion,mem_union]
  constructor
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact Or.inl (Or.inl (by simpa [family,Plank.set,Membership.mem,xPlank,dot] using hi))
    · exact Or.inl (Or.inr (by simpa [family,Plank.set,Membership.mem,yPlank,dot] using hi))
    · exact Or.inr hi
  · rintro ((hx | hy) | hn)
    · exact ⟨0,by simpa [family,Plank.set,Membership.mem,xPlank,dot] using hx⟩
    · exact ⟨1,by simpa [family,Plank.set,Membership.mem,yPlank,dot] using hy⟩
    · exact ⟨2,hn⟩

/-- This explicit three-plank family attains the quantitative square bound. -/
theorem sharp_family (S : Shape) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : r+s < 1) (n : Plank) (hn : n.lo = n.hi) :
    (volume (S.body \ ⋃ i, (family S r s hr.le hs.le n i).set)).toReal =
      (1-∑ i, relativeWidth S (family S r s hr.le hs.le n i))^2*
        (volume S.body).toReal := by
  have hw := relative_widths S hr.le hs.le n hn
  rw [family_union]
  simpa [family,Fin.sum_univ_three,hw.1,hw.2.1,hw.2.2,sub_add_eq_sub_sub] using
    area_gap_with_null S hr.le hs.le h n hn

/-- Splitting the horizontal-coordinate band gives three positive bands.
The displayed widths use the actual coordinate ranges of the body. -/
theorem split_band_attainment (S : Shape) {r s t : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : r+s < 1) (ht₀ : -S.c*r < t) (ht₁ : t < S.a*r) :
    let w₀ := (t-(-S.c*r))/rangeWidth S.body (direction (1,0))
    let w₁ := (S.a*r-t)/rangeWidth S.body (direction (1,0))
    let w₂ := (S.b*s-(-S.d*s))/rangeWidth S.body (direction (0,1))
    0 < w₀ ∧ 0 < w₁ ∧ 0 < w₂ ∧ w₀+w₁+w₂ = r+s ∧
      volume (S.body \ ({z : Point | -S.c*r ≤ z.1 ∧ z.1 ≤ t} ∪
        {z : Point | t ≤ z.1 ∧ z.1 ≤ S.a*r} ∪
        {z : Point | -S.d*s ≤ z.2 ∧ z.2 ≤ S.b*s})) =
        ENNReal.ofReal ((1-(w₀+w₁+w₂))^2)*volume S.body := by
  dsimp only
  rw [(coordinate_widths S).1,(coordinate_widths S).2]
  have hw₂ : (S.b*s-(-S.d*s))/(S.b+S.d) = s := by
    field_simp [ne_of_gt (add_pos S.hb S.hd)]; ring
  have hsum : (t-(-S.c*r))/(S.a+S.c)+(S.a*r-t)/(S.a+S.c) = r := by
    field_simp [ne_of_gt (add_pos S.ha S.hc)]; ring
  rw [hw₂,hsum]
  refine ⟨div_pos (sub_pos.mpr ht₀) (add_pos S.ha S.hc),
    div_pos (sub_pos.mpr ht₁) (add_pos S.ha S.hc),hs,rfl,?_⟩
  have hu : {z : Point | -S.c*r ≤ z.1 ∧ z.1 ≤ t} ∪
      {z : Point | t ≤ z.1 ∧ z.1 ≤ S.a*r} =
      {z : Point | -S.c*r ≤ z.1 ∧ z.1 ≤ S.a*r} := by
    exact congrArg (fun A : Set ℝ => Prod.fst ⁻¹' A)
      (Set.Icc_union_Icc_eq_Icc ht₀.le ht₁.le)
  rw [hu,sub_add_eq_sub_sub]
  exact volume_gap_two S hr.le hs.le h

end Quant.CrossedQuadrilateralAttainment

/-- info: 'Quant.CrossedQuadrilateralAttainment.sharp_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralAttainment.sharp_family

/-- info: 'Quant.CrossedQuadrilateralAttainment.split_band_attainment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralAttainment.split_band_attainment
