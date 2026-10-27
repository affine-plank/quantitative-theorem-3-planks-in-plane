module
/-
# Exterior caps of weighted cyclic threshold triangles

The three elementary caps have exact positive-part-square areas. A linear
compatibility condition makes each cap part of the full threshold region,
so its area can be refunded when that region is clipped to the body.
-/
public import Plank.Proofs.Quant.CyclicWeightedThresholdGeometry

@[expose] public section

noncomputable section

namespace Quant.CyclicThresholdCaps

open Set MeasureTheory CyclicWeightedThresholdGeometry

def direction (a b c : ℝ) : Fin 3 → ℝ := ![a, b, c]
def weight (a b c : ℝ) : Fin 3 → ℝ := ![k0 b c, k1 a c, k2 a b]
def coord (i : Fin 3) (p : ℝ × ℝ) : ℝ := ![p.1, p.2, 1-p.1-p.2] i

theorem direction_bounds {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (i : Fin 3) : 0 < direction a b c i ∧ direction a b c i < 1 := by
  fin_cases i <;> first | exact ha | exact hb | exact hc

theorem weight_pos {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (i : Fin 3) : 0 < weight a b c i := by
  obtain ⟨h0,h1,h2⟩ := weights_pos ha hb hc
  fin_cases i <;> first | exact h0 | exact h1 | exact h2

theorem value_coord (a b c : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    value a b c i p = direction a b c i * coord i p + coord (i+2) p := by
  fin_cases i <;> dsimp [value, direction, coord] <;> ring

theorem coordinate_identity (a b c : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    value a b c (i+1) p + direction a b c (i+1) * value a b c i p -
      direction a b c (i+1) = weight a b c (i+2) * coord i p := by
  fin_cases i <;> dsimp [value, direction, weight, coord, k0, k1, k2] <;> ring

theorem third_value_identity (a b c : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    direction a b c (i+1) * value a b c (i+2) p =
      direction a b c (i+1) * direction a b c (i+2) +
      (1-direction a b c (i+2)) * value a b c (i+1) p -
      weight a b c i * coord i p := by
  fin_cases i <;> dsimp [value, direction, weight, coord, k0, k1, k2] <;> ring

/-- The elementary triangle outside body side `i`, before imposing the third level. -/
def cap (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : Set (ℝ × ℝ) :=
  {p | coord i p ≤ 0 ∧ t i ≤ value a b c i p ∧ t (i+1) ≤ value a b c (i+1) p}

def capSize (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  direction a b c (i+1) - t (i+1) - direction a b c (i+1) * t i

def capLinear (a b c : ℝ) (i : Fin 3) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := ![(-k2 a b * p.1, p.1+b*p.2),
    (-k0 b c * p.2, -c*p.1+(1-c)*p.2),
    (k1 a c * (p.1+p.2), -(1-a)*p.1-p.2)] i
  map_add' p q := by
    fin_cases i <;> apply Prod.ext <;> dsimp <;> ring
  map_smul' r p := by
    fin_cases i <;> apply Prod.ext <;> dsimp <;> ring

def capShift (a _b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : ℝ × ℝ :=
  ![(0,-t 1), (0,c-t 2), (-k1 a c,1-t 0)] i

theorem cap_affine (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    capLinear a b c i p + capShift a b c t i =
      (-weight a b c (i+2) * coord i p, value a b c (i+1) p - t (i+1)) := by
  fin_cases i <;> apply Prod.ext <;>
    simp [capLinear, capShift, weight, coord, value] <;> ring

theorem det_capLinear (a b c : ℝ) (i : Fin 3) :
    LinearMap.det (capLinear a b c i) =
      -(direction a b c (i+1) * weight a b c (i+2)) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  fin_cases i <;>
    simp [LinearMap.toMatrix_apply, capLinear, Module.Basis.finTwoProd,
      direction, weight, k0, k1, k2] <;> ring

theorem volume_cap (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (i : Fin 3) :
    volume (cap a b c t i) = ENNReal.ofReal ((max 0 (capSize a b c t i))^2 /
      (2 * direction a b c (i+1) * weight a b c (i+2))) := by
  have hd := (direction_bounds ha hb hc (i+1)).1
  have hw := weight_pos ha hb hc (i+2)
  have he : cap a b c t i = capLinear a b c i ⁻¹'
      ((fun p => p + capShift a b c t i) ⁻¹' RowDeletion.triangle (capSize a b c t i)) := by
    ext p
    simp only [mem_preimage, cap_affine]
    change (coord i p ≤ 0 ∧ t i ≤ value a b c i p ∧
      t (i+1) ≤ value a b c (i+1) p) ↔
      (0 ≤ -weight a b c (i+2) * coord i p ∧
       0 ≤ value a b c (i+1) p - t (i+1) ∧
       -weight a b c (i+2) * coord i p + (value a b c (i+1) p-t (i+1)) ≤
         direction a b c (i+1)-t (i+1)-direction a b c (i+1)*t i)
    have hid := coordinate_identity a b c i p
    constructor
    · rintro ⟨hx,h0,h1⟩
      have hm := mul_le_mul_of_nonneg_left h0 hd.le
      exact ⟨by nlinarith, by linarith, by nlinarith only [hid,hm]⟩
    · rintro ⟨hx,h1,hs⟩
      have h0 : direction a b c (i+1)*t i ≤
          direction a b c (i+1)*value a b c i p := by nlinarith only [hid,hs]
      exact ⟨by nlinarith, le_of_mul_le_mul_left h0 hd, by linarith⟩
  have hdet : 0 < direction a b c (i+1)*weight a b c (i+2) := mul_pos hd hw
  rw [he, Measure.addHaar_preimage_linearMap volume
      (by rw [det_capLinear]; exact neg_ne_zero.mpr hdet.ne'),
    det_capLinear, measure_preimage_add_right,
    CyclicCenteredGeometry.volume_triangle_posPart, inv_neg, abs_neg,
    abs_of_pos (inv_pos.mpr hdet), ← ENNReal.ofReal_mul (inv_pos.mpr hdet).le]
  congr 1
  field_simp [hd.ne', hw.ne']

/-- Compatibility of neighboring levels prevents trimming an exterior cap. -/
def compatible (a b c : ℝ) (t : Fin 3 → ℝ) : Prop :=
  ∀ i, 0 ≤ (1-direction a b c (i+1))*t i - direction a b c i*t (i+1) +
    direction a b c i*direction a b c (i+1)

theorem cap_subset_upperRegion (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : compatible a b c t) (i : Fin 3) :
    cap a b c t i ⊆ upperRegion a b c t := by
  intro p hp
  have hmod : i+1+1 = i+2 := by fin_cases i <;> rfl
  have hj := ht (i+1)
  rw [hmod] at hj
  have hid := third_value_identity a b c i p
  have hmul := mul_le_mul_of_nonneg_left hp.2.2
    (sub_nonneg.mpr (direction_bounds ha hb hc (i+2)).2.le)
  have hcoord := mul_nonpos_of_nonneg_of_nonpos (weight_pos ha hb hc i).le hp.1
  have hthird : t (i+2) ≤ value a b c (i+2) p := by
    apply le_of_mul_le_mul_left (a := direction a b c (i+1)) _
      (direction_bounds ha hb hc (i+1)).1
    nlinarith only [hj, hid, hmul, hcoord]
  intro j
  fin_cases i <;> fin_cases j <;> first | exact hp.2.1 | exact hp.2.2 | exact hthird

theorem cap_eq_exterior (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : compatible a b c t) (i : Fin 3) :
    cap a b c t i = upperRegion a b c t ∩ {p | coord i p ≤ 0} := by
  ext p
  exact ⟨fun hp => ⟨cap_subset_upperRegion a b c t ha hb hc ht i hp, hp.1⟩,
    fun hp => ⟨hp.2, hp.1 i, hp.1 (i+1)⟩⟩

theorem continuous_coord (i : Fin 3) : Continuous (coord i) := by
  change Continuous (fun p => coord i p)
  fin_cases i <;> dsimp [coord] <;> fun_prop

theorem measurableSet_cap (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) :
    MeasurableSet (cap a b c t i) := by
  exact (measurableSet_le (continuous_coord i).measurable measurable_const).inter
    ((measurableSet_le measurable_const (continuous_value a b c i).measurable).inter
      (measurableSet_le measurable_const (continuous_value a b c (i+1)).measurable))

theorem volume_coord_zero (i : Fin 3) :
    volume {p : ℝ × ℝ | coord i p = 0} = 0 := by
  fin_cases i
  · simpa [coord, dot] using CommonVertex.volume_line_zero
      (u := (1,0)) (fun h => one_ne_zero (congrArg Prod.fst h)) (0 : ℝ)
  · simpa [coord, dot] using CommonVertex.volume_line_zero
      (u := (0,1)) (fun h => one_ne_zero (congrArg Prod.snd h)) (0 : ℝ)
  · change volume {p : ℝ × ℝ | coord 2 p = 0} = 0
    have he : {p : ℝ × ℝ | coord 2 p = 0} = {p | dot (1,1) p = 1} := by
      ext p
      change 1-p.1-p.2 = 0 ↔ 1*p.1+1*p.2 = 1
      constructor <;> intro h <;> linarith
    rw [he]
    exact CommonVertex.volume_line_zero
      (fun h => one_ne_zero (congrArg Prod.fst h)) 1

theorem mem_triangle_iff_coord (p : ℝ × ℝ) :
    p ∈ stdTriangle.set ↔ ∀ i, 0 ≤ coord i p := by
  rw [Proofs.Quant.stdTriangle_set_eq]
  constructor
  · rintro ⟨hx,hy,hxy⟩ i
    fin_cases i <;> dsimp [coord] <;> linarith
  · intro h
    have hz := h 2
    exact ⟨h 0,h 1,by dsimp [coord] at hz; linarith⟩

/-- Nonnegative levels exclude intersections of two strict exterior half-planes. -/
theorem coord_eq_zero_of_two_nonpos (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : ∀ i, 0 ≤ t i) {p : ℝ × ℝ} (hp : p ∈ upperRegion a b c t)
    {i j : Fin 3} (hij : i ≠ j) (hi : coord i p ≤ 0) (hj : coord j p ≤ 0) :
    coord i p = 0 := by
  have hval (k : Fin 3) : 0 ≤ value a b c k p := (ht k).trans (hp k)
  have hcases : j = i+1 ∨ j = i+2 := by
    fin_cases i <;> fin_cases j <;> simp_all
  apply le_antisymm hi
  rcases hcases with rfl | rfl
  · have hm := mul_nonpos_of_nonneg_of_nonpos
      (direction_bounds ha hb hc (i+1)).1.le hj
    have hv := hval (i+1)
    rw [value_coord] at hv
    have he : i+1+2 = i := by fin_cases i <;> rfl
    rw [he] at hv
    linarith
  · have hv := hval i
    rw [value_coord] at hv
    have hm : 0 ≤ direction a b c i * coord i p := by linarith
    exact nonneg_of_mul_nonneg_right hm (direction_bounds ha hb hc i).1

theorem pairwise_caps_aedisjoint (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hpos : ∀ i, 0 ≤ t i) (ht : compatible a b c t) :
    Pairwise (fun i j => AEDisjoint volume (cap a b c t i) (cap a b c t j)) := by
  intro i j hij
  apply measure_mono_null (s := cap a b c t i ∩ cap a b c t j)
    (t := {p | coord i p = 0}) _ (volume_coord_zero i)
  intro p hp
  exact coord_eq_zero_of_two_nonpos a b c t ha hb hc hpos
    (cap_subset_upperRegion a b c t ha hb hc ht i hp.1) hij hp.1.1 hp.2.1

theorem upperCell_cap_aedisjoint (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) :
    AEDisjoint volume (upperCell a b c t) (cap a b c t i) := by
  apply measure_mono_null (s := upperCell a b c t ∩ cap a b c t i)
    (t := {p | coord i p = 0}) _ (volume_coord_zero i)
  intro p hp
  exact le_antisymm hp.2.1 ((mem_triangle_iff_coord p).mp hp.1.1 i)

/-- Exact decomposition of the unrestricted region into its retained body part
and the three exterior triangles, with only null boundary intersections. -/
theorem volume_upperRegion_eq_cell_add_caps (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hpos : ∀ i, 0 ≤ t i) (ht : compatible a b c t) :
    volume (upperRegion a b c t) = volume (upperCell a b c t) +
      ∑ i, volume (cap a b c t i) := by
  classical
  have he : upperRegion a b c t = upperCell a b c t ∪ ⋃ i, cap a b c t i := by
    ext p
    constructor
    · intro hp
      by_cases hT : p ∈ stdTriangle.set
      · exact Or.inl ⟨hT,hp⟩
      · have hn : ¬ ∀ i, 0 ≤ coord i p := fun h => hT ((mem_triangle_iff_coord p).mpr h)
        obtain ⟨i,hi⟩ := not_forall.mp hn
        exact Or.inr (mem_iUnion.mpr ⟨i,le_of_lt (lt_of_not_ge hi),hp i,hp (i+1)⟩)
    · rintro (hp | hp)
      · exact hp.2
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hp
        exact cap_subset_upperRegion a b c t ha hb hc ht i hi
  have hd : AEDisjoint volume (upperCell a b c t) (⋃ i,cap a b c t i) := by
    change volume (upperCell a b c t ∩ ⋃ i,cap a b c t i) = 0
    rw [inter_iUnion]
    exact measure_iUnion_null (upperCell_cap_aedisjoint a b c t)
  rw [he, measure_union₀
    (MeasurableSet.iUnion (measurableSet_cap a b c t)).nullMeasurableSet hd,
    measure_iUnion₀ (pairwise_caps_aedisjoint a b c t ha hb hc hpos ht)
      (fun i => (measurableSet_cap a b c t i).nullMeasurableSet), tsum_fintype]

/-- Exact actual-body area with every exterior cap refunded. No containment
assumption is made on the threshold triangle itself. -/
theorem volume_upperCell_toReal (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hpos : ∀ i, 0 ≤ t i) (ht : compatible a b c t) :
    (volume (upperCell a b c t)).toReal =
      (max 0 (1+a*b*c-k0 b c*t 0-k1 a c*t 1-k2 a b*t 2))^2 /
        (2*k0 b c*k1 a c*k2 a b) -
      ∑ i, (max 0 (capSize a b c t i))^2 /
        (2*direction a b c (i+1)*weight a b c (i+2)) := by
  obtain ⟨hk0,hk1,hk2⟩ := weights_pos ha hb hc
  have hcapfin (i : Fin 3) : volume (cap a b c t i) ≠ ⊤ := by
    rw [volume_cap a b c t ha hb hc i]
    exact ENNReal.ofReal_ne_top
  have hbodyfin : volume (upperCell a b c t) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (upperRegion a b c t) ≠ ⊤ from ?_)
      (measure_mono Set.inter_subset_right)
    rw [volume_upperRegion a b c t ha hb hc]
    exact ENNReal.ofReal_ne_top
  have hreal := congrArg ENNReal.toReal
    (volume_upperRegion_eq_cell_add_caps a b c t ha hb hc hpos ht)
  rw [ENNReal.toReal_add hbodyfin (ENNReal.sum_ne_top.mpr (fun i _ => hcapfin i)),
    ENNReal.toReal_sum (fun i _ => hcapfin i),
    volume_upperRegion a b c t ha hb hc, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hcapreal (i : Fin 3) : (volume (cap a b c t i)).toReal =
      (max 0 (capSize a b c t i))^2 /
        (2*direction a b c (i+1)*weight a b c (i+2)) := by
    have hd := (direction_bounds ha hb hc (i+1)).1
    have hw := weight_pos ha hb hc (i+2)
    rw [volume_cap a b c t ha hb hc i, ENNReal.toReal_ofReal (by positivity)]
  simp_rw [hcapreal] at hreal
  linarith only [hreal]

def lowerRegion (a b c : ℝ) (t : Fin 3 → ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ i, value a b c i p ≤ t i}

def lowerCell (a b c : ℝ) (t : Fin 3 → ℝ) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ lowerRegion a b c t

def reflectionIndex : Fin 3 → Fin 3 := ![1,0,2]
def reflectedLevels (t : Fin 3 → ℝ) (i : Fin 3) : ℝ := 1-t (reflectionIndex i)

theorem reflectionIndex_involutive (i : Fin 3) :
    reflectionIndex (reflectionIndex i) = i := by fin_cases i <;> rfl

theorem value_reflect (a b c : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    value (1-b) (1-a) (1-c) i (Proofs.Symmetry.swapMap p) =
      1-value a b c (reflectionIndex i) p := by
  fin_cases i <;> dsimp [value, reflectionIndex, Proofs.Symmetry.swapMap] <;> ring

theorem lowerRegion_eq_preimage (a b c : ℝ) (t : Fin 3 → ℝ) :
    lowerRegion a b c t = Proofs.Symmetry.swapMap ⁻¹'
      upperRegion (1-b) (1-a) (1-c) (reflectedLevels t) := by
  ext p
  change (∀ i, value a b c i p ≤ t i) ↔
    ∀ i, reflectedLevels t i ≤ value (1-b) (1-a) (1-c) i (Proofs.Symmetry.swapMap p)
  constructor
  · intro hp i
    rw [value_reflect]
    exact sub_le_sub_left (hp (reflectionIndex i)) 1
  · intro hp i
    have h := hp (reflectionIndex i)
    rw [value_reflect, reflectedLevels, reflectionIndex_involutive] at h
    linarith

theorem lowerCell_eq_preimage (a b c : ℝ) (t : Fin 3 → ℝ) :
    lowerCell a b c t = Proofs.Symmetry.swapMap ⁻¹'
      upperCell (1-b) (1-a) (1-c) (reflectedLevels t) := by
  rw [lowerCell, lowerRegion_eq_preimage, upperCell, preimage_inter]
  congr 1
  ext p
  exact Proofs.Symmetry.swapMap_mem_iff p

theorem compatible_reflected {a b c : ℝ} {t : Fin 3 → ℝ}
    (ht : compatible a b c t) : compatible (1-b) (1-a) (1-c) (reflectedLevels t) := by
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  intro i
  fin_cases i <;> dsimp [direction, reflectedLevels, reflectionIndex] at * <;>
    nlinarith only [h0,h1,h2]

def lowerCapSize (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  t i + (1-direction a b c i)*t (i+1)-1

/-- The dual exact formula refunds the portions of an all-upper threshold
triangle that fall outside the body. -/
theorem volume_lowerCell_toReal (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hupper : ∀ i, t i ≤ 1) (ht : compatible a b c t) :
    (volume (lowerCell a b c t)).toReal =
      (max 0 (k0 b c*t 0+k1 a c*t 1+k2 a b*t 2-(1+a*b*c)))^2 /
        (2*k0 b c*k1 a c*k2 a b) -
      ∑ i, (max 0 (lowerCapSize a b c t i))^2 /
        (2*(1-direction a b c i)*weight a b c (i+2)) := by
  have ha' : 0 < 1-b ∧ 1-b < 1 := by constructor <;> linarith [hb.1,hb.2]
  have hb' : 0 < 1-a ∧ 1-a < 1 := by constructor <;> linarith [ha.1,ha.2]
  have hc' : 0 < 1-c ∧ 1-c < 1 := by constructor <;> linarith [hc.1,hc.2]
  have hpos : ∀ i, 0 ≤ reflectedLevels t i := fun i => sub_nonneg.mpr (hupper _)
  rw [lowerCell_eq_preimage, Proofs.Symmetry.volume_preimage_swapMap]
  have hv := volume_upperCell_toReal (1-b) (1-a) (1-c) (reflectedLevels t)
    ha' hb' hc' hpos (compatible_reflected ht)
  rw [hv]
  simp only [Fin.sum_univ_three]
  dsimp [reflectedLevels, reflectionIndex, capSize, lowerCapSize, direction, weight, k0, k1, k2]
  ring_nf

end Quant.CyclicThresholdCaps
