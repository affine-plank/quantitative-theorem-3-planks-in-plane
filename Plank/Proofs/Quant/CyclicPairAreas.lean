module
/-
# Exact areas of cyclic pairs of exterior half-planes

A raw low pair is an elementary wedge minus its outer vertex cap. The
compatibility inequality makes that entire cap removable. Reflection gives
the corresponding high-pair formula, with independent cyclic directions.
-/
public import Plank.Proofs.Quant.CyclicBadThresholds

@[expose] public section

noncomputable section

namespace Quant.CyclicPairAreas

open Set MeasureTheory CyclicWeightedThresholdGeometry CyclicThresholdCaps

def rawLow (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ {p | value a b c i p ≤ t i ∧ value a b c (i+1) p ≤ t (i+1)}

def rawHigh (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ {p | t i ≤ value a b c i p ∧ t (i+1) ≤ value a b c (i+1) p}

def lowWedge (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : Set (ℝ × ℝ) :=
  {p | 0 ≤ coord i p ∧ value a b c i p ≤ t i ∧ value a b c (i+1) p ≤ t (i+1)}

def outerLow (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : Set (ℝ × ℝ) :=
  {p | 0 ≤ coord i p ∧ coord (i+2) p ≤ 0 ∧ value a b c (i+1) p ≤ t (i+1)}

theorem complementary_coordinate_identity (a b c : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    1-value a b c i p-(1-direction a b c i)*value a b c (i+1) p =
      weight a b c (i+2)*coord (i+1) p := by
  fin_cases i <;> dsimp [value, direction, weight, coord, k0, k1, k2] <;> ring

theorem compatibility_coordinate_identity (a b c : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    (1-direction a b c (i+1))*value a b c i p -
      direction a b c i*value a b c (i+1) p +
      direction a b c i*direction a b c (i+1) =
      weight a b c (i+2)*coord (i+2) p := by
  fin_cases i <;> dsimp [value, direction, weight, coord, k0, k1, k2] <;> ring

def lowLinear (a b c : ℝ) (i : Fin 3) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  -capLinear a b c i

theorem low_affine (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    lowLinear a b c i p + -capShift a b c t i =
      (weight a b c (i+2)*coord i p, t (i+1)-value a b c (i+1) p) := by
  change -(capLinear a b c i p) + -capShift a b c t i = _
  rw [← neg_add, cap_affine]
  simp

theorem det_lowLinear (a b c : ℝ) (i : Fin 3) :
    LinearMap.det (lowLinear a b c i) =
      -(direction a b c (i+1)*weight a b c (i+2)) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  fin_cases i <;>
    simp [LinearMap.toMatrix_apply, lowLinear, capLinear, Module.Basis.finTwoProd,
      direction, weight, k0, k1, k2] <;> ring

theorem volume_lowWedge (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (i : Fin 3) :
    volume (lowWedge a b c t i) = ENNReal.ofReal ((max 0 (-capSize a b c t i))^2 /
      (2*direction a b c (i+1)*weight a b c (i+2))) := by
  have hd := (direction_bounds ha hb hc (i+1)).1
  have hw := weight_pos ha hb hc (i+2)
  have he : lowWedge a b c t i = lowLinear a b c i ⁻¹'
      ((fun p => p + -capShift a b c t i) ⁻¹' RowDeletion.triangle (-capSize a b c t i)) := by
    ext p
    simp only [mem_preimage, low_affine]
    change (0 ≤ coord i p ∧ value a b c i p ≤ t i ∧
      value a b c (i+1) p ≤ t (i+1)) ↔
      (0 ≤ weight a b c (i+2)*coord i p ∧
       0 ≤ t (i+1)-value a b c (i+1) p ∧
       weight a b c (i+2)*coord i p+(t (i+1)-value a b c (i+1) p) ≤
         -(direction a b c (i+1)-t (i+1)-direction a b c (i+1)*t i))
    have hid := coordinate_identity a b c i p
    constructor
    · rintro ⟨hx,h0,h1⟩
      have hm := mul_le_mul_of_nonneg_left h0 hd.le
      exact ⟨mul_nonneg hw.le hx, sub_nonneg.mpr h1, by nlinarith only [hid,hm]⟩
    · rintro ⟨hx,h1,hs⟩
      have h0 : direction a b c (i+1)*value a b c i p ≤
          direction a b c (i+1)*t i := by nlinarith only [hid,hs]
      exact ⟨nonneg_of_mul_nonneg_right hx hw, le_of_mul_le_mul_left h0 hd,
        by linarith⟩
  have hdet : 0 < direction a b c (i+1)*weight a b c (i+2) := mul_pos hd hw
  rw [he, Measure.addHaar_preimage_linearMap volume
      (by rw [det_lowLinear]; exact neg_ne_zero.mpr hdet.ne'),
    det_lowLinear, measure_preimage_add_right,
    CyclicCenteredGeometry.volume_triangle_posPart, inv_neg, abs_neg,
    abs_of_pos (inv_pos.mpr hdet), ← ENNReal.ofReal_mul (inv_pos.mpr hdet).le]
  congr 1
  field_simp [hd.ne', hw.ne']

def outerLinear (a b c : ℝ) (i : Fin 3) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := ![((1-b)*p.1, b*(p.1+p.2)),
    ((1-c)*p.2, -c*p.1), (-(1-a)*(p.1+p.2), -a*p.2)] i
  map_add' p q := by
    fin_cases i <;> apply Prod.ext <;> dsimp <;> ring
  map_smul' r p := by
    fin_cases i <;> apply Prod.ext <;> dsimp <;> ring

def outerShift (a b : ℝ) (i : Fin 3) : ℝ × ℝ := ![(0,-b),(0,0),(1-a,0)] i

theorem outer_affine (a b c : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    outerLinear a b c i p + outerShift a b i =
      ((1-direction a b c (i+1))*coord i p, -direction a b c (i+1)*coord (i+2) p) := by
  fin_cases i <;> apply Prod.ext <;>
    simp [outerLinear, outerShift, direction, coord] <;> ring

theorem det_outerLinear (a b c : ℝ) (i : Fin 3) :
    LinearMap.det (outerLinear a b c i) =
      direction a b c (i+1)*(1-direction a b c (i+1)) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  fin_cases i <;>
    simp [LinearMap.toMatrix_apply, outerLinear, Module.Basis.finTwoProd, direction] <;> ring

theorem outer_value_identity (a b c : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    (1-direction a b c (i+1))*coord i p-direction a b c (i+1)*coord (i+2) p =
      value a b c (i+1) p-direction a b c (i+1) := by
  fin_cases i <;> dsimp [value, direction, coord] <;> ring

theorem volume_outerLow (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (i : Fin 3) :
    volume (outerLow a b c t i) = ENNReal.ofReal
      ((max 0 (t (i+1)-direction a b c (i+1)))^2 /
        (2*direction a b c (i+1)*(1-direction a b c (i+1)))) := by
  have hd := (direction_bounds ha hb hc (i+1)).1
  have hd' := sub_pos.mpr (direction_bounds ha hb hc (i+1)).2
  have he : outerLow a b c t i = outerLinear a b c i ⁻¹'
      ((fun p => p + outerShift a b i) ⁻¹'
        RowDeletion.triangle (t (i+1)-direction a b c (i+1))) := by
    ext p
    simp only [mem_preimage, outer_affine]
    change (0 ≤ coord i p ∧ coord (i+2) p ≤ 0 ∧ value a b c (i+1) p ≤ t (i+1)) ↔
      (0 ≤ (1-direction a b c (i+1))*coord i p ∧
       0 ≤ -direction a b c (i+1)*coord (i+2) p ∧
       (1-direction a b c (i+1))*coord i p + -direction a b c (i+1)*coord (i+2) p ≤
         t (i+1)-direction a b c (i+1))
    have hid := outer_value_identity a b c i p
    constructor
    · rintro ⟨h0,h1,h2⟩
      exact ⟨mul_nonneg hd'.le h0, by nlinarith only [hd,h1], by linarith only [hid,h2]⟩
    · rintro ⟨h0,h1,h2⟩
      exact ⟨nonneg_of_mul_nonneg_right h0 hd', by nlinarith only [hd,h1],
        by linarith only [hid,h2]⟩
  have hdet := mul_pos hd hd'
  rw [he, Measure.addHaar_preimage_linearMap volume
      (by rw [det_outerLinear]; exact hdet.ne'), det_outerLinear,
    measure_preimage_add_right, CyclicCenteredGeometry.volume_triangle_posPart,
    abs_of_pos (inv_pos.mpr hdet), ← ENNReal.ofReal_mul (inv_pos.mpr hdet).le]
  congr 1
  field_simp [hd.ne', hd'.ne']

theorem outerLow_subset_lowWedge (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : compatible a b c t) (i : Fin 3) :
    outerLow a b c t i ⊆ lowWedge a b c t i := by
  rintro p ⟨h0,h1,h2⟩
  have hid := compatibility_coordinate_identity a b c i p
  have hm := mul_le_mul_of_nonneg_left h2 (direction_bounds ha hb hc i).1.le
  have hn := mul_nonpos_of_nonneg_of_nonpos (weight_pos ha hb hc (i+2)).le h1
  have hj := ht i
  have hh : (1-direction a b c (i+1))*value a b c i p ≤
      (1-direction a b c (i+1))*t i := by nlinarith only [hid,hm,hn,hj]
  exact ⟨h0, le_of_mul_le_mul_left hh (sub_pos.mpr (direction_bounds ha hb hc (i+1)).2), h2⟩

theorem lowWedge_eq_union (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : compatible a b c t) (i : Fin 3) (hcapi : lowerCapSize a b c t i ≤ 0) :
    lowWedge a b c t i = rawLow a b c t i ∪ outerLow a b c t i := by
  ext p
  constructor
  · rintro ⟨h0,h1,h2⟩
    by_cases hk : 0 ≤ coord (i+2) p
    · left
      have hid := complementary_coordinate_identity a b c i p
      have hm := mul_le_mul_of_nonneg_left h2
        (sub_nonneg.mpr (direction_bounds ha hb hc i).2.le)
      have hj : 0 ≤ coord (i+1) p := by
        have hm' : 0 ≤ weight a b c (i+2)*coord (i+1) p := by
          dsimp [lowerCapSize] at hcapi
          nlinarith only [hid,hm,h1,hcapi]
        exact nonneg_of_mul_nonneg_right hm' (weight_pos ha hb hc (i+2))
      refine ⟨(mem_triangle_iff_coord p).mpr ?_,h1,h2⟩
      intro j
      fin_cases i <;> fin_cases j <;> first | exact h0 | exact hj | exact hk
    · exact Or.inr ⟨h0,le_of_lt (lt_of_not_ge hk),h2⟩
  · rintro (hp | hp)
    · exact ⟨(mem_triangle_iff_coord p).mp hp.1 i,hp.2⟩
    · exact outerLow_subset_lowWedge a b c t ha hb hc ht i hp

theorem measurableSet_outerLow (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) :
    MeasurableSet (outerLow a b c t i) := by
  exact (measurableSet_le measurable_const (continuous_coord i).measurable).inter
    ((measurableSet_le (continuous_coord (i+2)).measurable measurable_const).inter
      (measurableSet_le (continuous_value a b c (i+1)).measurable measurable_const))

theorem rawLow_outerLow_aedisjoint (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) :
    AEDisjoint volume (rawLow a b c t i) (outerLow a b c t i) := by
  apply measure_mono_null (s := rawLow a b c t i ∩ outerLow a b c t i)
    (t := {p | coord (i+2) p = 0}) _ (volume_coord_zero (i+2))
  intro p hp
  exact le_antisymm hp.2.2.1 ((mem_triangle_iff_coord p).mp hp.1.1 (i+2))

/-- Actual low-pair area, after subtracting the cap beyond the opposite vertex. -/
theorem volume_rawLow_toReal (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : compatible a b c t) (i : Fin 3) (hcapi : lowerCapSize a b c t i ≤ 0) :
    (volume (rawLow a b c t i)).toReal =
      (max 0 (-capSize a b c t i))^2 /
        (2*direction a b c (i+1)*weight a b c (i+2)) -
      (max 0 (t (i+1)-direction a b c (i+1)))^2 /
        (2*direction a b c (i+1)*(1-direction a b c (i+1))) := by
  have hd := (direction_bounds ha hb hc (i+1)).1
  have hd' := sub_pos.mpr (direction_bounds ha hb hc (i+1)).2
  have hw := weight_pos ha hb hc (i+2)
  have hf : volume (lowWedge a b c t i) ≠ ⊤ := by
    rw [volume_lowWedge a b c t ha hb hc i]
    exact ENNReal.ofReal_ne_top
  have hrawf : volume (rawLow a b c t i) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hf (measure_mono ?_)
    intro p hp
    exact ⟨(mem_triangle_iff_coord p).mp hp.1 i,hp.2⟩
  have houtf : volume (outerLow a b c t i) ≠ ⊤ := by
    rw [volume_outerLow a b c t ha hb hc i]
    exact ENNReal.ofReal_ne_top
  have he : volume (lowWedge a b c t i) =
      volume (rawLow a b c t i) + volume (outerLow a b c t i) := by
    rw [lowWedge_eq_union a b c t ha hb hc ht i hcapi,
      measure_union₀ (measurableSet_outerLow a b c t i).nullMeasurableSet
        (rawLow_outerLow_aedisjoint a b c t i)]
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add hrawf houtf, volume_lowWedge a b c t ha hb hc i,
    volume_outerLow a b c t ha hb hc i, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at hr
  linarith only [hr]

def pairReflection : Fin 3 → Fin 3 := ![0,2,1]

theorem rawHigh_eq_preimage (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) :
    rawHigh a b c t i = Proofs.Symmetry.swapMap ⁻¹'
      rawLow (1-b) (1-a) (1-c) (reflectedLevels t) (pairReflection i) := by
  ext p
  change (p ∈ stdTriangle.set ∧ t i ≤ value a b c i p ∧
    t (i+1) ≤ value a b c (i+1) p) ↔
    (Proofs.Symmetry.swapMap p ∈ stdTriangle.set ∧
      value (1-b) (1-a) (1-c) (pairReflection i) (Proofs.Symmetry.swapMap p) ≤
        reflectedLevels t (pairReflection i) ∧
      value (1-b) (1-a) (1-c) (pairReflection i+1) (Proofs.Symmetry.swapMap p) ≤
        reflectedLevels t (pairReflection i+1))
  have hT : p ∈ stdTriangle.set ↔ Proofs.Symmetry.swapMap p ∈ stdTriangle.set :=
    Proofs.Symmetry.swapMap_mem_iff p
  rw [← hT, value_reflect, value_reflect]
  fin_cases i <;> dsimp [pairReflection, reflectedLevels, reflectionIndex] <;>
    constructor <;> rintro ⟨hT,h0,h1⟩ <;> exact ⟨hT,by linarith,by linarith⟩

theorem reflected_lowerCapSize (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) :
    lowerCapSize (1-b) (1-a) (1-c) (reflectedLevels t) (pairReflection i) =
      capSize a b c t i := by
  fin_cases i <;>
    dsimp [lowerCapSize, capSize, reflectedLevels, reflectionIndex, pairReflection, direction] <;>
    ring

/-- The reflected raw high-pair formula includes its actual outer clipping. -/
theorem volume_rawHigh_toReal (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : compatible a b c t) (i : Fin 3) (hcapi : capSize a b c t i ≤ 0) :
    (volume (rawHigh a b c t i)).toReal =
      (max 0 (-lowerCapSize a b c t i))^2 /
        (2*(1-direction a b c i)*weight a b c (i+2)) -
      (max 0 (direction a b c i-t i))^2 /
        (2*direction a b c i*(1-direction a b c i)) := by
  have ha' : 0 < 1-b ∧ 1-b < 1 := by constructor <;> linarith [hb.1,hb.2]
  have hb' : 0 < 1-a ∧ 1-a < 1 := by constructor <;> linarith [ha.1,ha.2]
  have hc' : 0 < 1-c ∧ 1-c < 1 := by constructor <;> linarith [hc.1,hc.2]
  rw [rawHigh_eq_preimage, Proofs.Symmetry.volume_preimage_swapMap]
  rw [volume_rawLow_toReal (1-b) (1-a) (1-c) (reflectedLevels t) ha' hb' hc'
    (compatible_reflected ht) (pairReflection i) (by rw [reflected_lowerCapSize]; exact hcapi)]
  fin_cases i <;>
    dsimp [reflectedLevels, reflectionIndex, pairReflection, capSize, lowerCapSize,
      direction, weight, k0, k1, k2] <;> ring_nf

/-- Slack in the positive weighted relation satisfied by the three functionals. -/
def thresholdSlack (a b c : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  1+a*b*c-k0 b c*t 0-k1 a c*t 1-k2 a b*t 2

theorem capSize_weighted_identity (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) :
    weight a b c i*capSize a b c t i + weight a b c (i+2)*
      ((1-direction a b c (i+2))*t (i+1)-direction a b c (i+1)*t (i+2)+
        direction a b c (i+1)*direction a b c (i+2)) =
      direction a b c (i+1)*thresholdSlack a b c t := by
  fin_cases i <;> dsimp [weight, capSize, direction, thresholdSlack, k0, k1, k2] <;> ring

theorem lowerCapSize_weighted_identity (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) :
    weight a b c (i+1)*lowerCapSize a b c t i + weight a b c (i+2)*
      ((1-direction a b c i)*t (i+2)-direction a b c (i+2)*t i+
        direction a b c (i+2)*direction a b c i) =
      -(1-direction a b c i)*thresholdSlack a b c t := by
  fin_cases i <;>
    dsimp [weight, lowerCapSize, direction, thresholdSlack, k0, k1, k2] <;> ring

theorem capSize_nonpos_of_slack_nonpos (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : compatible a b c t) (hq : thresholdSlack a b c t ≤ 0) (i : Fin 3) :
    capSize a b c t i ≤ 0 := by
  have hj := ht (i+1)
  have hmod : i+1+1 = i+2 := by fin_cases i <;> rfl
  rw [hmod] at hj
  have hm := mul_nonneg (weight_pos ha hb hc (i+2)).le hj
  have hq' := mul_nonpos_of_nonneg_of_nonpos (direction_bounds ha hb hc (i+1)).1.le hq
  have hid := capSize_weighted_identity a b c t i
  apply le_of_mul_le_mul_left (a := weight a b c i) _ (weight_pos ha hb hc i)
  nlinarith only [hid,hm,hq']

theorem lowerCapSize_nonpos_of_slack_nonneg (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : compatible a b c t) (hq : 0 ≤ thresholdSlack a b c t) (i : Fin 3) :
    lowerCapSize a b c t i ≤ 0 := by
  have hj := ht (i+2)
  have hmod : i+2+1 = i := by fin_cases i <;> rfl
  rw [hmod] at hj
  have hm := mul_nonneg (weight_pos ha hb hc (i+2)).le hj
  have hq' := mul_nonneg (sub_nonneg.mpr (direction_bounds ha hb hc i).2.le) hq
  have hid := lowerCapSize_weighted_identity a b c t i
  apply le_of_mul_le_mul_left (a := weight a b c (i+1)) _ (weight_pos ha hb hc (i+1))
  nlinarith only [hid,hm,hq']

open CyclicBadThresholds in
/-- The Bad predicate separates the all-low and all-high threshold regions. -/
theorem thresholdSlack_separation_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hzbad : z ∈ CyclicArea.badSeeds C b a c) :
    0 < thresholdSlack (1-a) b c (lowerLevels C c) ∧
      thresholdSlack (1-a) b c (upperLevels C c) < 0 := by
  have hs := CyclicGeometry.level_separation_of_bad C hb ha hc hu₀ hu₁ hu₂ hzbad
  dsimp [thresholdSlack, lowerLevels, upperLevels, k0, k1, k2,
    CyclicGeometry.w0, CyclicGeometry.w1, CyclicGeometry.w2] at *
  constructor <;> nlinarith only [hs.1,hs.2]

open CyclicBadThresholds in
/-- All clipping hypotheses for both raw-pair formulas follow from a Bad seed. -/
theorem pair_conditions_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ CyclicArea.badSeeds C b a c) :
    compatible (1-a) b c (lowerLevels C c) ∧
      compatible (1-a) b c (upperLevels C c) ∧
      ∀ i, lowerCapSize (1-a) b c (lowerLevels C c) i ≤ 0 ∧
        capSize (1-a) b c (upperLevels C c) i ≤ 0 := by
  have hle : ∀ i, lowerLevels C c i ≤ upperLevels C c i := by
    intro i
    fin_cases i <;> dsimp [lowerLevels,upperLevels] <;>
      linarith [(C.plank 0).lo_le_hi,(C.plank 1).lo_le_hi,(C.plank 2).lo_le_hi]
  have hl := compatible_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad (lowerLevels C c)
    (fun i => ⟨le_rfl,hle i⟩)
  have hh := compatible_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad (upperLevels C c)
    (fun i => ⟨hle i,le_rfl⟩)
  have hs := thresholdSlack_separation_of_bad C hb ha hc hu₀ hu₁ hu₂ hzbad
  have ha' : 0 < 1-a ∧ 1-a < 1 := by constructor <;> linarith [ha.1,ha.2]
  exact ⟨hl,hh,fun i => ⟨lowerCapSize_nonpos_of_slack_nonneg (1-a) b c _
    ha' hb hc hl hs.1.le i,capSize_nonpos_of_slack_nonpos (1-a) b c _
    ha' hb hc hh hs.2.le i⟩⟩

end Quant.CyclicPairAreas
