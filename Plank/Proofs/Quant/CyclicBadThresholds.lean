module
/-
# Bad seeds force compatible cyclic threshold windows

This links the existing ABC obstruction to the exact exterior-cap formulas.
Both open Bad boxes are included. Every threshold vector between the actual
window endpoints is internal and compatible; no extra clipping hypothesis
is imposed on those difficult configurations.
-/
public import Plank.Proofs.Quant.CyclicThresholdCaps

@[expose] public section

noncomputable section

namespace Quant.CyclicBadThresholds

open Set CyclicArea CyclicGeometry OrdinalArea CyclicThresholdCaps

/-- Cyclic functionals are `1-ABC₁`, `ABC₀`, and `c-ABC₂`. -/
def lowerLevels (C : Config) (c : ℝ) : Fin 3 → ℝ :=
  ![1-(C.plank 1).hi, (C.plank 0).lo, c-(C.plank 2).hi]

def upperLevels (C : Config) (c : ℝ) : Fin 3 → ℝ :=
  ![1-(C.plank 1).lo, (C.plank 0).hi, c-(C.plank 2).lo]

theorem endpoint_compatible_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ badSeeds C b a c) :
    ∀ i, 0 < (1-direction (1-a) b c (i+1))*lowerLevels C c i -
      direction (1-a) b c i*upperLevels C c (i+1) +
      direction (1-a) b c i*direction (1-a) b c (i+1) := by
  let r := widths C
  let x := threshold C z 0
  let y := threshold C z 1
  let w := threshold C z 2
  let g0 := (1-b)*(1-(C.plank 1).hi)-(1-a)*(C.plank 0).hi+(1-a)*b
  let g1 := (1-c)*(C.plank 0).lo+b*(C.plank 2).lo
  let g2 := c*(C.plank 1).lo-a*(C.plank 2).hi
  have hr : ∀ i, 0 < r i := widths_pos_of_bad C hb ha hc hzbad
  have ha' : 0 < 1-a := sub_pos.mpr ha.2
  have hb' : 0 < 1-b := sub_pos.mpr hb.2
  have hc' : 0 < 1-c := sub_pos.mpr hc.2
  obtain ⟨hk1,hk0,hk2⟩ := CyclicGeometry.weights_pos hb ha hc
  change 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ C.deficit at hz
  have hn0 := mul_nonneg hk2.le (sub_nonneg.mpr hz.2.2)
  have hn1 := mul_nonneg hk0.le hz.1
  have hn2 := mul_nonneg hk1.le hz.2.1
  have hid0 : g0 = w2 a b*(C.deficit-(z.1+z.2)) + a*(1-b)*r 0 +
      b*(1-a)*r 1-(1-a)*x-(1-b)*y := by
    rw [CyclicArea.deficit_eq C hb ha hc hu₀ hu₁ hu₂]
    dsimp [g0,r,x,y,threshold,base,widths,w2]
    rw [hu₀,hu₁]
    dsimp [dot]
    ring
  have hid1 : g1 = w1 b c*z.1+(1-c)*x+b*w := by
    dsimp [g1,r,x,w,threshold,base,widths,w1]
    rw [hu₀,hu₂]
    dsimp [dot]
    ring
  have hid2 : g2 = w0 a c*z.2+c*y-a*w+c*(1-a)*r 2 := by
    dsimp [g2,r,y,w,threshold,base,widths,w0]
    rw [hu₁,hu₂]
    dsimp [dot]
    ring
  have hbad : CyclicAssignment.Bad (b*r 1) ((1-b)*r 2)
      (a*r 0) ((1-a)*r 2) (c*r 0) ((1-c)*r 1) x y w := hzbad
  have hg : 0 < g0 ∧ 0 < g1 ∧ 0 < g2 := by
    rcases hbad with ⟨hX,hY,hW⟩ | ⟨hX,hY,hW⟩
    · refine ⟨?_,?_,?_⟩
      · nlinarith only [hid0,hn0,
          mul_lt_mul_of_pos_left hX.2 ha', mul_lt_mul_of_pos_left hY.2 hb',
          mul_pos (mul_pos ha.1 hb') (hr 0)]
      · nlinarith only [hid1,hn1,
          mul_lt_mul_of_pos_left hX.1 hc', mul_lt_mul_of_pos_left hW.1 hb.1,
          mul_pos (mul_pos hc' hb') (hr 2)]
      · nlinarith only [hid2,hn2,
          mul_lt_mul_of_pos_left hY.1 hc.1, mul_lt_mul_of_pos_left hW.2 ha.1,
          mul_pos (mul_pos ha.1 hc') (hr 1)]
    · refine ⟨?_,?_,?_⟩
      · nlinarith only [hid0,hn0,
          mul_lt_mul_of_pos_left hX.2 ha', mul_lt_mul_of_pos_left hY.2 hb',
          mul_pos (mul_pos hb.1 ha') (hr 1)]
      · nlinarith only [hid1,hn1,
          mul_lt_mul_of_pos_left hX.1 hc', mul_lt_mul_of_pos_left hW.1 hb.1,
          mul_pos (mul_pos hb.1 hc.1) (hr 0)]
      · nlinarith only [hid2,hn2,
          mul_lt_mul_of_pos_left hY.1 hc.1, mul_lt_mul_of_pos_left hW.2 ha.1,
          mul_pos (mul_pos hc.1 ha') (hr 2)]
  intro i
  fin_cases i <;> dsimp [direction,lowerLevels,upperLevels,g0,g1,g2] at * <;>
    nlinarith only [hg.1,hg.2.1,hg.2.2]

/-- Every point of the whole closed window box satisfies cap compatibility. -/
theorem compatible_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ badSeeds C b a c)
    (t : Fin 3 → ℝ)
    (ht : ∀ i, lowerLevels C c i ≤ t i ∧ t i ≤ upperLevels C c i) :
    compatible (1-a) b c t := by
  have ha' : 0 < 1-a ∧ 1-a < 1 := by constructor <;> linarith [ha.1,ha.2]
  intro i
  have h := endpoint_compatible_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad i
  have hlo := mul_le_mul_of_nonneg_left (ht i).1
    (sub_nonneg.mpr (direction_bounds ha' hb hc (i+1)).2.le)
  have hhi := mul_le_mul_of_nonneg_left (ht (i+1)).2
    (direction_bounds ha' hb hc i).1.le
  nlinarith only [h,hlo,hhi]

theorem levels_internal_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ badSeeds C b a c) :
    ∀ i, 0 < lowerLevels C c i ∧ upperLevels C c i < 1 := by
  obtain ⟨h0,h1,h2⟩ := bad_seed_implies_internal C hb ha hc hu₀ hu₁ hu₂ hz hzbad
  intro i
  fin_cases i <;> dsimp [lowerLevels,upperLevels] <;> constructor <;>
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2]

/-- All hypotheses of both exact clipped-threshold formulas follow from the
existing bad-seed predicate and membership in the actual window box. -/
theorem cap_conditions_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ badSeeds C b a c)
    (t : Fin 3 → ℝ)
    (ht : ∀ i, lowerLevels C c i ≤ t i ∧ t i ≤ upperLevels C c i) :
    (∀ i, 0 < t i ∧ t i < 1) ∧ compatible (1-a) b c t := by
  refine ⟨?_,compatible_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad t ht⟩
  intro i
  obtain ⟨hl,hu⟩ := levels_internal_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad i
  exact ⟨hl.trans_le (ht i).1,(ht i).2.trans_lt hu⟩

/-- For an obstructed seed, the whole intersection of the three infinite
strips already lies in the body. Its measure has no outer clipping loss. -/
theorem window_intersection_subset_triangle_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ badSeeds C b a c) :
    {p : ℝ × ℝ | ∀ i, lowerLevels C c i ≤
      CyclicWeightedThresholdGeometry.value (1-a) b c i p ∧
      CyclicWeightedThresholdGeometry.value (1-a) b c i p ≤ upperLevels C c i}
        ⊆ stdTriangle.set := by
  intro p hp
  have h := compatible_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad
    (fun i => CyclicWeightedThresholdGeometry.value (1-a) b c i p) hp
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have ha' : 0 < 1-a ∧ 1-a < 1 := by constructor <;> linarith [ha.1,ha.2]
  obtain ⟨hk0,hk1,hk2⟩ := CyclicWeightedThresholdGeometry.weights_pos ha' hb hc
  have hx : 0 ≤ CyclicWeightedThresholdGeometry.k0 b c*p.1 := by
    dsimp [direction,CyclicWeightedThresholdGeometry.value] at h1
    dsimp [CyclicWeightedThresholdGeometry.k0]
    nlinarith only [h1]
  have hy : 0 ≤ CyclicWeightedThresholdGeometry.k1 (1-a) c*p.2 := by
    dsimp [direction,CyclicWeightedThresholdGeometry.value] at h2
    dsimp [CyclicWeightedThresholdGeometry.k1]
    nlinarith only [h2]
  have hz' : 0 ≤ CyclicWeightedThresholdGeometry.k2 (1-a) b*(1-p.1-p.2) := by
    dsimp [direction,CyclicWeightedThresholdGeometry.value] at h0
    dsimp [CyclicWeightedThresholdGeometry.k2]
    nlinarith only [h0]
  rw [Proofs.Quant.stdTriangle_set_eq]
  exact ⟨nonneg_of_mul_nonneg_right hx hk0,nonneg_of_mul_nonneg_right hy hk1,
    by linarith [nonneg_of_mul_nonneg_right hz' hk2]⟩

end Quant.CyclicBadThresholds
