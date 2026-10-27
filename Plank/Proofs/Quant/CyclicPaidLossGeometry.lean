module
/- Refund hinges force strict threshold losses; coherent Bad boxes exclude one refund pair. -/
public import Plank.Proofs.Quant.CyclicVertexDescent

@[expose] public section
noncomputable section

namespace Quant.CyclicPaidLossGeometry

open CyclicVertexDescent CyclicWeightedThresholdGeometry CyclicThresholdCaps
  CyclicGapCancellation CyclicPairAreas CyclicExteriorAssembly CyclicExactGap
  CyclicBadThresholds

theorem refundArgument_zero_eq_cap (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    refundArgument a b c l h i 0 = capSize a b c (upperCorrectionLevels l h (i+1)) i := by
  fin_cases i <;> dsimp [refundArgument,lowPairSlack,capSize,windowWidth,
    upperCorrectionLevels,direction] <;> ring

theorem refundArgument_one_eq_cap (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    refundArgument a b c l h i 1 = capSize a b c (upperCorrectionLevels l h (i+2)) i := by
  fin_cases i <;> dsimp [refundArgument,lowPairSlack,capSize,windowWidth,
    upperCorrectionLevels,direction] <;> ring

theorem refundArgument_two_eq_lowerCap (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    refundArgument a b c l h i 2 = lowerCapSize a b c (lowerCorrectionLevels l h (i+2)) i := by
  fin_cases i <;> dsimp [refundArgument,highPairSlack,lowerCapSize,windowWidth,
    lowerCorrectionLevels,direction] <;> ring

theorem refundArgument_three_eq_lowerCap (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    refundArgument a b c l h i 3 = lowerCapSize a b c (lowerCorrectionLevels l h (i+1)) i := by
  fin_cases i <;> dsimp [refundArgument,highPairSlack,lowerCapSize,windowWidth,
    lowerCorrectionLevels,direction] <;> ring

theorem thresholdSlack_pos_of_cap_nonneg {a b c : ℝ} (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : strictCompatible a b c t) (i : Fin 3) (hcap : 0 ≤ capSize a b c t i) :
    0 < thresholdSlack a b c t := by
  by_contra hn
  exact (not_le_of_gt (capSize_neg_of_strictCompatible a b c t ha hb hc ht
    (le_of_not_gt hn) i)) hcap

theorem thresholdSlack_neg_of_lowerCap_nonneg {a b c : ℝ} (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : strictCompatible a b c t) (i : Fin 3) (hcap : 0 ≤ lowerCapSize a b c t i) :
    thresholdSlack a b c t < 0 := by
  by_contra hn
  exact (not_le_of_gt (lowerCapSize_neg_of_strictCompatible a b c t ha hb hc ht
    (le_of_not_gt hn) i)) hcap

/-- Refund slots are `(b1,b2,c1,c2)`. Each nonnegative refund, including a
zero hinge, forces the indicated threshold-loss argument to be strictly positive. -/
theorem refund_forces_strict_losses (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hwindow : ∀ t : Fin 3 → ℝ, (∀ i, l i ≤ t i ∧ t i ≤ h i) →
      strictCompatible a b c t) (i : Fin 3) :
    (0 ≤ refundArgument a b c l h i 0 →
      0 < weight a b c i*windowWidth l h i+thresholdSlack a b c h) ∧
    (0 ≤ refundArgument a b c l h i 1 →
      0 < weight a b c (i+1)*windowWidth l h (i+1)+thresholdSlack a b c h) ∧
    (0 ≤ refundArgument a b c l h i 2 →
      0 < weight a b c (i+1)*windowWidth l h (i+1)-thresholdSlack a b c l) ∧
    (0 ≤ refundArgument a b c l h i 3 →
      0 < weight a b c i*windowWidth l h i-thresholdSlack a b c l) := by
  have hmod0 : i+1+2 = i := by fin_cases i <;> rfl
  have hmod1 : i+2+2 = i+1 := by fin_cases i <;> rfl
  have hupper (j : Fin 3) : strictCompatible a b c (upperCorrectionLevels l h j) :=
    hwindow _ (upperCorrectionLevels_between l h hlh j)
  have hlower (j : Fin 3) : strictCompatible a b c (lowerCorrectionLevels l h j) :=
    hwindow _ (lowerCorrectionLevels_between l h hlh j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hr
    rw [refundArgument_zero_eq_cap] at hr
    have hs := thresholdSlack_pos_of_cap_nonneg _ ha hb hc (hupper (i+1)) i hr
    rw [thresholdSlack_upperCorrection, hmod0] at hs
    linarith only [hs]
  · intro hr
    rw [refundArgument_one_eq_cap] at hr
    have hs := thresholdSlack_pos_of_cap_nonneg _ ha hb hc (hupper (i+2)) i hr
    rw [thresholdSlack_upperCorrection, hmod1] at hs
    linarith only [hs]
  · intro hr
    rw [refundArgument_two_eq_lowerCap] at hr
    have hs := thresholdSlack_neg_of_lowerCap_nonneg _ ha hb hc (hlower (i+2)) i hr
    rw [thresholdSlack_lowerCorrection, hmod1] at hs
    linarith only [hs]
  · intro hr
    rw [refundArgument_three_eq_lowerCap] at hr
    have hs := thresholdSlack_neg_of_lowerCap_nonneg _ ha hb hc (hlower (i+1)) i hr
    rw [thresholdSlack_lowerCorrection, hmod0] at hs
    linarith only [hs]

theorem refund_forces_strict_losses_of_endpoint_bounds (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) :
    (0 ≤ refundArgument a b c l h i 0 →
      0 < weight a b c i*windowWidth l h i+thresholdSlack a b c h) ∧
    (0 ≤ refundArgument a b c l h i 1 →
      0 < weight a b c (i+1)*windowWidth l h (i+1)+thresholdSlack a b c h) ∧
    (0 ≤ refundArgument a b c l h i 2 →
      0 < weight a b c (i+1)*windowWidth l h (i+1)-thresholdSlack a b c l) ∧
    (0 ≤ refundArgument a b c l h i 3 →
      0 < weight a b c i*windowWidth l h i-thresholdSlack a b c l) :=
  refund_forces_strict_losses a b c l h ha hb hc hlh
    (fun t ht => strictCompatible_of_endpoint_bounds a b c l h t ha hb hc hend ht) i

theorem thresholdSlack_sub_eq_sum_widths (a b c : ℝ) (l h : Fin 3 → ℝ) :
    thresholdSlack a b c l-thresholdSlack a b c h =
      ∑ i, weight a b c i*windowWidth l h i := by
  simp only [Fin.sum_univ_three]
  dsimp [thresholdSlack,weight,windowWidth]
  ring

/-- Two strict excesses over complementary budgets cannot use distinct entries
of a finite nonnegative family. -/
theorem same_index_of_strict_excesses {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (α β : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : α+β = ∑ i, w i) (i j : κ) (hi : α < w i) (hj : β < w j) : i = j := by
  classical
  by_contra hne
  have hp : w i+w j ≤ ∑ k, w k := by
    have hsub : ({i,j} : Finset κ) ⊆ Finset.univ := Finset.subset_univ _
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hw k)
    simpa only [Finset.sum_pair hne] using hh
  linarith only [hsum, hi, hj, hp]

theorem active_threshold_losses_same_index (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i) (i j : Fin 3)
    (hi : 0 < weight a b c i*windowWidth l h i-thresholdSlack a b c l)
    (hj : 0 < weight a b c j*windowWidth l h j+thresholdSlack a b c h) : i = j := by
  apply same_index_of_strict_excesses (fun k => weight a b c k*windowWidth l h k)
    (thresholdSlack a b c l) (-thresholdSlack a b c h)
    (fun k => mul_nonneg (weight_pos ha hb hc k).le (sub_nonneg.mpr (hlh k)))
    (by simpa only [sub_eq_add_neg] using thresholdSlack_sub_eq_sum_widths a b c l h)
    i j <;> linarith only [hi, hj]

/-- Exact refund coordinates in the original ABC seed chart. The ABC direction
parameter `a` corresponds to cyclic direction `1-a`, and original widths are
ordered `(r₀,r₁,r₂)`, whereas cyclic window widths are `(r₁,r₀,r₂)`. -/
theorem refundArgument_seed_coordinates (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) (z : ℝ × ℝ) :
    let r := OrdinalArea.widths C
    let x := CyclicArea.threshold C z 0
    let y := CyclicArea.threshold C z 1
    let w := CyclicArea.threshold C z 2
    let s := z.1
    let t := z.2
    let u := C.deficit-z.1-z.2
    let k₀ := CyclicGeometry.w1 b c
    let k₁ := CyclicGeometry.w0 a c
    let k₂ := CyclicGeometry.w2 a b
    refundArgument (1-a) b c (lowerLevels C c) (upperLevels C c) =
      ![![b*y-x-k₂*s+b*r 1-r 0,
           b*y-x-k₂*s,
           a*x-y-k₂*(t+r 2)-r 1+a*r 0,
           a*x-y-k₂*(t+r 2)],
        ![w-c*x-k₀*(t+r 2),
           w-c*x-k₀*t+c*(1-b)*r 2-c*r 0,
           x-(1-b)*w-k₀*(u+r 0+r 1),
           x-(1-b)*w-k₀*(u+r 0+r 1)+r 0-(1-b)*r 2],
        ![y+(1-a)*w-k₁*(u+r 0+r 1)+(1-a)*r 2,
           y+(1-a)*w-k₁*u-k₁*r 0+(1-k₁)*r 1,
           -w-(1-c)*y-k₁*s-r 2,
           -w-(1-c)*y-k₁*s-(1-c)*r 1]] := by
  simp only
  rw [CyclicArea.deficit_eq C hb ha hc hu₀ hu₁ hu₂]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [refundArgument,lowPairSlack,highPairSlack,capSize,lowerCapSize,windowWidth,
      lowerLevels,upperLevels,direction,CyclicArea.threshold,CyclicArea.base,
      OrdinalArea.widths,CyclicGeometry.w0,CyclicGeometry.w1,CyclicGeometry.w2] <;>
    norm_num [hu₀,hu₁,hu₂,dot,Fin.add_def,
      Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

/-- Actual Bad seed geometry excludes an entire coherent pair of refund
families. The LEFT disjunct of `CyclicAssignment.Bad` gives slots `(1,2)`;
the RIGHT disjunct gives slots `(0,3)`. -/
theorem coherent_refund_exclusions_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ CyclicArea.badSeeds C b a c) :
    (∀ i, refundArgument (1-a) b c (lowerLevels C c) (upperLevels C c) i 0 < 0 ∧
      refundArgument (1-a) b c (lowerLevels C c) (upperLevels C c) i 3 < 0) ∨
    (∀ i, refundArgument (1-a) b c (lowerLevels C c) (upperLevels C c) i 1 < 0 ∧
      refundArgument (1-a) b c (lowerLevels C c) (upperLevels C c) i 2 < 0) := by
  let r := OrdinalArea.widths C
  let x := CyclicArea.threshold C z 0
  let y := CyclicArea.threshold C z 1
  let w := CyclicArea.threshold C z 2
  let s := z.1
  let t := z.2
  let u := C.deficit-z.1-z.2
  let k₀ := CyclicGeometry.w1 b c
  let k₁ := CyclicGeometry.w0 a c
  let k₂ := CyclicGeometry.w2 a b
  have hr : ∀ i, 0 < r i := CyclicGeometry.widths_pos_of_bad C hb ha hc hzbad
  have ha' : 0 < 1-a := sub_pos.mpr ha.2
  have hb' : 0 < 1-b := sub_pos.mpr hb.2
  have hc' : 0 < 1-c := sub_pos.mpr hc.2
  obtain ⟨hk₁,hk₀,hk₂⟩ := CyclicGeometry.weights_pos hb ha hc
  change 0 ≤ s ∧ 0 ≤ t ∧ z.1+z.2 ≤ C.deficit at hz
  have hu : 0 ≤ u := by simp only [u]; linarith only [hz.2.2]
  have h₂s : 0 ≤ k₂*s := mul_nonneg hk₂.le hz.1
  have h₂t : 0 ≤ k₂*t := mul_nonneg hk₂.le hz.2.1
  have h₀t : 0 ≤ k₀*t := mul_nonneg hk₀.le hz.2.1
  have h₀u : 0 ≤ k₀*u := mul_nonneg hk₀.le hu
  have h₁s : 0 ≤ k₁*s := mul_nonneg hk₁.le hz.1
  have h₁u : 0 ≤ k₁*u := mul_nonneg hk₁.le hu
  have he := refundArgument_seed_coordinates C hb ha hc hu₀ hu₁ hu₂ z
  have hbad : CyclicAssignment.Bad (b*r 1) ((1-b)*r 2)
      (a*r 0) ((1-a)*r 2) (c*r 0) ((1-c)*r 1) x y w := hzbad
  rcases hbad with ⟨hX,hY,hW⟩ | ⟨hX,hY,hW⟩
  · right
    intro i
    rw [he]
    fin_cases i
    · change b*y-x-k₂*s < 0 ∧ a*x-y-k₂*(t+r 2)-r 1+a*r 0 < 0
      constructor
      · have hxpos := (mul_pos hb' (hr 2)).trans hX.1
        have hby := mul_neg_of_pos_of_neg hb.1 hY.2
        nlinarith only [hxpos,hby,h₂s]
      · have hax := mul_lt_mul_of_pos_left hX.2 ha.1
        have hkr := mul_nonneg hk₂.le (hr 1).le
        have har := mul_nonneg (mul_nonneg ha.1.le hb'.le) (hr 2).le
        simp only [k₂,CyclicGeometry.w2] at h₂t hkr ⊢
        nlinarith only [hax,hY.1,h₂t,hkr,har]
    · change w-c*x-k₀*t+c*(1-b)*r 2-c*r 0 < 0 ∧
        x-(1-b)*w-k₀*(u+r 0+r 1) < 0
      constructor
      · have hcx := mul_lt_mul_of_pos_left hX.1 hc.1
        have hcr := mul_nonneg hc'.le (hr 1).le
        nlinarith only [hcx,hW.2,hcr,h₀t]
      · have hbw := mul_pos hb' hW.1
        have hkge : b ≤ k₀ := by
          simp only [k₀,CyclicGeometry.w1]
          nlinarith only [mul_nonneg hb'.le hc'.le]
        have hkr := mul_le_mul_of_nonneg_right hkge (hr 1).le
        have hkr0 := mul_nonneg hk₀.le (hr 0).le
        nlinarith only [hX.2,hbw,hkr,hkr0,h₀u]
    · change y+(1-a)*w-k₁*u-k₁*r 0+(1-k₁)*r 1 < 0 ∧
        -w-(1-c)*y-k₁*s-r 2 < 0
      constructor
      · have haw := mul_lt_mul_of_pos_left hW.2 ha'
        have har := mul_nonneg ha.1.le (hr 0).le
        simp only [k₁,CyclicGeometry.w0] at h₁u ⊢
        nlinarith only [hY.2,haw,har,h₁u]
      · have hcy := mul_lt_mul_of_pos_left hY.1 hc'
        have hkr := mul_nonneg hk₁.le (hr 2).le
        have har := mul_nonneg (mul_nonneg ha.1.le hc'.le) (hr 0).le
        simp only [k₁,CyclicGeometry.w0] at h₁s hkr ⊢
        nlinarith only [hW.1,hcy,hkr,har,h₁s]
  · left
    intro i
    rw [he]
    fin_cases i
    · change b*y-x-k₂*s+b*r 1-r 0 < 0 ∧ a*x-y-k₂*(t+r 2) < 0
      constructor
      · have hby := mul_lt_mul_of_pos_left hY.2 hb.1
        have hkr := mul_nonneg hk₂.le (hr 0).le
        have hbr := mul_nonneg (mul_nonneg hb.1.le ha'.le) (hr 2).le
        simp only [k₂,CyclicGeometry.w2] at h₂s hkr ⊢
        nlinarith only [hX.1,hby,hkr,hbr,h₂s]
      · have hax := mul_lt_mul_of_pos_left hX.2 ha.1
        have har := mul_nonneg ha'.le (hr 2).le
        simp only [k₂,CyclicGeometry.w2] at h₂t ⊢
        nlinarith only [hax,hY.1,har,h₂t]
    · change w-c*x-k₀*(t+r 2) < 0 ∧
        x-(1-b)*w-k₀*(u+r 0+r 1)+r 0-(1-b)*r 2 < 0
      constructor
      · have hxpos := (mul_pos hb.1 (hr 1)).trans hX.1
        have hcx := mul_pos hc.1 hxpos
        have hkr := mul_nonneg hk₀.le (hr 2).le
        nlinarith only [hW.2,hcx,h₀t,hkr]
      · have hbw := mul_lt_mul_of_pos_left hW.1 hb'
        have hbr := mul_nonneg hb.1.le (hr 1).le
        simp only [k₀,CyclicGeometry.w1] at h₀u ⊢
        nlinarith only [hX.2,hbw,hbr,h₀u]
    · change y+(1-a)*w-k₁*(u+r 0+r 1)+(1-a)*r 2 < 0 ∧
        -w-(1-c)*y-k₁*s-(1-c)*r 1 < 0
      constructor
      · have haw := mul_neg_of_pos_of_neg ha' hW.2
        have hkge : a ≤ k₁ := by
          simp only [k₁,CyclicGeometry.w0]
          nlinarith only [mul_nonneg ha'.le hc.1.le]
        have hkr := mul_le_mul_of_nonneg_right hkge (hr 0).le
        have hkr1 := mul_nonneg hk₁.le (hr 1).le
        nlinarith only [hY.2,haw,hkr,hkr1,h₁u]
      · have hcy := mul_pos hc' hY.1
        have hcr := mul_nonneg hc.1.le (hr 0).le
        nlinarith only [hW.1,hcy,hcr,h₁s]

end Quant.CyclicPaidLossGeometry
