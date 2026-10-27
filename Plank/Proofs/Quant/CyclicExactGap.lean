module
/-
# The actual uncovered area as an explicit scalar expression

The pair areas, clipped threshold areas and eight-cell partition combine
without a geometric error term. Every hypothesis follows from an obstructed
deficit seed in the existing ABC chart. The sharp scalar lower bound on this
expression remains a separate problem.
-/
public import Plank.Proofs.Quant.CyclicPairAreas
public import Plank.Proofs.Quant.CyclicExteriorAssembly

@[expose] public section

noncomputable section

namespace Quant.CyclicExactGap

open Set MeasureTheory CyclicWeightedThresholdGeometry CyclicThresholdCaps
  CyclicPairAreas CyclicBadThresholds

def lowPairArea (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (max 0 (-capSize a b c t i))^2 /
    (2*direction a b c (i+1)*weight a b c (i+2)) -
  (max 0 (t (i+1)-direction a b c (i+1)))^2 /
    (2*direction a b c (i+1)*(1-direction a b c (i+1)))

def highPairArea (a b c : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (max 0 (-lowerCapSize a b c t i))^2 /
    (2*(1-direction a b c i)*weight a b c (i+2)) -
  (max 0 (direction a b c i-t i))^2 /
    (2*direction a b c i*(1-direction a b c i))

def lowerThresholdArea (a b c : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  (max 0 (k0 b c*t 0+k1 a c*t 1+k2 a b*t 2-(1+a*b*c)))^2 /
    (2*k0 b c*k1 a c*k2 a b) -
  ∑ i, (max 0 (lowerCapSize a b c t i))^2 /
    (2*(1-direction a b c i)*weight a b c (i+2))

def upperThresholdArea (a b c : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  (max 0 (1+a*b*c-k0 b c*t 0-k1 a c*t 1-k2 a b*t 2))^2 /
    (2*k0 b c*k1 a c*k2 a b) -
  ∑ i, (max 0 (capSize a b c t i))^2 /
    (2*direction a b c (i+1)*weight a b c (i+2))

/-- An explicit finite sum of positive-part squares, with all clipping refunded. -/
def gapExpression (a b c : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  (∑ i, lowPairArea a b c l i) + (∑ i, highPairArea a b c h i) -
  (∑ i, lowerThresholdArea a b c (CyclicExteriorAssembly.lowerCorrectionLevels l h i)) -
  (∑ i, upperThresholdArea a b c (CyclicExteriorAssembly.upperCorrectionLevels l h i))

theorem lowerCell_eq_empty_of_slack_pos (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hq : 0 < thresholdSlack a b c t) : lowerCell a b c t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨_,hp⟩
  obtain ⟨h0,h1,h2⟩ := weights_pos ha hb hc
  have hh0 := mul_le_mul_of_nonneg_left (hp 0) h0.le
  have hh1 := mul_le_mul_of_nonneg_left (hp 1) h1.le
  have hh2 := mul_le_mul_of_nonneg_left (hp 2) h2.le
  have hs := weighted_value_sum a b c p
  dsimp [thresholdSlack] at hq
  linarith only [hs,hh0,hh1,hh2,hq]

theorem upperCell_eq_empty_of_slack_neg (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hq : thresholdSlack a b c t < 0) : upperCell a b c t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨_,hp⟩
  obtain ⟨h0,h1,h2⟩ := weights_pos ha hb hc
  have hh0 := mul_le_mul_of_nonneg_left (hp 0) h0.le
  have hh1 := mul_le_mul_of_nonneg_left (hp 1) h1.le
  have hh2 := mul_le_mul_of_nonneg_left (hp 2) h2.le
  have hs := weighted_value_sum a b c p
  dsimp [thresholdSlack] at hq
  linarith only [hs,hh0,hh1,hh2,hq]

theorem lowerCorrectionLevels_between (l h : Fin 3 → ℝ)
    (hlh : ∀ i, l i ≤ h i) (i j : Fin 3) :
    l j ≤ CyclicExteriorAssembly.lowerCorrectionLevels l h i j ∧
      CyclicExteriorAssembly.lowerCorrectionLevels l h i j ≤ h j := by
  dsimp [CyclicExteriorAssembly.lowerCorrectionLevels]
  split_ifs <;> exact ⟨by first | exact hlh j | exact le_rfl,
    by first | exact hlh j | exact le_rfl⟩

theorem upperCorrectionLevels_between (l h : Fin 3 → ℝ)
    (hlh : ∀ i, l i ≤ h i) (i j : Fin 3) :
    l j ≤ CyclicExteriorAssembly.upperCorrectionLevels l h i j ∧
      CyclicExteriorAssembly.upperCorrectionLevels l h i j ≤ h j := by
  dsimp [CyclicExteriorAssembly.upperCorrectionLevels]
  split_ifs <;> exact ⟨by first | exact hlh j | exact le_rfl,
    by first | exact hlh j | exact le_rfl⟩

/-- The exact scalar expression for any compatible window with separated pure cells. -/
theorem uncovered_area_eq_expression (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i < h i) (hlo : ∀ i, 0 ≤ l i) (hhi : ∀ i, h i ≤ 1)
    (hwindow : ∀ t : Fin 3 → ℝ, (∀ i, l i ≤ t i ∧ t i ≤ h i) → compatible a b c t)
    (hql : 0 < thresholdSlack a b c l) (hqh : thresholdSlack a b c h < 0) :
    (volume (CyclicExteriorAssembly.uncovered a b c l h)).toReal = gapExpression a b c l h := by
  have hl := hwindow l (fun i => ⟨le_rfl,(hlh i).le⟩)
  have hh := hwindow h (fun i => ⟨(hlh i).le,le_rfl⟩)
  have hrawlo (i : Fin 3) :
      (volume (CyclicExteriorAssembly.rawLow a b c l i)).toReal = lowPairArea a b c l i :=
    volume_rawLow_toReal a b c l ha hb hc hl i
      (lowerCapSize_nonpos_of_slack_nonneg a b c l ha hb hc hl hql.le i)
  have hrawhi (i : Fin 3) :
      (volume (CyclicExteriorAssembly.rawHigh a b c h i)).toReal = highPairArea a b c h i :=
    volume_rawHigh_toReal a b c h ha hb hc hh i
      (capSize_nonpos_of_slack_nonpos a b c h ha hb hc hh hqh.le i)
  have hcorlo (i : Fin 3) : (volume (lowerCell a b c
      (CyclicExteriorAssembly.lowerCorrectionLevels l h i))).toReal =
      lowerThresholdArea a b c (CyclicExteriorAssembly.lowerCorrectionLevels l h i) := by
    have ht := lowerCorrectionLevels_between l h (fun j => (hlh j).le) i
    exact volume_lowerCell_toReal a b c _ ha hb hc (fun j => (ht j).2.trans (hhi j))
      (hwindow _ ht)
  have hcorhi (i : Fin 3) : (volume (upperCell a b c
      (CyclicExteriorAssembly.upperCorrectionLevels l h i))).toReal =
      upperThresholdArea a b c (CyclicExteriorAssembly.upperCorrectionLevels l h i) := by
    have ht := upperCorrectionLevels_between l h (fun j => (hlh j).le) i
    exact volume_upperCell_toReal a b c _ ha hb hc (fun j => (hlo j).trans (ht j).1)
      (hwindow _ ht)
  rw [CyclicExteriorAssembly.uncovered_area_eq a b c l h hlh,
    lowerCell_eq_empty_of_slack_pos a b c l ha hb hc hql,
    upperCell_eq_empty_of_slack_neg a b c h ha hb hc hqh]
  simp_rw [hrawlo,hrawhi,hcorlo,hcorhi]
  simp only [measure_empty,ENNReal.toReal_zero,add_zero]
  rfl

/-- The exact area of the original ABC configuration in the obstructed case.
No clipping or area-assembly premise remains for the scalar lower-bound task. -/
theorem gapArea_eq_expression_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ CyclicArea.badSeeds C b a c) :
    C.gapArea = gapExpression (1-a) b c (lowerLevels C c) (upperLevels C c) := by
  have ha' : 0 < 1-a ∧ 1-a < 1 := by constructor <;> linarith [ha.1,ha.2]
  have hr := CyclicGeometry.widths_pos_of_bad C hb ha hc hzbad
  have hwidth : ∀ i, (C.plank i).lo < (C.plank i).hi := by
    intro i
    exact sub_pos.mp (hr i)
  have hi := levels_internal_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad
  have hs := thresholdSlack_separation_of_bad C hb ha hc hu₀ hu₁ hu₂ hzbad
  rw [Config.gapArea,CyclicExteriorAssembly.configuration_uncovered C hu₀ hu₁ hu₂]
  exact uncovered_area_eq_expression (1-a) b c _ _ ha' hb hc
    (CyclicExteriorAssembly.lowerLevels_lt_upperLevels C c hwidth)
    (fun i => (hi i).1.le) (fun i => (hi i).2.le)
    (compatible_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad) hs.1 hs.2

end Quant.CyclicExactGap
