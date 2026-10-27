module
/- The explicit linear remainder in the zero-cut-anchor Euler identity. -/
public import Plank.Proofs.Quant.CyclicMarginEuler
public import Plank.Proofs.Quant.CyclicAnchorAlgebra

@[expose] public section
noncomputable section

namespace Quant.CyclicAnchorRemainder

open CyclicGapCancellation CyclicVertexDescent CyclicThresholdCaps
  CyclicWeightedThresholdGeometry CyclicPairAreas CyclicAnchorAlgebra

def lowerVertex (a b c : ℝ) (l : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (direction a b c i-lowerAnchor a b c i)*max 0 (l i-direction a b c i)/
    (direction a b c i*(1-direction a b c i))

def upperVertex (a b c : ℝ) (h : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (upperAnchor a b c i-direction a b c i)*max 0 (direction a b c i-h i)/
    (direction a b c i*(1-direction a b c i))

def alphaTerm (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  alphaCost a b c i*max 0 (weight a b c i*windowWidth l h i-thresholdSlack a b c l)/
    (k0 b c*k1 a c*k2 a b)

def betaTerm (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  betaCost a b c i*max 0 (weight a b c i*windowWidth l h i+thresholdSlack a b c h)/
    (k0 b c*k1 a c*k2 a b)

def lowRefund (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (anchorWidth a b c (i+1)*max 0 (refundArgument a b c l h i 0)+
    direction a b c (i+1)*anchorWidth a b c i*max 0 (refundArgument a b c l h i 1))/
      (direction a b c (i+1)*weight a b c (i+2))

def highRefund (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (anchorWidth a b c i*max 0 (refundArgument a b c l h i 2)+
    (1-direction a b c i)*anchorWidth a b c (i+1)*max 0 (refundArgument a b c l h i 3))/
      ((1-direction a b c i)*weight a b c (i+2))

def remainder (a b c : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  (∑ i, (lowerVertex a b c l i+upperVertex a b c h i))+
    (∑ i, (alphaTerm a b c l h i+betaTerm a b c l h i))-
    (∑ i, lowRefund a b c l h i)-(∑ i, highRefund a b c l h i)

theorem lowerVertex_nonneg {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (l : Fin 3 → ℝ) (i : Fin 3) :
    0 ≤ lowerVertex a b c l i := by
  have hd := direction_bounds ha hb hc i
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr (anchor_bounds ha hb hc i).2.1.le)
    (le_max_left 0 _)) (mul_pos hd.1 (sub_pos.mpr hd.2)).le

theorem upperVertex_nonneg {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (h : Fin 3 → ℝ) (i : Fin 3) :
    0 ≤ upperVertex a b c h i := by
  have hd := direction_bounds ha hb hc i
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr (anchor_bounds ha hb hc i).2.2.1.le)
    (le_max_left 0 _)) (mul_pos hd.1 (sub_pos.mpr hd.2)).le

theorem anchorTerms_eq_remainder {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (l h : Fin 3 → ℝ) :
    CyclicMarginEuler.anchorTerms a b c l h (lowerAnchor a b c) (upperAnchor a b c) =
      remainder a b c l h := by
  have hp := (SixTriangleAlgebra.p_pos ha.1 hb.1 hc.1).ne'
  have hq := (SixTriangleAlgebra.q_pos ha.2 hb.2 hc.2).ne'
  simp only [CyclicMarginEuler.anchorTerms,remainder,
    ← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  norm_num [CyclicMarginEuler.argument,CyclicMarginEuler.coefficient,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three]
  simp only [lowPairSlack_lowerAnchor hp,highPairSlack_upperAnchor hq,
    alphaArgument_anchor hp hq,betaArgument_anchor hp hq,refundArgument_anchor hp hq,
    zero_mul,mul_zero,zero_add]
  norm_num [lowerVertex,upperVertex,alphaTerm,betaTerm,lowRefund,highRefund,
    Matrix.cons_val_two,Matrix.cons_val_three]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- At any ambient local minimum, the margin equals the linear remainder plus
the nonnegative direction-imbalance contribution when the deficit is nonnegative. -/
theorem localMin_margin_eq {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (l h : Fin 3 → ℝ)
    (hmin : IsLocalMin (CyclicDescentSymmetry.jointMargin a b c) (l,h)) :
    margin a b c l h = remainder a b c l h+
      SixTriangleResidual.deficit l h*SixTriangleAlgebra.imbalance a b c := by
  have he := CyclicMarginEuler.localMin_anchor_identity a b c l h
    (lowerAnchor a b c) (upperAnchor a b c) hmin
  rw [anchorTerms_eq_remainder ha hb hc,deficit_anchor
    (SixTriangleAlgebra.p_pos ha.1 hb.1 hc.1).ne'
    (SixTriangleAlgebra.q_pos ha.2 hb.2 hc.2).ne',mul_neg,sub_neg_eq_add] at he
  exact he

end Quant.CyclicAnchorRemainder
