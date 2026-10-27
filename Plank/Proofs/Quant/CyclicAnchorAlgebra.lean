module
/- Exact zero-cut anchor and scalar compensation coefficients. This module
does not assert a local-minimum theorem or a sharp geometric area bound. -/
public import Plank.Proofs.Quant.CyclicVertexDescent

@[expose] public section
noncomputable section

namespace Quant.CyclicAnchorAlgebra

open CyclicThresholdCaps CyclicWeightedThresholdGeometry CyclicPairAreas
  CyclicGapCancellation CyclicVertexDescent

def lowerAnchor (a b c : ℝ) (i : Fin 3) : ℝ :=
  direction a b c i*weight a b c i/SixTriangleAlgebra.p a b c

def upperAnchor (a b c : ℝ) (i : Fin 3) : ℝ :=
  weight a b c (i+2)/SixTriangleAlgebra.q a b c

def anchorWidth (a b c : ℝ) (i : Fin 3) : ℝ :=
  upperAnchor a b c i-lowerAnchor a b c i

def alphaCost (a b c : ℝ) (i : Fin 3) : ℝ :=
  weight a b c i*(1-direction a b c i)*anchorWidth a b c (i+1)

def betaCost (a b c : ℝ) (i : Fin 3) : ℝ :=
  weight a b c i*direction a b c i*anchorWidth a b c (i+2)

theorem lowCut_lowerAnchor {a b c : ℝ} (hp : SixTriangleAlgebra.p a b c ≠ 0)
    (i : Fin 3) : SixTriangleAlgebra.lowCut a b c (lowerAnchor a b c) i = 0 := by
  fin_cases i <;>
    norm_num [SixTriangleAlgebra.lowCut,lowerAnchor,direction,weight,Fin.add_def] <;>
    field_simp [hp] <;> dsimp [k0,k1,k2,SixTriangleAlgebra.p] <;> ring

theorem highCut_upperAnchor {a b c : ℝ} (hq : SixTriangleAlgebra.q a b c ≠ 0)
    (i : Fin 3) : SixTriangleAlgebra.highCut a b c (upperAnchor a b c) i = 0 := by
  fin_cases i <;>
    norm_num [SixTriangleAlgebra.highCut,upperAnchor,direction,weight,Fin.add_def] <;>
    field_simp [hq] <;> dsimp [k0,k1,k2,SixTriangleAlgebra.q] <;> ring

theorem lowPairSlack_lowerAnchor {a b c : ℝ} (hp : SixTriangleAlgebra.p a b c ≠ 0)
    (i : Fin 3) : lowPairSlack a b c (lowerAnchor a b c) i = 0 := by
  have he := lowCut_lowerAnchor hp i
  fin_cases i <;> dsimp [lowPairSlack,capSize,direction,SixTriangleAlgebra.lowCut] at * <;>
    linarith only [he]

theorem highPairSlack_upperAnchor {a b c : ℝ} (hq : SixTriangleAlgebra.q a b c ≠ 0)
    (i : Fin 3) : highPairSlack a b c (upperAnchor a b c) i = 0 := by
  have he := highCut_upperAnchor hq i
  fin_cases i <;> dsimp [highPairSlack,lowerCapSize,direction,SixTriangleAlgebra.highCut] at * <;>
    linarith only [he]

theorem lower_middle_margin {a b c : ℝ} (hp : SixTriangleAlgebra.p a b c ≠ 0)
    (i : Fin 3) : direction a b c i-lowerAnchor a b c i =
      direction a b c i*direction a b c (i+2)*weight a b c (i+2)/
        SixTriangleAlgebra.p a b c := by
  fin_cases i <;> norm_num [lowerAnchor,direction,weight,Fin.add_def] <;>
    field_simp [hp] <;> dsimp [k0,k1,k2,SixTriangleAlgebra.p] <;> ring

theorem upper_middle_margin {a b c : ℝ} (hq : SixTriangleAlgebra.q a b c ≠ 0)
    (i : Fin 3) : upperAnchor a b c i-direction a b c i =
      (1-direction a b c i)*(1-direction a b c (i+1))*weight a b c (i+1)/
        SixTriangleAlgebra.q a b c := by
  fin_cases i <;> norm_num [upperAnchor,direction,weight,Fin.add_def] <;>
    field_simp [hq] <;> dsimp [k0,k1,k2,SixTriangleAlgebra.q] <;> ring

theorem upper_physical_margin {a b c : ℝ} (hq : SixTriangleAlgebra.q a b c ≠ 0)
    (i : Fin 3) : 1-upperAnchor a b c i =
      (1-direction a b c i)*weight a b c i/SixTriangleAlgebra.q a b c := by
  fin_cases i <;> norm_num [upperAnchor,direction,weight,Fin.add_def] <;>
    field_simp [hq] <;> dsimp [k0,k1,k2,SixTriangleAlgebra.q] <;> ring

theorem anchor_bounds {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (i : Fin 3) :
    0 < lowerAnchor a b c i ∧ lowerAnchor a b c i < direction a b c i ∧
      direction a b c i < upperAnchor a b c i ∧ upperAnchor a b c i < 1 := by
  have hp := SixTriangleAlgebra.p_pos ha.1 hb.1 hc.1
  have hq := SixTriangleAlgebra.q_pos ha.2 hb.2 hc.2
  have hd := direction_bounds ha hb hc i
  have hj := direction_bounds ha hb hc (i+1)
  have hk := direction_bounds ha hb hc (i+2)
  have hw := weight_pos ha hb hc i
  have hwj := weight_pos ha hb hc (i+1)
  have hwk := weight_pos ha hb hc (i+2)
  refine ⟨div_pos (mul_pos hd.1 hw) hp,?_,?_,?_⟩
  · apply sub_pos.mp
    rw [lower_middle_margin hp.ne']
    exact div_pos (mul_pos (mul_pos hd.1 hk.1) hwk) hp
  · apply sub_pos.mp
    rw [upper_middle_margin hq.ne']
    exact div_pos (mul_pos (mul_pos (sub_pos.mpr hd.2) (sub_pos.mpr hj.2)) hwj) hq
  · apply sub_pos.mp
    rw [upper_physical_margin hq.ne']
    exact div_pos (mul_pos (sub_pos.mpr hd.2) hw) hq

theorem anchorWidth_pos {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (i : Fin 3) :
    0 < anchorWidth a b c i := by
  obtain ⟨_,hl,hh,_⟩ := anchor_bounds ha hb hc i
  exact sub_pos.mpr (hl.trans hh)

theorem alphaCost_pos {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (i : Fin 3) :
    0 < alphaCost a b c i :=
  mul_pos (mul_pos (weight_pos ha hb hc i)
    (sub_pos.mpr (direction_bounds ha hb hc i).2)) (anchorWidth_pos ha hb hc (i+1))

theorem betaCost_pos {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (i : Fin 3) :
    0 < betaCost a b c i :=
  mul_pos (mul_pos (weight_pos ha hb hc i)
    (direction_bounds ha hb hc i).1) (anchorWidth_pos ha hb hc (i+2))

theorem deficit_anchor {a b c : ℝ} (hp : SixTriangleAlgebra.p a b c ≠ 0)
    (hq : SixTriangleAlgebra.q a b c ≠ 0) :
    SixTriangleResidual.deficit (lowerAnchor a b c) (upperAnchor a b c) =
      -SixTriangleAlgebra.imbalance a b c := by
  have he := SixTriangleAlgebra.linear_identity hp hq (lowerAnchor a b c) (upperAnchor a b c)
  simp only [lowCut_lowerAnchor hp,highCut_upperAnchor hq,mul_zero,Finset.sum_const_zero,
    zero_add] at he
  change 0 = SixTriangleResidual.deficit (lowerAnchor a b c) (upperAnchor a b c)+
    SixTriangleAlgebra.imbalance a b c at he
  linarith only [he]

theorem alphaArgument_anchor {a b c : ℝ} (hp : SixTriangleAlgebra.p a b c ≠ 0)
    (hq : SixTriangleAlgebra.q a b c ≠ 0) (i : Fin 3) :
    weight a b c i*windowWidth (lowerAnchor a b c) (upperAnchor a b c) i-
      thresholdSlack a b c (lowerAnchor a b c) = -alphaCost a b c i := by
  fin_cases i <;>
    norm_num [alphaCost,anchorWidth,lowerAnchor,upperAnchor,windowWidth,thresholdSlack,
      direction,weight,Fin.add_def] <;>
    field_simp [hp,hq] <;> dsimp [k0,k1,k2,SixTriangleAlgebra.p,SixTriangleAlgebra.q] <;> ring

theorem betaArgument_anchor {a b c : ℝ} (hp : SixTriangleAlgebra.p a b c ≠ 0)
    (hq : SixTriangleAlgebra.q a b c ≠ 0) (i : Fin 3) :
    weight a b c i*windowWidth (lowerAnchor a b c) (upperAnchor a b c) i+
      thresholdSlack a b c (upperAnchor a b c) = -betaCost a b c i := by
  fin_cases i <;>
    norm_num [betaCost,anchorWidth,lowerAnchor,upperAnchor,windowWidth,thresholdSlack,
      direction,weight,Fin.add_def] <;>
    field_simp [hp,hq] <;> dsimp [k0,k1,k2,SixTriangleAlgebra.p,SixTriangleAlgebra.q] <;> ring

theorem refundArgument_anchor {a b c : ℝ} (hp : SixTriangleAlgebra.p a b c ≠ 0)
    (hq : SixTriangleAlgebra.q a b c ≠ 0) (i : Fin 3) :
    refundArgument a b c (lowerAnchor a b c) (upperAnchor a b c) i =
      ![-anchorWidth a b c (i+1),-direction a b c (i+1)*anchorWidth a b c i,
        -anchorWidth a b c i,-(1-direction a b c i)*anchorWidth a b c (i+1)] := by
  simp only [refundArgument,lowPairSlack_lowerAnchor hp,highPairSlack_upperAnchor hq,
    neg_zero,zero_sub,neg_mul,anchorWidth,windowWidth]

theorem positive_vertex_payment_gap {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (i : Fin 3) :
    weight a b c (i+2)*(direction a b c i-lowerAnchor a b c i)/direction a b c i+
      alphaCost a b c (i+1)/weight a b c i-anchorWidth a b c i =
      direction a b c (i+2)*(1-direction a b c (i+1))*weight a b c (i+2)*
        anchorWidth a b c (i+2)/weight a b c i := by
  have hp := (SixTriangleAlgebra.p_pos ha.1 hb.1 hc.1).ne'
  have hq := (SixTriangleAlgebra.q_pos ha.2 hb.2 hc.2).ne'
  obtain ⟨h0,h1,h2⟩ := weights_pos ha hb hc
  fin_cases i <;>
    norm_num [alphaCost,anchorWidth,lowerAnchor,upperAnchor,direction,weight,Fin.add_def] <;>
    field_simp [hp,hq,ha.1.ne',hb.1.ne',hc.1.ne',h0.ne',h1.ne',h2.ne'] <;>
    dsimp [k0,k1,k2,SixTriangleAlgebra.p,SixTriangleAlgebra.q] <;> ring

theorem negative_vertex_payment_gap {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (i : Fin 3) :
    weight a b c (i+2)*(upperAnchor a b c (i+1)-direction a b c (i+1))/
        (1-direction a b c (i+1))+
      betaCost a b c i/weight a b c (i+1)-anchorWidth a b c (i+1) =
      direction a b c i*(1-direction a b c (i+2))*weight a b c (i+2)*
        anchorWidth a b c (i+2)/weight a b c (i+1) := by
  have hp := (SixTriangleAlgebra.p_pos ha.1 hb.1 hc.1).ne'
  have hq := (SixTriangleAlgebra.q_pos ha.2 hb.2 hc.2).ne'
  obtain ⟨h0,h1,h2⟩ := weights_pos ha hb hc
  fin_cases i <;>
    norm_num [betaCost,anchorWidth,lowerAnchor,upperAnchor,direction,weight,Fin.add_def] <;>
    field_simp [hp,hq,(sub_pos.mpr ha.2).ne',(sub_pos.mpr hb.2).ne',
      (sub_pos.mpr hc.2).ne',h0.ne',h1.ne',h2.ne'] <;>
    dsimp [k0,k1,k2,SixTriangleAlgebra.p,SixTriangleAlgebra.q] <;> ring

theorem positive_vertex_payment_gap_pos {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (i : Fin 3) :
    0 < weight a b c (i+2)*(direction a b c i-lowerAnchor a b c i)/direction a b c i+
      alphaCost a b c (i+1)/weight a b c i-anchorWidth a b c i := by
  rw [positive_vertex_payment_gap ha hb hc]
  exact div_pos (mul_pos (mul_pos (mul_pos (direction_bounds ha hb hc (i+2)).1
    (sub_pos.mpr (direction_bounds ha hb hc (i+1)).2)) (weight_pos ha hb hc (i+2)))
      (anchorWidth_pos ha hb hc (i+2))) (weight_pos ha hb hc i)

theorem negative_vertex_payment_gap_pos {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (i : Fin 3) :
    0 < weight a b c (i+2)*(upperAnchor a b c (i+1)-direction a b c (i+1))/
        (1-direction a b c (i+1))+
      betaCost a b c i/weight a b c (i+1)-anchorWidth a b c (i+1) := by
  rw [negative_vertex_payment_gap ha hb hc]
  exact div_pos (mul_pos (mul_pos (mul_pos (direction_bounds ha hb hc i).1
    (sub_pos.mpr (direction_bounds ha hb hc (i+2)).2)) (weight_pos ha hb hc (i+2)))
      (anchorWidth_pos ha hb hc (i+2))) (weight_pos ha hb hc (i+1))


end Quant.CyclicAnchorAlgebra
