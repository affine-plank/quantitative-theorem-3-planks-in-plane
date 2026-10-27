/- Equality conditions in the six-triangle algebraic estimate.
The geometric identification is supplied separately by CyclicUnclippedEquality. -/
module

public import Plank.Proofs.Quant.SixTriangleResidual

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.SixTriangleEquality

open SixTriangleAlgebra SixTriangleResidual

/-- Positive deficit makes each completed-square equality a genuine linear
equation, with a strictly positive cut. -/
theorem termResidual_eq_zero_iff {k c v w : ℝ}
    (hk : 0 < k) (hc : 0 < c) (hw : 0 < w) :
    termResidual k c v w = 0 ↔ v = k*c*w := by
  have hkcw : 0 < k*c*w := mul_pos (mul_pos hk hc) hw
  constructor
  · intro he
    have hA : 0 ≤ (max 0 v-k*c*w)^2/w := div_nonneg (sq_nonneg _) hw.le
    have hB : 0 ≤ 2*k*c*max 0 (-v) := by positivity
    have hsq : (max 0 v-k*c*w)^2/w = 0 := by
      dsimp [termResidual] at he
      linarith only [he,hA,hB]
    have hz : (max 0 v-k*c*w)^2 = 0 :=
      (div_eq_zero_iff.mp hsq).resolve_right hw.ne'
    have hm : max 0 v = k*c*w := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    have hv : 0 < v := by
      have hp : 0 < max 0 v := by rw [hm]; exact hkcw
      exact (lt_max_iff.mp hp).resolve_left (lt_irrefl 0)
    rwa [max_eq_right hv.le] at hm
  · intro hv
    rw [termResidual, hv, max_eq_right hkcw.le, max_eq_left (neg_nonpos.mpr hkcw.le)]
    ring

theorem imbalance_eq_zero_iff {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    imbalance a b c = 0 ↔ a*b*c = (1-a)*(1-b)*(1-c) := by
  have hd : p a b c*q a b c ≠ 0 :=
    (mul_pos (p_pos ha.1 hb.1 hc.1) (q_pos ha.2 hb.2 hc.2)).ne'
  rw [imbalance, div_eq_zero_iff, or_iff_left hd, sq_eq_zero_iff, sub_eq_zero]
  dsimp [p,q]
  constructor <;> intro h <;> linarith only [h]

/-- Explicit equations for the equality locus: one direction balance and
six linear endpoint conditions. No area or scalar objective occurs here. -/
def CutCalibration (a b c : ℝ) (l h : Fin 3 → ℝ) : Prop :=
  a*b*c = (1-a)*(1-b)*(1-c) ∧
    ∀ i, lowCut a b c l i = deficit l h*lowWeight a b c i*lowDenom a b c i ∧
      highCut a b c h i = deficit l h*highWeight a b c i*highDenom a b c i

/-- Exhaustive equality conditions for the scalar six-term estimate at
positive deficit. This theorem alone makes no geometric sharpness claim. -/
theorem sixArea_eq_square_iff {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (l h : Fin 3 → ℝ) (hδ : 0 < deficit l h) :
    sixArea a b c l h = (deficit l h)^2 ↔ CutCalibration a b c l h := by
  have hid := sixArea_eq_baseline_add_residual ha hb hc l h
  have hI := imbalance_nonneg ha hb hc
  have hR := sixResidual_nonneg ha hb hc l h hδ.le
  have hnL (i : Fin 3) :
      0 ≤ termResidual (deficit l h) (lowWeight a b c i) (lowCut a b c l i)
        (lowDenom a b c i) :=
    termResidual_nonneg hδ.le (weights_pos ha hb hc i).1.le (denoms_pos ha hb hc i).1
  have hnH (i : Fin 3) :
      0 ≤ termResidual (deficit l h) (highWeight a b c i) (highCut a b c h i)
        (highDenom a b c i) :=
    termResidual_nonneg hδ.le (weights_pos ha hb hc i).2.le (denoms_pos ha hb hc i).2
  constructor
  · intro he
    have hI0 : imbalance a b c = 0 := by
      have hp := mul_nonneg (sq_nonneg (deficit l h)) (sq_nonneg (imbalance a b c))
      nlinarith only [hid,he,hI,hR,hp,hδ]
    have hR0 : sixResidual a b c l h (deficit l h) = 0 := by
      rw [hI0] at hid
      simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] at hid
      linarith only [hid,he]
    have hsL : (∑ i, termResidual (deficit l h) (lowWeight a b c i)
        (lowCut a b c l i) (lowDenom a b c i)) = 0 := by
      have hL := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hnL i)
      have hH := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hnH i)
      dsimp [sixResidual] at hR0
      linarith only [hR0,hL,hH]
    have hsH : (∑ i, termResidual (deficit l h) (highWeight a b c i)
        (highCut a b c h i) (highDenom a b c i)) = 0 := by
      dsimp [sixResidual] at hR0
      linarith only [hR0,hsL]
    refine ⟨(imbalance_eq_zero_iff ha hb hc).mp hI0, fun i => ⟨?_,?_⟩⟩
    · apply (termResidual_eq_zero_iff hδ (weights_pos ha hb hc i).1
        (denoms_pos ha hb hc i).1).mp
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnL j)).mp hsL i (Finset.mem_univ i)
    · apply (termResidual_eq_zero_iff hδ (weights_pos ha hb hc i).2
        (denoms_pos ha hb hc i).2).mp
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnH j)).mp hsH i (Finset.mem_univ i)
  · rintro ⟨hbal,hcut⟩
    have hI0 := (imbalance_eq_zero_iff ha hb hc).mpr hbal
    have hL (i : Fin 3) : termResidual (deficit l h) (lowWeight a b c i)
        (lowCut a b c l i) (lowDenom a b c i) = 0 :=
      (termResidual_eq_zero_iff hδ (weights_pos ha hb hc i).1
        (denoms_pos ha hb hc i).1).mpr (hcut i).1
    have hH (i : Fin 3) : termResidual (deficit l h) (highWeight a b c i)
        (highCut a b c h i) (highDenom a b c i) = 0 :=
      (termResidual_eq_zero_iff hδ (weights_pos ha hb hc i).2
        (denoms_pos ha hb hc i).2).mpr (hcut i).2
    have hR0 : sixResidual a b c l h (deficit l h) = 0 := by
      simp only [sixResidual,hL,hH,Finset.sum_const_zero,add_zero]
    simpa only [hI0,hR0,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero] using hid

end Quant.SixTriangleEquality

/-- info: 'Quant.SixTriangleEquality.sixArea_eq_square_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.SixTriangleEquality.sixArea_eq_square_iff
