module
/-
# The exact surplus in the six-triangle estimate

Keep the completed-square residual, including the negative-cut correction,
instead of discarding it in the positive-part lower bound. This identity is
unconditional in the window positions and is intended to pay clipping losses.
-/
public import Plank.Proofs.Quant.SixTriangleAlgebra

@[expose] public section
noncomputable section

namespace Quant.SixTriangleResidual

open SixTriangleAlgebra

def termResidual (k c v w : ℝ) : ℝ :=
  (max 0 v-k*c*w)^2/w + 2*k*c*max 0 (-v)

theorem term_identity (k c v w : ℝ) (hw : w ≠ 0) :
    (max 0 v)^2/w = 2*k*c*v-k^2*c^2*w+termResidual k c v w := by
  have hn : max 0 (-v) = max 0 v-v := by
    by_cases hv : 0 ≤ v
    · rw [max_eq_left (neg_nonpos.mpr hv), max_eq_right hv]
      ring
    · have hv' : v ≤ 0 := le_of_lt (lt_of_not_ge hv)
      rw [max_eq_right (neg_nonneg.mpr hv'), max_eq_left hv']
      ring
  unfold termResidual
  rw [hn]
  field_simp
  ring

theorem termResidual_nonneg {k c v w : ℝ}
    (hk : 0 ≤ k) (hc : 0 ≤ c) (hw : 0 < w) :
    0 ≤ termResidual k c v w := by
  unfold termResidual
  positivity

theorem sum_term_identity (k : ℝ) (c v w : Fin 3 → ℝ) (hw : ∀ i, w i ≠ 0) :
    (∑ i, (max 0 (v i))^2/w i) =
      2*k*(∑ i, c i*v i)-k^2*(∑ i, (c i)^2*w i)+
        ∑ i, termResidual k (c i) (v i) (w i) := by
  calc
    _ = ∑ i, (2*k*c i*v i-k^2*(c i)^2*w i+
        termResidual k (c i) (v i) (w i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact term_identity k (c i) (v i) (w i) (hw i)
    _ = _ := by
      simp only [Fin.sum_univ_three]
      ring

def deficit (l h : Fin 3 → ℝ) : ℝ :=
  1-((h 0-l 0)+(h 1-l 1)+(h 2-l 2))

def sixResidual (a b c : ℝ) (l h : Fin 3 → ℝ) (k : ℝ) : ℝ :=
  (∑ i, termResidual k (lowWeight a b c i) (lowCut a b c l i) (lowDenom a b c i))+
    ∑ i, termResidual k (highWeight a b c i) (highCut a b c h i) (highDenom a b c i)

theorem sixArea_eq_dual_add_residual {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (l h : Fin 3 → ℝ) (k : ℝ) :
    sixArea a b c l h = 2*k*(deficit l h+imbalance a b c)-
      k^2*(1-(imbalance a b c)^2)+sixResidual a b c l h k := by
  have hlow := sum_term_identity k (lowWeight a b c) (lowCut a b c l)
    (lowDenom a b c) (fun i => (denoms_pos ha hb hc i).1.ne')
  have hhigh := sum_term_identity k (highWeight a b c) (highCut a b c h)
    (highDenom a b c) (fun i => (denoms_pos ha hb hc i).2.ne')
  calc
    sixArea a b c l h =
        2*k*((∑ i, lowWeight a b c i*lowCut a b c l i)+
          ∑ i, highWeight a b c i*highCut a b c h i)-
        k^2*((∑ i, (lowWeight a b c i)^2*lowDenom a b c i)+
          ∑ i, (highWeight a b c i)^2*highDenom a b c i)+
        sixResidual a b c l h k := by
      dsimp only [sixArea, sixResidual]
      rw [hlow, hhigh]
      ring
    _ = _ := by
      rw [linear_identity (p_pos ha.1 hb.1 hc.1).ne' (q_pos ha.2 hb.2 hc.2).ne' l h,
        norm_identity (p_pos ha.1 hb.1 hc.1).ne' (q_pos ha.2 hb.2 hc.2).ne']
      rfl

theorem sixArea_eq_baseline_add_residual {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (l h : Fin 3 → ℝ) :
    sixArea a b c l h = (deficit l h)^2+2*deficit l h*imbalance a b c+
      (deficit l h)^2*(imbalance a b c)^2+
      sixResidual a b c l h (deficit l h) := by
  rw [sixArea_eq_dual_add_residual ha hb hc l h (deficit l h)]
  ring

theorem sixResidual_nonneg {a b c k : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (l h : Fin 3 → ℝ) (hk : 0 ≤ k) :
    0 ≤ sixResidual a b c l h k := by
  unfold sixResidual
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact termResidual_nonneg hk (weights_pos ha hb hc i).1.le (denoms_pos ha hb hc i).1
  · apply Finset.sum_nonneg
    intro i _
    exact termResidual_nonneg hk (weights_pos ha hb hc i).2.le (denoms_pos ha hb hc i).2


end Quant.SixTriangleResidual
