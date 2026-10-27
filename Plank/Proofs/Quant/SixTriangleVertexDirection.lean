module
/-
# A direction whose low-cut energy is dominated by one vertex penalty

The explicit direction and midpoint bounds avoid a matrix-inverse hypothesis.
They support the subsequent descent theorem; no global minimization result
is asserted in this file.
-/
public import Plank.Proofs.Quant.SixTriangleAlgebra

@[expose] public section
noncomputable section

namespace Quant.SixTriangleVertexDirection

def p (a b c : ℝ) : ℝ := 1+a*b*c
def k0 (a b : ℝ) : ℝ := 1-b+a*b
def k1 (b c : ℝ) : ℝ := 1-c+b*c
def k2 (a c : ℝ) : ℝ := 1-a+a*c

def v0 (a b c : ℝ) : ℝ :=
  a*(a*b*c^2*k0 a b+a*c*k1 b c+k2 a c)/(p a b c)^2
def v1 (a b c : ℝ) : ℝ := -a*b*k1 b c*k2 a c/(p a b c)^2
def v2 (a b c : ℝ) : ℝ := -a*c*k0 a b*k1 b c/(p a b c)^2

theorem k0_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b ∧ b < 1) : 0 < k0 a b := by
  dsimp [k0]
  have h := mul_pos ha hb.1
  linarith [hb.2]

theorem p_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < p a b c := by dsimp [p]; positivity

theorem slope0 {a b c : ℝ} (hp : p a b c ≠ 0) :
    b*v0 a b c+v1 a b c = a*b*c*k0 a b/p a b c := by
  dsimp [v0,v1]
  field_simp
  dsimp [p,k0,k1,k2]
  ring

theorem slope1 {a b c : ℝ} (hp : p a b c ≠ 0) :
    c*v1 a b c+v2 a b c = -a*c*k1 b c/p a b c := by
  dsimp [v1,v2]
  field_simp
  dsimp [p,k0,k1,k2]
  ring

theorem slope2 {a b c : ℝ} (hp : p a b c ≠ 0) :
    v0 a b c+a*v2 a b c = a*k2 a c/p a b c := by
  dsimp [v0,v2]
  field_simp
  dsimp [p,k0,k1,k2]
  ring

theorem diagonal_gap {a b c : ℝ} (hp : p a b c ≠ 0) :
    v0 a b c-a*(1-a) =
      a^2*c*k0 a b*(2-c+b*c+a*b*c)/(p a b c)^2 := by
  dsimp [v0]
  field_simp
  dsimp [p,k0,k1,k2]
  ring

theorem diagonal_gt {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    a*(1-a) < v0 a b c := by
  have hp := p_pos ha.1 hb.1 hc.1
  have hk := k0_pos ha.1 hb
  have hrest : 0 < 2-c+b*c+a*b*c := by
    have hbc := mul_pos hb.1 hc.1
    have habc := mul_pos (mul_pos ha.1 hb.1) hc.1
    linarith [hc.2]
  have hpos : 0 < a^2*c*k0 a b*(2-c+b*c+a*b*c)/(p a b c)^2 :=
    div_pos (mul_pos (mul_pos (mul_pos (sq_pos_of_pos ha.1) hc.1) hk) hrest)
      (sq_pos_of_pos hp)
  rw [← diagonal_gap hp.ne'] at hpos
  linarith

def lowEnergy (a b c : ℝ) : ℝ :=
  (b*v0 a b c+v1 a b c)^2/(b*k0 a b)+
  (c*v1 a b c+v2 a b c)^2/(c*k1 b c)+
  (v0 a b c+a*v2 a b c)^2/(a*k2 a c)

theorem lowEnergy_eq {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    lowEnergy a b c = v0 a b c := by
  have hp := (p_pos ha.1 hb.1 hc.1).ne'
  have hk0 := (k0_pos ha.1 hb).ne'
  have hk1 : k1 b c ≠ 0 := (k0_pos hb.1 hc).ne'
  have hk2 : k2 a c ≠ 0 := by
    simpa only [k0,k2,mul_comm] using (k0_pos hc.1 ha).ne'
  rw [lowEnergy,slope0 hp,slope1 hp,slope2 hp]
  dsimp [v0]
  field_simp [ha.1.ne',hb.1.ne',hc.1.ne',hk0,hk1,hk2]

theorem selected_cap_strictly_dominates {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    lowEnergy a b c-(v0 a b c)^2/(a*(1-a)) < 0 := by
  have hden : 0 < a*(1-a) := mul_pos ha.1 (sub_pos.mpr ha.2)
  have hv := diagonal_gt ha hb hc
  have hv0 : 0 < v0 a b c := lt_trans hden hv
  rw [lowEnergy_eq ha hb hc]
  calc
    v0 a b c-(v0 a b c)^2/(a*(1-a)) =
        v0 a b c*(a*(1-a)-v0 a b c)/(a*(1-a)) := by
      field_simp [ha.1.ne', (sub_pos.mpr ha.2).ne']
    _ < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hv0 (sub_neg.mpr hv)) hden

theorem positive_square_midpoint_bounds (x t : ℝ) :
    2*(max 0 x)^2 ≤ (max 0 (x+t))^2+(max 0 (x-t))^2 ∧
    (max 0 (x+t))^2+(max 0 (x-t))^2 ≤ 2*(max 0 x)^2+2*t^2 := by
  by_cases hx : 0 ≤ x <;> by_cases hp : 0 ≤ x+t <;> by_cases hm : 0 ≤ x-t <;>
    simp only [max_def, hx, hp, hm, if_true, if_false] <;>
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg t, sq_nonneg (x+t), sq_nonneg (x-t)]

end Quant.SixTriangleVertexDirection
