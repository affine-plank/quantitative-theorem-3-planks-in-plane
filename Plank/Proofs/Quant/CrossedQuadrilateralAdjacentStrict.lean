/- Strictness for separated vertical bands reaching beyond the residual valley. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralAdjacentVariation

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralAdjacentStrict
open Set MeasureTheory Filter CrossedQuadrilateralAttainment
open CrossedQuadrilateralAdjacentProfile CrossedQuadrilateralAdjacentDifferences
open CrossedQuadrilateralPairBudget CrossedQuadrilateralAdjacentVariation
open scoped Topology

theorem small_step (S : Shape) {k a b c d lo hi : ℝ} (e : ℝ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hv : valley S k lo < d)
    (hR : budget S k a b c d lo hi < 1) :
    ∃ t : ℝ, 0 < t ∧
      (a-S.c*t ≤ b+e*t ∧ b+e*t ≤ c ∧ c ≤ d+S.a*t) ∧
      (a+S.c*t ≤ b-e*t ∧ b-e*t ≤ c ∧ c ≤ d-S.a*t) ∧
      valley S k lo ≤ d-S.a*t ∧
      budget S k (a-S.c*t) (b+e*t) c (d+S.a*t) lo hi < 1 ∧
      budget S k (a+S.c*t) (b-e*t) c (d-S.a*t) lo hi < 1 := by
  have h₁ : ∀ᶠ t : ℝ in 𝓝 0, a-S.c*t < b+e*t :=
    (by fun_prop : ContinuousAt (fun t : ℝ => a-S.c*t) 0).eventually_lt
      (by fun_prop) (by simpa using hab)
  have h₂ : ∀ᶠ t : ℝ in 𝓝 0, b+e*t < c :=
    (by fun_prop : ContinuousAt (fun t : ℝ => b+e*t) 0).eventually_lt
      continuousAt_const (by simpa using hbc)
  have h₃ : ∀ᶠ t : ℝ in 𝓝 0, c < d+S.a*t :=
    continuousAt_const.eventually_lt
      (by fun_prop : ContinuousAt (fun t : ℝ => d+S.a*t) 0) (by simpa using hcd)
  have h₄ : ∀ᶠ t : ℝ in 𝓝 0, a+S.c*t < b-e*t :=
    (by fun_prop : ContinuousAt (fun t : ℝ => a+S.c*t) 0).eventually_lt
      (by fun_prop) (by simpa using hab)
  have h₅ : ∀ᶠ t : ℝ in 𝓝 0, b-e*t < c :=
    (by fun_prop : ContinuousAt (fun t : ℝ => b-e*t) 0).eventually_lt
      continuousAt_const (by simpa using hbc)
  have h₆ : ∀ᶠ t : ℝ in 𝓝 0, c < d-S.a*t :=
    continuousAt_const.eventually_lt
      (by fun_prop : ContinuousAt (fun t : ℝ => d-S.a*t) 0) (by simpa using hcd)
  have h₇ : ∀ᶠ t : ℝ in 𝓝 0, valley S k lo < d-S.a*t :=
    continuousAt_const.eventually_lt
      (by fun_prop : ContinuousAt (fun t : ℝ => d-S.a*t) 0) (by simpa using hv)
  have h₈ : ∀ᶠ t : ℝ in 𝓝 0,
      budget S k (a-S.c*t) (b+e*t) c (d+S.a*t) lo hi < 1 :=
    (by unfold budget; fun_prop : ContinuousAt
      (fun t : ℝ => budget S k (a-S.c*t) (b+e*t) c (d+S.a*t) lo hi) 0).eventually_lt
      continuousAt_const (by simpa using hR)
  have h₉ : ∀ᶠ t : ℝ in 𝓝 0,
      budget S k (a+S.c*t) (b-e*t) c (d-S.a*t) lo hi < 1 :=
    (by unfold budget; fun_prop : ContinuousAt
      (fun t : ℝ => budget S k (a+S.c*t) (b-e*t) c (d-S.a*t) lo hi) 0).eventually_lt
      continuousAt_const (by simpa using hR)
  have hall := h₁.and (h₂.and (h₃.and (h₄.and (h₅.and (h₆.and (h₇.and (h₈.and h₉)))))))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hall
  have ht : 0 < δ/2 := half_pos hδ
  have hm := hball (y := δ/2) (by
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    linarith only [hδ])
  exact ⟨δ/2,ht,⟨hm.1.le,hm.2.1.le,hm.2.2.1.le⟩,
    ⟨hm.2.2.2.1.le,hm.2.2.2.2.1.le,hm.2.2.2.2.2.1.le⟩,
    hm.2.2.2.2.2.2.1.le,hm.2.2.2.2.2.2.2⟩

/-- This is strictness for the actual geometric gap and actual total relative width. -/
theorem strict (S : Shape) {k a b c d lo hi : ℝ}
    (hk : Sector S k) (ho : lo < hi) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hv : valley S k lo < d) (hR : budget S k a b c d lo hi < 1) :
    (1-budget S k a b c d lo hi)^2*(volume S.body).toReal <
      gap S k a b c d lo hi := by
  rw [actual_area]
  have hbnd := lower_bound S hab.le hcd.le ho.le hR
  apply lt_of_le_of_ne hbnd
  intro heq
  let H := S.b+S.d
  let W := S.a+S.c
  let L := lowerConstant S k
  have hH : 0 < H := add_pos S.hb S.hd
  have hW : 0 < W := add_pos S.ha S.hc
  have hL : 0 < L := lowerConstant_pos S hk
  let e := H/(L+1)
  have he : 0 < e := div_pos hH (by linarith only [hL])
  have hes : L*e < H := by
    have hx : e*(L+1) = H := div_mul_cancel₀ H (by linarith only [hL] : L+1 ≠ 0)
    nlinarith only [hx,he]
  obtain ⟨t,ht,hp,hm,hv',hRp,hRm⟩ := small_step S e hab hbc hcd hv hR
  have hpB := lower_bound S hp.1 hp.2.2 ho.le hRp
  have hmB := lower_bound S hm.1 hm.2.2 ho.le hRm
  rw [budget_plus] at hpB
  rw [budget_minus] at hmB
  have hu := gap_difference_upper S hk ho he.le ht.le hab.le hbc.le hcd.le hp hm hv'
  have hc := coefficient_strict hH hW he hes
  have hc' := mul_lt_mul_of_pos_right hc (sq_pos_of_pos ht)
  have hw : H/W*(W+e)^2 = 2*((W+e)/W)^2*(H*W/2) := by
    field_simp
  rw [hw] at hc'
  dsimp only [H,W,L] at hc'
  nlinarith only [hpB,hmB,hu,hc',heq]

end Quant.CrossedQuadrilateralAdjacentStrict

/-- info: 'Quant.CrossedQuadrilateralAdjacentStrict.strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralAdjacentStrict.strict
