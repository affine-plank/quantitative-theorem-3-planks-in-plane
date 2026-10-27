/- The paper's six-support width criterion, with all numerical steps together. -/
module
public import Plank.Convex.CyclicBox
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Bound
@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace Plank.Convex.PlanarWidthCriterion
abbrev Triple := Fin 3 → ℝ

/-- Each one-sided slope condition supplies a box inequality. Adding the two
inequalities proves the cycle factor nonnegative without expanding six slacks. -/
theorem slope_gap_nonneg (a b : Triple) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, a (i+1)*(1-b i) ≤ 1) (hba : ∀ i, b (i+1)*(1-a i) ≤ 1) :
    0 ≤ 2*((∏ i, a i)-1)*((∏ i, b i)-1) + (∏ i, (a i+b i)) := by
  have H (u v : Triple) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
      (h : ∀ i, u (i+1)*(1-v i) ≤ 1) :=
    CyclicBox.cyclic_product_le u (fun i => u i*v (i+2))
      (fun i => mul_nonneg (hu i) (hv (i+2))) hu (fun i => by
        have hi : (i+2)+1 = i := by fin_cases i <;> rfl
        have H := h (i+2)
        rw [hi] at H
        nlinarith only [H])
  have hA := H a b ha hb hab
  have hB := H b a hb ha hba
  simp [Fin.sum_univ_three, Fin.prod_univ_three] at hA hB ⊢
  nlinarith only [hA,hB]

/-- Eliminate the other two coordinates with three alternating inequalities. -/
theorem three_rows (x y z a b c A B C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : x + a*y ≤ A) (h₂ : B ≤ y + b*z) (h₃ : z + c*x ≤ C) :
    (1 + a*b*c)*x ≤ A - a*B + a*b*C := by
  have h₂ := mul_le_mul_of_nonneg_left h₂ ha
  have h₃ := mul_le_mul_of_nonneg_left h₃ (mul_nonneg ha hb)
  nlinarith only [h₁, h₂, h₃]

/-- Two supporting rows bound their slopes when their contact heights are ordered.
Only these two coordinate sums are compared; no ambient plane is required. -/
theorem contact_slope_bound (xp yp zp xq yq zq a b : ℝ)
    (hy : yq < yp) (ha : 0 ≤ a)
    (hu : yq + a*zq ≤ yp + a*zp) (hl : xq + b*yq ≤ xp + b*yp)
    (hs : xp + yp + zp ≤ xq + yq + zq) : a * (1-b) ≤ 1 := by
  have hl := mul_le_mul_of_nonneg_left hl ha
  have hs := mul_le_mul_of_nonneg_left hs ha
  apply (mul_le_mul_iff_left₀ (sub_pos.mpr hy)).mp
  nlinarith only [hu, hl, hs]

/-- The three-variable numerator separates into pair and cycle coefficients. -/
theorem budget_remainder (E F J w S : Triple)
    (hs : ∀ i, S i = E i * w i + F i * w (i+1) + J i * w (i+2)) :
    (∑ i, E i * w i * S (i+1) * S (i+2)) - (∏ i, S i) =
      (2 * (∏ i, E i) - (∏ i, F i) - (∏ i, J i)) * (∏ i, w i) +
        ∑ i, (E i * E (i+1) - F i * J (i+1)) * w i * w (i+1) *
          (S (i+2) - E (i+2) * w (i+2)) := by
  simp [hs, Fin.sum_univ_three, Fin.prod_univ_three]
  ring

/-- Nonnegative pair and cycle coefficients make three linear budgets sufficient. -/
private theorem budget_bound (E F J w S R : Triple)
    (hw : ∀ i, 0 ≤ w i) (hR : ∀ i, 0 < R i) (hE : ∀ i, 0 < E i)
    (hF : ∀ i, 0 ≤ F i) (hJ : ∀ i, 0 ≤ J i)
    (hs : ∀ i, S i = E i * w i + F i * w (i+1) + J i * w (i+2))
    (hbudget : ∀ i, E i * R i ≤ S i)
    (hp : ∀ i, 0 ≤ E i * E (i+1) - F i * J (i+1))
    (hc : 0 ≤ 2 * (∏ i, E i) - (∏ i, F i) - (∏ i, J i)) :
    1 ≤ ∑ i, w i / R i := by
  have hS (i) : 0 < S i := (mul_pos (hE i) (hR i)).trans_le (hbudget i)
  have hoff (i) : 0 ≤ S i - E i * w i := by
    rw [hs]
    nlinarith only [mul_nonneg (hF i) (hw (i+1)), mul_nonneg (hJ i) (hw (i+2))]
  have hrem : 0 ≤ (∑ i, E i * w i * S (i+1) * S (i+2)) - (∏ i, S i) := by
    rw [budget_remainder E F J w S hs]
    exact add_nonneg (mul_nonneg hc (Finset.prod_nonneg fun i _ => hw i))
      (Finset.sum_nonneg fun i _ => by bound [hp i, hw i, hw (i+1), hoff (i+2)])
  have hsum : 1 ≤ ∑ i, E i * w i / S i := by
    have h0 := hS 0; have h1 := hS 1; have h2 := hS 2
    simp only [Fin.sum_univ_three]
    field_simp
    simp [Fin.sum_univ_three, Fin.prod_univ_three] at hrem
    linarith only [hrem]
  refine hsum.trans (Finset.sum_le_sum fun i _ => ?_)
  apply (div_le_div_iff₀ (hS i) (hR i)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left (hbudget i) (hw i)]

/-- Six inequalities and attained coordinate extrema suffice. No convexity,
plane equation, or positive window width is assumed in this numerical lemma. -/
theorem width_bound {ι : Type*} (X : ι → Triple) (lo hi R a b : Triple)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (horder : ∀ i, lo i ≤ hi i) (hR : ∀ i, 0 < R i)
    (hzero : ∀ i, ∃ v, X v i = 0) (hmax : ∀ i, ∃ v, X v i = R i)
    (hupper : ∀ i v, X v i + a i * X v (i+1) ≤ hi i + a i * hi (i+1))
    (hlower : ∀ i v, lo i + b i * lo (i+1) ≤ X v i + b i * X v (i+1))
    (hab : ∀ i, a (i+1) * (1-b i) ≤ 1)
    (hba : ∀ i, b (i+1) * (1-a i) ≤ 1) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  let w : Triple := fun i => hi i - lo i
  change 1 ≤ ∑ i, w i / R i
  let L : Triple := fun i => 1 + b i * a (i+1) * b (i+2)
  let U : Triple := fun i => 1 + a i * b (i+1) * a (i+2)
  let E : Triple := fun i => L i * U i
  let F : Triple := fun i => b i * U i + a i * L i
  let J : Triple := fun i => b i * a (i+1) * U i + a i * b (i+1) * L i
  let S : Triple := fun i => E i * w i + F i * w (i+1) + J i * w (i+2)
  have hL (i) : 0 < L i := by apply add_pos_of_pos_of_nonneg zero_lt_one; bound
  have hU (i) : 0 < U i := by apply add_pos_of_pos_of_nonneg zero_lt_one; bound
  have hbudget (i : Fin 3) : E i * R i ≤ S i := by
    have hn : (i+1)+1 = i+2 := by fin_cases i <;> rfl
    have hp : (i+2)+1 = i := by fin_cases i <;> rfl
    obtain ⟨p, hpi⟩ := hmax i
    obtain ⟨z, hzi⟩ := hzero i
    have H := three_rows _ _ _ _ _ _ _ _ _ (ha i) (hb (i+1))
      (hupper i p) (by simpa only [hn] using hlower (i+1) p)
      (by simpa only [hp] using hupper (i+2) p)
    have Z := three_rows (-X z i) (-X z (i+1)) (-X z (i+2))
      _ _ _ _ _ _ (hb i) (ha (i+1))
      (by simpa only [neg_add, mul_neg] using neg_le_neg (hlower i z))
      (by simpa only [hn, neg_add, mul_neg] using neg_le_neg (hupper (i+1) z))
      (by simpa only [hp, neg_add, mul_neg] using neg_le_neg (hlower (i+2) z))
    rw [hpi] at H
    rw [hzi] at Z
    have H := mul_le_mul_of_nonneg_left H (hL i).le
    have Z := mul_le_mul_of_nonneg_left Z (hU i).le
    dsimp only [S, F, J, E, w, L, U] at *
    linarith only [H, Z]
  let d := ((∏ i, a i) * (∏ i, b i) - 1)^2
  have hp (i : Fin 3) : 0 ≤ E i * E (i+1) - F i * J (i+1) := by
    have he : E i * E (i+1) - F i * J (i+1) = d := by
      fin_cases i <;> simp [F, J, E, L, U, d, Fin.prod_univ_three] <;> ring
    rw [he]
    exact sq_nonneg _
  have hc : 0 ≤ 2 * (∏ i, E i) - (∏ i, F i) - (∏ i, J i) := by
    let G := 2*((∏ i, a i)-1)*((∏ i, b i)-1) + (∏ i, (a i+b i))
    have hG : 0 ≤ G := slope_gap_nonneg a b ha hb hab hba
    have he : 2 * (∏ i, E i) - (∏ i, F i) - (∏ i, J i) = d * G := by
      simp [F, J, E, L, U, d, G, Fin.prod_univ_three]
      ring
    rw [he]
    exact mul_nonneg (sq_nonneg _) hG
  have hw (i) : 0 ≤ w i := sub_nonneg.mpr (horder i)
  have hE (i) : 0 < E i := mul_pos (hL i) (hU i)
  have hF (i) : 0 ≤ F i := by dsimp [F]; bound
  have hJ (i) : 0 ≤ J i := by dsimp [J]; bound
  exact budget_bound E F J w S R hw hR hE hF hJ (fun _ => rfl) hbudget hp hc

end Plank.Convex.PlanarWidthCriterion
