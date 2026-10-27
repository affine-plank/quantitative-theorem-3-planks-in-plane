/- Two opposite caps in a nonnegative affine relation force a total window
width of at least one. The family of affine coordinates can be any finite
size. Four contacts replace global coordinate-range assumptions. -/
module
public import Plank.Convex.ConvexCapWidth
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.OppositeCapsWidth

variable {E ι κ : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- An upper-cap gate from three contacts, with no global coordinate bounds. -/
theorem upper_gate_affine (K : Set E) (hK : Convex ℝ K) (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (b : ℝ) (a : ι → ℝ) (d : ℝ) (hb : 0 ≤ b) (ha : ∀ j, 0 ≤ a j)
    (hplane : ∀ x ∈ K, b * Y x + ∑ j, a j * X j x = d)
    (i : ι) (hai : 0 < a i) (l : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hUm : ∃ x ∈ K, Y x = 1)
    (hLi : ∃ x ∈ K, X i x = 0 ∧ 0 ≤ Y x)
    (hUi : ∃ x ∈ K, X i x = 1 ∧ 0 ≤ Y x)
    (hcap : ∀ x ∈ K, t < Y x → ∀ j, l j ≤ X j x) :
    a i * (1 - t) ≤ d - b * t - ∑ j, a j * l j := by
  obtain ⟨P, hP, hPm⟩ := hUm
  obtain ⟨Q, hQ, hQi, hQy⟩ := hLi
  obtain ⟨R, hR, hRi, hRy⟩ := hUi
  let δ := d - b * t - ∑ j, a j * l j
  have hinterval (x : E) (hx : x ∈ K) (htx : t < Y x) :
      l i ≤ X i x ∧ X i x ≤ l i + δ / a i := by
    refine ⟨hcap x hx htx i, ?_⟩
    have hi : a i * (X i x - l i) ≤ ∑ j, a j * (X j x - l j) :=
      Finset.single_le_sum (fun j _ => mul_nonneg (ha j) (sub_nonneg.2 (hcap x hx htx j)))
        (Finset.mem_univ i)
    have hsum : (∑ j, a j * (X j x - l j)) = d - b * Y x - ∑ j, a j * l j := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      linarith only [hplane x hx]
    have ht := mul_le_mul_of_nonneg_left htx.le hb
    have hdiv : X i x - l i ≤ δ / a i := (le_div_iff₀ hai).2 (by
      dsimp [δ]
      nlinarith only [hi, hsum, ht])
    linarith only [hdiv]
  have hPcap := hinterval P hP (by simpa only [hPm] using ht1)
  have hwidth := Plank.Convex.ConvexCapWidth.cap_bound_upper_affine K hK (X i) Y
    Q R P hQ hR hP hQi hRi hPm hQy hRy t ht0 ht1.le
    (l i) (l i + δ / a i) (hPcap.1.trans hPcap.2) hinterval
  have hδ : δ / a i * a i = δ := div_mul_cancel₀ _ hai.ne'
  change a i * (1 - t) ≤ δ
  nlinarith only [mul_le_mul_of_nonneg_left hwidth hai.le, hδ]


/-- Reflecting every affine coordinate turns the lower gate into the upper gate. -/
theorem lower_gate_affine (K : Set E) (hK : Convex ℝ K)
    (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (b : ℝ) (a : ι → ℝ) (d : ℝ) (hb : 0 ≤ b) (ha : ∀ j, 0 ≤ a j)
    (hplane : ∀ x ∈ K, b * Y x + ∑ j, a j * X j x = d)
    (i : ι) (hai : 0 < a i) (h : ι → ℝ) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hLm : ∃ x ∈ K, Y x = 0)
    (hLi : ∃ x ∈ K, X i x = 0 ∧ Y x ≤ 1)
    (hUi : ∃ x ∈ K, X i x = 1 ∧ Y x ≤ 1)
    (hcap : ∀ x ∈ K, Y x < t → ∀ j, X j x ≤ h j) :
    a i * t ≤ b * t + (∑ j, a j * h j) - d := by
  let Y' := AffineMap.const ℝ E (1 : ℝ) - Y
  let X' := fun j => AffineMap.const ℝ E (1 : ℝ) - X j
  have hplane' (x : E) (hx : x ∈ K) :
      b * Y' x + ∑ j, a j * X' j x = b + (∑ j, a j) - d := by
    change b * (1 - Y x) + ∑ j, a j * (1 - X j x) = _
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib]
    linarith only [hplane x hx]
  have hUm' : ∃ x ∈ K, Y' x = 1 := by
    simpa [Y'] using hLm
  have hLi' : ∃ x ∈ K, X' i x = 0 ∧ 0 ≤ Y' x := by
    obtain ⟨p, hp, hpx, hpy⟩ := hUi
    exact ⟨p, hp, by simp [X', hpx], by simpa [Y'] using hpy⟩
  have hUi' : ∃ x ∈ K, X' i x = 1 ∧ 0 ≤ Y' x := by
    simpa [X', Y'] using hLi
  have hu := upper_gate_affine K hK Y' X' b a (b + (∑ j, a j) - d) hb ha hplane'
    i hai (fun j => 1 - h j) (1 - t) (sub_nonneg.mpr ht1) (by linarith only [ht0])
    hUm' hLi' hUi' (by
      intro x hx hxt j
      change 1 - t < 1 - Y x at hxt
      change 1 - h j ≤ 1 - X j x
      linarith only [hcap x hx (by linarith only [hxt]) j])
  calc
    a i * t = a i * (1 - (1 - t)) := by ring
    _ ≤ (b + (∑ j, a j) - d) - b * (1 - t) - ∑ j, a j * (1 - h j) := hu
    _ = b * t + (∑ j, a j * h j) - d := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib]
      ring

/-- Four contacts suffice for any finite family of opposite-cap constraints.
The chosen coordinate has maximal positive coefficient, and only its two
contacts need heights in `[0,1]`. No other coordinate ranges are assumed. -/
theorem width_bound_of_maximal_affine (K : Set E) (hK : Convex ℝ K)
    (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (b : ℝ) (a : ι → ℝ) (d : ℝ) (hb : 0 ≤ b) (ha : ∀ j, 0 ≤ a j)
    (hplane : ∀ x ∈ K, b * Y x + ∑ j, a j * X j x = d)
    (i : ι) (hai : 0 < a i) (hmax : ∀ j, a j ≤ a i)
    (l h : ι → ℝ) (lm hm : ℝ) (horder : ∀ j, l j ≤ h j) (hmorder : lm ≤ hm)
    (hlm : 0 < lm) (hhm : hm < 1)
    (hLm : ∃ x ∈ K, Y x = 0) (hUm : ∃ x ∈ K, Y x = 1)
    (hLi : ∃ x ∈ K, X i x = 0 ∧ 0 ≤ Y x ∧ Y x ≤ 1)
    (hUi : ∃ x ∈ K, X i x = 1 ∧ 0 ≤ Y x ∧ Y x ≤ 1)
    (hupper : ∀ x ∈ K, hm < Y x → ∀ j, l j ≤ X j x)
    (hlower : ∀ x ∈ K, Y x < lm → ∀ j, X j x ≤ h j) :
    1 ≤ hm - lm + ∑ j, (h j - l j) := by
  obtain ⟨Q, hQ, hQi, hQy⟩ := hLi
  obtain ⟨R, hR, hRi, hRy⟩ := hUi
  have hu := upper_gate_affine K hK Y X b a d hb ha hplane i hai l hm
    (hlm.le.trans hmorder) hhm hUm ⟨Q, hQ, hQi, hQy.1⟩ ⟨R, hR, hRi, hRy.1⟩ hupper
  have hl := lower_gate_affine K hK Y X b a d hb ha hplane i hai h lm
    hlm (hmorder.trans hhm.le) hLm ⟨Q, hQ, hQi, hQy.2⟩ ⟨R, hR, hRi, hRy.2⟩ hlower
  have hsum : (∑ j, a j * (h j - l j)) ≤ a i * ∑ j, (h j - l j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
      (hmax j) (sub_nonneg.2 (horder j))
  have hsum_eq : (∑ j, a j * (h j - l j)) = (∑ j, a j * h j) - ∑ j, a j * l j := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hbm := mul_nonneg hb (sub_nonneg.2 hmorder)
  have htotal : a i * 1 ≤ a i * (hm - lm + ∑ j, (h j - l j)) := by
    nlinarith only [hu, hl, hsum, hsum_eq, hbm]
  exact le_of_mul_le_mul_left htotal hai


/-! ### Coordinate interfaces -/

/-- The coordinate upper-gate interface. -/
theorem upper_gate (K : Set (κ → ℝ)) (hK : Convex ℝ K) (m : κ) (c : ι → κ)
    (b : ℝ) (a : ι → ℝ) (d : ℝ) (hb : 0 ≤ b) (ha : ∀ j, 0 ≤ a j)
    (hplane : ∀ x ∈ K, b * x m + ∑ j, a j * x (c j) = d)
    (i : ι) (hai : 0 < a i) (l : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hbox : ∀ x ∈ K, ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hUm : ∃ x ∈ K, x m = 1)
    (hLi : ∃ x ∈ K, x (c i) = 0) (hUi : ∃ x ∈ K, x (c i) = 1)
    (hcap : ∀ x ∈ K, t < x m → ∀ j, l j ≤ x (c j)) :
    a i * (1 - t) ≤ d - b * t - ∑ j, a j * l j := by
  exact upper_gate_affine K hK (AffineMap.proj m) (fun j => AffineMap.proj (c j))
    b a d hb ha hplane i hai l t ht0 ht1 hUm
    (by obtain ⟨x, hx, hxi⟩ := hLi; exact ⟨x, hx, hxi, (hbox x hx m).1⟩)
    (by obtain ⟨x, hx, hxi⟩ := hUi; exact ⟨x, hx, hxi, (hbox x hx m).1⟩) hcap

/-- The coordinate lower-gate interface. -/
theorem lower_gate (K : Set (κ → ℝ)) (hK : Convex ℝ K) (m : κ) (c : ι → κ)
    (b : ℝ) (a : ι → ℝ) (d : ℝ) (hb : 0 ≤ b) (ha : ∀ j, 0 ≤ a j)
    (hplane : ∀ x ∈ K, b * x m + ∑ j, a j * x (c j) = d)
    (i : ι) (hai : 0 < a i) (h : ι → ℝ) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hbox : ∀ x ∈ K, ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hLm : ∃ x ∈ K, x m = 0)
    (hLi : ∃ x ∈ K, x (c i) = 0) (hUi : ∃ x ∈ K, x (c i) = 1)
    (hcap : ∀ x ∈ K, x m < t → ∀ j, x (c j) ≤ h j) :
    a i * t ≤ b * t + (∑ j, a j * h j) - d := by
  exact lower_gate_affine K hK (AffineMap.proj m) (fun j => AffineMap.proj (c j))
    b a d hb ha hplane i hai h t ht0 ht1 hLm
    (by obtain ⟨x, hx, hxi⟩ := hLi; exact ⟨x, hx, hxi, (hbox x hx m).2⟩)
    (by obtain ⟨x, hx, hxi⟩ := hUi; exact ⟨x, hx, hxi, (hbox x hx m).2⟩) hcap

/-- The coordinate-family interface, allowing repeated indices. -/
theorem width_bound (K : Set (κ → ℝ)) (hK : Convex ℝ K) (m : κ) (c : ι → κ)
    (b : ℝ) (a : ι → ℝ) (d : ℝ) (hb : 0 ≤ b) (ha : ∀ j, 0 ≤ a j)
    (hpos : ∃ j, 0 < a j)
    (hplane : ∀ x ∈ K, b * x m + ∑ j, a j * x (c j) = d)
    (l h : ι → ℝ) (lm hm : ℝ) (horder : ∀ j, l j ≤ h j) (hmorder : lm ≤ hm)
    (hlm : 0 < lm) (hhm : hm < 1)
    (hbox : ∀ x ∈ K, ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hLm : ∃ x ∈ K, x m = 0) (hUm : ∃ x ∈ K, x m = 1)
    (hL : ∀ j, ∃ x ∈ K, x (c j) = 0) (hU : ∀ j, ∃ x ∈ K, x (c j) = 1)
    (hupper : ∀ x ∈ K, hm < x m → ∀ j, l j ≤ x (c j))
    (hlower : ∀ x ∈ K, x m < lm → ∀ j, x (c j) ≤ h j) :
    1 ≤ hm - lm + ∑ j, (h j - l j) := by
  obtain ⟨j, hj⟩ := hpos
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ a ⟨j, Finset.mem_univ j⟩
  have hai : 0 < a i := hj.trans_le (hmax j (Finset.mem_univ j))
  exact width_bound_of_maximal_affine K hK (AffineMap.proj m)
    (fun j => AffineMap.proj (c j)) b a d hb ha hplane i hai
    (fun j => hmax j (Finset.mem_univ j)) l h lm hm horder hmorder hlm hhm hLm hUm
    (by obtain ⟨x, hx, hxi⟩ := hL i; exact ⟨x, hx, hxi, hbox x hx m⟩)
    (by obtain ⟨x, hx, hxi⟩ := hU i; exact ⟨x, hx, hxi, hbox x hx m⟩) hupper hlower

end Plank.Convex.OppositeCapsWidth

/-- info: 'Plank.Convex.OppositeCapsWidth.upper_gate_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.OppositeCapsWidth.upper_gate_affine


/-- info: 'Plank.Convex.OppositeCapsWidth.lower_gate_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.OppositeCapsWidth.lower_gate_affine


/-- info: 'Plank.Convex.OppositeCapsWidth.width_bound_of_maximal_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.OppositeCapsWidth.width_bound_of_maximal_affine

/-- info: 'Plank.Convex.OppositeCapsWidth.upper_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.OppositeCapsWidth.upper_gate
/-- info: 'Plank.Convex.OppositeCapsWidth.lower_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.OppositeCapsWidth.lower_gate
/-- info: 'Plank.Convex.OppositeCapsWidth.width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.OppositeCapsWidth.width_bound
