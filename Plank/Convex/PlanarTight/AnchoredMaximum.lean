/- An anchored positive planar equality cover has a unique point on
the opposite supporting line. The contraction center is therefore fixed. -/
module
public import Plank.Convex.PlanarTight.AnchoredNoQuadrilateral
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Separation.Connected
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AnchoredMaximum

abbrev Point := Fin 3 → ℝ

/-- In the positive-plane normalization, the opposite face of an
anchored positive equality plank is a single point. No strict convexity
or nonempty-interior assumption is needed. -/
theorem subsingleton (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1) :
    ({z ∈ K | z 0 = 1} : Set Point).Subsingleton := by
  let r : ℝ := hi 0
  have hr : 0 < r := by simpa only [hanchor] using hwidth 0
  have hr₁ : r < 1 := by
    have hs := hsum
    rw [Fin.sum_univ_three, hanchor, sub_zero] at hs
    have h₁ := hwidth 1
    have h₂ := hwidth 2
    change hi 0 < 1
    linarith only [hs, h₁, h₂]
  have hd : 1 - r ≠ 0 := (sub_pos.mpr hr₁).ne'
  let M : Set Point := {z ∈ K | z 0 = 1}
  let Y (t : ℝ) : Set Point := {z ∈ M | r * z 1 = t}
  let Z (t : ℝ) : Set Point := {z ∈ M | r * z 2 = t}
  have hyfinite (t : ℝ) : (Y t).Finite := by
    apply Set.Subsingleton.finite
    intro x hx y hy
    have hx₀ : x 0 = 1 := hx.1.2
    have hy₀ : y 0 = 1 := hy.1.2
    have he₁ : x 1 = y 1 := mul_left_cancel₀ hr.ne' (hx.2.trans hy.2.symm)
    have hp := hplane x hx.1.1
    have hq := hplane y hy.1.1
    rw [hx₀] at hp
    rw [hy₀, ← he₁] at hq
    have he₂ : x 2 = y 2 := by nlinarith only [hp, hq, hc]
    funext i
    fin_cases i
    · exact hx₀.trans hy₀.symm
    · exact he₁
    · exact he₂
  have hzfinite (t : ℝ) : (Z t).Finite := by
    apply Set.Subsingleton.finite
    intro x hx y hy
    have hx₀ : x 0 = 1 := hx.1.2
    have hy₀ : y 0 = 1 := hy.1.2
    have he₂ : x 2 = y 2 := mul_left_cancel₀ hr.ne' (hx.2.trans hy.2.symm)
    have hp := hplane x hx.1.1
    have hq := hplane y hy.1.1
    rw [hx₀] at hp
    rw [hy₀, ← he₂] at hq
    have he₁ : x 1 = y 1 := by nlinarith only [hp, hq, hb]
    funext i
    fin_cases i
    · exact hx₀.trans hy₀.symm
    · exact he₁
    · exact he₂
  have lower (u y : ℝ) (he : (u - r * y) / (1 - r) = 0) : r * y = u := by
    have he' := (div_eq_zero_iff.mp he).resolve_right hd
    linarith only [he']
  have upper (u y : ℝ) (he : 1 - (u - r * y) / (1 - r) = 0) :
      r * y = u + r - 1 := by
    have he' : (u - r * y) / (1 - r) = 1 := by linarith only [he]
    have he'' := (div_eq_iff hd).mp he'
    nlinarith only [he'']
  have hMfinite : M.Finite := by
    apply (((hyfinite (lo 1)).union (hyfinite (hi 1 + r - 1))).union
      ((hzfinite (lo 2)).union (hzfinite (hi 2 + r - 1)))).subset
    intro T hT
    have hnormal := AnchoredNoQuadrilateral.two_plank_triangular K hK hbox hL hU a b c d
      ha hb hc hplane lo hi hwidth hanchor hcover hsum T hT.1 hT.2
    rcases hnormal with h | h | h | h
    · exact Or.inl (Or.inl ⟨hT, lower _ _ h.1⟩)
    · exact Or.inl (Or.inr ⟨hT, upper _ _ h.1⟩)
    · exact Or.inr (Or.inl ⟨hT, lower _ _ h.1⟩)
    · exact Or.inr (Or.inr ⟨hT, upper _ _ h.1⟩)
  have hface : Convex ℝ {z : Point | z 0 = 1} := by
    intro x hx y hy s t _ _ hst
    change s * x 0 + t * y 0 = 1
    rw [hx, hy, mul_one, mul_one]
    exact hst
  have hMconvex : Convex ℝ M := hK.inter hface
  by_contra hn
  exact hMfinite.not_infinite
    (hMconvex.isPreconnected.infinite_of_nontrivial (Set.not_subsingleton_iff.mp hn))

/-- The canonical contraction center exists and is unique. -/
theorem exists_unique (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1) :
    ∃! T, T ∈ K ∧ T 0 = 1 := by
  obtain ⟨T, hT, hT₀⟩ := hU 0
  exact ⟨T, ⟨hT, hT₀⟩, fun S hS =>
    subsingleton K hK hbox hL hU a b c d ha hb hc hplane lo hi hwidth hanchor hcover hsum
      hS ⟨hT, hT₀⟩⟩

end Plank.Convex.PlanarTight.AnchoredMaximum

/-- info: 'Plank.Convex.PlanarTight.AnchoredMaximum.subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredMaximum.subsingleton

/-- info: 'Plank.Convex.PlanarTight.AnchoredMaximum.exists_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredMaximum.exists_unique
