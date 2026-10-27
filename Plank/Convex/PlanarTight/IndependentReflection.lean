/- Independent coordinate reflections preserve exact windows and orient a plane positively. -/
module
public import Plank.Convex.AffineWindowOrientation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.IndependentReflection

abbrev Point := Fin 3 → ℝ

def reflection (flip : Fin 3 → Bool) : Point →ᵃ[ℝ] Point :=
  AffineMap.pi (OrientedCommonChord.coordinates flip (fun i => AffineMap.proj i))

theorem reflection_apply (flip : Fin 3 → Bool) (x : Point) (i : Fin 3) :
    reflection flip x i = if flip i then 1 - x i else x i := by
  cases hf : flip i <;> simp [reflection, OrientedCommonChord.coordinates, hf,
    TwoPlankClassification.reflect]

theorem box (K : Set Point) (flip : Fin 3 → Bool)
    (hb : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∀ z ∈ reflection flip '' K, ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
  rintro _ ⟨x, hx, rfl⟩ i
  exact OrientedCommonChord.box flip (fun j => AffineMap.proj j) x i (hb x hx i)

theorem zero_contacts (K : Set Point) (flip : Fin 3 → Bool)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1) :
    ∀ i, ∃ z ∈ reflection flip '' K, z i = 0 := by
  intro i
  cases hf : flip i
  · obtain ⟨x, hx, he⟩ := hL i
    exact ⟨reflection flip x, ⟨x, hx, rfl⟩, by simp only [reflection_apply, hf, Bool.false_eq_true,
      ↓reduceIte, he]⟩
  · obtain ⟨x, hx, he⟩ := hU i
    exact ⟨reflection flip x, ⟨x, hx, rfl⟩, by simp only [reflection_apply, hf, ↓reduceIte, he,
      sub_self]⟩

theorem unit_contacts (K : Set Point) (flip : Fin 3 → Bool)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1) :
    ∀ i, ∃ z ∈ reflection flip '' K, z i = 1 := by
  intro i
  cases hf : flip i
  · obtain ⟨x, hx, he⟩ := hU i
    exact ⟨reflection flip x, ⟨x, hx, rfl⟩, by simp only [reflection_apply, hf, Bool.false_eq_true,
      ↓reduceIte, he]⟩
  · obtain ⟨x, hx, he⟩ := hL i
    exact ⟨reflection flip x, ⟨x, hx, rfl⟩, by simp only [reflection_apply, hf, ↓reduceIte, he,
      sub_zero]⟩

theorem ordered (flip : Fin 3 → Bool) (lo hi : Point) (ho : ∀ i, lo i ≤ hi i) :
    ∀ i, OrientedCommonChord.lower flip lo hi i ≤ OrientedCommonChord.upper flip lo hi i := by
  intro i
  cases hf : flip i <;> simp only [OrientedCommonChord.lower, OrientedCommonChord.upper, hf,
    Bool.false_eq_true, ↓reduceIte]
  · exact ho i
  · exact sub_le_sub_left (ho i) 1

theorem cover_iff (K : Set Point) (flip : Fin 3 → Bool) (lo hi : Point) :
    (∀ z ∈ reflection flip '' K, ∃ i, OrientedCommonChord.lower flip lo hi i ≤ z i ∧
      z i ≤ OrientedCommonChord.upper flip lo hi i) ↔
      (∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) := by
  constructor
  · intro h x hx
    obtain ⟨i, hi⟩ := h (reflection flip x) ⟨x, hx, rfl⟩
    exact ⟨i, (OrientedCommonChord.window_iff flip (fun j => AffineMap.proj j) lo _ x i).mp hi⟩
  · rintro h _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := h x hx
    exact ⟨i, (OrientedCommonChord.window_iff flip (fun j => AffineMap.proj j) lo _ x i).mpr hi⟩

/-- Reflect negative coefficients to make the normal nonnegative. Zero
coefficients are allowed, and the body and windows are transformed exactly. -/
theorem orient_plane (K : Set Point) (a : Point) (d : ℝ)
    (hp : ∀ x ∈ K, ∑ i, a i * x i = d) :
    ∃ (flip : Fin 3 → Bool) (D : ℝ),
      ∀ z ∈ reflection flip '' K, ∑ i, |a i| * z i = D := by
  let flip : Fin 3 → Bool := fun i => decide (a i < 0)
  let c : Point := fun i => if a i < 0 then -a i else 0
  refine ⟨flip, d + ∑ i, c i, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have he (i : Fin 3) : |a i| * reflection flip x i = a i * x i + c i := by
    by_cases hn : a i < 0
    · simp only [reflection_apply, flip, hn, decide_true,
        ↓reduceIte, abs_of_neg hn, c]
      ring
    · simp only [reflection_apply, flip, hn, decide_false,
        Bool.false_eq_true, ↓reduceIte, abs_of_nonneg (le_of_not_gt hn), c, add_zero]
  simp only [he, Finset.sum_add_distrib, hp x hx]

/-- A plane with three nonzero coefficients can be oriented so all three
coefficients are strictly positive. The body is reflected exactly. -/
theorem positive_plane (K : Set Point) (a : Point) (d : ℝ) (ha : ∀ i, a i ≠ 0)
    (hp : ∀ x ∈ K, ∑ i, a i * x i = d) :
    ∃ (flip : Fin 3 → Bool) (A : Point) (D : ℝ), (∀ i, 0 < A i) ∧
      ∀ z ∈ reflection flip '' K, ∑ i, A i * z i = D := by
  obtain ⟨flip, D, hp'⟩ := orient_plane K a d hp
  exact ⟨flip, fun i => |a i|, D, fun i => abs_pos.mpr (ha i), hp'⟩

end Plank.Convex.PlanarTight.IndependentReflection

/-- info: 'Plank.Convex.PlanarTight.IndependentReflection.cover_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.IndependentReflection.cover_iff

/-- info: 'Plank.Convex.PlanarTight.IndependentReflection.positive_plane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.IndependentReflection.positive_plane
