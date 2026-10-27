/- A boundary window transfers a covering bound from any finite affine
family to that family with one additional window. A contact homothety
handles the lower boundary; reflection handles the upper boundary. -/
module
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.AffineBoundaryWindows

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- A lower boundary window can be added to any finite family whose covers
already have total width at least one. Only a lower height bound and one
upper contact are needed. -/
theorem width_bound_of_lower_boundary (K : Set E) (hK : Convex ℝ K)
    (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (hY : ∀ x ∈ K, 0 ≤ Y x) (A : E) (hA : A ∈ K) (hYA : Y A = 1)
    (hcore : ∀ l h : ι → ℝ, (∀ j, l j ≤ h j) →
      (∀ x ∈ K, ∃ j, l j ≤ X j x ∧ X j x ≤ h j) →
      1 ≤ ∑ j, (h j - l j))
    (b : ℝ) (hb : 0 ≤ b) (lo hi : ι → ℝ) (horder : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, Y x ≤ b ∨ ∃ j, lo j ≤ X j x ∧ X j x ≤ hi j) :
    1 ≤ b + ∑ j, (hi j - lo j) := by
  by_contra hn
  have hdef : b + ∑ j, (hi j - lo j) < 1 := lt_of_not_ge hn
  let C := ∑ j, (hi j - lo j)
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => sub_nonneg.mpr (horder j)
  obtain ⟨t, hbt, htC⟩ := exists_between (show b < 1 - C by dsimp [C]; linarith only [hdef])
  have ht0 : 0 ≤ t := (hb.trans_lt hbt).le
  have ht1 : t < 1 := by linarith only [htC, hC]
  have hscale : 0 < 1 - t := sub_pos.mpr ht1
  let l := fun j => (lo j - t * X j A) / (1 - t)
  let h := fun j => (hi j - t * X j A) / (1 - t)
  have hresidual : ∀ x ∈ K, ∃ j, l j ≤ X j x ∧ X j x ≤ h j := by
    intro x hx
    let y := AffineMap.lineMap x A t
    have hy : y ∈ K := hK.lineMap_mem hx hA ⟨ht0, ht1.le⟩
    have hmap (f : E →ᵃ[ℝ] ℝ) : f y = (1 - t) * f x + t * f A := by
      simp only [y, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
    have havoid : b < Y y := by
      rw [hmap, hYA]
      have hh := mul_nonneg hscale.le (hY x hx)
      nlinarith only [hbt, hh]
    obtain ⟨j, hj0, hj1⟩ := (hcover y hy).resolve_left (not_le.mpr havoid)
    rw [hmap] at hj0 hj1
    refine ⟨j, ?_, ?_⟩
    · exact (div_le_iff₀ hscale).mpr (by nlinarith only [hj0])
    · exact (le_div_iff₀ hscale).mpr (by nlinarith only [hj1])
  have hbound := hcore l h (fun j =>
    div_le_div_of_nonneg_right (sub_le_sub_right (horder j) _) hscale.le) hresidual
  have hcost (j : ι) : h j - l j = (hi j - lo j) / (1 - t) := by
    dsimp [h, l]
    ring
  simp_rw [hcost] at hbound
  rw [← Finset.sum_div] at hbound
  have hCbig : 1 - t ≤ C := by
    simpa only [one_mul, C] using (le_div_iff₀ hscale).mp hbound
  linarith only [hCbig, htC]

/-- The upper boundary case follows by reflecting the height. -/
theorem width_bound_of_upper_boundary (K : Set E) (hK : Convex ℝ K)
    (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (hY : ∀ x ∈ K, Y x ≤ 1) (A : E) (hA : A ∈ K) (hYA : Y A = 0)
    (hcore : ∀ l h : ι → ℝ, (∀ j, l j ≤ h j) →
      (∀ x ∈ K, ∃ j, l j ≤ X j x ∧ X j x ≤ h j) →
      1 ≤ ∑ j, (h j - l j))
    (a : ℝ) (ha : a ≤ 1) (lo hi : ι → ℝ) (horder : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, a ≤ Y x ∨ ∃ j, lo j ≤ X j x ∧ X j x ≤ hi j) :
    1 ≤ 1 - a + ∑ j, (hi j - lo j) := by
  apply width_bound_of_lower_boundary K hK (AffineMap.const ℝ E (1 : ℝ) - Y) X
    (fun x hx => by change 0 ≤ 1 - Y x; exact sub_nonneg.mpr (hY x hx))
    A hA (by change 1 - Y A = 1; rw [hYA, sub_zero]) hcore
    (1 - a) (sub_nonneg.mpr ha) lo hi horder
  intro x hx
  rcases hcover x hx with h | h
  · exact Or.inl (show 1 - Y x ≤ 1 - a from sub_le_sub_left h 1)
  · exact Or.inr h

/-- An ordered window reaching either endpoint of the normalized height
range preserves a known covering bound for the remaining affine coordinates. -/
theorem width_bound (K : Set E) (hK : Convex ℝ K)
    (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (hY : ∀ x ∈ K, 0 ≤ Y x ∧ Y x ≤ 1)
    (hY0 : ∃ x ∈ K, Y x = 0) (hY1 : ∃ x ∈ K, Y x = 1)
    (hcore : ∀ l h : ι → ℝ, (∀ j, l j ≤ h j) →
      (∀ x ∈ K, ∃ j, l j ≤ X j x ∧ X j x ≤ h j) →
      1 ≤ ∑ j, (h j - l j))
    (a b : ℝ) (hab : a ≤ b) (lo hi : ι → ℝ) (horder : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, (a ≤ Y x ∧ Y x ≤ b) ∨
      ∃ j, lo j ≤ X j x ∧ X j x ≤ hi j)
    (hboundary : a = 0 ∨ b = 1) :
    1 ≤ b - a + ∑ j, (hi j - lo j) := by
  rcases hboundary with rfl | rfl
  · obtain ⟨A, hA, hYA⟩ := hY1
    simpa only [sub_zero] using width_bound_of_lower_boundary K hK Y X
      (fun x hx => (hY x hx).1) A hA hYA hcore b hab lo hi horder
      (fun x hx => (hcover x hx).imp (fun h => h.2) id)
  · obtain ⟨A, hA, hYA⟩ := hY0
    exact width_bound_of_upper_boundary K hK Y X
      (fun x hx => (hY x hx).2) A hA hYA hcore a hab lo hi horder
      (fun x hx => (hcover x hx).imp (fun h => h.1) id)

end Plank.Convex.AffineBoundaryWindows

/-- info: 'Plank.Convex.AffineBoundaryWindows.width_bound_of_lower_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.AffineBoundaryWindows.width_bound_of_lower_boundary

/-- info: 'Plank.Convex.AffineBoundaryWindows.width_bound_of_upper_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.AffineBoundaryWindows.width_bound_of_upper_boundary

/-- info: 'Plank.Convex.AffineBoundaryWindows.width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.AffineBoundaryWindows.width_bound
