/- Positive pair separation from the standard finite affine separation theorem. -/
module
public import ResearchFormalized.Convex.FiniteAffineSeparation
public import Mathlib.Tactic.FieldSimp
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ConvexCellSeparation
open scoped BigOperators

/-- Two individually nonempty strict cuts force both separating weights to be
positive. Normalize the first weight to obtain a positive separating slope. -/
theorem exists_pos_separator {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (hK : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (hp : ∃ p ∈ K, 0 < g p) (hq : ∃ q ∈ K, 0 < h q)
    (he : ¬ ∃ x ∈ K, 0 < g x ∧ 0 < h x) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, g x+a*h x ≤ 0 := by
  obtain ⟨m, hm, hsum, hs⟩ := ResearchFormalized.FiniteAffineSeparation.exists_weights
    K hK (![g,h] : Fin 2 → E →ᵃ[ℝ] ℝ)
    (fun ⟨x, hx, hp⟩ => he ⟨x, hx, hp 0, hp 1⟩)
  have hsum : m 0 + m 1 = 1 := by simpa [Fin.sum_univ_two] using hsum
  have hs (x : E) (hx : x ∈ K) : m 0*g x + m 1*h x ≤ 0 := by
    simpa [Fin.sum_univ_two] using hs x hx
  obtain ⟨p, hp, hgp⟩ := hp
  obtain ⟨q, hq, hhq⟩ := hq
  have h0 : 0 < m 0 := by
    by_contra! hn
    have hz : m 0 = 0 := le_antisymm hn (hm 0)
    have ho : m 1 = 1 := by linarith only [hsum, hz]
    have h := hs q hq
    simp only [hz, ho, zero_mul, one_mul, zero_add] at h
    linarith only [hhq, h]
  have h1 : 0 < m 1 := by
    by_contra! hn
    have hz : m 1 = 0 := le_antisymm hn (hm 1)
    have ho : m 0 = 1 := by linarith only [hsum, hz]
    have h := hs p hp
    simp only [hz, ho, zero_mul, one_mul, add_zero] at h
    linarith only [hgp, h]
  refine ⟨m 1 / m 0, div_pos h1 h0, fun x hx => ?_⟩
  have h := div_nonpos_of_nonpos_of_nonneg (hs x hx) h0.le
  convert h using 1
  field_simp [h0.ne']

/-- Positive witnesses for both cuts force both separator coefficients positive. -/
theorem positive_support {E : Type*} [AddCommGroup E] [Module ℝ E] (K : Set E) (hv : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (u v : ℝ) (hp : ∃ p ∈ K, u < g p) (hq : ∃ q ∈ K, v < h q)
    (hcap : ¬ ∃ x ∈ K, u < g x ∧ v < h x) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, g x + a * h x ≤ u + a * v := by
  obtain ⟨p, hp, hgp⟩ := hp
  obtain ⟨q, hq, hhq⟩ := hq
  obtain ⟨a, ha, hs⟩ := exists_pos_separator K hv
    (g - AffineMap.const ℝ E u) (h - AffineMap.const ℝ E v)
    ⟨p, hp, sub_pos.mpr hgp⟩ ⟨q, hq, sub_pos.mpr hhq⟩
    (fun ⟨x, hx, h1, h2⟩ => hcap ⟨x, hx, sub_pos.mp h1, sub_pos.mp h2⟩)
  refine ⟨a, ha, fun x hx => ?_⟩
  have hh : g x - u + a * (h x - v) ≤ 0 := hs x hx
  nlinarith only [hh]


end Plank.Convex.ConvexCellSeparation
