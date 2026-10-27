/- Directional widths, extrema and reflection of affine values.
These facts do not require affine-combination or homothety estimates. -/
module

public import Plank.Convex.AffineRangeWidth
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

open Set Finset

namespace Plank.Body

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The width is read off a maximiser and a minimiser. -/
theorem width_eq_of_realisers {K : Set E} {f : E →ᵃ[ℝ] ℝ} {a b : E} (ha : a ∈ K)
    (hb : b ∈ K) (hamax : ∀ x ∈ K, f x ≤ f a) (hbmin : ∀ x ∈ K, f b ≤ f x) :
    width K f = f a - f b := by
  have h1 : IsGreatest (f '' K) (f a) :=
    ⟨⟨a, ha, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hamax x hx⟩
  have h2 : IsLeast (f '' K) (f b) :=
    ⟨⟨b, hb, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hbmin x hx⟩
  rw [width, h1.csSup_eq, h2.csInf_eq]

variable [TopologicalSpace E]

/-- A continuous functional attains its extremes on a compact body. -/
theorem exists_realisers {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {f : E →ᵃ[ℝ] ℝ} (hf : Continuous f) :
    ∃ a ∈ K, ∃ b ∈ K, (∀ x ∈ K, f x ≤ f a) ∧ (∀ x ∈ K, f b ≤ f x) := by
  obtain ⟨a, ha, hamax⟩ := hK.exists_isMaxOn hne hf.continuousOn
  obtain ⟨b, hb, hbmin⟩ := hK.exists_isMinOn hne hf.continuousOn
  exact ⟨a, ha, b, hb, fun x hx => hamax hx, fun x hx => hbmin hx⟩

/-- Two points of a compact body differ by at most its width. -/
theorem sub_le_width {K : Set E} (hK : IsCompact K) {f : E →ᵃ[ℝ] ℝ} (hf : Continuous f)
    {p q : E} (hp : p ∈ K) (hq : q ∈ K) : f p - f q ≤ width K f := by
  obtain ⟨a, ha, b, hb, hamax, hbmin⟩ := exists_realisers hK ⟨p, hp⟩ hf
  rw [width_eq_of_realisers ha hb hamax hbmin]
  linarith [hamax p hp, hbmin q hq]

/-- Reflecting affine values about any constant preserves their width. -/
theorem width_const_sub {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {f : E →ᵃ[ℝ] ℝ} (hf : Continuous f) (c : ℝ) :
    width K (AffineMap.const ℝ E c - f) = width K f := by
  obtain ⟨a, ha, b, hb, hamax, hbmin⟩ := exists_realisers hK hne hf
  rw [width_eq_of_realisers ha hb hamax hbmin,
    width_eq_of_realisers hb ha (fun x hx => sub_le_sub_left (hbmin x hx) c)
      (fun x hx => sub_le_sub_left (hamax x hx) c)]
  change (c - f b) - (c - f a) = f a - f b
  ring

/-- Reversing a direction does not change the width. -/
theorem width_neg {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {f : E →ᵃ[ℝ] ℝ}
    (hf : Continuous f) : width K (-f) = width K f := by
  have h0 : AffineMap.const ℝ E (0 : ℝ) = 0 := by ext x; rfl
  simpa only [h0, zero_sub] using width_const_sub hK hne hf 0

end Plank.Body
