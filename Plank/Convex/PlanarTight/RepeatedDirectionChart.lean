/- Transport a repeated pair to its two actual planar coordinates. -/
module
public import Plank.Convex.PlanarTight.TwoDirectionUnclipped
public import Plank.Convex.ThreePlanarDirections
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.RepeatedDirectionChart

abbrev E := Fin 2 → ℝ
abbrev P := Fin 3 → ℝ
abbrev Forms := Fin 3 → E →ᵃ[ℝ] ℝ

def chart (f : Forms) : E →ᵃ[ℝ] E := ThreePlanarDirections.coordinateMap (f 0) (f 2) 1 1

@[simp] theorem chart_zero (f : Forms) (x : E) : chart f x 0 = f 0 x := by
  change 1 * f 0 x = f 0 x
  exact one_mul _

@[simp] theorem chart_one (f : Forms) (x : E) : chart f x 1 = f 2 x := by
  change 1 * f 2 x = f 2 x
  exact one_mul _

theorem interior_nonempty (K : Set E) (f : Forms) (hfull : (interior K).Nonempty)
    (hind : LinearIndependent ℝ ![(f 0).linear, (f 2).linear]) :
    (interior (chart f '' K)).Nonempty := by
  let e : E ≃ᵃ[ℝ] E := AffineEquiv.ofBijective
    (ThreePlanarDirections.coordinateMap_bijective (f 0) (f 2) hind 1 1 one_ne_zero one_ne_zero)
  change (interior ((e.toContinuousAffineEquiv).toHomeomorph '' K)).Nonempty
  rw [← (e.toContinuousAffineEquiv).toHomeomorph.image_interior]
  exact hfull.image _

theorem box (K : Set E) (f : Forms)
    (hb : ∀ x ∈ K, ∀ i, 0 ≤ f i x ∧ f i x ≤ 1) :
    ∀ z ∈ chart f '' K, ∀ j, 0 ≤ z j ∧ z j ≤ 1 := by
  rintro _ ⟨x, hx, rfl⟩ j
  fin_cases j
  · change 0 ≤ chart f x 0 ∧ chart f x 0 ≤ 1
    simpa only [chart_zero] using hb x hx 0
  · change 0 ≤ chart f x 1 ∧ chart f x 1 ≤ 1
    simpa only [chart_one] using hb x hx 2

theorem zero_contacts (K : Set E) (f : Forms)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) : ∀ j, ∃ z ∈ chart f '' K, z j = 0 := by
  intro j
  fin_cases j
  · obtain ⟨x, hx, he⟩ := hL 0
    refine ⟨chart f x, ⟨x, hx, rfl⟩, ?_⟩
    change chart f x 0 = 0
    simpa only [chart_zero] using he
  · obtain ⟨x, hx, he⟩ := hL 2
    refine ⟨chart f x, ⟨x, hx, rfl⟩, ?_⟩
    change chart f x 1 = 0
    simpa only [chart_one] using he

theorem unit_contacts (K : Set E) (f : Forms)
    (hU : ∀ i, ∃ x ∈ K, f i x = 1) : ∀ j, ∃ z ∈ chart f '' K, z j = 1 := by
  intro j
  fin_cases j
  · obtain ⟨x, hx, he⟩ := hU 0
    refine ⟨chart f x, ⟨x, hx, rfl⟩, ?_⟩
    change chart f x 0 = 1
    simpa only [chart_zero] using he
  · obtain ⟨x, hx, he⟩ := hU 2
    refine ⟨chart f x, ⟨x, hx, rfl⟩, ?_⟩
    change chart f x 1 = 1
    simpa only [chart_one] using he

theorem tight_iff (K : Set E) (f : Forms) (heq : f 0 = f 1) (lo hi : P) :
    TwoDirectionClassification.Tight (chart f '' K) (AffineMap.proj 0) (AffineMap.proj 1)
      (lo 0) (hi 0) (lo 1) (hi 1) (lo 2) (hi 2) ↔
      ((∑ i, (hi i - lo i)) = 1 ∧ ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) := by
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨by simpa only [Fin.sum_univ_three] using hs, ?_⟩
    intro x hx
    have h := hc (chart f x) ⟨x, hx, rfl⟩
    simp only [AffineMap.proj_apply, chart_zero, chart_one] at h
    rcases h with h | h | h
    · exact ⟨0, h⟩
    · rw [heq] at h
      exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨hs, hc⟩
    refine ⟨by simpa only [Fin.sum_univ_three] using hs, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    simp only [AffineMap.proj_apply, chart_zero, chart_one]
    obtain ⟨i, hi'⟩ := hc x hx
    fin_cases i
    · exact Or.inl hi'
    · change lo 1 ≤ f 1 x ∧ f 1 x ≤ hi 1 at hi'
      rw [← heq] at hi'
      exact Or.inr (Or.inl hi')
    · exact Or.inr (Or.inr hi')

end Plank.Convex.PlanarTight.RepeatedDirectionChart
