/- An explicit equality family when one of two planks is anchored at a
directional extremum. The body has the exact freedom of a triangular enclosure. -/
module
public import Plank.Convex.PlanarTight.CapTriangle
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TwoPlankBoundary

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Complete anchored two-plank equality normal form in attained unit
coordinates. The first window is `[0,g]`; the second and the permitted body
enclosure are parameterized by `c∈[0,1]`. No coverage or tightness condition
appears on the right. The coordinates may be dependent and the body need
not be compact or have interior. -/
theorem tight_iff (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ p ∈ K, (0 ≤ X p ∧ X p ≤ 1) ∧ (0 ≤ Y p ∧ Y p ≤ 1))
    (hX₁ : ∃ p ∈ K, X p = 1)
    (hY₀ : ∃ p ∈ K, Y p = 0) (hY₁ : ∃ p ∈ K, Y p = 1)
    (g l u : ℝ) (hg : 0 < g) (hg₁ : g < 1) (hl : 0 ≤ l) (hu : u ≤ 1) :
    (g + (u - l) = 1 ∧
      ∀ p ∈ K, (0 ≤ X p ∧ X p ≤ g) ∨ (l ≤ Y p ∧ Y p ≤ u)) ↔
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ l = g * c ∧ u = g * c + (1 - g) ∧
      (∀ p ∈ K, c * X p ≤ Y p ∧ Y p ≤ 1 - (1 - c) * X p) := by
  constructor
  · rintro ⟨hw, hcover⟩
    apply CapTriangle.upper K hK Y X (fun p hp => (hbox p hp).symm)
      hY₀ hY₁ hX₁ g l u hg hg₁ hl hu (by linarith only [hw])
    intro p hp hxg
    rcases hcover p hp with h | h
    · exact False.elim (not_lt_of_ge h.2 hxg)
    · exact h
  · rintro ⟨c, hc₀, hc₁, hlc, huc, hshape⟩
    refine ⟨by linarith only [hlc, huc], ?_⟩
    intro p hp
    by_cases hxg : X p ≤ g
    · exact Or.inl ⟨(hbox p hp).1.1, hxg⟩
    apply Or.inr
    obtain ⟨hleft, hright⟩ := hshape p hp
    have hdiff : 0 ≤ X p - g := sub_nonneg.mpr (le_of_not_ge hxg)
    constructor
    · nlinarith only [hleft, hlc, mul_nonneg hc₀ hdiff]
    · nlinarith only [hright, huc, mul_nonneg (sub_nonneg.mpr hc₁) hdiff]

end Plank.Convex.PlanarTight.TwoPlankBoundary

/-- info: 'Plank.Convex.PlanarTight.TwoPlankBoundary.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankBoundary.tight_iff
