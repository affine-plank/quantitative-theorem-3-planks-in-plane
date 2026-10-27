/- Compactness sharpens a positive pair separator when its corner misses the body. -/
module
public import Plank.Convex.ConvexCellSeparation
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Plank.Convex.CompactPairSeparation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive witnesses for both cuts force both separator coefficients positive. -/
theorem positive_support (K : Set E) (hv : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (u v : ℝ) (hp : ∃ p ∈ K, u < g p) (hq : ∃ q ∈ K, v < h q)
    (hcap : ¬ ∃ x ∈ K, u < g x ∧ v < h x) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, g x + a * h x ≤ u + a * v := by
  exact ConvexCellSeparation.positive_support K hv g h u v hp hq hcap

/-- If the strict upper quadrant and its corner both miss a compact convex set,
a positive separator leaves a uniform strict margin at the corner. -/
theorem strict_support_of_no_corner (K : Set E) (hc : IsCompact K)
    (hv : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ) (hg : Continuous g) (hh : Continuous h)
    (u v : ℝ) (hp : ∃ p ∈ K, u < g p) (hq : ∃ q ∈ K, v < h q)
    (hcap : ¬ ∃ x ∈ K, u < g x ∧ v < h x)
    (hcorner : ¬ ∃ x ∈ K, g x = u ∧ h x = v) :
    ∃ a : ℝ, 0 < a ∧ ∃ c < u + a * v, ∀ x ∈ K, g x + a * h x ≤ c := by
  obtain ⟨a, ha, hs⟩ :=
    positive_support K hv g h u v hp hq hcap
  let gap : E → ℝ := fun x => max (u - g x) (v - h x)
  have hgap (x : E) (hx : x ∈ K) : 0 < gap x := by
    by_contra hn
    have hg0 : u ≤ g x := by have := (le_max_left (u - g x) (v - h x)).trans
                                              (le_of_not_gt hn); dsimp [gap] at *; linarith
    have hh0 : v ≤ h x := by have := (le_max_right (u - g x) (v - h x)).trans
                                              (le_of_not_gt hn); dsimp [gap] at *; linarith
    have hp0 := mul_nonneg ha.le (sub_nonneg.mpr hh0)
    have hgs : g x = u := by have := hs x hx; nlinarith only [this, hg0, hp0]
    have hhs : h x = v := by have := hs x hx; nlinarith only [this, hgs, hh0, ha]
    exact hcorner ⟨x, hx, hgs, hhs⟩
  have hcont : Continuous gap := (continuous_const.sub hg).max (continuous_const.sub hh)
  obtain ⟨z, hz, hmin⟩ := hc.exists_isMinOn (by obtain ⟨p, hp, _⟩ := hp; exact ⟨p, hp⟩)
    hcont.continuousOn
  let e := gap z / 2
  have he : 0 < e := half_pos (hgap z hz)
  have hcap' : ¬ ∃ x ∈ K, u - e < g x ∧ v - e < h x := by
    rintro ⟨x, hx, hgx, hhx⟩
    have hlt : gap x < e := max_lt (by linarith only [hgx]) (by linarith only [hhx])
    have hle : gap z ≤ gap x := hmin hx
    dsimp [e] at hlt he
    linarith only [hlt, hle, he]
  obtain ⟨b, hb, hs'⟩ :=
    positive_support K hv g h (u-e) (v-e)
      (by obtain ⟨p, hp, hgp⟩ := hp; exact ⟨p, hp, by linarith only [hgp, he]⟩)
      (by obtain ⟨q, hq, hhq⟩ := hq; exact ⟨q, hq, by linarith only [hhq, he]⟩) hcap'
  exact ⟨b, hb, (u-e)+b*(v-e), by nlinarith only [he, mul_pos hb he], hs'⟩

/-- Choose a support tight at the prescribed corner exactly when that corner meets the body. -/
theorem support_with_contact (K : Set E) (hc : IsCompact K)
    (hv : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ) (hg : Continuous g) (hh : Continuous h)
    (u v : ℝ) (hp : ∃ p ∈ K, u < g p) (hq : ∃ q ∈ K, v < h q)
    (hcap : ¬ ∃ x ∈ K, u < g x ∧ v < h x) :
    ∃ a : ℝ, 0 < a ∧ ∃ c : ℝ, c ≤ u + a * v ∧
      (c = u + a * v ↔ ∃ x ∈ K, g x = u ∧ h x = v) ∧
      ∀ x ∈ K, g x + a * h x ≤ c := by
  by_cases hcorner : ∃ x ∈ K, g x = u ∧ h x = v
  · obtain ⟨a, ha, hs⟩ := positive_support K hv g h u v hp hq hcap
    exact ⟨a, ha, _, le_rfl, ⟨fun _ => hcorner, fun _ => rfl⟩, hs⟩
  · obtain ⟨a, ha, c, hlt, hs⟩ := strict_support_of_no_corner K hc hv g h hg hh u v hp hq hcap hcorner
    exact ⟨a, ha, c, hlt.le, ⟨fun he => (hlt.ne he).elim, fun h => (hcorner h).elim⟩, hs⟩

end Plank.Convex.CompactPairSeparation
