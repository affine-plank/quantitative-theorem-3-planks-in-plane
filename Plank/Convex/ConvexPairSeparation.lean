/- Unit-range adapters for the shared two-cut separator. -/
module
public import Plank.Convex.ConvexPairSupport
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ConvexCellSeparation
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The mixed-cap form of positive pair separation, with unit-range witnesses. -/
theorem exists_slope (K : Set E) (hK : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (hi lo : ℝ) (hhi : hi < 1) (hlo : 0 < lo)
    (p q : E) (hp : p ∈ K) (hq : q ∈ K) (hgp : g p = 1) (hhq : h q = 0)
    (he : ¬ ∃ x ∈ K, hi < g x ∧ h x < lo) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, a * g x + (lo - a * hi) ≤ h x := by
  obtain ⟨a, ha, har⟩ := exists_pos_pair K hK
    (AffineMap.const ℝ E lo - h) (g - AffineMap.const ℝ E hi) q p hq hp
    (by change 0 < lo - h q; simpa only [hhq, sub_zero] using hlo)
    (by change 0 < g p - hi; rw [hgp]; exact sub_pos.mpr hhi)
    (fun ⟨x, hx, hh, hg⟩ => he ⟨x, hx, sub_pos.mp hg, sub_pos.mp hh⟩)
  refine ⟨a, ha, fun x hx => ?_⟩
  have hr := har x hx
  change lo - h x + a * (g x - hi) ≤ 0 at hr
  nlinarith only [hr]

/-- An empty upper pair cap has a positive weighted upper support. -/
theorem exists_upper_support (K : Set E) (hK : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (u v : ℝ) (hu : u < 1) (hv : v < 1)
    (hg : ∃ p ∈ K, g p = 1) (hh : ∃ q ∈ K, h q = 1)
    (he : ¬ ∃ x ∈ K, u < g x ∧ v < h x) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, g x + a * h x ≤ u + a * v := by
  apply positive_support K hK g h u v ?_ ?_ he
  · obtain ⟨p, hp, hgp⟩ := hg
    exact ⟨p, hp, by rw [hgp]; exact hu⟩
  · obtain ⟨q, hq, hhq⟩ := hh
    exact ⟨q, hq, by rw [hhq]; exact hv⟩

/-- An empty lower pair cap has a positive weighted lower support. -/
theorem exists_lower_support (K : Set E) (hK : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hg : ∃ p ∈ K, g p = 0) (hh : ∃ q ∈ K, h q = 0)
    (he : ¬ ∃ x ∈ K, g x < u ∧ h x < v) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, u + a * v ≤ g x + a * h x := by
  obtain ⟨a, ha, hs⟩ := positive_support K hK (-g) (-h) (-u) (-v)
    (by obtain ⟨p, hp, hgp⟩ := hg; exact ⟨p, hp, by change -u < -g p; rw [hgp]; linarith⟩)
    (by obtain ⟨q, hq, hhq⟩ := hh; exact ⟨q, hq, by change -v < -h q; rw [hhq]; linarith⟩)
    (by simpa using he)
  refine ⟨a, ha, fun x hx => ?_⟩
  have H : -g x + a * -h x ≤ -u + a * -v := hs x hx
  linarith only [H]

/-- An empty mixed pair cap has a positive weighted difference support. -/
theorem exists_mixed_support (K : Set E) (hK : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (u v : ℝ) (hu : u < 1) (hv : 0 < v)
    (hg : ∃ p ∈ K, g p = 1) (hh : ∃ q ∈ K, h q = 0)
    (he : ¬ ∃ x ∈ K, u < g x ∧ h x < v) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, g x - a * h x ≤ u - a * v := by
  obtain ⟨a, ha, hs⟩ := positive_support K hK g (-h) u (-v)
    (by obtain ⟨p, hp, hgp⟩ := hg; exact ⟨p, hp, by rw [hgp]; exact hu⟩)
    (by obtain ⟨q, hq, hhq⟩ := hh; exact ⟨q, hq, by change -v < -h q; rw [hhq]; linarith⟩)
    (by simpa using he)
  refine ⟨a, ha, fun x hx => ?_⟩
  have H : g x + a * -h x ≤ u + a * -v := hs x hx
  linarith only [H]


end Plank.Convex.ConvexCellSeparation

/-- info: 'Plank.Convex.ConvexCellSeparation.exists_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexCellSeparation.exists_slope

/-- info: 'Plank.Convex.ConvexCellSeparation.exists_upper_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexCellSeparation.exists_upper_support

/-- info: 'Plank.Convex.ConvexCellSeparation.exists_lower_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexCellSeparation.exists_lower_support

/-- info: 'Plank.Convex.ConvexCellSeparation.exists_mixed_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexCellSeparation.exists_mixed_support
