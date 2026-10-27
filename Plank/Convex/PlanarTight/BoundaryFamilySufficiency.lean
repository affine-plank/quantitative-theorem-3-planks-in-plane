/- The displayed boundary families give tight covers without extra endpoint hypotheses. -/
module
public import Plank.Convex.PlanarTight.BoundaryClassification
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight
open CubeSymmetry (Point transform lower upper)

theorem AnchoredClassification.Normal.tight (K : Set Point)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (lo hi : Point) (h : AnchoredClassification.Normal K lo hi) :
    (∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i := by
  rcases h with h | h
  · obtain ⟨T, r, l, u, m, v, hcap, hr, hr₁, hl, hu, hm, hv, hlu, hmv, heL, heU, hn⟩ := h
    obtain ⟨hT₀, A, B, hA₀, hB₀, hbody⟩ := hcap
    rw [heL, heU]
    exact (TriangleContraction.tight_iff K T A B hbody hT₀ hA₀ hB₀ hbox hL hU
      r l u m v hr hr₁ hl hu hm hv hlu hmv).mpr hn
  · exact OrientedCommonChord.Normal.tight K (fun i => AffineMap.proj i) hbox lo hi h

theorem BoundaryClassification.Normal.tight (K : Set Point)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (lo hi : Point) (h : BoundaryClassification.Normal K lo hi) :
    (∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i := by
  obtain ⟨p, flip, _, hn⟩ := h
  obtain ⟨hsum, hcover⟩ := AnchoredClassification.Normal.tight (transform p flip '' K)
    (CubeSymmetry.box K p flip hbox) (CubeSymmetry.zero_contacts K p flip hL hU)
    (CubeSymmetry.unit_contacts K p flip hL hU) (lower lo hi p flip) (upper lo hi p flip) hn
  refine ⟨by simpa only [CubeSymmetry.width_sum] using hsum, ?_⟩
  intro z hz
  obtain ⟨i, hil, hiu⟩ := hcover (transform p flip z) ⟨z, hz, rfl⟩
  refine ⟨p i, ?_⟩
  cases flip
  · exact ⟨hil, hiu⟩
  · change 1 - hi (p i) ≤ 1 - z (p i) at hil
    change 1 - z (p i) ≤ 1 - lo (p i) at hiu
    exact ⟨by linarith only [hiu], by linarith only [hil]⟩

end Plank.Convex.PlanarTight

/-- info: 'Plank.Convex.PlanarTight.BoundaryClassification.Normal.tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.BoundaryClassification.Normal.tight
