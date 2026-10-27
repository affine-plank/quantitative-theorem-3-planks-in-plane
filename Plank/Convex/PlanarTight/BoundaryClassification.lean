/- All six boundary choices reduce to the explicit anchored families
by coordinate permutation and, for an upper endpoint, global reflection. -/
module
public import Plank.Convex.PlanarTight.AnchoredClassification
public import Plank.Convex.CubeSymmetry
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.BoundaryClassification

open CubeSymmetry (Point transform lower upper)

/-- The explicit anchored families, allowing every coordinate order
and a simultaneous reflection of the three coordinates and windows. -/
def Normal (K : Set Point) (lo hi : Point) : Prop :=
  ∃ (p : Equiv.Perm (Fin 3)) (flip : Bool), lower lo hi p flip 0 = 0 ∧
    AnchoredClassification.Normal (transform p flip '' K) (lower lo hi p flip) (upper lo hi p flip)

theorem transformed_iff (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ z ∈ K, ∑ i, A i * z i = D)
    (lo hi : Point) (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hwidth : ∀ i, lo i < hi i)
    (p : Equiv.Perm (Fin 3)) (flip : Bool) (hanchor : lower lo hi p flip 0 = 0) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i) ↔
      AnchoredClassification.Normal (transform p flip '' K)
        (lower lo hi p flip) (upper lo hi p flip) := by
  have hlo' : ∀ i, 0 ≤ lower lo hi p flip i := by
    intro i
    cases flip
    · exact hlo (p i)
    · exact sub_nonneg.mpr (hhi (p i))
  have hhi' : ∀ i, upper lo hi p flip i ≤ 1 := by
    intro i
    cases flip
    · exact hhi (p i)
    · change 1 - lo (p i) ≤ 1
      linarith only [hlo (p i)]
  have hwidth' : ∀ i, lower lo hi p flip i < upper lo hi p flip i := by
    intro i
    cases flip
    · exact hwidth (p i)
    · exact sub_lt_sub_left (hwidth (p i)) 1
  have ht := AnchoredClassification.tight_iff (transform p flip '' K)
    (CubeSymmetry.convex_image K hK p flip) (CubeSymmetry.box K p flip hbox)
    (CubeSymmetry.zero_contacts K p flip hL hU) (CubeSymmetry.unit_contacts K p flip hL hU)
    (A (p 0)) (A (p 1)) (A (p 2)) (if flip then (∑ i, A i) - D else D)
    (hA _) (hA _) (hA _) (by
      intro z hz
      simpa only [Fin.sum_univ_three] using CubeSymmetry.transformed_plane K A D hplane p flip z hz)
    (lower lo hi p flip) (upper lo hi p flip) hlo' hhi' hwidth' hanchor
  constructor
  · rintro ⟨hsum, hcover⟩
    apply ht.mp
    exact ⟨by simpa only [CubeSymmetry.width_sum] using hsum,
      CubeSymmetry.cover K lo hi p flip hcover⟩
  · intro hn
    obtain ⟨hsum, hcover⟩ := ht.mpr hn
    refine ⟨by simpa only [CubeSymmetry.width_sum] using hsum, ?_⟩
    intro z hz
    obtain ⟨i, hil, hiu⟩ := hcover (transform p flip z) ⟨z, hz, rfl⟩
    refine ⟨p i, ?_⟩
    cases flip
    · exact ⟨hil, hiu⟩
    · change 1 - hi (p i) ≤ 1 - z (p i) at hil
      change 1 - z (p i) ≤ 1 - lo (p i) at hiu
      exact ⟨by linarith only [hiu], by linarith only [hil]⟩

/-- Complete positive equality classification whenever at least one
window endpoint is on a support face. Its six choices are all included. -/
theorem tight_iff (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ z ∈ K, ∑ i, A i * z i = D)
    (lo hi : Point) (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hwidth : ∀ i, lo i < hi i) (hboundary : ∃ i, lo i = 0 ∨ hi i = 1) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i) ↔
      Normal K lo hi := by
  constructor
  · intro ht
    obtain ⟨i, h | h⟩ := hboundary
    · have he : lower lo hi (Equiv.swap 0 i) false 0 = 0 := by
        simpa only [lower, Equiv.swap_apply_left] using h
      exact ⟨Equiv.swap 0 i, false, he,
        (transformed_iff K hK hbox hL hU A D hA hplane lo hi hlo hhi hwidth _ _ he).mp ht⟩
    · have he : lower lo hi (Equiv.swap 0 i) true 0 = 0 := by
        simp only [lower, Equiv.swap_apply_left, h, sub_self]
      exact ⟨Equiv.swap 0 i, true, he,
        (transformed_iff K hK hbox hL hU A D hA hplane lo hi hlo hhi hwidth _ _ he).mp ht⟩
  · rintro ⟨p, flip, he, hn⟩
    exact (transformed_iff K hK hbox hL hU A D hA hplane lo hi hlo hhi hwidth p flip he).mpr hn

end Plank.Convex.PlanarTight.BoundaryClassification

/-- info: 'Plank.Convex.PlanarTight.BoundaryClassification.transformed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.BoundaryClassification.transformed_iff

/-- info: 'Plank.Convex.PlanarTight.BoundaryClassification.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.BoundaryClassification.tight_iff
