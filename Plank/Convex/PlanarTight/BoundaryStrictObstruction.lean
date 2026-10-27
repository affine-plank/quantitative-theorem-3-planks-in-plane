/- A positive tight cover with a support endpoint excludes every
strict cover of the same normalized body in the same three directions. -/
module
public import Plank.Convex.PlanarTight.AnchoredCapClassification
public import Plank.Convex.PlanarTight.TriangleStrictCover
public import Plank.Convex.CubeSymmetry
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.BoundaryStrictObstruction

open CubeSymmetry (Point transform lower upper)

theorem anchored_not_strict (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (glo ghi : Point) (hgl : ∀ i, 0 < glo i) (hgh : ∀ i, ghi i < 1) :
    ¬ ∀ z ∈ K, ∃ i, glo i ≤ z i ∧ z i ≤ ghi i := by
  intro hgcover
  obtain ⟨T, hT, hT₀⟩ := hU 0
  rcases AnchoredCapClassification.cap_or_opposite_vertices K hK hbox hL hU
      a b c d ha hb hc hplane lo hi hwidth hanchor hcover hsum T hT hT₀ with hcap | hchord
  · exact TriangleStrictCover.cap_not_cover K hK T hcap hbox hL hU glo ghi hgl hgh hgcover
  · obtain ⟨A, hA, _, _, hv, _⟩ := hchord
    obtain ⟨i, hil, hiu⟩ := hgcover A hA
    rcases hv i with h | h
    · have hpos := hgl i
      linarith only [h, hil, hpos]
    · have hlt := hgh i
      linarith only [h, hiu, hlt]

/-- All six support-endpoint choices are incompatible with a strict
cover in the same directions, regardless of that strict cover's width sum. -/
theorem boundary_not_strict (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ z ∈ K, ∑ i, A i * z i = D)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1) (hboundary : ∃ i, lo i = 0 ∨ hi i = 1)
    (glo ghi : Point) (hgl : ∀ i, 0 < glo i) (hgh : ∀ i, ghi i < 1) :
    ¬ ∀ z ∈ K, ∃ i, glo i ≤ z i ∧ z i ≤ ghi i := by
  intro hgcover
  have impossible (p : Equiv.Perm (Fin 3)) (flip : Bool)
      (he : lower lo hi p flip 0 = 0) : False := by
    have hw : ∀ i, lower lo hi p flip i < upper lo hi p flip i := by
      intro i
      cases flip
      · exact hwidth (p i)
      · exact sub_lt_sub_left (hwidth (p i)) 1
    have hs := CubeSymmetry.strict glo ghi p flip (fun i => ⟨hgl i, hgh i⟩)
    apply anchored_not_strict (transform p flip '' K)
      (CubeSymmetry.convex_image K hK p flip) (CubeSymmetry.box K p flip hbox)
      (CubeSymmetry.zero_contacts K p flip hL hU) (CubeSymmetry.unit_contacts K p flip hL hU)
      (A (p 0)) (A (p 1)) (A (p 2)) (if flip then (∑ i, A i) - D else D)
      (hA _) (hA _) (hA _) (by
        intro z hz
        simpa only [Fin.sum_univ_three] using CubeSymmetry.transformed_plane K A D hplane p flip z hz)
      (lower lo hi p flip) (upper lo hi p flip) hw he
      (CubeSymmetry.cover K lo hi p flip hcover)
      (by simpa only [CubeSymmetry.width_sum] using hsum)
      (lower glo ghi p flip) (upper glo ghi p flip) (fun i => (hs i).1) (fun i => (hs i).2)
    exact CubeSymmetry.cover K glo ghi p flip hgcover
  obtain ⟨i, h | h⟩ := hboundary
  · apply impossible (Equiv.swap 0 i) false
    simpa only [lower, Equiv.swap_apply_left] using h
  · apply impossible (Equiv.swap 0 i) true
    simp only [lower, Equiv.swap_apply_left, h, sub_self]

end Plank.Convex.PlanarTight.BoundaryStrictObstruction

/-- info: 'Plank.Convex.PlanarTight.BoundaryStrictObstruction.anchored_not_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.BoundaryStrictObstruction.anchored_not_strict

/-- info: 'Plank.Convex.PlanarTight.BoundaryStrictObstruction.boundary_not_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.BoundaryStrictObstruction.boundary_not_strict
