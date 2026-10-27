/- The shape forced by one-plank equality: two cones over a level section.
The affine coordinate is normalized to have range [0,1]. -/
module

public import Plank.Proofs.Quant.PlanarOnePlankEquality
public import Plank.Proofs.Quant.FiniteDimensionalOnePlankShape

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarOnePlankShape

open Set MeasureTheory Topology PlanarQuantitative PlanarOnePlankEquality
open Plank.Convex.DeficientHeightTilt
open scoped Pointwise

theorem normalized_ray (f : Point →ᵃ[ℝ] ℝ) {b : Point} (hb : f b = 0)
    (x : Point) (t : ℝ) : f (b+t • (x-b)) = t*f x := by
  exact FiniteDimensionalOnePlankShape.normalized_ray f hb x t

/-- An exact lower-copy condition forces all lower points onto rays from
the minimum support point to the indicated level section. Compactness rules
out a ray that would keep expanding without reaching that section. -/
theorem lower_copy_forces_cone {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : Point →ᵃ[ℝ] ℝ) (b : Point) (hb : b ∈ K) (hfb : f b = 0)
    (hmin : ∀ x ∈ K, 0 ≤ f x) {q d : ℝ} (hq : 0 < q) (hq1 : q < 1) (hd : 0 < d)
    (hcopy : ∀ x ∈ K, f x < q*d → x-(1-q) • b ∈ q • K)
    {x : Point} (hx : x ∈ K) (hxd : f x ≤ d) :
    x = b ∨ ∃ z ∈ K, f z = d ∧ x ∈ segment ℝ b z := by
  exact FiniteDimensionalOnePlankShape.lower_copy_forces_cone hK hconv f b hb hfb hmin hq hq1 hd hcopy hx hxd

/-- The cone with its apex included, even when its base is empty. -/
def cone (b : Point) (S : Set Point) : Set Point :=
  insert b (⋃ z ∈ S, segment ℝ b z)

def levelSection (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) (t : ℝ) : Set Point :=
  K ∩ {x | f x = t}

def doubleCone (a b : Point) (S : Set Point) : Set Point := cone b S ∪ cone a S

theorem mem_cone_of_segment {b x z : Point} {S : Set Point}
    (hz : z ∈ S) (hx : x ∈ segment ℝ b z) : x ∈ cone b S :=
  Or.inr (mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨hz,hx⟩⟩)

theorem cone_subset {K S : Set Point} (hK : Convex ℝ K) {b : Point}
    (hb : b ∈ K) (hS : S ⊆ K) : cone b S ⊆ K := by
  exact FiniteDimensionalOnePlankShape.cone_subset hK hb hS

theorem cone_range (f : Point →ᵃ[ℝ] ℝ) {b : Point} (hb : f b = 0)
    {S : Set Point} {d : ℝ} (hd : 0 ≤ d) (hS : ∀ z ∈ S, f z = d)
    {x : Point} (hx : x ∈ cone b S) : 0 ≤ f x ∧ f x ≤ d := by
  exact FiniteDimensionalOnePlankShape.cone_range f hb hd hS hx

theorem lower_cone_gives_copy {K S : Set Point} (hK : Convex ℝ K)
    (f : Point →ᵃ[ℝ] ℝ) {b : Point} (hb : b ∈ K) (hfb : f b = 0)
    {d q : ℝ} (hd : 0 ≤ d) (hq : 0 < q) (hS : S ⊆ K) (hfS : ∀ z ∈ S, f z = d)
    {x : Point} (hx : x ∈ cone b S) (hfx : f x < q*d) :
    x-(1-q) • b ∈ q • K := by
  exact FiniteDimensionalOnePlankShape.lower_cone_gives_copy hK f hb hfb hd hq hS hfS hx hfx

/-- The self-similarity criterion is exactly a double-cone shape, at the
calibrated level t. In the plane its base is a segment (possibly at an
extreme level), so this describes triangles and quadrilaterals. -/
theorem homothetic_cover_iff_doubleCone {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    {q t : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 ≤ t ∧ t ≤ 1) :
    K ⊆ closedHomotheticCover K f (q*t) (q*t+1-q) a b (1-q) ↔
      K = doubleCone a b (levelSection K f t) := by
  exact FiniteDimensionalOnePlankShape.homothetic_cover_iff_doubleCone hK hconv f a b ha hb hfa hfb hf hq hq1 ht

theorem affine_mix (f : Point →ᵃ[ℝ] ℝ) (q : ℝ) (x y : Point) :
    f (q • x+(1-q) • y) = q*f x+(1-q)*f y := by
  exact FiniteDimensionalOnePlankShape.affine_mix f q x y

/-- A positive-width equality cover cannot waste either end outside the
support interval. The proof uses actual segments between the support points. -/
theorem position_of_homothetic_cover {K : Set Point} (hconv : Convex ℝ K)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0) (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    {q lo : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hcov : K ⊆ closedHomotheticCover K f lo (lo+1-q) a b (1-q)) :
    0 ≤ lo ∧ lo ≤ q := by
  exact FiniteDimensionalOnePlankShape.position_of_homothetic_cover hconv f a b ha hb hfa hfb hf hq hq1 hcov

/-- Exhaustive one-plank shape classification in a normalized affine
coordinate. For width r in (0,1), the cut must be [lo,lo+r] inside [0,1]
and the body must be the two cones over its section at lo/(1-r). -/
theorem equality_iff_doubleCone {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0) (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (lo r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (volume (K \ {x | lo ≤ f x ∧ f x ≤ lo+r})).toReal = (1-r)^2*(volume K).toReal ↔
      0 ≤ lo ∧ lo+r ≤ 1 ∧
      K = doubleCone a b (levelSection K f (lo/(1-r))) := by
  simpa only [Module.finrank_pi,Fintype.card_fin,doubleCone,cone,levelSection,
    FiniteDimensionalOnePlankShape.doubleCone,FiniteDimensionalOnePlankShape.cone,
    FiniteDimensionalOnePlankShape.levelSection] using
    FiniteDimensionalOnePlankShape.equality_iff_doubleCone volume hK hconv hV
      f a b ha hb hfa hfb hf lo r hr hr1

end Plank.PlanarOnePlankShape

/-- info: 'Plank.PlanarOnePlankShape.lower_copy_forces_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankShape.lower_copy_forces_cone
/-- info: 'Plank.PlanarOnePlankShape.equality_iff_doubleCone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankShape.equality_iff_doubleCone
