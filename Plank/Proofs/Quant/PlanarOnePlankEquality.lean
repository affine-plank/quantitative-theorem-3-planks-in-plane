/- An exact geometric equality criterion for one plank on an arbitrary
planar convex body. The two exterior caps must exhaust translated copies
of the contracted body. No triangular or polyhedral body is assumed. -/
module

public import Plank.Proofs.Quant.PlanarOnePlank
public import Plank.Proofs.Quant.PlanarGapAnalysis
public import Plank.Proofs.Quant.FiniteDimensionalOnePlankEquality

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarOnePlankEquality

open Set MeasureTheory Function PlanarQuantitative PlanarGapCells
open Plank.Convex.DeficientHeightTilt
open scoped Pointwise

/-- The lower and upper pieces of the body contracted by `1-r`, translated
toward its two support points, and restricted to the corresponding gap side. -/
def homotheticCaps (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (a b : Point) (r : ℝ) : Set Point :=
  ({x | x-r • b ∈ (1-r) • K} ∩ {x | f x < lo}) ∪
    ({x | x-r • a ∈ (1-r) • K} ∩ {x | hi < f x})

/-- Exhaustive self-similarity criterion, for any chosen maximum and minimum
support points. The right side contains only the body, affine cuts and
homotheties; it imposes no area equation. Classifying the shapes satisfying
this self-similarity is a separate geometric problem. -/
theorem equality_iff_homothetic_caps {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (f : Point →ᵃ[ℝ] ℝ)
    (lo hi : ℝ) (ho : lo ≤ hi) (hW : 0 < rangeWidth K f)
    (hr1 : (hi-lo)/rangeWidth K f < 1)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x) :
    (volume (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
        (1-(hi-lo)/rangeWidth K f)^2*(volume K).toReal ↔
      homotheticCaps K f lo hi a b ((hi-lo)/rangeWidth K f) =ᵐ[volume]
        (K \ {x | lo ≤ f x ∧ f x ≤ hi}) := by
  simpa only [Module.finrank_pi,Fintype.card_fin,Body.width,rangeWidth,
    homotheticCaps,FiniteDimensionalOnePlankEquality.homotheticCaps] using
    FiniteDimensionalOnePlankEquality.equality_iff_homothetic_caps volume
      hK hconv f lo hi ho hW hr1 a b ha hb hmax hmin

/-- A closed, entirely geometric covering condition: the original plank
together with the correctly sided pieces of its two support homothets. -/
def closedHomotheticCover (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (a b : Point) (r : ℝ) : Set Point :=
  {x | lo ≤ f x ∧ f x ≤ hi} ∪
    (({x | x-r • b ∈ (1-r) • K} ∩ {x | f x ≤ lo}) ∪
      ({x | x-r • a ∈ (1-r) • K} ∩ {x | hi ≤ f x}))

/-- For a positive-area body the criterion is an actual closed cover,
including all body-boundary points. No almost-everywhere condition remains. -/
theorem equality_iff_homothetic_cover {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) (ho : lo ≤ hi) (hW : 0 < rangeWidth K f)
    (hr1 : (hi-lo)/rangeWidth K f < 1)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x) :
    (volume (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
        (1-(hi-lo)/rangeWidth K f)^2*(volume K).toReal ↔
      K ⊆ closedHomotheticCover K f lo hi a b ((hi-lo)/rangeWidth K f) := by
  simpa only [Module.finrank_pi,Fintype.card_fin,Body.width,rangeWidth,
    closedHomotheticCover,FiniteDimensionalOnePlankEquality.closedHomotheticCover] using
    FiniteDimensionalOnePlankEquality.equality_iff_homothetic_cover volume
      hK hconv hV f lo hi ho hW hr1 a b ha hb hmax hmin

end Plank.PlanarOnePlankEquality

/-- info: 'Plank.PlanarOnePlankEquality.equality_iff_homothetic_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankEquality.equality_iff_homothetic_caps
/-- info: 'Plank.PlanarOnePlankEquality.equality_iff_homothetic_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankEquality.equality_iff_homothetic_cover
