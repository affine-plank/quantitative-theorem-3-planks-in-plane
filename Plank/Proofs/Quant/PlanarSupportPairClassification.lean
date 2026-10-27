/- Exhaustive equality families for two planks when the first reaches a
supporting line. In particular, equality forces a body with at most four
vertices, without any prior polygon assumption. -/
module

public import Plank.Proofs.Quant.PlanarSupportPairReduction
public import Plank.Proofs.Quant.PlanarOnePlankClassification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSupportPairClassification

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarSupportPairReduction
  PlanarOnePlankVertices
open Plank.Convex.DeficientHeightTilt

/-- An explicit finite-point body family together with a closed covering
condition. The latter uses the two physical planks and a specified homothet;
neither condition refers to an area equality. -/
def Family (K : Set Point) (f g : Point →ᵃ[ℝ] ℝ) (a : Point) (r lo hi : ℝ) : Prop :=
  (∃ u ∈ K, ∃ v ∈ K, (∀ x ∈ K, g x ≤ g u) ∧ (∀ x ∈ K, g v ≤ g x) ∧
    g v ≤ pulledEndpoint g a r lo ∧ pulledEndpoint g a r hi ≤ g u ∧
    ∃ c ∈ K, ∃ d ∈ K,
      g c = g v+(pulledEndpoint g a r lo-g v)/
        (1-(pulledEndpoint g a r hi-pulledEndpoint g a r lo)/rangeWidth K g) ∧
      g d = g v+(pulledEndpoint g a r lo-g v)/
        (1-(pulledEndpoint g a r hi-pulledEndpoint g a r lo)/rangeWidth K g) ∧
      K = fourPointBody u v c d) ∧
  K ⊆ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ {x | lo ≤ g x ∧ g x ≤ hi}) ∪
    (AffineMap.homothety a (1-r) '' K)

/-- Both necessity and actual-area sufficiency for the entire lower-support
two-plank stratum. The second direction is arbitrary, and the first may
have width zero. Positive widths are not assumed to be generic. -/
theorem equality_iff_family {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f g : Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (r lo hi : ℝ) (hr : 0 ≤ r) (hlohi : lo < hi) (hW : 0 < rangeWidth K g)
    (hR : r+(hi-lo)/rangeWidth K g < 1) :
    (volume (K \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal =
        (1-r-(hi-lo)/rangeWidth K g)^2*(volume K).toReal ↔
      Family K f g a r lo hi := by
  have hs : 0 < (hi-lo)/rangeWidth K g := div_pos (sub_pos.mpr hlohi) hW
  have hq : 0 < 1-r := by linarith only [hR,hs]
  have hpull : pulledEndpoint g a r lo < pulledEndpoint g a r hi := sub_pos.mp (by
    rw [pulled_width]
    exact div_pos (sub_pos.mpr hlohi) hq)
  have hsmall : (pulledEndpoint g a r hi-pulledEndpoint g a r lo)/rangeWidth K g < 1 := by
    rw [pulled_relativeWidth]
    exact (div_lt_one hq).mpr (by linarith only [hR])
  rw [equality_iff_reduced hK hconv hV f g a b ha hb hfa hfb hf r lo hi hr hlohi hW hR,
    PlanarOnePlankClassification.equality_iff_exists_fourPointBody hK hconv ⟨a,ha⟩ hV
      g (pulledEndpoint g a r lo) (pulledEndpoint g a r hi) hpull hW hsmall]
  rfl

/-- A tight two-plank configuration with one support plank cannot live on
a body requiring more than four vertices. The planks need not be parallel. -/
theorem equality_implies_four_vertices {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f g : Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (r lo hi : ℝ) (hr : 0 ≤ r) (hlohi : lo < hi) (hW : 0 < rangeWidth K g)
    (hR : r+(hi-lo)/rangeWidth K g < 1)
    (he : (volume (K \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal =
      (1-r-(hi-lo)/rangeWidth K g)^2*(volume K).toReal) :
    ∃ u v c d : Point, K = convexHull ℝ {u,v,c,d} := by
  obtain ⟨⟨u,_,v,_,_,_,_,_,c,_,d,_,_,_,hshape⟩,_⟩ :=
    (equality_iff_family hK hconv hV f g a b ha hb hfa hfb hf r lo hi hr hlohi hW hR).mp he
  exact ⟨u,v,c,d,hshape.trans (fourPointBody_eq_hull u v c d (by rwa [← hshape]))⟩

end Plank.PlanarSupportPairClassification

/-- info: 'Plank.PlanarSupportPairClassification.equality_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSupportPairClassification.equality_iff_family
/-- info: 'Plank.PlanarSupportPairClassification.equality_implies_four_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSupportPairClassification.equality_implies_four_vertices
