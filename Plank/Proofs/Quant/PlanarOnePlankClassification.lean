/- Exhaustive one-plank equality families in the original affine coordinate. -/
module

public import Plank.Proofs.Quant.PlanarOnePlankVertices

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarOnePlankClassification

open Set MeasureTheory PlanarQuantitative PlanarOnePlankVertices PlanarOnePlankShape
open Plank.Convex.DeficientHeightTilt

/-- The full positive-width, positive-deficit one-plank classification on
an arbitrary compact convex planar body of positive area. The two support
points may be chosen arbitrarily. All endpoint and shape restrictions occur
in the conclusion; no polygon hypothesis is assumed. -/
theorem equality_iff_fourPointBody {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) (hlohi : lo < hi)
    (hW : 0 < rangeWidth K f) (hr1 : (hi-lo)/rangeWidth K f < 1)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x) :
    (volume (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
        (1-(hi-lo)/rangeWidth K f)^2*(volume K).toReal ↔
      f b ≤ lo ∧ hi ≤ f a ∧ ∃ c ∈ K, ∃ d ∈ K,
        f c = f b+(lo-f b)/(1-(hi-lo)/rangeWidth K f) ∧
        f d = f b+(lo-f b)/(1-(hi-lo)/rangeWidth K f) ∧
        K = fourPointBody a b c d := by
  let W := rangeWidth K f
  let r := (hi-lo)/W
  let ell := (lo-f b)/W
  let g : Point →ᵃ[ℝ] ℝ := W⁻¹ • (f-AffineMap.const ℝ Point (f b))
  have hpos : 0 < W := hW
  have hspan : W = f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
  have hg (x : Point) : g x = (f x-f b)/W := by simp [g,div_eq_mul_inv,mul_comm]
  have hga : g a = 1 := by rw [hg,← hspan,div_self hW.ne']
  have hgb : g b = 0 := by rw [hg,sub_self,zero_div]
  have hgf : ∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1 := by
    intro x hx
    rw [hg]
    refine ⟨div_nonneg (sub_nonneg.mpr (hmin x hx)) hW.le,?_⟩
    apply (div_le_one hpos).mpr
    rw [hspan]
    linarith only [hmax x hx]
  have hr : 0 < r := div_pos (sub_pos.mpr hlohi) hW
  have hq : 0 < 1-r := sub_pos.mpr hr1
  have he : ell+r = (hi-f b)/W := by dsimp [ell,r]; ring
  have hplank : {x | ell ≤ g x ∧ g x ≤ ell+r} = {x | lo ≤ f x ∧ f x ≤ hi} := by
    ext x
    rw [mem_ofPred_eq,mem_ofPred_eq,he,hg]
    dsimp only [ell]
    simp only [div_le_div_iff_of_pos_right hpos,sub_le_sub_iff_right]
  have hlow : 0 ≤ ell ↔ f b ≤ lo := by
    dsimp only [ell]
    rw [le_div_iff₀ hW,zero_mul]
    exact sub_nonneg
  have hhigh : ell+r ≤ 1 ↔ hi ≤ f a := by
    rw [he,div_le_one hpos,hspan]
    exact sub_le_sub_iff_right (f b)
  have hlevel (x : Point) : g x = ell/(1-r) ↔ f x = f b+(lo-f b)/(1-r) := by
    rw [hg,div_eq_iff hW.ne']
    have hc : (ell/(1-r))*W = (lo-f b)/(1-r) := by dsimp [ell]; field_simp [hpos.ne']
    rw [hc]
    constructor <;> intro h <;> linarith only [h]
  have hh := PlanarOnePlankVertices.equality_iff_fourPointBody hK hconv hV g a b ha hb
    hga hgb hgf ell r hr hr1
  rw [hplank,hlow,hhigh] at hh
  simp_rw [hlevel] at hh
  exact hh

/-- No support-point existence assumption is needed in the classification:
compactness supplies suitable actual extrema. -/
theorem equality_iff_exists_fourPointBody {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) (hlohi : lo < hi)
    (hW : 0 < rangeWidth K f) (hr1 : (hi-lo)/rangeWidth K f < 1) :
    (volume (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
        (1-(hi-lo)/rangeWidth K f)^2*(volume K).toReal ↔
      ∃ a ∈ K, ∃ b ∈ K, (∀ x ∈ K, f x ≤ f a) ∧ (∀ x ∈ K, f b ≤ f x) ∧
        f b ≤ lo ∧ hi ≤ f a ∧ ∃ c ∈ K, ∃ d ∈ K,
          f c = f b+(lo-f b)/(1-(hi-lo)/rangeWidth K f) ∧
          f d = f b+(lo-f b)/(1-(hi-lo)/rangeWidth K f) ∧
          K = fourPointBody a b c d := by
  constructor
  · intro he
    obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne (PlanarGapCells.continuous_form f)
    exact ⟨a,ha,b,hb,hmax,hmin,
      (equality_iff_fourPointBody hK hconv hV f lo hi hlohi hW hr1 a b ha hb hmax hmin).mp he⟩
  · rintro ⟨a,ha,b,hb,hmax,hmin,he⟩
    exact (equality_iff_fourPointBody hK hconv hV f lo hi hlohi hW hr1 a b ha hb hmax hmin).mpr he

/-- In particular, no body requiring more than four vertices can be tight
for a plank of positive relative width strictly below one. -/
theorem equality_implies_four_vertices {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) (hlohi : lo < hi)
    (hW : 0 < rangeWidth K f) (hr1 : (hi-lo)/rangeWidth K f < 1)
    (he : (volume (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
        (1-(hi-lo)/rangeWidth K f)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨a,_,b,_,_,_,_,_,c,_,d,_,_,_,hshape⟩ :=
    (equality_iff_exists_fourPointBody hK hconv hne hV f lo hi hlohi hW hr1).mp he
  exact ⟨a,b,c,d,hshape.trans (fourPointBody_eq_hull a b c d (by rwa [← hshape]))⟩

end Plank.PlanarOnePlankClassification

/-- info: 'Plank.PlanarOnePlankClassification.equality_iff_exists_fourPointBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankClassification.equality_iff_exists_fourPointBody
/-- info: 'Plank.PlanarOnePlankClassification.equality_implies_four_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankClassification.equality_implies_four_vertices
