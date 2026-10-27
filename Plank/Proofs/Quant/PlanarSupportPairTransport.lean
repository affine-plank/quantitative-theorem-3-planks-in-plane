/- The support-line two-plank equality families in original affine coordinates. -/
module

public import Plank.Proofs.Quant.PlanarSupportPairClassification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSupportPairClassification

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarOnePlankVertices
open Plank.Convex.DeficientHeightTilt

def unitCoordinate (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) (base : ℝ) : Point →ᵃ[ℝ] ℝ :=
  (rangeWidth K f)⁻¹ • (f-AffineMap.const ℝ Point base)

/-- Exact lower-support family criterion for the original physical planks
and their actual relative widths. There are no normalization premises. -/
theorem equality_iff_lower_support_family {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f g : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo₀ hi₀ lo hi : ℝ) (hbase : f b = lo₀) (horder : lo₀ ≤ hi₀) (hlohi : lo < hi)
    (hWf : 0 < rangeWidth K f) (hWg : 0 < rangeWidth K g)
    (hR : (hi₀-lo₀)/rangeWidth K f+(hi-lo)/rangeWidth K g < 1) :
    (volume (K \ ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal =
        (max 0 (1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g))^2*(volume K).toReal ↔
      Family K (unitCoordinate K f lo₀) g a ((hi₀-lo₀)/rangeWidth K f) lo hi := by
  let F := unitCoordinate K f lo₀
  let r := (hi₀-lo₀)/rangeWidth K f
  have heval (x) : F x = (f x-lo₀)/rangeWidth K f := by
    simp [F,unitCoordinate,div_eq_mul_inv,mul_comm]
  have hspan : rangeWidth K f = f a-lo₀ := by
    have hh : rangeWidth K f = f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
    rwa [hbase] at hh
  have hFa : F a = 1 := by rw [heval,← hspan,div_self hWf.ne']
  have hFb : F b = 0 := by rw [heval,hbase,sub_self,zero_div]
  have hF (x) (hx : x ∈ K) : 0 ≤ F x ∧ F x ≤ 1 := by
    rw [heval]
    refine ⟨div_nonneg (sub_nonneg.mpr (by rw [← hbase]; exact hmin x hx)) hWf.le,?_⟩
    apply (div_le_one hWf).mpr
    rw [hspan]
    exact sub_le_sub_right (hmax x hx) _
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr horder) hWf.le
  have hband : {x | 0 ≤ F x ∧ F x ≤ r} = {x | lo₀ ≤ f x ∧ f x ≤ hi₀} := by
    ext x
    change (0 ≤ F x ∧ F x ≤ r) ↔ (lo₀ ≤ f x ∧ f x ≤ hi₀)
    rw [heval]
    dsimp only [r]
    rw [div_le_div_iff_of_pos_right hWf]
    simp only [le_div_iff₀ hWf,zero_mul,sub_nonneg,sub_le_sub_iff_right]
  have hh := equality_iff_family hK hconv hV F g a b ha hb hFa hFb hF r lo hi hr hlohi hWg hR
  rw [hband] at hh
  rw [max_eq_right (by linarith only [hR] : 0 ≤ 1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g)]
  exact hh

/-- The upper-support family is the same proved family after reversing
the first functional. Other physical planks remain fixed. -/
theorem equality_iff_upper_support_family {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f g : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo₀ hi₀ lo hi : ℝ) (hbase : f a = hi₀) (horder : lo₀ ≤ hi₀) (hlohi : lo < hi)
    (hWf : 0 < rangeWidth K f) (hWg : 0 < rangeWidth K g)
    (hR : (hi₀-lo₀)/rangeWidth K f+(hi-lo)/rangeWidth K g < 1) :
    (volume (K \ ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal =
        (max 0 (1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g))^2*(volume K).toReal ↔
      Family K (unitCoordinate K (-f) (-hi₀)) g b ((hi₀-lo₀)/rangeWidth K f) lo hi := by
  have hWneg : rangeWidth K (-f) = rangeWidth K f :=
    Body.width_neg hK ⟨a,ha⟩ (continuous_form f)
  have hnum : -lo₀ - -hi₀ = hi₀-lo₀ := by ring
  have hh := equality_iff_lower_support_family hK hconv hV (-f) g b a hb ha
    (fun x hx => by simpa using neg_le_neg (hmin x hx))
    (fun x hx => by simpa using neg_le_neg (hmax x hx))
    (-hi₀) (-lo₀) lo hi (by simpa using congrArg Neg.neg hbase)
    (neg_le_neg horder) hlohi (by rw [hWneg]; exact hWf) hWg
    (by rw [hnum,hWneg]; exact hR)
  have hband : {x | -hi₀ ≤ (-f) x ∧ (-f) x ≤ -lo₀} = {x | lo₀ ≤ f x ∧ f x ≤ hi₀} := by
    ext x
    change (-hi₀ ≤ -f x ∧ -f x ≤ -lo₀) ↔ (lo₀ ≤ f x ∧ f x ≤ hi₀)
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]
  rwa [hband,hnum,hWneg] at hh

/-- For either supporting side of the first physical plank, actual equality
forces the arbitrary body to be the convex hull of at most four points. -/
theorem equality_implies_four_vertices_of_support {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f g : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo₀ hi₀ lo hi : ℝ) (hface : f b = lo₀ ∨ f a = hi₀)
    (horder : lo₀ ≤ hi₀) (hlohi : lo < hi)
    (hWf : 0 < rangeWidth K f) (hWg : 0 < rangeWidth K g)
    (hR : (hi₀-lo₀)/rangeWidth K f+(hi-lo)/rangeWidth K g < 1)
    (he : (volume (K \ ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal =
      (max 0 (1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g))^2*(volume K).toReal) :
    ∃ u v c d : Point, K = convexHull ℝ {u,v,c,d} := by
  have hshape {F : Point →ᵃ[ℝ] ℝ} {z : Point}
      (ht : Family K F g z ((hi₀-lo₀)/rangeWidth K f) lo hi) :
      ∃ u v c d : Point, K = convexHull ℝ {u,v,c,d} := by
    obtain ⟨⟨u,_,v,_,_,_,_,_,c,_,d,_,_,_,hbody⟩,_⟩ := ht
    exact ⟨u,v,c,d,hbody.trans (fourPointBody_eq_hull u v c d (by rwa [← hbody]))⟩
  rcases hface with hl | hh
  · exact hshape ((equality_iff_lower_support_family hK hconv hV f g a b ha hb hmax hmin
      lo₀ hi₀ lo hi hl horder hlohi hWf hWg hR).mp he)
  · exact hshape ((equality_iff_upper_support_family hK hconv hV f g a b ha hb hmax hmin
      lo₀ hi₀ lo hi hh horder hlohi hWf hWg hR).mp he)

end Plank.PlanarSupportPairClassification

/-- info: 'Plank.PlanarSupportPairClassification.equality_iff_lower_support_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSupportPairClassification.equality_iff_lower_support_family
/-- info: 'Plank.PlanarSupportPairClassification.equality_iff_upper_support_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSupportPairClassification.equality_iff_upper_support_family
/-- info: 'Plank.PlanarSupportPairClassification.equality_implies_four_vertices_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSupportPairClassification.equality_implies_four_vertices_of_support
