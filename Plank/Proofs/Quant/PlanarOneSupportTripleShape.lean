/- A single supporting window already forces four-vertex rigidity for triples. -/
module

public import Plank.Proofs.Quant.PlanarTwoPlankShapeOriginal
public import Plank.Proofs.Quant.PlanarSupportReduction

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarOneSupportTripleShape

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarSupportPairReduction PlanarSupportPairClassification
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Three-plank equality with one normalized lower-support window and
positive total width in the other two forces a triangle or quadrilateral.
The other two directions and window locations are arbitrary. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : Point →ᵃ[ℝ] ℝ)
    (g : Fin 2 → Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (r : ℝ) (lo hi : Fin 2 → ℝ) (hr : 0 ≤ r)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < rangeWidth K (g i))
    (hS : 0 < ∑ i, (hi i-lo i)/rangeWidth K (g i))
    (hR : r+∑ i, (hi i-lo i)/rangeWidth K (g i) < 1)
    (heq : (volume (K \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪
        ⋃ i, {x | lo i ≤ g i x ∧ g i x ≤ hi i}))).toReal =
        (1-r-∑ i, (hi i-lo i)/rangeWidth K (g i))^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  have hq : 0 < 1-r := by linarith only [hR,hS]
  let p : Endpoints 2 :=
    (fun i => pulledEndpoint (g i) a r (lo i),fun i => pulledEndpoint (g i) a r (hi i))
  have hbudget : budget K g p = (∑ i, (hi i-lo i)/rangeWidth K (g i))/(1-r) := by
    simp only [budget,p,pulled_relativeWidth]
    exact (Finset.sum_div _ _ _).symm
  have hpo (i) : p.1 i ≤ p.2 i := sub_nonneg.mp (by
    change 0 ≤ pulledEndpoint (g i) a r (hi i)-pulledEndpoint (g i) a r (lo i)
    rw [pulled_width]
    exact div_nonneg (sub_nonneg.mpr (horder i)) hq.le)
  have hpeq := ((PlanarSupportReduction.equality_three_iff_reduced hK hconv hV f g
    a b ha hb hfa hfb hf r lo hi hr horder hW hR).mp heq).1
  apply PlanarTwoPlankShapeOriginal.four_vertices hK hconv ⟨a,ha⟩ hV g p hW hpo
  · rw [hbudget]
    exact div_pos hS hq
  · rw [hbudget]
    exact (div_lt_one hq).mpr (by linarith only [hR])
  · exact hpeq

/-- Original-coordinate version for a lower-support first window. No
unit range is assumed for any of the three directions. -/
theorem four_vertices_of_lower_support {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (g : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo₀ hi₀ : ℝ) (lo hi : Fin 2 → ℝ) (hbase : f b = lo₀)
    (hfirst : lo₀ ≤ hi₀) (horder : ∀ i, lo i ≤ hi i)
    (hWf : 0 < rangeWidth K f) (hW : ∀ i, 0 < rangeWidth K (g i))
    (hS : 0 < ∑ i, (hi i-lo i)/rangeWidth K (g i))
    (hR : (hi₀-lo₀)/rangeWidth K f+∑ i, (hi i-lo i)/rangeWidth K (g i) < 1)
    (heq : (volume (K \ ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪
        ⋃ i, {x | lo i ≤ g i x ∧ g i x ≤ hi i}))).toReal =
        (max 0 (1-(hi₀-lo₀)/rangeWidth K f-∑ i, (hi i-lo i)/rangeWidth K (g i)))^2*
          (volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
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
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hfirst) hWf.le
  have hband : {x | 0 ≤ F x ∧ F x ≤ r} = {x | lo₀ ≤ f x ∧ f x ≤ hi₀} := by
    ext x
    change (0 ≤ F x ∧ F x ≤ r) ↔ (lo₀ ≤ f x ∧ f x ≤ hi₀)
    rw [heval]
    dsimp only [r]
    rw [div_le_div_iff_of_pos_right hWf]
    simp only [le_div_iff₀ hWf,zero_mul,sub_nonneg,sub_le_sub_iff_right]
  apply four_vertices hK hconv hV F g a b ha hb hFa hFb hF r lo hi hr horder hW hS hR
  rw [hband]
  have hd : 0 ≤ 1-(hi₀-lo₀)/rangeWidth K f-∑ i, (hi i-lo i)/rangeWidth K (g i) := by
    linarith only [hR]
  simpa only [max_eq_right hd] using heq

/-- Either supporting side of the first physical window is allowed.
The first plank can be chosen arbitrarily by the caller's indexing. -/
theorem four_vertices_of_support {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (g : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo₀ hi₀ : ℝ) (lo hi : Fin 2 → ℝ) (hface : f b = lo₀ ∨ f a = hi₀)
    (hfirst : lo₀ ≤ hi₀) (horder : ∀ i, lo i ≤ hi i)
    (hWf : 0 < rangeWidth K f) (hW : ∀ i, 0 < rangeWidth K (g i))
    (hS : 0 < ∑ i, (hi i-lo i)/rangeWidth K (g i))
    (hR : (hi₀-lo₀)/rangeWidth K f+∑ i, (hi i-lo i)/rangeWidth K (g i) < 1)
    (heq : (volume (K \ ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪
        ⋃ i, {x | lo i ≤ g i x ∧ g i x ≤ hi i}))).toReal =
        (max 0 (1-(hi₀-lo₀)/rangeWidth K f-∑ i, (hi i-lo i)/rangeWidth K (g i)))^2*
          (volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  rcases hface with hl | hu
  · exact four_vertices_of_lower_support hK hconv hV f g a b ha hb hmax hmin
      lo₀ hi₀ lo hi hl hfirst horder hWf hW hS hR heq
  · have hWneg : rangeWidth K (-f) = rangeWidth K f :=
      Body.width_neg hK ⟨a,ha⟩ (continuous_form f)
    have hnum : -lo₀ - -hi₀ = hi₀-lo₀ := by ring
    have hband : {x | -hi₀ ≤ (-f) x ∧ (-f) x ≤ -lo₀} = {x | lo₀ ≤ f x ∧ f x ≤ hi₀} := by
      ext x
      change (-hi₀ ≤ -f x ∧ -f x ≤ -lo₀) ↔ (lo₀ ≤ f x ∧ f x ≤ hi₀)
      constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]
    apply four_vertices_of_lower_support hK hconv hV (-f) g b a hb ha
      (fun x hx => by simpa using neg_le_neg (hmin x hx))
      (fun x hx => by simpa using neg_le_neg (hmax x hx))
      (-hi₀) (-lo₀) lo hi (by simpa using congrArg Neg.neg hu) (neg_le_neg hfirst)
      horder (by rw [hWneg]; exact hWf) hW hS
    · rwa [hnum,hWneg]
    · rwa [hband,hnum,hWneg]

end Plank.PlanarOneSupportTripleShape

/-- info: 'Plank.PlanarOneSupportTripleShape.four_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOneSupportTripleShape.four_vertices
/-- info: 'Plank.PlanarOneSupportTripleShape.four_vertices_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOneSupportTripleShape.four_vertices_of_support
