/- An anchored positive equality cover determines a triangle unless
the body contains a vertex of its three-coordinate unit cube. -/
module
public import Plank.Convex.PlanarTight.AnchoredTriangleShape
public import Plank.Convex.PlanarTight.AnchoredNoQuadrilateral
public import Plank.Convex.PlanarTight.CornerEnclosure
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AnchoredShape

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A nondegenerate triangle, specified by its actual three vertices. -/
def IsTriangle (K : Set E) : Prop :=
  ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v)

/-- Interior apex parameters give the whole triangle; endpoint parameters
give one of the four diagonal triangles in the unit square. -/
theorem triangle_or_corner_of_anchored (K : Set E) (hK : Convex ℝ K)
    (X Y : E →ᵃ[ℝ] ℝ) (H : TwoPlankClassification.Ranges K X Y)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, X x = X y → Y x = Y y → x = y)
    (l u m v : ℝ) (h : TwoPlankClassification.Anchored K X Y l u m v) :
    IsTriangle K ∨ CornerEnclosure.Enclosed K X Y := by
  obtain ⟨_, _, _, c, hc, hc₁, _, _, hshape⟩ := h
  by_cases he₀ : c = 0
  · apply Or.inr ∘ Or.inl
    intro z hz
    have hs := (hshape z hz).2
    rw [he₀] at hs
    nlinarith only [hs]
  by_cases he₁ : c = 1
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    intro z hz
    have hs := (hshape z hz).1
    simpa only [he₁, one_mul] using hs
  obtain ⟨w, _, _, _, _, _, _, _, hind, heq⟩ := AnchoredTriangleShape.eq_triangle K hK X Y
    H hinj c (lt_of_le_of_ne hc (Ne.symm he₀)) (lt_of_le_of_ne hc₁ he₁) hshape
  exact Or.inl ⟨w, hind, heq⟩

abbrev Point := Fin 3 → ℝ

/-- Exhaustive shape obstruction for the anchored positive case. The
cube-vertex alternative retains the possible freedom in the body's shape. -/
theorem triangle_or_cube_vertex (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1) :
    IsTriangle K ∨ ∃ z ∈ K, ∀ i, z i = 0 ∨ z i = 1 := by
  let X : Point →ᵃ[ℝ] ℝ := AffineMap.proj 1
  let Y : Point →ᵃ[ℝ] ℝ := AffineMap.proj 2
  have H : TwoPlankClassification.Ranges K X Y :=
    ⟨fun z hz => ⟨hbox z hz 1, hbox z hz 2⟩, hL 1, hU 1, hL 2, hU 2⟩
  have hinj : ∀ x ∈ K, ∀ y ∈ K, X x = X y → Y x = Y y → x = y := by
    intro x hx y hy h₁ h₂
    change x 1 = y 1 at h₁
    change x 2 = y 2 at h₂
    have hp := hplane x hx
    have hq := hplane y hy
    rw [← h₁, ← h₂] at hq
    have h₀ : x 0 = y 0 := by nlinarith only [hp, hq, ha]
    funext i
    fin_cases i <;> assumption
  have hinjSwap : ∀ x ∈ K, ∀ y ∈ K, Y x = Y y → X x = X y → x = y :=
    fun x hx y hy h₁ h₂ => hinj x hx y hy h₂ h₁
  have hinjReflect : ∀ x ∈ K, ∀ y ∈ K,
      TwoPlankClassification.reflect X x = TwoPlankClassification.reflect X y →
      Y x = Y y → x = y := by
    intro x hx y hy h₁ h₂
    apply hinj x hx y hy _ h₂
    change 1 - X x = 1 - X y at h₁
    linarith only [h₁]
  have hinjSwapReflect : ∀ x ∈ K, ∀ y ∈ K,
      TwoPlankClassification.reflect Y x = TwoPlankClassification.reflect Y y →
      X x = X y → x = y := by
    intro x hx y hy h₁ h₂
    apply hinjSwap x hx y hy _ h₂
    change 1 - Y x = 1 - Y y at h₁
    linarith only [h₁]
  obtain ⟨T, hT, hT₀⟩ := hU 0
  have hn := AnchoredNoQuadrilateral.two_plank_triangular K hK hbox hL hU a b c d
    ha hb hc hplane lo hi hwidth hanchor hcover hsum T hT hT₀
  have hresult : IsTriangle K ∨ CornerEnclosure.Enclosed K X Y := by
    rcases hn with hn | hn | hn | hn
    · exact triangle_or_corner_of_anchored K hK X Y H hinj _ _ _ _ hn
    · rcases triangle_or_corner_of_anchored K hK (TwoPlankClassification.reflect X) Y
        H.reflect hinjReflect _ _ _ _ hn with ht | hs
      · exact Or.inl ht
      · exact Or.inr (CornerEnclosure.reflect hs)
    · rcases triangle_or_corner_of_anchored K hK Y X H.swap hinjSwap _ _ _ _ hn with ht | hs
      · exact Or.inl ht
      · exact Or.inr (CornerEnclosure.swap hs)
    · rcases triangle_or_corner_of_anchored K hK (TwoPlankClassification.reflect Y) X
        H.swap.reflect hinjSwapReflect _ _ _ _ hn with ht | hs
      · exact Or.inl ht
      · exact Or.inr (CornerEnclosure.swap (CornerEnclosure.reflect hs))
  exact hresult.imp_right
    (CornerEnclosure.exists_cube_vertex K hbox hL hU a b c d ha hb hc hplane)

/-- If the same body also has a strictly internal cover in the same
directions, the anchored equality alternative forces the body to be a triangle.
The two covers can have different endpoints. -/
theorem triangle_of_anchored_and_strict_cover (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (lo' hi' : Point) (hlo' : ∀ i, 0 < lo' i) (hhi' : ∀ i, hi' i < 1)
    (hcover' : ∀ z ∈ K, ∃ i, lo' i ≤ z i ∧ z i ≤ hi' i) : IsTriangle K :=
  (triangle_or_cube_vertex K hK hbox hL hU a b c d ha hb hc hplane
    lo hi hwidth hanchor hcover hsum).resolve_right
    (CornerEnclosure.no_cube_vertex_of_strict_cover K lo' hi' hlo' hhi' hcover')

end Plank.Convex.PlanarTight.AnchoredShape

/-- info: 'Plank.Convex.PlanarTight.AnchoredShape.triangle_or_cube_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredShape.triangle_or_cube_vertex

/-- info: 'Plank.Convex.PlanarTight.AnchoredShape.triangle_of_anchored_and_strict_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredShape.triangle_of_anchored_and_strict_cover
