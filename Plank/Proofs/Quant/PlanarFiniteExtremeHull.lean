/- Finite planar hulls from extreme points on two cuts and four singleton cells. -/
module

public import Plank.Proofs.Quant.PlanarOnePlankVertices
public import Plank.Proofs.Quant.PlanarExtremeCells
public import Plank.Proofs.Quant.PlanarParameterDomain
public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFiniteExtremeHull

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarParameterDomain
  PlanarOnePlankShape PlanarOnePlankVertices
open Plank.Convex.DeficientHeightTilt

/-- At most two extreme points of a compact convex planar body lie on a
fixed nonconstant affine level. Both representatives are actual body points. -/
theorem level_extreme_endpoints {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (t : ℝ) :
    ∃ a ∈ K, ∃ b ∈ K, ∀ x ∈ K.extremePoints ℝ, f x = t → x = a ∨ x = b := by
  by_cases hs : (levelSection K f t).Nonempty
  · obtain ⟨a,ha,b,hb,hab⟩ := levelSection_eq_segment hK hconv f hf t hs
    refine ⟨a,ha.1,b,hb.1,fun x hx hfx => ?_⟩
    have hseg : x ∈ segment ℝ a b := by rw [← hab]; exact ⟨hx.1,hfx⟩
    by_cases hxa : x = a
    · exact Or.inl hxa
    · by_cases hxb : x = b
      · exact Or.inr hxb
      · have ho : x ∈ openSegment ℝ a b :=
          mem_openSegment_of_ne_left_right (fun he => hxa he.symm) (fun he => hxb he.symm) hseg
        exact Or.inl (hx.2 ha.1 hb.1 ho).symm
  · obtain ⟨a,ha⟩ := hne
    exact ⟨a,ha,a,ha,fun x hx hfx => (hs ⟨x,hx.1,hfx⟩).elim⟩

/-- Two cutting lines contribute at most four extreme points, and four
critical singleton cells at most four more. Krein--Milman then identifies
the actual original body as a hull of at most eight of its points. -/
theorem eight_of_locations {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (q r : Endpoints 2)
    (hloc : ∀ x ∈ K.extremePoints ℝ, (∃ i, f i x = q.1 i) ∨
      ∃ s, signCell K f r.1 r.2 s = {x}) :
    ∃ S : Finset Point, S.card ≤ 8 ∧ (↑S : Set Point) ⊆ K ∧ K = convexHull ℝ (↑S : Set Point) := by
  classical
  choose a ha b hb hab using fun i => level_extreme_endpoints hK hconv hne (f i)
    (linear_ne_zero_of_rangeWidth_pos hne (f i) (hW i)) (q.1 i)
  have hcenters (s : Finset (Fin 2)) : ∃ y ∈ K,
      ∀ x, signCell K f r.1 r.2 s = {x} → x = y := by
    by_cases hs : ∃ x, signCell K f r.1 r.2 s = {x}
    · obtain ⟨y,hy⟩ := hs
      have hyK : y ∈ K := (show y ∈ signCell K f r.1 r.2 s by rw [hy]; exact mem_singleton y).1
      refine ⟨y,hyK,fun x hx => ?_⟩
      have he : ({y} : Set Point) = {x} := hy.symm.trans hx
      simpa only [singleton_eq_singleton_iff] using he.symm
    · obtain ⟨y,hy⟩ := hne
      exact ⟨y,hy,fun x hx => (hs ⟨x,hx⟩).elim⟩
  choose y hy hyprop using hcenters
  let A := (Finset.univ : Finset (Fin 2)).image a
  let B := (Finset.univ : Finset (Fin 2)).image b
  let C := (Finset.univ : Finset (Finset (Fin 2))).image y
  let S := A ∪ B ∪ C
  have hAc : A.card ≤ 2 := by
    simpa only [A,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_image_le (f := a) (s := (Finset.univ : Finset (Fin 2))))
  have hBc : B.card ≤ 2 := by
    simpa only [B,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_image_le (f := b) (s := (Finset.univ : Finset (Fin 2))))
  have hCc : C.card ≤ 4 := by
    simpa only [C,Finset.card_univ,Fintype.card_finset,Fintype.card_fin,
      show (2 : ℕ)^2 = 4 by decide] using
      (Finset.card_image_le (f := y) (s := (Finset.univ : Finset (Finset (Fin 2)))))
  have hSc : S.card ≤ 8 := by
    have h1 := Finset.card_union_le A B
    have h2 := Finset.card_union_le (A ∪ B) C
    dsimp [S]
    omega
  have hsub : (↑S : Set Point) ⊆ K := by
    intro x hx
    simp only [S,A,B,C,Finset.mem_coe,Finset.mem_union,Finset.mem_image,Finset.mem_univ,
      true_and] at hx
    rcases hx with (⟨i,rfl⟩ | ⟨i,rfl⟩) | ⟨s,rfl⟩
    · exact ha i
    · exact hb i
    · exact hy s
  have hex : K.extremePoints ℝ ⊆ (↑S : Set Point) := by
    intro x hx
    rcases hloc x hx with ⟨i,hi⟩ | ⟨s,hs⟩
    · rcases hab i x hx hi with rfl | rfl
      · simp [S,A]
      · simp [S,B]
    · rw [hyprop s x hs]
      simp [S,C]
  refine ⟨S,hSc,hsub,Subset.antisymm ?_ (convexHull_min hsub hconv)⟩
  rw [← closure_convexHull_extremePoints hK hconv]
  exact closure_minimal (convexHull_mono hex) (S.finite_toSet.isClosed_convexHull ℝ)

end Plank.PlanarFiniteExtremeHull

/-- info: 'Plank.PlanarFiniteExtremeHull.eight_of_locations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFiniteExtremeHull.eight_of_locations
