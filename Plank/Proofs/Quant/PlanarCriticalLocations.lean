/- All orientations of the critical triangular-enclosure vertex reduction. -/
module

public import Plank.Proofs.Quant.PlanarTriangularSections
public import Plank.Proofs.Quant.PlanarCriticalShapeAlternatives

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCriticalLocations

open Set PlanarQuantitative PlanarSingletonCorners PlanarCriticalAnchoredShape
open Plank.Convex.PlanarTight TwoPlankClassification

def Locations (K : Set Point) (X Y : Point →ᵃ[ℝ] ℝ)
    (qX qY l u m v : ℝ) : Prop :=
  ∀ x ∈ K.extremePoints ℝ, X x = qX ∨ Y x = qY ∨
    ∃ sx sy, corner K X Y l u m v sx sy = {x}

/-- A terminal cut avoids a support endpoint at which its critical
window is anchored. Actual strict initial windows imply these conditions. -/
def Clears (qX qY l u m v : ℝ) : Prop :=
  (l = 0 → 0 < qX) ∧ (u = 1 → qX < 1) ∧
    (m = 0 → 0 < qY) ∧ (v = 1 → qY < 1)

/-- The two normalized coordinates agree or are complementary on K. -/
def Paired (K : Set Point) (X Y : Point →ᵃ[ℝ] ℝ) : Prop :=
  (∀ x ∈ K, Y x = X x) ∨ (∀ x ∈ K, Y x = 1-X x)

theorem Locations.swap {K : Set Point} {X Y : Point →ᵃ[ℝ] ℝ}
    {qX qY l u m v : ℝ} (h : Locations K X Y qX qY l u m v) :
    Locations K Y X qY qX m v l u := by
  intro x hx
  rcases h x hx with hh | hh | ⟨sx,sy,hh⟩
  · exact Or.inr (Or.inl hh)
  · exact Or.inl hh
  · exact Or.inr (Or.inr ⟨sy,sx,by rwa [corner_swap]⟩)

theorem Locations.reflect {K : Set Point} {X Y : Point →ᵃ[ℝ] ℝ}
    {qX qY l u m v : ℝ} (h : Locations K X Y qX qY l u m v) :
    Locations K (reflect X) Y (1-qX) qY (1-u) (1-l) m v := by
  intro x hx
  rcases h x hx with hh | hh | ⟨sx,sy,hh⟩
  · exact Or.inl (by rw [reflect_apply,hh])
  · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr ⟨!sx,sy,by simpa only [corner_reflect,Bool.not_not] using hh⟩)

theorem Clears.swap {qX qY l u m v : ℝ} (h : Clears qX qY l u m v) :
    Clears qY qX m v l u := ⟨h.2.2.1,h.2.2.2,h.1,h.2.1⟩

theorem Clears.reflect {qX qY l u m v : ℝ} (h : Clears qX qY l u m v) :
    Clears (1-qX) qY (1-u) (1-l) m v := by
  refine ⟨fun hu => ?_,fun hl => ?_,h.2.2.1,h.2.2.2⟩
  · have hh := h.2.1 (by linarith only [hu])
    linarith only [hh]
  · have hh := h.1 (by linarith only [hl])
    linarith only [hh]

theorem Paired.swap {K : Set Point} {X Y : Point →ᵃ[ℝ] ℝ}
    (h : Paired K X Y) : Paired K Y X := by
  rcases h with h | h
  · exact Or.inl (fun x hx => (h x hx).symm)
  · exact Or.inr (fun x hx => by linarith only [h x hx])

theorem paired_of_reflect {K : Set Point} {X Y : Point →ᵃ[ℝ] ℝ}
    (h : Paired K (reflect X) Y) : Paired K X Y := by
  rcases h with h | h
  · exact Or.inr (fun x hx => by simpa only [reflect_apply] using h x hx)
  · exact Or.inl (fun x hx => by have hh := h x hx; rw [reflect_apply] at hh; linarith only [hh])

theorem triangle_case {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (hshape : ∀ x ∈ K, X x+Y x ≤ 1)
    (qX qY u : ℝ) (hqX : 0 < qX) (hqX1 : qX ≤ 1)
    (hqY : 0 < qY) (hqY1 : qY ≤ 1) (hu : 0 < u) (hu1 : u < 1)
    (hloc : Locations K X Y qX qY 0 u 0 (1-u)) :
    (∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) ∨ Paired K X Y := by
  rcases PlanarTriangularExtreme.injective_or_complementary X Y H hshape with hi | hc
  · exact Or.inl (PlanarTriangularSections.four_of_locations hK hconv X Y H hi hshape
      qX qY u hqX hqX1 hqY hqY1 hu hu1 hloc)
  · exact Or.inr (Or.inr hc)

/-- Both endpoint-apex enclosures force a four-vertex body, except for
the normalized parallel case. This is purely geometric. -/
theorem anchored_case {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (qX qY l u m v : ℝ) (hqX : 0 ≤ qX ∧ qX ≤ 1) (hqY : 0 ≤ qY ∧ qY ≤ 1)
    (hclear : Clears qX qY l u m v) (hloc : Locations K X Y qX qY l u m v)
    (hn : DegenerateAnchored K X Y l u m v) :
    (∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) ∨ Paired K X Y := by
  rcases hn with ⟨hl,hu,hu1,hc⟩
  subst l
  rcases hc with ⟨hm,hv,hshape⟩ | ⟨hm,hv,hshape⟩
  · subst m
    subst v
    exact triangle_case hK hconv X Y H hshape qX qY u (hclear.1 rfl) hqX.2
      (hclear.2.2.1 rfl) hqY.2 hu hu1 hloc
  · subst m
    subst v
    have hshape' : ∀ x ∈ K, X x+(reflect Y) x ≤ 1 := by
      intro x hx
      rw [reflect_apply]
      linarith only [hshape x hx]
    have hloc' : Locations K X (reflect Y) qX (1-qY) 0 u 0 (1-u) := by
      simpa only [sub_self] using hloc.swap.reflect.swap
    rcases triangle_case hK hconv X (reflect Y) H.swap.reflect.swap hshape'
      qX (1-qY) u (hclear.1 rfl) hqX.2
      (by linarith only [hclear.2.2.2 rfl]) (by linarith only [hqY.1]) hu hu1 hloc' with hf | hp
    · exact Or.inl hf
    · exact Or.inr (paired_of_reflect hp.swap).swap

/-- Every degenerate critical normal form satisfies the same
four-vertex-or-parallel alternative; all reflections and swaps are included. -/
theorem normal_case {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (qX qY l u m v : ℝ) (hqX : 0 ≤ qX ∧ qX ≤ 1) (hqY : 0 ≤ qY ∧ qY ≤ 1)
    (hclear : Clears qX qY l u m v) (hloc : Locations K X Y qX qY l u m v)
    (hn : PlanarCriticalShapeAlternatives.DegenerateNormal K X Y l u m v) :
    (∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) ∨ Paired K X Y := by
  rcases hn with h | h | h | h
  · exact anchored_case hK hconv X Y H qX qY l u m v hqX hqY hclear hloc h
  · rcases anchored_case hK hconv (reflect X) Y H.reflect (1-qX) qY (1-u) (1-l) m v
      ⟨by linarith only [hqX.2],by linarith only [hqX.1]⟩ hqY hclear.reflect hloc.reflect h with hf | hp
    · exact Or.inl hf
    · exact Or.inr (paired_of_reflect hp)
  · rcases anchored_case hK hconv Y X H.swap qY qX m v l u hqY hqX hclear.swap hloc.swap h with hf | hp
    · exact Or.inl hf
    · exact Or.inr hp.swap
  · rcases anchored_case hK hconv (reflect Y) X H.swap.reflect (1-qY) qX (1-v) (1-m) l u
      ⟨by linarith only [hqY.2],by linarith only [hqY.1]⟩ hqX hclear.swap.reflect hloc.swap.reflect h with hf | hp
    · exact Or.inl hf
    · exact Or.inr (paired_of_reflect hp).swap

end Plank.PlanarCriticalLocations

/-- info: 'Plank.PlanarCriticalLocations.normal_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCriticalLocations.normal_case
