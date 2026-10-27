/- Exhaustive equality families for four-point bodies and actual two-plank equality. -/
module

public import Plank.Proofs.Quant.PlanarAffineEquality
public import Plank.Proofs.Quant.PlanarTwoPlankShapeOriginal

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFourPointClassification

open Set MeasureTheory PlanarQuantitative FourPointHalfplanes FourPointPlacements
open PlanarAffineEquality PlanarParameterDomain
open Plank.Convex.DeficientHeightTilt

variable {ι : Type*} [Fintype ι]

/-- The explicit affine family: pull back one normalized four-point body
and a tuple passing the finite arithmetic placement tests. The predicate
does not assume the quantitative area equality. -/
def Family (K : Set Point) (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) : Prop :=
  ∃ (T : Point ≃ᵃ[ℝ] Point) (a b : ℝ), T '' K = body a b ∧
    TightParameters a b (fun i => transform T (f i)) lo hi

theorem family_sound {K : Set Point} (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, lo i ≤ hi i)
    (hfamily : Family K f lo hi) : Equality K f lo hi := by
  obtain ⟨T,a,b,hK,ht⟩ := hfamily
  have hw (i) : 0 < width a b (transform T (f i)) := by
    rw [← rangeWidth_eq,← hK,rangeWidth_transform]
    exact hW i
  have he : Equality (body a b) (fun i => transform T (f i)) lo hi :=
    (FourPointPlacements.equality_iff a b _ lo hi hw ho).mpr ht
  rw [← hK] at he
  exact (equality_transform_iff T K f lo hi).mp he

/-- Every positive-area body which is a hull of at most four points has
the same exhaustive arithmetic classification, in original coordinates.
This applies to every finite number of planks, with no genericity assumptions. -/
theorem equality_iff_of_four_vertices {K : Set Point}
    (hV : 0 < (volume K).toReal) (hs : ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d})
    (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, lo i ≤ hi i) :
    Equality K f lo hi ↔ Family K f lo hi := by
  classical
  constructor
  · intro he
    obtain ⟨a,b,c,d,hK⟩ := hs
    let v : Finset Point := {a,b,c,d}
    have hv : v.card ≤ 4 := by
      have h1 := Finset.card_insert_le a ({b,c,d} : Finset Point)
      have h2 := Finset.card_insert_le b ({c,d} : Finset Point)
      have h3 := Finset.card_insert_le c ({d} : Finset Point)
      have h4 : ({d} : Finset Point).card = 1 := Finset.card_singleton d
      dsimp [v]
      omega
    have hKv : K = convexHull ℝ (v : Set Point) := by simpa [v] using hK
    obtain ⟨T,u,w,hT⟩ := FourPointNormalization.normalize v hv (hKv ▸ hV)
    rw [← hKv] at hT
    refine ⟨T,u,w,hT,?_⟩
    have hw (i) : 0 < width u w (transform T (f i)) := by
      rw [← rangeWidth_eq,← hT,rangeWidth_transform]
      exact hW i
    apply (FourPointPlacements.equality_iff u w _ lo hi hw ho).mp
    have hh := (equality_transform_iff T K f lo hi).mpr he
    rwa [hT] at hh
  · exact family_sound f lo hi hW ho

/-- Complete two-plank classification in the positive-deficit regime.
The body restriction is derived, not assumed; the reverse direction is
proved for every member of the explicit affine/arithmetic family. -/
theorem two_plank_iff {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1) :
    gapArea K f p = (1-budget K f p)^2*(volume K).toReal ↔ Family K f p.1 p.2 := by
  have hequiv : Equality K f p.1 p.2 ↔
      gapArea K f p = (1-budget K f p)^2*(volume K).toReal := by
    change (gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal) ↔ _
    rw [max_eq_right (sub_pos.mpr hR1).le]
  constructor
  · intro he
    have hs := PlanarTwoPlankShapeOriginal.four_vertices hK hc hne hV f p hW ho hR0 hR1 he
    exact (equality_iff_of_four_vertices hV hs f p.1 p.2 hW ho).mp (hequiv.mpr he)
  · exact fun hf => hequiv.mp (family_sound f p.1 p.2 hW ho hf)

end Plank.PlanarFourPointClassification

/-- info: 'Plank.PlanarFourPointClassification.two_plank_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFourPointClassification.two_plank_iff
