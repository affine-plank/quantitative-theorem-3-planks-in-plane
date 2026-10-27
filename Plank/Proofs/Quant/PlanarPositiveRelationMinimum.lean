/- Close the quantitative minimum directly when the coordinates have a
positive affine relation. -/
module
public import Plank.Proofs.Quant.PlanarSixContactMinimum
public import Plank.Proofs.Quant.FiniteDimensionalMinimumCompletion
public import Plank.Proofs.Quant.FiniteDimensionalNormalization
public import Plank.Proofs.Quant.PlanarTwoPlankCells
public import Plank.Proofs.Quant.PlanarSevenNonemptyBound

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPositiveRelationMinimum

open Set MeasureTheory Filter FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalParameterDomain FiniteDimensionalMinimumCompletion
  FiniteDimensionalNormalization PlanarSixContactMinimum
open scoped Topology BigOperators

variable {n m : ℕ}

/-- Ordinary interior also excludes contact with either supporting level. -/
theorem strict_endpoints_of_interior (K : Set (Point n))
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) {p : Endpoints (Fin m)}
    (hp : p ∈ interior (domain K f)) :
    ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1 := by
  have hs : domain K f ⊆
      (univ.pi fun _ : Fin m => Ici (0 : ℝ)) ×ˢ
        (univ.pi fun _ : Fin m => Iic (1 : ℝ)) := by
    intro q hq
    exact ⟨fun i _ => (hq.1 i).1, fun i _ => (hq.1 i).2.2⟩
  have h := interior_mono hs hp
  rw [interior_prod_eq, interior_pi_set finite_univ,
    interior_pi_set finite_univ] at h
  simp only [interior_Ici, interior_Iic] at h
  exact fun i => ⟨h.1 i (mem_univ i), strict_windows_of_interior K f hp i,
    h.2 i (mem_univ i)⟩

/-- The shared quantitative reduction leaves only the six-contact cover
geometry to prove for a positive affine relation. No completed three-plank
covering theorem is an input. -/
theorem bound_normalized (h2 : FiniteDimensionalInductionBoundary.SharpBound n 2)
    {K : Set (Point n)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin 3 → (Point n) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (hcell : ManyCellBound K f)
    (c : Fin 3 → ℝ) (level : ℝ) (hcpos : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i * f i x = level)
    (p₀ : Endpoints (Fin 3)) (hp₀ : p₀ ∈ domain K f) :
    (max 0 (1-budget K f p₀))^(n+1)*(volume K).toReal ≤ gapVolume K f p₀ := by
  refine FiniteDimensionalMinimumCompletion.bound_normalized_of_counted_covers
    h2 hK hc hne hV f hnorm hunit hcell ?_ p₀ hp₀
  intro p hp hcover hcount
  have himage : Convex ℝ (coordinateImage K f) := hc.affine_image (AffineMap.pi f)
  have hL : ∀ i, ∃ x ∈ coordinateImage K f, x i = 0 := by
    intro i
    obtain ⟨x,hx,hxi⟩ := (unit_realisers hK hne (f i) (hnorm i) (hunit i)).1
    exact ⟨fun j => f j x,⟨x,hx,rfl⟩,hxi⟩
  have hU : ∀ i, ∃ x ∈ coordinateImage K f, x i = 1 := by
    intro i
    obtain ⟨x,hx,hxi⟩ := (unit_realisers hK hne (f i) (hnorm i) (hunit i)).2
    exact ⟨fun j => f j x,⟨x,hx,rfl⟩,hxi⟩
  have hcoordinateCover : Convex.PlanarCoverSpace.Covers (coordinateImage K f) p := by
    rintro _ ⟨x,hx,rfl⟩
    exact mem_iUnion.mp (hcover hx)
  have hwidth := PlanarSixContactMinimum.width_bound_of_six_contact_cells himage hL hU c level hcpos
    (by rintro _ ⟨x,hx,rfl⟩; exact hplane x hx)
    (strict_endpoints_of_interior K f hp) hcoordinateCover
    hcount
  simpa [budget,hunit] using hwidth

/-- In the plane the two-plank and seven-cell inputs are already proved.
Thus a positive affine relation gives the full quantitative inequality. -/
theorem planar_bound_normalized
    {K : Set (Point 1)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin 3 → (Point 1) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (c : Fin 3 → ℝ) (level : ℝ) (hcpos : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i * f i x = level)
    (p₀ : Endpoints (Fin 3)) (hp₀ : p₀ ∈ domain K f) :
    (max 0 (1-budget K f p₀))^2*(volume K).toReal ≤ gapVolume K f p₀ :=
  bound_normalized PlanarTwoPlankCells.sharpBound_two hK hc hne hV f hnorm hunit
    (PlanarSevenNonemptyBound.manyCellBound hK hc hne f hnorm hunit)
    c level hcpos hplane p₀ hp₀

end Plank.PlanarPositiveRelationMinimum

#print axioms Plank.PlanarPositiveRelationMinimum.strict_endpoints_of_interior
#print axioms Plank.PlanarPositiveRelationMinimum.bound_normalized
#print axioms Plank.PlanarPositiveRelationMinimum.planar_bound_normalized
