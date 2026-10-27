/- Construct concave section densities and actual single-plank derivatives. -/
module

public import Plank.Proofs.Quant.PlanarWindowData

public import Plank.Proofs.Quant.PlanarSectionConcavity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarBodySectionDensity

open Set MeasureTheory PlanarQuantitative PlanarPolygonHalfplanes
open PlanarDirectionDerivatives PlanarSectionDerivatives PlanarSectionConcavity
open PlanarSevenCellArea (plank)

/-- A section density is attached to the actual body and affine coordinate.
Both endpoint derivative identities are part of its proved geometric data. -/
structure BodySectionDensity (K : Set Point) (g : Point →ᵃ[ℝ] ℝ) where
  density : ℝ → ℝ
  continuous : Continuous density
  nonnegative : ∀ t, 0 ≤ density t
  concave : ConcaveOn ℝ (g '' K) density
  lower_deriv : ∀ lo hi, lo < hi →
    HasDerivAt (fun t => coveredArea K g t hi) (-density lo) lo
  upper_deriv : ∀ lo hi, lo < hi →
    HasDerivAt (fun t => coveredArea K g lo t) (density hi) hi
  line_deriv : ∀ lo hi, lo < hi → ∀ a b : ℝ,
    HasDerivAt (fun t => coveredArea K g (lo+t*a) (hi+t*b))
      (density hi*b-density lo*a) 0

/-- The actual body intersected with a plank has an exact boxed-coordinate
representation for every pair of endpoints. Only the transverse coordinate
needs a fixed enclosing interval. -/
theorem body_plank_eq_boxed_preimage {ι : Type*} (K : Set Point)
    (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (hK : K = {x | ∀ i, F i x ≤ C i})
    (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0) (c d : ℝ)
    (hbound : ∀ x ∈ K, directionCoordinates g hg x 1 ∈ Icc c d) (lo hi : ℝ) :
    K ∩ plank g lo hi = directionCoordinates g hg ⁻¹'
      boxedRegion (lo-g 0) (hi-g 0) c d
        (bodyA (directionCoordinates g hg) F) (bodyB (directionCoordinates g hg) F)
        (bodyC F C) := by
  let T := directionCoordinates g hg
  ext x
  have he (i) := affine_eval_coordinates (transform T (F i)) (T x)
  simp only [transform_apply, transform_zero] at he
  have hx0 := directionCoordinates_first g hg x
  constructor
  · intro hx
    refine ⟨?_, hbound x hx.1, fun i => ?_⟩
    · change lo-g 0 ≤ T x 0 ∧ T x 0 ≤ hi-g 0
      rw [hx0]
      exact ⟨sub_le_sub_right hx.2.1 _, sub_le_sub_right hx.2.2 _⟩
    · have hmem : x ∈ {x | ∀ i, F i x ≤ C i} := by rw [← hK]; exact hx.1
      have hi := hmem i
      change bodyA T F i*T x 0+bodyB T F i*T x 1 ≤ C i-F i 0
      dsimp [bodyA, bodyB]
      linarith only [he i, hi]
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [hK]
      intro i
      have hi := hx.2.2 i
      change bodyA T F i*T x 0+bodyB T F i*T x 1 ≤ C i-F i 0 at hi
      dsimp [bodyA, bodyB] at hi
      linarith only [he i, hi]
    · have hx' := hx.1
      change lo-g 0 ≤ T x 0 ∧ T x 0 ≤ hi-g 0 at hx'
      rw [hx0] at hx'
      constructor <;> linarith only [hx'.1, hx'.2]

/-- Every compact convex finite-half-plane body transverse to the given
nonzero affine coordinate has a continuous nonnegative concave section
density giving the actual covered-area endpoint derivatives. -/
theorem exists_bodySectionDensity {ι : Type*} [Fintype ι]
    (K : Set Point) (hcompact : IsCompact K) (hconv : Convex ℝ K)
    (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (hK : K = {x | ∀ i, F i x ≤ C i})
    (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0) (hbody : ∀ i, cross g (F i) ≠ 0) :
    Nonempty (BodySectionDensity K g) := by
  classical
  let T := directionCoordinates g hg
  obtain ⟨M, _, hM⟩ := (hcompact.image T.toContinuousLinearEquiv.continuous).isBounded.exists_pos_norm_le
  have hbound (x) (hx : x ∈ K) : T x 1 ∈ Icc (-M) M := by
    have hh := (norm_le_pi_norm (T x) 1).trans (hM _ ⟨x, hx, rfl⟩)
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hh)
  let A := bodyA T F
  let B := bodyB T F
  let E := bodyC F C
  have hB (i) : B i ≠ 0 := transform_second_ne_zero g hg (F i) (hbody i)
  let ls := graphSlope (p := fun i => B i < 0) A B
  let lc := graphOffset (p := fun i => B i < 0) B E (-M)
  let us := graphSlope (p := fun i => 0 < B i) A B
  let uc := graphOffset (p := fun i => 0 < B i) B E M
  let L := sectionLength ls lc us uc
  let D := fun t => areaFactor T * L (t-g 0)
  have hrep (lo hi) : K ∩ plank g lo hi = T ⁻¹'
      boxedRegion (lo-g 0) (hi-g 0) (-M) M A B E :=
    body_plank_eq_boxed_preimage K F C hK g hg (-M) M hbound lo hi
  have harea (lo hi) : coveredArea K g lo hi = areaFactor T *
      (volume (boxedRegion (lo-g 0) (hi-g 0) (-M) M A B E)).toReal := by
    rw [coveredArea, hrep, area_preimage]
  have hordered : ∀ t ∈ g '' K,
      lowerEnvelope ls lc (t-g 0) ≤ upperEnvelope us uc (t-g 0) := by
    rintro t ⟨x, hx, rfl⟩
    have hp : T x ∈ boxedRegion (g x-g 0) (g x-g 0) (-M) M A B E := by
      change x ∈ T ⁻¹' boxedRegion (g x-g 0) (g x-g 0) (-M) M A B E
      rw [← hrep]
      exact ⟨hx, le_rfl, le_rfl⟩
    rw [boxedRegion_eq_closedSlab _ _ _ _ _ _ _ hB] at hp
    have hl : lowerEnvelope ls lc (T x 0) ≤ T x 1 :=
      (lowerEnvelope_le_iff _ _ _ _).mpr hp.2.1
    have hu : T x 1 ≤ upperEnvelope us uc (T x 0) :=
      (le_upperEnvelope_iff _ _ _ _).mpr hp.2.2
    have hh := hl.trans hu
    simpa only [T, directionCoordinates_first] using hh
  have hconc : ConcaveOn ℝ (g '' K) (fun t => L (t-g 0)) := by
    let shift : ℝ →ᵃ[ℝ] ℝ := AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ (g 0)
    have hc : Convex ℝ (g '' K) := hconv.affine_image g
    have hshift : ConcaveOn ℝ (shift '' (g '' K)) L := by
      apply concaveOn_sectionLength ls lc us uc (hc.affine_image shift)
      rintro t ⟨u, hu, rfl⟩
      exact hordered u hu
    exact (hshift.comp_affineMap shift).subset (fun t ht => ⟨t, ht, rfl⟩) hc
  refine ⟨{
    density := D
    continuous := continuous_const.mul
      ((continuous_sectionLength_level ls lc us uc).comp (continuous_id.sub continuous_const))
    nonnegative := fun t => mul_nonneg (areaFactor_pos T).le (sectionLength_nonneg _ _ _ _ _)
    concave := hconc.smul (areaFactor_pos T).le
    lower_deriv := ?_
    upper_deriv := ?_
    line_deriv := ?_ }⟩
  · intro lo hi horder
    have hd := hasDerivAt_area_boxedRegion_left (sub_lt_sub_right horder (g 0)) (-M) M A B E hB
    have hh := ((hd.comp lo ((hasDerivAt_id lo).sub_const (g 0))).const_mul (areaFactor T))
    simp only [Function.comp_def, mul_one, mul_neg] at hh
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => harea t hi))
  · intro lo hi horder
    have hd := hasDerivAt_area_boxedRegion_right (sub_lt_sub_right horder (g 0)) (-M) M A B E hB
    have hh := ((hd.comp hi ((hasDerivAt_id hi).sub_const (g 0))).const_mul (areaFactor T))
    simp only [Function.comp_def, mul_one] at hh
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => harea lo t))
  · intro lo hi horder a b
    have hp : HasDerivAt (fun t : ℝ => (lo+t*a-g 0, hi+t*b-g 0)) (a, b) 0 := by
      convert! ((((hasDerivAt_id (0 : ℝ)).mul_const a).const_add lo).sub_const (g 0)).prodMk
        ((((hasDerivAt_id (0 : ℝ)).mul_const b).const_add hi).sub_const (g 0)) using 1
      simp
    have hd := hasFDerivAt_area_closedSlab (sub_lt_sub_right horder (g 0)) ls lc us uc
    have hc := (hd.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)).const_mul
      (areaFactor T)
    have hh : HasDerivAt (fun t : ℝ => areaFactor T *
        (volume (closedSlab (lo+t*a-g 0) (hi+t*b-g 0) ls lc us uc)).toReal)
        (D hi*b-D lo*a) 0 := by
      convert! hc using 1
      simp [D, L]
      ring
    apply hh.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only
      rw [harea, boxedRegion_eq_closedSlab _ _ _ _ _ _ _ hB])

theorem BodySectionDensity.concave_unit {K : Set Point} {g : Point →ᵃ[ℝ] ℝ}
    (D : BodySectionDensity K g) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hnorm : ∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1)
    (hunit : Plank.Convex.DeficientHeightTilt.rangeWidth K g = 1) :
    ConcaveOn ℝ (Icc 0 1) D.density := by
  rw [← image_eq_unitInterval hK hconv hne g hnorm hunit]
  exact D.concave

end Plank.PlanarBodySectionDensity
