/- Transport actual section derivatives to arbitrary nonzero affine directions. -/
module

public import Plank.Proofs.Quant.PlanarAffineCoordinates

public import Plank.Proofs.Quant.PlanarGapSectionDerivatives
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarDirectionDerivatives

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarPolygonHalfplanes
open PlanarSectionDerivatives PlanarGapSectionDerivatives PlanarPlankCellCharts

/-- Coordinates with first coordinate `a*x0+b*x1`. The second coordinate
is a fixed transverse direction, and the inverse is explicit. -/
def coordinates (a b : ℝ) (h : 0 < a^2+b^2) : Point ≃ₗ[ℝ] Point where
  toFun x := ![a*x 0+b*x 1, -b*x 0+a*x 1]
  invFun y := ![(a*y 0-b*y 1)/(a^2+b^2), (b*y 0+a*y 1)/(a^2+b^2)]
  left_inv x := by
    ext i
    fin_cases i <;> dsimp <;>
      field_simp [ne_of_gt h] <;> ring
  right_inv y := by
    ext i
    fin_cases i <;> dsimp <;>
      field_simp [ne_of_gt h] <;> ring
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp <;> ring

theorem coefficients_sq_pos (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) :
    0 < (f.linear (Pi.single 0 1))^2+(f.linear (Pi.single 1 1))^2 := by
  by_cases hb : f.linear (Pi.single 1 1) = 0
  · have ha := coefficients_nonzero f hf hb
    simpa only [hb, zero_pow (by decide : 2 ≠ 0), add_zero] using sq_pos_of_ne_zero ha
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb)

def directionCoordinates (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) : Point ≃ₗ[ℝ] Point :=
  coordinates _ _ (coefficients_sq_pos f hf)

theorem directionCoordinates_first (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (x : Point) :
    directionCoordinates f hf x 0 = f x-f 0 := by
  change f.linear (Pi.single 0 1)*x 0+f.linear (Pi.single 1 1)*x 1 = f x-f 0
  rw [affine_eval_coordinates]
  ring

/-- The same affine form expressed in new linear coordinates. -/
def transform (T : Point ≃ₗ[ℝ] Point) (f : Point →ᵃ[ℝ] ℝ) : Point →ᵃ[ℝ] ℝ :=
  f.comp (T.symm : Point →ₗ[ℝ] Point).toAffineMap

@[simp] theorem transform_apply (T : Point ≃ₗ[ℝ] Point) (f : Point →ᵃ[ℝ] ℝ) (x : Point) :
    transform T f (T x) = f x := by
  change f (T.symm (T x)) = f x
  rw [T.symm_apply_apply]

@[simp] theorem transform_zero (T : Point ≃ₗ[ℝ] Point) (f : Point →ᵃ[ℝ] ℝ) :
    transform T f 0 = f 0 := by
  change f (T.symm 0) = f 0
  rw [map_zero]

/-- Transversality is exactly the nonzero coefficient required by the
coordinate section calculation. -/
theorem transform_second (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    (f : Point →ᵃ[ℝ] ℝ) :
    (transform (directionCoordinates g hg) f).linear (Pi.single 1 1) =
      cross g f / ((g.linear (Pi.single 0 1))^2+(g.linear (Pi.single 1 1))^2) := by
  have heval := affine_eval_coordinates f
    ((directionCoordinates g hg).symm (Pi.single 1 1))
  have hlin := affine_eval f ((directionCoordinates g hg).symm (Pi.single 1 1))
  change f.linear ((directionCoordinates g hg).symm (Pi.single 1 1)) = _
  dsimp [directionCoordinates, coordinates] at heval hlin ⊢
  norm_num at heval hlin ⊢
  unfold cross
  linear_combination heval - hlin

theorem transform_second_ne_zero (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    (f : Point →ᵃ[ℝ] ℝ) (ht : cross g f ≠ 0) :
    (transform (directionCoordinates g hg) f).linear (Pi.single 1 1) ≠ 0 := by
  rw [transform_second]
  exact div_ne_zero ht (ne_of_gt (coefficients_sq_pos g hg))

/-- Remove any fixed family of planks and one distinguished plank. -/
def distinguishedGap {κ : Type*} (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ)
    (g : Point →ᵃ[ℝ] ℝ) (lo hi : κ → ℝ) (ell h : ℝ) : Set Point :=
  (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) \ {x | ell ≤ g x ∧ g x ≤ h}

/-- Exact set transport, including the affine constant of the moving
plank. The representation concerns the actual body. -/
theorem distinguishedGap_eq_preimage {ι κ : Type*}
    (K : Set Point) (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    (a b c d : ℝ) (A B C : ι → ℝ)
    (hK : K = directionCoordinates g hg ⁻¹' boxedRegion a b c d A B C)
    (f : κ → Point →ᵃ[ℝ] ℝ) (lo hi : κ → ℝ) (ell h : ℝ) :
    distinguishedGap K f g lo hi ell h = directionCoordinates g hg ⁻¹'
      verticalGap a b c d A B C (fun i => transform (directionCoordinates g hg) (f i))
        lo hi (ell-g 0) (h-g 0) := by
  ext x
  simp only [distinguishedGap, verticalGap, boxedGap, mem_sdiff, mem_preimage,
    mem_iUnion, mem_ofPred_eq, transform_apply, directionCoordinates_first, hK,
    sub_le_sub_iff_right]

def directionalSectionLength {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    (c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (p : EndpointSpace κ × ℝ) : ℝ :=
  areaFactor (directionCoordinates g hg) * residualSectionLength c d A B C
    (fun i => transform (directionCoordinates g hg) (f i)) p.1 (p.2-g 0)

theorem continuous_directionalSectionLength {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    (c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ) :
    Continuous (directionalSectionLength g hg c d A B C f) := by
  have hp : Continuous (fun p : EndpointSpace κ × ℝ => (p.1, p.2-g 0)) :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hL := (continuous_residualSectionLength c d A B C
    (fun i => transform (directionCoordinates g hg) (f i))).comp hp
  exact continuous_const.mul hL

/-- Lower-endpoint differentiation is invariant under the constructed
coordinates, with the proved area factor included. -/
theorem hasDerivAt_distinguishedGap_lower_of_rep {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : Set Point) (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    (a b c d : ℝ) (A B C : ι → ℝ)
    (hK : K = directionCoordinates g hg ⁻¹' boxedRegion a b c d A B C)
    (hB : ∀ i, B i ≠ 0) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, cross g (f i) ≠ 0) (lo hi : κ → ℝ) (hwidth : ∀ i, lo i ≤ hi i)
    (ell h : ℝ) (hell : a < ell-g 0) (horder : ell < h) (hh : h-g 0 < b) :
    HasDerivAt (fun t => (volume (distinguishedGap K f g lo hi t h)).toReal)
      (directionalSectionLength g hg c d A B C f ((lo, hi), ell)) ell := by
  have hd := hasDerivAt_area_verticalGap_lower hell (sub_lt_sub_right horder (g 0)) hh
    c d A B C (fun i => transform (directionCoordinates g hg) (f i)) hB
    (fun i => transform_second_ne_zero g hg (f i) (hf i)) lo hi hwidth
  have hchain := ((hd.comp ell ((hasDerivAt_id ell).sub_const (g 0))).const_mul
    (areaFactor (directionCoordinates g hg)))
  simp only [Function.comp_def, mul_one] at hchain
  apply hchain.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only [id]
    rw [distinguishedGap_eq_preimage K g hg a b c d A B C hK, area_preimage])

theorem hasDerivAt_distinguishedGap_upper_of_rep {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : Set Point) (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    (a b c d : ℝ) (A B C : ι → ℝ)
    (hK : K = directionCoordinates g hg ⁻¹' boxedRegion a b c d A B C)
    (hB : ∀ i, B i ≠ 0) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, cross g (f i) ≠ 0) (lo hi : κ → ℝ) (hwidth : ∀ i, lo i ≤ hi i)
    (ell h : ℝ) (hell : a < ell-g 0) (horder : ell < h) (hh : h-g 0 < b) :
    HasDerivAt (fun t => (volume (distinguishedGap K f g lo hi ell t)).toReal)
      (-directionalSectionLength g hg c d A B C f ((lo, hi), h)) h := by
  have hd := hasDerivAt_area_verticalGap_upper hell (sub_lt_sub_right horder (g 0)) hh
    c d A B C (fun i => transform (directionCoordinates g hg) (f i)) hB
    (fun i => transform_second_ne_zero g hg (f i) (hf i)) lo hi hwidth
  have hchain := ((hd.comp h ((hasDerivAt_id h).sub_const (g 0))).const_mul
    (areaFactor (directionCoordinates g hg)))
  simp only [Function.comp_def, mul_one, mul_neg] at hchain
  apply hchain.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only [id]
    rw [distinguishedGap_eq_preimage K g hg a b c d A B C hK, area_preimage])

def bodyA {ι : Type*} (T : Point ≃ₗ[ℝ] Point) (F : ι → Point →ᵃ[ℝ] ℝ) (i : ι) : ℝ :=
  (transform T (F i)).linear (Pi.single 0 1)

def bodyB {ι : Type*} (T : Point ≃ₗ[ℝ] Point) (F : ι → Point →ᵃ[ℝ] ℝ) (i : ι) : ℝ :=
  (transform T (F i)).linear (Pi.single 1 1)

def bodyC {ι : Type*} (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (i : ι) : ℝ := C i-F i 0

/-- A finite affine half-plane body has the required representation after
the coordinate change, once an enclosing rectangle has been supplied. -/
theorem body_eq_boxed_preimage {ι : Type*} (K : Set Point)
    (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (hK : K = {x | ∀ i, F i x ≤ C i})
    (T : Point ≃ₗ[ℝ] Point) (a b c d : ℝ)
    (hbox : ∀ x ∈ K, T x 0 ∈ Icc a b ∧ T x 1 ∈ Icc c d) :
    K = T ⁻¹' boxedRegion a b c d (bodyA T F) (bodyB T F) (bodyC F C) := by
  ext x
  have he (i) := affine_eval_coordinates (transform T (F i)) (T x)
  simp only [transform_apply, transform_zero] at he
  constructor
  · intro hx
    refine ⟨(hbox x hx).1, (hbox x hx).2, fun i => ?_⟩
    have hmem : x ∈ {x | ∀ i, F i x ≤ C i} := by rwa [← hK]
    have hi : F i x ≤ C i := hmem i
    change bodyA T F i*T x 0+bodyB T F i*T x 1 ≤ C i-F i 0
    dsimp [bodyA, bodyB]
    linarith only [he i, hi]
  · intro hx
    rw [hK]
    intro i
    have hi := hx.2.2 i
    change bodyA T F i*T x 0+bodyB T F i*T x 1 ≤ C i-F i 0 at hi
    dsimp [bodyA, bodyB] at hi
    linarith only [he i, hi]

/-- A bound on the transformed compact body supplies every enclosing
rectangle needed to differentiate at arbitrary finite plank endpoints. -/
theorem body_eq_boxed_preimage_of_bound {ι : Type*} (K : Set Point)
    (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (hK : K = {x | ∀ i, F i x ≤ C i})
    (T : Point ≃ₗ[ℝ] Point) (M : ℝ) (hM : ∀ x ∈ K, ‖T x‖ ≤ M)
    (a b : ℝ) (ha : a ≤ -M) (hb : M ≤ b) :
    K = T ⁻¹' boxedRegion a b (-M) M (bodyA T F) (bodyB T F) (bodyC F C) := by
  apply body_eq_boxed_preimage K F C hK T a b (-M) M
  intro x hx
  have hcoord (i : Fin 2) : |T x i| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (T x) i).trans (hM x hx)
  exact ⟨⟨ha.trans (abs_le.mp (hcoord 0)).1, (abs_le.mp (hcoord 0)).2.trans hb⟩,
    abs_le.mp (hcoord 1)⟩

/-- For an actual compact finite-half-plane body transverse to a nonzero
affine plank direction, construct one continuous residual-section function
that gives both endpoint derivatives for every strictly positive width.
The rectangle and coordinate representation are proved inside the theorem. -/
theorem exists_continuous_endpoint_derivatives {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : Set Point) (hcompact : IsCompact K)
    (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (hK : K = {x | ∀ i, F i x ≤ C i})
    (g : Point →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0) (hbody : ∀ i, cross g (F i) ≠ 0)
    (f : κ → Point →ᵃ[ℝ] ℝ) (hf : ∀ i, cross g (f i) ≠ 0) :
    ∃ L : EndpointSpace κ × ℝ → ℝ, Continuous L ∧
      ∀ (lo hi : κ → ℝ), (∀ i, lo i ≤ hi i) → ∀ ell h : ℝ, ell < h →
        HasDerivAt (fun t => (volume (distinguishedGap K f g lo hi t h)).toReal)
          (L ((lo, hi), ell)) ell ∧
        HasDerivAt (fun t => (volume (distinguishedGap K f g lo hi ell t)).toReal)
          (-L ((lo, hi), h)) h := by
  let T := directionCoordinates g hg
  obtain ⟨M, _, hM⟩ := (hcompact.image T.toContinuousLinearEquiv.continuous).isBounded.exists_pos_norm_le
  have hnorm (x) (hx : x ∈ K) : ‖T x‖ ≤ M := hM _ ⟨x, hx, rfl⟩
  refine ⟨directionalSectionLength g hg (-M) M (bodyA T F) (bodyB T F) (bodyC F C) f,
    continuous_directionalSectionLength g hg (-M) M _ _ _ f, ?_⟩
  intro lo hi hwidth ell h horder
  let a := min (-M) (ell-g 0)-1
  let b := max M (h-g 0)+1
  have ha : a ≤ -M := by dsimp [a]; linarith only [min_le_left (-M) (ell-g 0)]
  have hb : M ≤ b := by dsimp [b]; linarith only [le_max_left M (h-g 0)]
  have hell : a < ell-g 0 := by dsimp [a]; linarith only [min_le_right (-M) (ell-g 0)]
  have hh : h-g 0 < b := by dsimp [b]; linarith only [le_max_right M (h-g 0)]
  have hrep := body_eq_boxed_preimage_of_bound K F C hK T M hnorm a b ha hb
  have hB (i) : bodyB T F i ≠ 0 := transform_second_ne_zero g hg (F i) (hbody i)
  exact ⟨hasDerivAt_distinguishedGap_lower_of_rep K g hg a b (-M) M _ _ _ hrep hB
      f hf lo hi hwidth ell h hell horder hh,
    hasDerivAt_distinguishedGap_upper_of_rep K g hg a b (-M) M _ _ _ hrep hB
      f hf lo hi hwidth ell h hell horder hh⟩

end Plank.PlanarDirectionDerivatives
