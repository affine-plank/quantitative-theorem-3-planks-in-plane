/- Normalize actual planks while preserving all direction transversality. -/
module

public import Plank.Proofs.Quant.PlanarNormalization
public import Plank.Proofs.Quant.PlanarDirectionDerivatives

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarTransverseNormalization

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarNormalization
open PlanarDirectionDerivatives PlanarGapCells
open Plank.Convex.DeficientHeightTilt

theorem linear_eq_of_formula (f g : Point →ᵃ[ℝ] ℝ) (c W : ℝ)
    (hg : ∀ x, g x = (f x-c)/W) : g.linear = W⁻¹ • f.linear := by
  apply LinearMap.ext
  intro x
  have hx := hg x
  have h0 := hg 0
  rw [affine_eval g x, affine_eval f x, div_eq_mul_inv] at hx
  rw [div_eq_mul_inv] at h0
  change g.linear x = W⁻¹*f.linear x
  linear_combination hx-h0

/-- Strengthened normalization retains the exact scaling of every linear part. -/
theorem normalize_data_with_linear {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (hne : K.Nonempty) (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (horder : ∀ i, p.1 i ≤ p.2 i) (hW : ∀ i, 0 < rangeWidth K (f i)) :
    ∃ (g : Fin m → Point →ᵃ[ℝ] ℝ) (q : Endpoints m),
      (∀ i, rangeWidth K (g i) = 1) ∧
      (∀ i x, x ∈ K → 0 ≤ g i x ∧ g i x ≤ 1) ∧
      (∀ i, (g i).linear = (rangeWidth K (f i))⁻¹ • (f i).linear) ∧
      (∀ i, q.1 i ≤ q.2 i) ∧ budget K g q = budget K f p ∧
      gapArea K g q = gapArea K f p := by
  obtain ⟨g, q, c, happly, hunit, hbounds, hordered, hbudget, _, hgap⟩ :=
    FiniteDimensionalNormalization.normalize_data_with_formula hK hne f p.1 p.2 horder hW
  exact ⟨g, q, hunit, hbounds, fun i => linear_eq_of_formula _ _ _ _ (happly i),
    hordered, hbudget, hgap⟩

theorem cross_scaled (f g F : Point →ᵃ[ℝ] ℝ) (a : ℝ)
    (h : g.linear = a • f.linear) : cross g F = a*cross f F := by
  simp only [cross, h, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem cross_scaled_pair (f g f' g' : Point →ᵃ[ℝ] ℝ) (a b : ℝ)
    (h : g.linear = a • f.linear) (h' : g'.linear = b • f'.linear) :
    cross g g' = a*b*cross f f' := by
  simp only [cross, h, h', LinearMap.smul_apply, smul_eq_mul]
  ring

/-- A transverse counterexample can be normalized and clipped into the
actual endpoint domain without losing either transversality or strict failure. -/
theorem exists_normalized_transverse_counterexample {m : ℕ} {ι : Type*}
    (K : Set Point) (hK : IsCompact K) (hne : K.Nonempty)
    (F : ι → Point →ᵃ[ℝ] ℝ) (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, p.1 i ≤ p.2 i)
    (hbody : ∀ i j, cross (f i) (F j) ≠ 0)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hbad : gapArea K f p < (max 0 (1-budget K f p))^2*(volume K).toReal) :
    ∃ (g : Fin m → Point →ᵃ[ℝ] ℝ) (q : Endpoints m),
      (∀ i, rangeWidth K (g i) = 1) ∧
      (∀ i x, x ∈ K → 0 ≤ g i x ∧ g i x ≤ 1) ∧
      (∀ i j, cross (g i) (F j) ≠ 0) ∧
      (∀ i j, i ≠ j → cross (g i) (g j) ≠ 0) ∧
      q ∈ domain K g ∧
      gapArea K g q < (max 0 (1-budget K g q))^2*(volume K).toReal := by
  obtain ⟨g, q, hunit, hnorm, hlinear, hordered, hbudget, hgap⟩ :=
    normalize_data_with_linear hK hne f p horder hW
  have hgW (i) : 0 < rangeWidth K (g i) := by rw [hunit]; norm_num
  have hbodyg (i j) : cross (g i) (F j) ≠ 0 := by
    rw [cross_scaled (f i) (g i) (F j) _ (hlinear i)]
    exact mul_ne_zero (inv_ne_zero (hW i).ne') (hbody i j)
  have hpairsg (i j) (hij : i ≠ j) : cross (g i) (g j) ≠ 0 := by
    rw [cross_scaled_pair (f i) (g i) (f j) (g j) _ _ (hlinear i) (hlinear j)]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hW i).ne') (inv_ne_zero (hW j).ne'))
      (hpairs i j hij)
  have hbadq : gapArea K g q < (max 0 (1-budget K g q))^2*(volume K).toReal := by
    rwa [hbudget, hgap]
  have hR : budget K g q ≤ 1 := by
    by_contra hn
    have hz : max 0 (1-budget K g q) = 0 := max_eq_left (by linarith only [hn])
    rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at hbadq
    exact (not_lt_of_ge (show 0 ≤ gapArea K g q from ENNReal.toReal_nonneg)) hbadq
  have hdeficit : max 0 (1-budget K g q) ≤ max 0 (1-budget K g (clipEndpoints q)) :=
    max_le_max le_rfl (sub_le_sub_left (budget_clip_le g hgW q hordered) 1)
  refine ⟨g, clipEndpoints q, hunit, hnorm, hbodyg, hpairsg,
    clipEndpoints_mem_domain g hgW q hordered hR, ?_⟩
  rw [gapArea_clip hne g hgW hnorm q]
  exact hbadq.trans_le (mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (le_max_left _ _) (le_max_left _ _)).mpr hdeficit) ENNReal.toReal_nonneg)

end Plank.PlanarTransverseNormalization
