/- Affine normalization and clipping of actual planar plank windows. -/
module

public import Plank.Proofs.Quant.PlanarParameterDomain
public import Plank.Proofs.Quant.FiniteDimensionalNormalization
import Mathlib.Tactic.Choose

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarNormalization

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarParameterDomain
open Plank.Convex.DeficientHeightTilt

/-- Normalize one affine functional using actual support points. Its new
range is exactly one and its values on the body lie in the unit interval. -/
theorem exists_unit_form {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (hW : 0 < rangeWidth K f) :
    ∃ (g : Point →ᵃ[ℝ] ℝ) (c : ℝ),
      (∀ x, g x = (f x-c)/rangeWidth K f) ∧
      (∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1) ∧ rangeWidth K g = 1 := by
  exact FiniteDimensionalNormalization.exists_unit_form hK hne f hW

/-- Simultaneous normalization preserves the actual plank sets, gap area
and relative budget. Endpoints may extend outside the new support interval. -/
theorem normalize_data {m : ℕ} {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < rangeWidth K (f i)) :
    ∃ (g : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m),
      (∀ i, rangeWidth K (g i) = 1) ∧
      (∀ i x, x ∈ K → 0 ≤ g i x ∧ g i x ≤ 1) ∧
      (∀ i, p.1 i ≤ p.2 i) ∧ budget K g p = budget K f (lo, hi) ∧
      gapArea K g p = gapArea K f (lo, hi) := by
  exact FiniteDimensionalNormalization.normalize_data hK hne f lo hi horder hW

/-- Clamp an endpoint to the normalized support interval. -/
def clip (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clip_bounds (x : ℝ) : 0 ≤ clip x ∧ clip x ≤ 1 := by
  exact FiniteDimensionalNormalization.clip_bounds x

theorem monotone_clip : Monotone clip := by
  exact FiniteDimensionalNormalization.monotone_clip

theorem clip_sub_le {lo hi : ℝ} (h : lo ≤ hi) : clip hi - clip lo ≤ hi-lo := by
  exact FiniteDimensionalNormalization.clip_sub_le h

/-- At a point strictly inside the support interval, clipping does not
change membership in the plank. Support levels are handled by nullity below. -/
theorem mem_clipped_iff {lo hi z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    (clip lo ≤ z ∧ z ≤ clip hi) ↔ (lo ≤ z ∧ z ≤ hi) := by
  exact FiniteDimensionalNormalization.mem_clipped_iff hz hz1

def clipEndpoints {m : ℕ} (p : Endpoints m) : Endpoints m :=
  (fun i => clip (p.1 i), fun i => clip (p.2 i))

theorem budget_clip_le {m : ℕ} {K : Set Point} (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (p : Endpoints m)
    (horder : ∀ i, p.1 i ≤ p.2 i) :
    budget K f (clipEndpoints p) ≤ budget K f p := by
  exact FiniteDimensionalNormalization.budget_clip_le f hW p horder

theorem clipEndpoints_mem_domain {m : ℕ} {K : Set Point}
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p : Endpoints m) (horder : ∀ i, p.1 i ≤ p.2 i) (hbudget : budget K f p ≤ 1) :
    clipEndpoints p ∈ domain K f := by
  exact FiniteDimensionalNormalization.clipEndpoints_mem_domain f hW p horder hbudget

/-- Clipping preserves the actual gap area. It can change the closed covered
set on support lines, so equality is proved after removing those null lines. -/
theorem gapArea_clip {m : ℕ} {K : Set Point} (hne : K.Nonempty)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) (p : Endpoints m) :
    gapArea K f (clipEndpoints p) = gapArea K f p := by
  exact FiniteDimensionalNormalization.gapVolume_clip hne f hW hnorm p

/-- The normalized domain version of the full actual-area target. It retains
arbitrary compact convex bodies and imposes no polygon or area-chart premise. -/
def UnitDomainBound (m : ℕ) : Prop :=
  ∀ (K : Set Point), IsCompact K → Convex ℝ K → K.Nonempty →
    ∀ (f : Fin m → Point →ᵃ[ℝ] ℝ),
      (∀ i, rangeWidth K (f i) = 1) →
      (∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) →
      ∀ p ∈ domain K f,
        (max 0 (1-budget K f p))^2 * (volume K).toReal ≤ gapArea K f p

/-- Normalizing and clipping loses no part of the original theorem. In
particular, planks outside the support window, zero-width planks and bodies
of zero area are included in this equivalence. -/
theorem sharpPlanarBound_iff_unitDomainBound (m : ℕ) :
    SharpPlanarBound m ↔ UnitDomainBound m := by
  exact FiniteDimensionalNormalization.sharpBound_iff_unitDomainBound (d := 1) m

/-- Failure of the full statement already gives a positive-area normalized
counterexample. This is an actual body and actual plank family, not abstract
area functions satisfying unproved geometric assumptions. -/
theorem exists_normalized_counterexample {m : ℕ} (h : ¬ SharpPlanarBound m) :
    ∃ (K : Set Point), IsCompact K ∧ Convex ℝ K ∧ K.Nonempty ∧
      0 < (volume K).toReal ∧
      ∃ (f : Fin m → Point →ᵃ[ℝ] ℝ),
        (∀ i, rangeWidth K (f i) = 1) ∧
        (∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) ∧
        ∃ p ∈ domain K f,
          gapArea K f p < (max 0 (1-budget K f p))^2 * (volume K).toReal := by
  exact FiniteDimensionalNormalization.exists_normalized_counterexample (d := 1) h

/-- The complete next quantitative theorem reduces to excluding a negative
interior minimum for a genuine normalized body/plank family. The previous
full case is used only to pay the boundary. -/
theorem exists_normalized_interior_minimum {m : ℕ} (hm : SharpPlanarBound m)
    (h : ¬ SharpPlanarBound (m+1)) :
    ∃ (K : Set Point), IsCompact K ∧ Convex ℝ K ∧ K.Nonempty ∧
      0 < (volume K).toReal ∧
      ∃ (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ),
        (∀ i, rangeWidth K (f i) = 1) ∧
        (∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) ∧
        ∃ p ∈ interior (domain K f), rootMargin K f p < 0 ∧
          ∀ q ∈ domain K f, rootMargin K f p ≤ rootMargin K f q := by
  obtain ⟨K, hK, hconv, hne, hV, f, hunit, hnorm, p, hp, hbad⟩ :=
    exists_normalized_counterexample h
  refine ⟨K, hK, hconv, hne, hV, f, hunit, hnorm, ?_⟩
  exact exists_negative_interior_minimum hm hK hconv hne hV f
    (fun i => by rw [hunit]; norm_num) hnorm hp hbad

end Plank.PlanarNormalization
