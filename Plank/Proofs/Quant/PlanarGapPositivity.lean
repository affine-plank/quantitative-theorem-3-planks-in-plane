/- The qualitative planar theorem makes an actual deficient gap positive. -/
module

public import Plank.Proofs.Quant.PlanarNormalization
public import Plank.Proofs.Quant.PlanarOnePlankCaps
public import Plank.Convex.PlanarAffineCover
import Mathlib.Tactic.IntervalCases

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarGapPositivity

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarNormalization
open Plank.Convex.DeficientHeightTilt

/-- The existing qualitative theorem, with the same actual ranges and
closed-plank cover used by the quantitative statement. -/
theorem cover_budget_three {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (horder : ∀ i, p.1 i ≤ p.2 i) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  apply Plank.Convex.PlanarAffineCover.width_bound (by simp [Point]) K hK hne hconv
    f p.1 p.2 hW horder
  intro x hx
  exact mem_iUnion.mp (hcover hx)

/-- Pad a two-plank cover by a zero-width plank in an existing direction.
The padding preserves the actual relative budget. -/
theorem cover_budget_two {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (horder : ∀ i, p.1 i ≤ p.2 i) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  let g : Fin 3 → Point →ᵃ[ℝ] ℝ := Fin.cons (f 0) f
  let q : Endpoints 3 := (Fin.cons 0 p.1, Fin.cons 0 p.2)
  have hgW : ∀ i, 0 < rangeWidth K (g i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hW 0
    · exact hW j
  have hqorder : ∀ i, q.1 i ≤ q.2 i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_rfl
    · exact horder j
  have hqcover : K ⊆ ⋃ i, {x | q.1 i ≤ g i x ∧ g i x ≤ q.2 i} := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i.succ, hi⟩
  have H := cover_budget_three hK hconv hne g q hqorder hgW hqcover
  simpa [budget, g, q, Fin.sum_univ_succ] using H

theorem gapArea_pos_three {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (horder : ∀ i, p.1 i ≤ p.2 i) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hR : budget K f p < 1) : 0 < gapArea K f p := by
  apply PlanarGapAnalysis.area_sdiff_pos_of_not_subset hK hconv hV
    (PlanarGapAnalysis.isClosed_plank_union f p.1 p.2)
  intro hcover
  exact hR.not_ge (cover_budget_three hK hconv hne f p horder hW hcover)

theorem gapArea_pos_two {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (horder : ∀ i, p.1 i ≤ p.2 i) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hR : budget K f p < 1) : 0 < gapArea K f p := by
  apply PlanarGapAnalysis.area_sdiff_pos_of_not_subset hK hconv hV
    (PlanarGapAnalysis.isClosed_plank_union f p.1 p.2)
  intro hcover
  exact hR.not_ge (cover_budget_two hK hconv hne f p horder hW hcover)

theorem gapArea_pos_of_sharpPlanarBound {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (horder : ∀ i, p.1 i ≤ p.2 i) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hR : budget K f p < 1) : 0 < gapArea K f p := by
  have hbound := hm K hK hconv hne f p.1 p.2 horder hW
  change (max 0 (1-budget K f p))^2 * (volume K).toReal ≤ gapArea K f p at hbound
  rw [max_eq_right (sub_pos.mpr hR).le] at hbound
  exact (mul_pos (sq_pos_of_pos (sub_pos.mpr hR)) hV).trans_le hbound

/-- Positive gap for every deficient family of at most three planks. No
quantitative two- or three-plank theorem is assumed in this proof. -/
theorem gapArea_pos_of_le_three {m : ℕ} (hm : m ≤ 3)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (horder : ∀ i, p.1 i ≤ p.2 i) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hR : budget K f p < 1) : 0 < gapArea K f p := by
  interval_cases m
  · exact gapArea_pos_of_sharpPlanarBound PlanarGapAnalysis.sharpPlanarBound_zero
      hK hconv hne hV f p horder hW hR
  · exact gapArea_pos_of_sharpPlanarBound PlanarOnePlankCaps.sharpPlanarBound_one
      hK hconv hne hV f p horder hW hR
  · exact gapArea_pos_two hK hconv hne hV f p horder hW hR
  · exact gapArea_pos_three hK hconv hne hV f p horder hW hR

theorem budget_lt_one_of_rootMargin_neg {m : ℕ} {K : Set Point}
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) (h : rootMargin K f p < 0) :
    budget K f p < 1 := by
  unfold rootMargin at h
  linarith only [Real.sqrt_nonneg (gapArea K f p / (volume K).toReal), h]

/-- A counterexample to either remaining planar case gives an interior
minimum with strictly positive actual gap area. Qualitative covering supplies
positivity; the full preceding quantitative case pays the boundary. -/
theorem exists_positive_interior_minimum {m : ℕ} (hsmall : m+1 ≤ 3)
    (hm : SharpPlanarBound m) (h : ¬ SharpPlanarBound (m+1)) :
    ∃ (K : Set Point), IsCompact K ∧ Convex ℝ K ∧ K.Nonempty ∧
      0 < (volume K).toReal ∧
      ∃ (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ),
        (∀ i, rangeWidth K (f i) = 1) ∧
        (∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) ∧
        ∃ p ∈ interior (domain K f), 0 < gapArea K f p ∧ rootMargin K f p < 0 ∧
          ∀ q ∈ domain K f, rootMargin K f p ≤ rootMargin K f q := by
  obtain ⟨K, hK, hconv, hne, hV, f, hunit, hnorm, p, hp, hneg, hmin⟩ :=
    exists_normalized_interior_minimum hm h
  have hmem : p ∈ domain K f := interior_subset hp
  have hG := gapArea_pos_of_le_three hsmall hK hconv hne hV f p
    (fun i => (hmem.1 i).2.1) (fun i => by rw [hunit]; norm_num)
    (budget_lt_one_of_rootMargin_neg f p hneg)
  exact ⟨K, hK, hconv, hne, hV, f, hunit, hnorm, p, hp, hG, hneg, hmin⟩

end Plank.PlanarGapPositivity
