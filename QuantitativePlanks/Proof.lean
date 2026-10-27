/-
# The compact affine plank inequalities

This file contains the central argument, in proof order:

1. Minimize total width among covers. Separation and rank force six exterior
   contacts at a deficient minimum; the six-contact inequality excludes it.
   This proves the planar Affine Plank Conjecture (APC).
2. Minimize total relative width plus the uncovered-volume fraction to the
   power `1 / dimension`. APC excludes zero gap, and the positive-gap minimum
   has at least `2 * number_of_planks + 1` exterior cells.
3. Two planks have only four cells. Three planar planks with seven cells obey
   the area bound. These give the two-plank and three-planar-plank QAPC.

The reusable separation, minimization and geometric estimates are imported
below. The main proof bodies are here; old module names remain compatibility
imports. Noncompact extensions and equality classifications are optional.

Notation: `Point d` is real coordinate space of dimension `d + 1`; `SharpBound d m`
says the uncovered volume is at least `max 0 (1 - R)^(d+1)` times the volume
of the compact convex body, for `m` planks of total relative width `R`.
`budget` is `R`; `gapVolume` is the real-valued uncovered volume. Affine forms
are normalized to have range `[0,1]` on the body when selecting the minima.
-/
module

public import Plank.Convex.CoveringMinimum
public import Plank.Convex.PlanarAffineRelation
public import Plank.Proofs.Quant.PlanarSixContactMinimum
public import Plank.Proofs.Quant.FiniteDimensionalRelationPerturbation
public import Plank.Proofs.Quant.AntipodalEndpointCells
public import Plank.Proofs.Quant.FiniteDimensionalOnePlankCaps
public import Plank.Proofs.Quant.PlanarSevenNonemptyBound

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology

/-! ## A covering minimum and planar APC -/

namespace Plank.CoveringFirstContact

open FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling FiniteDimensionalMinimumCellRank
  Convex.PlanarCoverSpace Convex.PlanarCoverMinimum

variable {n : ℕ}

/-- A deficient three-plank cover has a strict minimum with six closed
exterior contacts. Boundary exclusion uses only the two-plank covering bound. -/
theorem exists_deficient_minimum
    {K : Set (FiniteDimensionalCapWindowScaling.Point n)}
    (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Fin 3 → FiniteDimensionalCapWindowScaling.Point n →ᵃ[ℝ] ℝ)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (p₀ : Endpoints (Fin 3)) (horder : ∀ i, p₀.1 i ≤ p₀.2 i)
    (hcover : Covers (Image K f) p₀) (hbad : width p₀ < 1) :
    ∃ p ∈ strictWindows, width p < 1 ∧ Covers (Image K f) p ∧
      6 ≤ (nonemptyCells K f p).card := by
  let S := Image K f
  have hcS : Convex ℝ S := hc.affine_image (AffineMap.pi f)
  have hbS : ∀ x ∈ S, ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
    rintro _ ⟨x, hx, rfl⟩; exact hbox x hx
  have hlS : ∀ i, ∃ x ∈ S, x i = 0 := by
    intro i; obtain ⟨x, hx, hi⟩ := hL i; exact ⟨_, ⟨x, hx, rfl⟩, hi⟩
  have huS : ∀ i, ∃ x ∈ S, x i = 1 := by
    intro i; obtain ⟨x, hx, hi⟩ := hU i; exact ⟨_, ⟨x, hx, rfl⟩, hi⟩
  have hp₀ := clipped_unitCovers S hbS p₀ horder hcover
  obtain ⟨p, hp, hmin, hnomotion⟩ :=
    Convex.FiniteMinimumMotion.exists_minimizer_no_motion
      (unitCovers S) (compact_unitCovers S) ⟨_, hp₀⟩ width
  have hdef : width p < 1 :=
    (hmin hp₀).trans_lt ((clipped_width_le p₀ horder).trans_lt hbad)
  have hw := widths_positive S hcS hbS hlS huS p hp.1.2 hp.2 hdef
  have he := endpoints_strict S hcS hbS hlS huS p hp.1.2
    (fun i => ⟨hp.1.1.1.1 i, hp.1.1.2.2 i⟩) hp.2 hdef
  have hstrict : p ∈ strictWindows := fun i => ⟨(he i).1, hw i, (he i).2⟩
  exact ⟨p, hstrict, hdef, hp.2, contact_count hK hc f p hstrict hp.2 hnomotion⟩


end Plank.CoveringFirstContact

namespace Plank.CoveringFirstPlanar

open FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling FiniteDimensionalNormalization
  FiniteDimensionalRelationPerturbation CoveringFirstContact

variable {n : ℕ}

/-- The normalized positive-relation covering bound uses only a covering
minimum, the two-plank covering theorem, and the existing six-support geometry. -/
theorem normalized_positive
    {K : Set (Point n)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 3 → Point n →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (c : Fin 3 → ℝ) (level : ℝ) (hcpos : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i*f i x = level)
    (p : Endpoints (Fin 3)) (horder : ∀ i, p.1 i ≤ p.2 i)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  by_contra! hbad
  have hL (i) := (unit_realisers hK hne (f i) (hnorm i) (hunit i)).1
  have hU (i) := (unit_realisers hK hne (f i) (hnorm i) (hunit i)).2
  obtain ⟨q, hq, hqbad, hqcover, hcount⟩ := exists_deficient_minimum hK hc f
    (fun x hx i => hnorm i x hx) hL hU p horder
    (by rintro _ ⟨x, hx, rfl⟩; exact mem_iUnion.mp (hcover hx))
    (by simpa [Convex.PlanarCoverMinimum.width_apply, budget, hunit] using hbad)
  have hb := PlanarSixContactMinimum.width_bound_of_six_contact_cells
    (hc.affine_image (AffineMap.pi f))
    (fun i => by obtain ⟨x, hx, hi⟩ := hL i; exact ⟨_, ⟨x, hx, rfl⟩, hi⟩)
    (fun i => by obtain ⟨x, hx, hi⟩ := hU i; exact ⟨_, ⟨x, hx, rfl⟩, hi⟩)
    c level hcpos (by rintro _ ⟨x, hx, rfl⟩; exact hplane x hx)
    hq hqcover hcount
  exact hqbad.not_ge (by simpa [Convex.PlanarCoverMinimum.width_apply] using hb)

/-- Affine normalization preserves the actual covered set and total relative width. -/
theorem positive_relation
    {K : Set (Point n)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 3 → Point n →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (c : Fin 3 → ℝ) (level : ℝ) (hcpos : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i*f i x = level)
    (p : Endpoints (Fin 3)) (horder : ∀ i, p.1 i ≤ p.2 i)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  obtain ⟨g, q, b, hg, hunit, hnorm, hqorder, hbudget, hbands, _⟩ :=
    normalize_data_with_formula hK hne f p.1 p.2 horder hW
  have hgplane : ∀ x ∈ K,
      ∑ i, (c i*Body.width K (f i))*g i x = level-∑ i, c i*b i := by
    intro x hx
    rw [← hplane x hx, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hg]
    field_simp [(hW i).ne']
  have hb := normalized_positive hK hc hne g hnorm hunit
    (fun i => c i*Body.width K (f i)) (level-∑ i, c i*b i)
    (fun i => mul_pos (hcpos i) (hW i)) hgplane q hqorder
    (by rw [iUnion_congr hbands]; exact hcover)
  rwa [hbudget] at hb

/-- Complete planar APC, including repeated directions, zero-width planks,
and external windows. No quantitative plank theorem is used. -/
theorem cover_bound
    {K : Set (Point 1)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 3 → Point 1 →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (p : Endpoints (Fin 3)) (horder : ∀ i, p.1 i ≤ p.2 i)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  obtain ⟨g, q, _, _, hunit, hnorm, hqorder, hbudget, hbands, _⟩ :=
    normalize_data_with_formula hK hne f p.1 p.2 horder hW
  obtain ⟨a, ha, level, hplane⟩ := Convex.PlanarAffineRelation.exists_relation g
  have h := relation_cover_bound_of_order hK hne (positive_relation hK hc hne)
    g hnorm hunit a level ha (fun x _ => hplane x) q hqorder
    (by rw [iUnion_congr hbands]; exact hcover)
  rwa [hbudget] at h

end Plank.CoveringFirstPlanar

/-! ## A common positive-gap minimum -/

namespace Plank.CoveringFirstQuantitative

open FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling FiniteDimensionalParameterDomain
  FiniteDimensionalNormalization FiniteDimensionalInductionBoundary
  FiniteDimensionalMinimumCellRank FiniteDimensionalMinimumCompletion

/-- Once the covering inequality is known, a strict quantitative
counterexample has a positive-gap minimum and the stronger cell count. -/
theorem positive_gap_minimum {d m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point d →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hcover : ∀ p ∈ domain K f,
      K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} → 1 ≤ budget K f p)
    {p₀ : Endpoints (Fin (m+1))} (hp₀ : p₀ ∈ domain K f)
    (hbad : rootCost K f p₀ < 1) :
    ∃ p ∈ interior (domain K f), rootCost K f p < 1 ∧ 0 < gapVolume K f p ∧
      2*(m+1)+1 ≤ (nonemptyCells K f p).card := by
  obtain ⟨p, hp, hneg, _, _, hpositive⟩ :=
    AntipodalEndpointCells.exists_minimum_contact_counts hm hK hc hne hV f hW hnorm hp₀ hbad
  have hR := (budget_le_rootCost K f p).trans_lt hneg
  have hzero : gapVolume K f p ≠ 0 := by
    intro hz
    exact hR.not_ge (hcover p (interior_subset hp)
      ((gap_eq_zero_iff_cover hK hc hV f p).mp hz))
  have hgap : 0 < gapVolume K f p :=
    lt_of_le_of_ne ENNReal.toReal_nonneg hzero.symm
  exact ⟨p, hp, hneg, hgap, hpositive hgap⟩

end Plank.CoveringFirstQuantitative

/-! ## Two planks in every positive dimension -/

namespace Plank.FiniteDimensionalTwoPlank

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalInductionBoundary FiniteDimensionalParameterDomain
  FiniteDimensionalNormalization

variable {d : ℕ}

/-- The elementary two-window covering theorem, without the qualitative
three-plank theorem, expressed in normalized endpoint coordinates. -/
theorem cover_budget_normalized {K : Set (Point d)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 2 → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (p : Endpoints (Fin 2)) (hp : p ∈ domain K f)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  have hrange (i : Fin 2) := unit_realisers hK hne (f i) (hnorm i) (hunit i)
  have h := Plank.Convex.TwoAffineWindows.width_bound K hc (f 0) (f 1)
    (fun x hx => ⟨hnorm 0 x hx,hnorm 1 x hx⟩)
    (p.1 0) (p.2 0) (p.1 1) (p.2 1) (hp.1 0).2.1 (hp.1 1).2.1
    (hrange 0).1 (hrange 0).2
    (hrange 1).1 (hrange 1).2 (by
      intro x hx
      simpa only [mem_iUnion,Fin.exists_fin_two,mem_ofPred_eq] using hcover hx)
  simpa only [budget,hunit,div_one,Fin.sum_univ_two] using h

/-- A strict two-plank counterexample would have a positive-gap minimum with
at least five exterior cells, but two planks have only four sign patterns. -/
theorem sharpBound_two : SharpBound d 2 := by
  classical
  by_contra hn
  obtain ⟨K, hK, hc, hne, hV, f, hunit, hnorm, p, hp, hbad⟩ :=
    exists_normalized_counterexample hn
  have hW (i) : 0 < Body.width K (f i) := by rw [hunit]; norm_num
  obtain ⟨q, _, _, _, hcount⟩ := CoveringFirstQuantitative.positive_gap_minimum
    FiniteDimensionalOnePlankCaps.sharpBound_one hK hc hne hV f hW hnorm
    (cover_budget_normalized hK hc hne f hnorm hunit)
    hp ((rootCost_lt_one_iff hV f p hp.2).mpr hbad)
  have hcard := Finset.card_le_univ
    (FiniteDimensionalMinimumCellRank.nonemptyCells K f q)
  norm_num at hcard
  omega

end Plank.FiniteDimensionalTwoPlank

/-! ## Three planks in the plane -/

namespace Plank.CoveringFirstQuantitative

open FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling FiniteDimensionalParameterDomain
  FiniteDimensionalNormalization FiniteDimensionalInductionBoundary

/-- Planar QAPC: the covering bound excludes zero gap; seven exterior cells
at a positive-gap minimum give the required area bound. -/
theorem sharpBound_three : SharpBound 1 3 := by
  by_contra hn
  obtain ⟨K, hK, hc, hne, hV, f, hunit, hnorm, p, hp, hbad⟩ :=
    exists_normalized_counterexample hn
  have hW (i) : 0 < Body.width K (f i) := by rw [hunit]; norm_num
  obtain ⟨q, hq, hneg, _, hcount⟩ := positive_gap_minimum
    FiniteDimensionalTwoPlank.sharpBound_two hK hc hne hV f hW hnorm
    (fun q hq hcover => CoveringFirstPlanar.cover_bound hK hc hne f hW q
      (fun i => (hq.1 i).2.1) hcover)
    hp ((rootCost_lt_one_iff hV f p hp.2).mpr hbad)
  have hR := (FiniteDimensionalMinimumCellRank.budget_le_rootCost K f q).trans_lt hneg
  have hbadq := (rootCost_lt_one_iff hV f q (interior_subset hq).2).mp hneg
  rw [max_eq_right (sub_nonneg.mpr hR.le)] at hbadq
  exact hbadq.not_ge
    (PlanarSevenNonemptyBound.manyCellBound hK hc hne f hnorm hunit q hq hR hcount)

end Plank.CoveringFirstQuantitative
