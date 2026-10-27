/- Transfer the direct minimum argument to arbitrary affine relations by
normalization, reflection and a one-sided perturbation of actual bands. -/
module
public import Plank.Proofs.Quant.PlanarPositiveRelationMinimum
public import Plank.Convex.PlanarAffineRelation
public import Plank.Proofs.Quant.FiniteDimensionalRelationPerturbation

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarRelationPerturbation

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalMinimumCellRank FiniteDimensionalParameterDomain
  FiniteDimensionalNormalization
open scoped BigOperators

/-- Normalize and clip before selecting a minimum. The positive relation
is transported together with the actual bands and their relative widths. -/
theorem positive_relation_bound
    {K : Set (Point 1)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin 3 → (Point 1) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (c : Fin 3 → ℝ) (level : ℝ) (hcpos : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i*f i x = level)
    (p : Endpoints (Fin 3)) (horder : ∀ i, p.1 i ≤ p.2 i) :
    (max 0 (1-budget K f p))^2*(volume K).toReal ≤ gapVolume K f p := by
  by_cases hR : budget K f p ≤ 1
  · obtain ⟨g,q,b,hg,hunit,hnorm,hqorder,hbudget,_,hgap⟩ :=
      normalize_data_with_formula hK hne f p.1 p.2 horder hW
    have hgW (i) : 0 < Body.width K (g i) := by rw [hunit]; norm_num
    have hgplane : ∀ x ∈ K,
        ∑ i, (c i*Body.width K (f i))*g i x = level-∑ i, c i*b i := by
      intro x hx
      rw [← hplane x hx,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hg]
      field_simp [(hW i).ne']
    have hmem := clipEndpoints_mem_domain g hgW q hqorder (by rwa [hbudget])
    have hdef : max 0 (1-budget K f p) ≤ max 0 (1-budget K g (clipEndpoints q)) := by
      rw [← hbudget]
      exact max_le_max le_rfl (sub_le_sub_left (budget_clip_le g hgW q hqorder) 1)
    calc
      _ ≤ (max 0 (1-budget K g (clipEndpoints q)))^2*(volume K).toReal :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_left _ _) hdef 2)
          ENNReal.toReal_nonneg
      _ ≤ gapVolume K g (clipEndpoints q) :=
        PlanarPositiveRelationMinimum.planar_bound_normalized hK hc hne hV g hnorm hunit
          (fun i => c i*Body.width K (f i)) (level-∑ i, c i*b i)
          (fun i => mul_pos (hcpos i) (hW i)) hgplane _ hmem
      _ = gapVolume K f p := (gapVolume_clip hne g hgW hnorm q).trans hgap
  · rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge hR)),zero_pow (by decide : 2 ≠ 0),zero_mul]
    exact ENNReal.toReal_nonneg

/-- The finite-family perturbation specializes to three planar planks. -/
theorem nonnegative_relation_bound
    {K : Set (Point 1)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin 3 → (Point 1) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (A : Fin 3 → ℝ) (level : ℝ) (hA : ∀ i, 0 ≤ A i) (hpos : ∃ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i*f i x = level)
    (p : Endpoints (Fin 3)) (hp : p ∈ domain K f) :
    (max 0 (1-budget K f p))^2*(volume K).toReal ≤ gapVolume K f p := by
  exact FiniteDimensionalRelationPerturbation.nonnegative_relation_bound hK hne hV
    (positive_relation_bound hK hc hne hV) f hnorm hunit A level hA hpos hplane p hp

/-- Reflect and perturb through the dimension-independent transfer. -/
theorem relation_bound
    {K : Set (Point 1)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin 3 → (Point 1) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (a : Fin 3 → ℝ) (level : ℝ) (ha : ∃ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i*f i x = level)
    (p : Endpoints (Fin 3)) (hp : p ∈ domain K f) :
    (max 0 (1-budget K f p))^2*(volume K).toReal ≤ gapVolume K f p := by
  exact FiniteDimensionalRelationPerturbation.relation_bound hK hne hV
    (positive_relation_bound hK hc hne hV) f hnorm hunit a level ha hplane p hp

/-- The complete planar quantitative theorem follows from one quantitative
minimum argument. The outer transfer uses the original endpoints, without
preliminary clipping. The established qualitative theorem is not used. -/
theorem sharpPlanarBound_three : FiniteDimensionalInductionBoundary.SharpBound 1 3 := by
  intro K hK hc hne f lo hi horder hW
  change (max 0 (1-budget K f (lo,hi)))^2*(volume K).toReal ≤ gapVolume K f (lo,hi)
  by_cases hV : 0 < (volume K).toReal
  · obtain ⟨a,ha,level,hplane⟩ := Convex.PlanarAffineRelation.exists_relation f
    exact FiniteDimensionalRelationPerturbation.bound_of_relation hK hne hV
      (positive_relation_bound hK hc hne hV) f hW a level ha
      (fun x _ => hplane x) (lo,hi) horder
  · have hz : (volume K).toReal = 0 :=
      le_antisymm (le_of_not_gt hV) ENNReal.toReal_nonneg
    rw [hz,mul_zero]
    exact ENNReal.toReal_nonneg

/-- Specializing the quantitative inequality to a cover recovers the
qualitative bound for a planar convex body of positive area. -/
theorem cover_budget
    {K : Set (Point 1)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin 3 → (Point 1) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (p : Endpoints (Fin 3)) (horder : ∀ i, p.1 i ≤ p.2 i)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  have hbound := sharpPlanarBound_three K hK hc hne f p.1 p.2 horder hW
  change (max 0 (1-budget K f p))^2*(volume K).toReal ≤ gapVolume K f p at hbound
  have hzero : gapVolume K f p = 0 := by
    simp only [gapVolume,sdiff_eq_empty.mpr hcover,measure_empty,ENNReal.toReal_zero]
  by_contra hn
  have hpos : 0 < (max 0 (1-budget K f p))^2*(volume K).toReal :=
    mul_pos (pow_pos (lt_max_of_lt_right (sub_pos.mpr (lt_of_not_ge hn))) 2) hV
  rw [hzero] at hbound
  exact hpos.not_ge hbound

end Plank.PlanarRelationPerturbation

#print axioms Plank.PlanarRelationPerturbation.positive_relation_bound
#print axioms Plank.PlanarRelationPerturbation.nonnegative_relation_bound
#print axioms Plank.PlanarRelationPerturbation.relation_bound
#print axioms Plank.PlanarRelationPerturbation.sharpPlanarBound_three
#print axioms Plank.PlanarRelationPerturbation.cover_budget
