/- Quantitative cover completion in every positive dimension. The preceding
quantitative case and a many-cell bound are hypotheses; covering comes last. -/
module

public import Plank.Proofs.Quant.AntipodalEndpointCells
public import Plank.Proofs.Quant.FiniteDimensionalManyCellBound

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalMinimumCompletion

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalMinimumCellRank FiniteDimensionalInductionBoundary
  FiniteDimensionalParameterDomain

variable {d : ℕ}

/-- The many-cell bound turns a strict counterexample into a cover retaining
the minimum's `2*(m+1)` contact cells. It costs at most the original root cost.
No covering bound is used in this construction. -/
theorem exists_counted_cover_of_counterexample {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1) (hcell : ManyCellBound K f)
    (p₀ : Endpoints (Fin (m+1))) (hp₀ : p₀ ∈ domain K f)
    (hbad : gapVolume K f p₀ < (max 0 (1-budget K f p₀))^(d+1)*(volume K).toReal) :
    ∃ p ∈ interior (domain K f),
      K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∧
      budget K f p < 1 ∧ budget K f p ≤ budget K f p₀+gapRoot K f p₀ ∧
      2*(m+1) ≤ (nonemptyCells K f p).card := by
  have hW (i) : 0 < Body.width K (f i) := by rw [hunit]; norm_num
  have hneg₀ := (rootCost_lt_one_iff hV f p₀ hp₀.2).mpr hbad
  obtain ⟨p,hp,hneg,hmin,hcount,hpositive⟩ := AntipodalEndpointCells.exists_minimum_contact_counts
    hm hK hc hne hV f hW hnorm hp₀ hneg₀
  have hR := (budget_le_rootCost K f p).trans_lt hneg
  have hzero : gapVolume K f p = 0 := by
    by_contra hn
    have hgap : 0 < gapVolume K f p :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (fun h => hn h.symm)
    have hh := (rootCost_lt_one_iff hV f p (interior_subset hp).2).mp hneg
    rw [max_eq_right (sub_nonneg.mpr (interior_subset hp).2)] at hh
    exact hh.not_ge (hcell p hp hR (hpositive hgap))
  refine ⟨p,hp,(gap_eq_zero_iff_cover hK hc hV f p).mp hzero,hR,?_,hcount⟩
  exact (budget_le_rootCost K f p).trans (by simpa only [rootCost,add_comm] using hmin p₀ hp₀)

/-- Forget the contact count to recover the original cover-completion interface. -/
theorem exists_cover_of_counterexample {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1) (hcell : ManyCellBound K f)
    (p₀ : Endpoints (Fin (m+1))) (hp₀ : p₀ ∈ domain K f)
    (hbad : gapVolume K f p₀ < (max 0 (1-budget K f p₀))^(d+1)*(volume K).toReal) :
    ∃ p ∈ interior (domain K f),
      K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∧
      budget K f p < 1 ∧ budget K f p ≤ budget K f p₀+gapRoot K f p₀ := by
  obtain ⟨p,hp,hcover,hR,hcost,_⟩ :=
    exists_counted_cover_of_counterexample hm hK hc hne hV f hnorm hunit hcell p₀ hp₀ hbad
  exact ⟨p,hp,hcover,hR,hcost⟩

/-- Complete any normalized family to a cover in the same directions, at no
greater original width plus normalized root-volume cost. -/
theorem exists_cover_completion {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1) (hcell : ManyCellBound K f)
    (p₀ : Endpoints (Fin (m+1))) (hp₀ : p₀ ∈ domain K f) :
    ∃ p ∈ domain K f,
      K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∧
      budget K f p ≤ budget K f p₀+gapRoot K f p₀ := by
  classical
  by_cases hcost : 1 ≤ budget K f p₀+gapRoot K f p₀
  · let p : Endpoints (Fin (m+1)) := (0,fun i => if i=0 then 1 else 0)
    have hbudget : budget K f p = 1 := by simp [budget,p,hunit]
    refine ⟨p,⟨?_,hbudget.le⟩,?_,hbudget.le.trans hcost⟩
    · intro i
      dsimp [p]
      split_ifs <;> norm_num
    · intro x hx
      exact mem_iUnion.mpr ⟨0,by simpa [p] using hnorm 0 x hx⟩
  · have hneg : rootCost K f p₀ < 1 := by
      simpa only [rootCost,add_comm] using lt_of_not_ge hcost
    have hbad := (rootCost_lt_one_iff hV f p₀ hp₀.2).mp hneg
    obtain ⟨p,hp,hcover,_,hbound⟩ :=
      exists_cover_of_counterexample hm hK hc hne hV f hnorm hunit hcell p₀ hp₀ hbad
    exact ⟨p,interior_subset hp,hcover,hbound⟩

/-- It suffices to bound covers with at least `2*(m+1)` contact cells in the
interior endpoint domain. The preceding plank case and many-cell inequality
are the other two explicit inputs. No bound for arbitrary covers is required. -/
theorem bound_normalized_of_counted_covers {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1) (hcell : ManyCellBound K f)
    (hcover : ∀ p ∈ interior (domain K f),
      K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} →
      2*(m+1) ≤ (nonemptyCells K f p).card → 1 ≤ budget K f p)
    (p₀ : Endpoints (Fin (m+1))) (hp₀ : p₀ ∈ domain K f) :
    (max 0 (1-budget K f p₀))^(d+1)*(volume K).toReal ≤ gapVolume K f p₀ := by
  by_contra hn
  obtain ⟨p,hp,hcov,hR,_,hcount⟩ := exists_counted_cover_of_counterexample
    hm hK hc hne hV f hnorm hunit hcell p₀ hp₀ (lt_of_not_ge hn)
  exact hR.not_ge (hcover p hp hcov hcount)

/-- A bound for all covers is a sufficient specialization of the counted-cover
criterion. The original interface is preserved. -/
theorem bound_normalized {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1) (hcell : ManyCellBound K f)
    (hcover : ∀ p ∈ domain K f,
      K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} → 1 ≤ budget K f p)
    (p₀ : Endpoints (Fin (m+1))) (hp₀ : p₀ ∈ domain K f) :
    (max 0 (1-budget K f p₀))^(d+1)*(volume K).toReal ≤ gapVolume K f p₀ := by
  exact bound_normalized_of_counted_covers hm hK hc hne hV f hnorm hunit hcell
    (fun p hp hcov _ => hcover p (interior_subset hp) hcov) p₀ hp₀

end Plank.FiniteDimensionalMinimumCompletion

#print axioms Plank.FiniteDimensionalMinimumCompletion.exists_counted_cover_of_counterexample
#print axioms Plank.FiniteDimensionalMinimumCompletion.exists_cover_of_counterexample
#print axioms Plank.FiniteDimensionalMinimumCompletion.exists_cover_completion
#print axioms Plank.FiniteDimensionalMinimumCompletion.bound_normalized
#print axioms Plank.FiniteDimensionalMinimumCompletion.bound_normalized_of_counted_covers
