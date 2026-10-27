/- Exhaustive quantitative equality for triples with a null-width member. -/
module

public import Plank.Proofs.Quant.PlanarArithmeticStrata

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarNullPlankTriple

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarAffineEquality PlanarFourPointClassification
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Removing any selected zero-width member preserves both actual gap and
relative budget, in the remaining two original directions. -/
theorem delete_null {K : Set Point} (hne : K.Nonempty)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (i : Fin 3) (hi : p.1 i = p.2 i) :
    gapArea K f p = gapArea K (fun j : Fin 2 => f (i.succAbove j))
      (fun j => p.1 (i.succAbove j),fun j => p.2 (i.succAbove j)) ∧
    budget K f p = budget K (fun j : Fin 2 => f (i.succAbove j))
      (fun j => p.1 (i.succAbove j),fun j => p.2 (i.succAbove j)) := by
  constructor
  · have hu : (⋃ j : Fin 3, {x | p.1 j ≤ f j x ∧ f j x ≤ p.2 j}) =
        {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∪
          ⋃ j : Fin 2, {x | p.1 (i.succAbove j) ≤ f (i.succAbove j) x ∧
            f (i.succAbove j) x ≤ p.2 (i.succAbove j)} := by
      ext x
      simp only [mem_iUnion,mem_union,mem_ofPred_eq]
      exact Fin.exists_iff_succAbove i
    unfold gapArea
    rw [hu,← hi]
    exact PlanarInductionBoundary.area_delete_zero_width K _ (f i)
      (linear_ne_zero_of_rangeWidth_pos hne (f i) (hW i)) _
  · unfold budget
    rw [Fin.sum_univ_succAbove _ i,hi,sub_self,zero_div,zero_add]

theorem four_vertices {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hnull : ∃ i, p.1 i = p.2 i) (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : Equality K f p.1 p.2) : ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨i,hi⟩ := hnull
  obtain ⟨hg,hb⟩ := delete_null hne f p hW i hi
  apply PlanarTwoPlankShapeOriginal.four_vertices hK hc hne hV
    (fun j : Fin 2 => f (i.succAbove j))
    (fun j => p.1 (i.succAbove j),fun j => p.2 (i.succAbove j))
    (fun j => hW (i.succAbove j)) (fun j => ho (i.succAbove j))
    (by rwa [← hb]) (by rwa [← hb])
  rw [← hg,← hb]
  change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at heq
  rwa [max_eq_right (sub_pos.mpr hR1).le] at heq

/-- The complete positive-deficit classification with a null member,
without assumptions on cell counts, parallelism, endpoint positions or K's shape. -/
theorem equality_iff {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hnull : ∃ i, p.1 i = p.2 i) (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1) :
    Equality K f p.1 p.2 ↔ Family K f p.1 p.2 := by
  constructor
  · intro he
    exact (equality_iff_of_four_vertices hV
      (four_vertices hK hc hne hV f p hW ho hnull hR0 hR1 he) f p.1 p.2 hW ho).mp he
  · exact family_sound f p.1 p.2 hW ho

def Family (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) : Prop :=
  budget K f p = 0 ∨
    (1 ≤ budget K f p ∧ K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) ∨
    (0 < budget K f p ∧ budget K f p < 1 ∧ PlanarFourPointClassification.Family K f p.1 p.2)

/-- All budgets are included: zero budget, actual covers at exhausted
budget, and the explicit finite arithmetic family for positive deficit. -/
theorem equality_iff_all_budgets {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hnull : ∃ i, p.1 i = p.2 i) : Equality K f p.1 p.2 ↔ Family K f p := by
  have hn : 0 ≤ budget K f p := Finset.sum_nonneg fun i _ =>
    div_nonneg (sub_nonneg.mpr (ho i)) (hW i).le
  constructor
  · intro he
    by_cases hz : budget K f p = 0
    · exact Or.inl hz
    by_cases hb : 1 ≤ budget K f p
    · exact Or.inr (Or.inl ⟨hb,(PlanarEqualityReductions.equality_iff_cover_of_one_le
        hK hc hV f p hb).mp he⟩)
    · have hp := lt_of_le_of_ne hn (Ne.symm hz)
      have hl := lt_of_not_ge hb
      exact Or.inr (Or.inr ⟨hp,hl,(equality_iff hK hc hne hV f p hW ho hnull hp hl).mp he⟩)
  · rintro (hz | ⟨hb,hcover⟩ | ⟨_,_,hf⟩)
    · exact PlanarEqualityReductions.equality_of_budget_zero hne f p hW ho hz
    · exact (PlanarEqualityReductions.equality_iff_cover_of_one_le hK hc hV f p hb).mpr hcover
    · exact family_sound f p.1 p.2 hW ho hf

end Plank.PlanarNullPlankTriple

/-- info: 'Plank.PlanarNullPlankTriple.equality_iff_all_budgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarNullPlankTriple.equality_iff_all_budgets
