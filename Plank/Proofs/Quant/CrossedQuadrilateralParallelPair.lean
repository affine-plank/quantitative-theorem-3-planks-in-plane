/- Equality restrictions on two parallel planks and one transverse plank. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralPlacement

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralParallelPair
open Set MeasureTheory
open Quant.CrossedQuadrilateralAttainment Quant.CrossedQuadrilateralPlacement

theorem overlapping_union {l₀ u₀ l₁ u₁ : ℝ} (h₀ : l₁ ≤ u₀) (h₁ : l₀ ≤ u₁) :
    band false l₀ u₀ ∪ band false l₁ u₁ = band false (min l₀ l₁) (max u₀ u₁) :=
  congrArg (fun A : Set ℝ => Prod.fst ⁻¹' A) (Set.Icc_union_Icc' h₀ h₁)

/-- Overlap of positive length wastes relative width and makes the square
bound strict. This is an actual-area statement, not a scalar surrogate. -/
theorem positive_overlap_strict (S : Shape) (l₀ u₀ l₁ u₁ ly uy : ℝ)
    (h₀ : l₀ ≤ u₀) (_h₁ : l₁ ≤ u₁) (hy : ly ≤ uy)
    (hoverlap : max l₀ l₁ < min u₀ u₁)
    (hbudget : (u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (1-((u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d)))^2*
        (volume S.body).toReal <
      (volume (S.body \ (band false l₀ u₀ ∪ band false l₁ u₁ ∪ band true ly uy))).toReal := by
  have hcross₀ : l₁ ≤ u₀ := (le_max_right _ _).trans (hoverlap.le.trans (min_le_left _ _))
  have hcross₁ : l₀ ≤ u₁ := (le_max_left _ _).trans (hoverlap.le.trans (min_le_right _ _))
  rw [overlapping_union hcross₀ hcross₁]
  have hordered : min l₀ l₁ ≤ max u₀ u₁ :=
    (min_le_left _ _).trans (h₀.trans (le_max_left _ _))
  have hlen : max u₀ u₁-min l₀ l₁ < (u₀-l₀)+(u₁-l₁) := by
    linarith [min_add_max l₀ l₁,min_add_max u₀ u₁]
  have hwidth : (max u₀ u₁-min l₀ l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d) <
      (u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d) := by
    rw [← add_div]
    have h := div_lt_div_of_pos_right hlen (add_pos S.ha S.hc)
    linarith
  have hbound := arbitrary_placement_lower_bound S _ _ ly uy hordered hy (hwidth.trans hbudget)
  have hsquare :
      (1-((u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d)))^2 <
      (1-(max u₀ u₁-min l₀ l₁)/(S.a+S.c)-(uy-ly)/(S.b+S.d))^2 := by
    nlinarith
  exact (mul_lt_mul_of_pos_right hsquare (area_body_pos S)).trans_le hbound

/-- If the parallel intervals meet and both have positive width, equality
forces them to be adjacent. The two interval endpoints may initially interlace
or one interval may be contained in the other. -/
theorem meeting_equality_iff (S : Shape) (l₀ u₀ l₁ u₁ ly uy : ℝ)
    (h₀ : l₀ < u₀) (h₁ : l₁ < u₁) (horder : l₀ ≤ l₁) (hmeet : l₁ ≤ u₀)
    (hy : ly ≤ uy)
    (hbudget : (u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (volume (S.body \ (band false l₀ u₀ ∪ band false l₁ u₁ ∪ band true ly uy))).toReal =
        (1-((u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d)))^2*
          (volume S.body).toReal ↔
      u₀ = l₁ ∧ u₁/S.a = -l₀/S.c ∧ (uy = ly ∨ uy/S.b = -ly/S.d) := by
  have hsum (he : u₀ = l₁) :
      (u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c) = (u₁-l₀)/(S.a+S.c) := by
    rw [← add_div,he]
    congr 1
    ring
  constructor
  · intro he
    have hadj : u₀ = l₁ := by
      apply le_antisymm ?_ hmeet
      by_contra h
      have hl : l₁ < u₀ := lt_of_not_ge h
      have hover : max l₀ l₁ < min u₀ u₁ := by
        rw [max_eq_right horder]
        exact lt_min hl h₁
      have hstrict := positive_overlap_strict S l₀ u₀ l₁ u₁ ly uy h₀.le h₁.le hy hover hbudget
      linarith
    refine ⟨hadj,?_⟩
    have hb : (u₁-l₀)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1 := by rwa [hsum hadj] at hbudget
    have hu : band false l₀ u₀ ∪ band false l₁ u₁ = band false l₀ u₁ := by
      rw [hadj]
      exact congrArg (fun A : Set ℝ => Prod.fst ⁻¹' A) (Set.Icc_union_Icc_eq_Icc horder h₁.le)
    rw [hu,hsum hadj,sub_add_eq_sub_sub] at he
    have hh := (arbitrary_placement_equality_iff S l₀ u₁ ly uy
      (horder.trans h₁.le) hy hb).mp he
    exact ⟨hh.1.resolve_left (ne_of_gt (horder.trans_lt h₁)),hh.2⟩
  · rintro ⟨hadj,hx,hyc⟩
    have hb : (u₁-l₀)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1 := by rwa [hsum hadj] at hbudget
    have hu : band false l₀ u₀ ∪ band false l₁ u₁ = band false l₀ u₁ := by
      rw [hadj]
      exact congrArg (fun A : Set ℝ => Prod.fst ⁻¹' A) (Set.Icc_union_Icc_eq_Icc horder h₁.le)
    rw [hu,hsum hadj,sub_add_eq_sub_sub]
    exact (arbitrary_placement_equality_iff S l₀ u₁ ly uy
      (horder.trans h₁.le) hy hb).mpr ⟨Or.inr hx,hyc⟩

end Quant.CrossedQuadrilateralParallelPair

/-- info: 'Quant.CrossedQuadrilateralParallelPair.meeting_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralParallelPair.meeting_equality_iff
