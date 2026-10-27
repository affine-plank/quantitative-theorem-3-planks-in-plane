/- Exhaustive placement for a positive parallel pair and the other diagonal direction. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCaps
public import Plank.Proofs.Quant.CrossedQuadrilateralParallelPair

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralTwoDirections
open Set MeasureTheory
open Quant.CrossedQuadrilateralAttainment Quant.CrossedQuadrilateralPlacement
open Quant.CrossedQuadrilateralParallelPair Quant.CrossedQuadrilateralCaps
open scoped BigOperators

theorem separated_endpoints_strict (S : Shape) (l₀ u₀ l₁ u₁ ly uy : ℝ)
    (h₀ : l₀ < u₀) (h₁ : l₁ < u₁) (hsep : u₀ < l₁) (hy : ly ≤ uy)
    (hbudget : (u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (1-((u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d)))^2*
        (volume S.body).toReal <
      (volume (S.body \ (band false l₀ u₀ ∪ band false l₁ u₁ ∪ band true ly uy))).toReal := by
  let lo : Bool → ℝ := fun i => if i then l₁ else l₀
  let hi : Bool → ℝ := fun i => if i then u₁ else u₀
  have ho (i : Bool) : lo i < hi i := by cases i <;> assumption
  have hw : parallelBudget S lo hi = (u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c) := by
    simp [parallelBudget,lo,hi,add_comm]
    ring
  have hu : (⋃ i, band false (lo i) (hi i)) = band false l₀ u₀ ∪ band false l₁ u₁ := by
    ext z
    simp [lo,hi]
  have h := separated_pair_arbitrary_transverse_strict S lo hi ho hsep ly uy hy (by rwa [hw])
  simpa only [hw,hu,sub_add_eq_sub_sub] using h

/-- Complete iff for this two-direction chart: the positive parallel pair must
be adjacent and its union must be calibrated. The transverse band is calibrated
when positive and may be anywhere when null. No overlap, clipping, meeting, or
origin-containment premise is assumed. -/
theorem equality_iff_adjacent (S : Shape) (l₀ u₀ l₁ u₁ ly uy : ℝ)
    (h₀ : l₀ < u₀) (h₁ : l₁ < u₁) (horder : l₀ ≤ l₁) (hy : ly ≤ uy)
    (hbudget : (u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (volume (S.body \ (band false l₀ u₀ ∪ band false l₁ u₁ ∪ band true ly uy))).toReal =
        (1-((u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d)))^2*
          (volume S.body).toReal ↔
      u₀ = l₁ ∧ u₁/S.a = -l₀/S.c ∧ (uy = ly ∨ uy/S.b = -ly/S.d) := by
  constructor
  · intro he
    by_cases hmeet : l₁ ≤ u₀
    · exact (meeting_equality_iff S l₀ u₀ l₁ u₁ ly uy h₀ h₁ horder hmeet hy hbudget).mp he
    · have hstrict := separated_endpoints_strict S l₀ u₀ l₁ u₁ ly uy h₀ h₁
        (lt_of_not_ge hmeet) hy hbudget
      linarith
  · intro h
    exact (meeting_equality_iff S l₀ u₀ l₁ u₁ ly uy h₀ h₁ horder h.1.symm.le hy hbudget).mpr h

def physicalFamily (l₀ u₀ l₁ u₁ ly uy : ℝ) (h₀ : l₀ ≤ u₀) (h₁ : l₁ ≤ u₁) (hy : ly ≤ uy) :
    Fin 3 → Plank := ![axisPlank false l₀ u₀ h₀,axisPlank false l₁ u₁ h₁,axisPlank true ly uy hy]

theorem physicalFamily_union (l₀ u₀ l₁ u₁ ly uy : ℝ)
    (h₀ : l₀ ≤ u₀) (h₁ : l₁ ≤ u₁) (hy : ly ≤ uy) :
    (⋃ i, (physicalFamily l₀ u₀ l₁ u₁ ly uy h₀ h₁ hy i).set) =
      band false l₀ u₀ ∪ band false l₁ u₁ ∪ band true ly uy := by
  ext z
  simp only [mem_iUnion,mem_union]
  constructor
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact Or.inl (Or.inl (by simpa [physicalFamily] using hi))
    · exact Or.inl (Or.inr (by simpa [physicalFamily] using hi))
    · exact Or.inr (by simpa [physicalFamily] using hi)
  · rintro ((hx | hx) | hy)
    · exact ⟨0,by simpa [physicalFamily] using hx⟩
    · exact ⟨1,by simpa [physicalFamily] using hx⟩
    · exact ⟨2,by simpa [physicalFamily] using hy⟩

/-- Three physical planks, with the total formed from their actual relative widths. -/
theorem physicalFamily_equality_iff (S : Shape) (l₀ u₀ l₁ u₁ ly uy : ℝ)
    (h₀ : l₀ < u₀) (h₁ : l₁ < u₁) (horder : l₀ ≤ l₁) (hy : ly ≤ uy)
    (hbudget : (u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    (volume (S.body \ ⋃ i, (physicalFamily l₀ u₀ l₁ u₁ ly uy h₀.le h₁.le hy i).set)).toReal =
        (1-∑ i, relativeWidth S (physicalFamily l₀ u₀ l₁ u₁ ly uy h₀.le h₁.le hy i))^2*
          (volume S.body).toReal ↔
      u₀ = l₁ ∧ u₁/S.a = -l₀/S.c ∧ (uy = ly ∨ uy/S.b = -ly/S.d) := by
  have hw₀ := axisPlank_relative_width S l₀ u₀ ly uy h₀.le hy
  have hw₁ := axisPlank_relative_width S l₁ u₁ ly uy h₁.le hy
  rw [physicalFamily_union]
  simpa [physicalFamily,Fin.sum_univ_three,hw₀.1,hw₁.1,hw₀.2] using
    equality_iff_adjacent S l₀ u₀ l₁ u₁ ly uy h₀ h₁ horder hy hbudget

end Quant.CrossedQuadrilateralTwoDirections

/-- info: 'Quant.CrossedQuadrilateralTwoDirections.physicalFamily_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralTwoDirections.physicalFamily_equality_iff
