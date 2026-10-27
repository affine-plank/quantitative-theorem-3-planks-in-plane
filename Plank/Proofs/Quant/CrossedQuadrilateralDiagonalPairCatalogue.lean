/- Exhaustive two-family catalogue when two positive planks follow one diagonal. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralVerticalStack
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonSupportAffine

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralDiagonalPairCatalogue
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralPlacement
open CrossedQuadrilateralBandPresentation CrossedQuadrilateralSectionGeometry
open CrossedQuadrilateralTwoPlankCatalogue
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def mixedDirections : Fin 3 → Bool := ![false,false,true]

/-- Every witness preserves the whole original plank and its actual relative width. -/
def Presented (S : Shape) (p : Fin 3 → Plank) (v : Fin 3 → Bool) (l u : Fin 3 → ℝ) : Prop :=
  ∀ i, l i < u i ∧ (p i).set = band (v i) (l i) (u i) ∧
    relativeWidth S (p i) = (u i-l i)/span S (v i)

def Mixed (S : Shape) (l u : Fin 3 → ℝ) : Prop :=
  ((u 0 = l 1 ∧ u 1/S.a = -l 0/S.c) ∨ (u 1 = l 0 ∧ u 0/S.a = -l 1/S.c)) ∧
    u 2/S.b = -l 2/S.d

/-- Three adjacent calibrated parallel pieces, or two adjacent calibrated
pieces together with a calibrated band in the other diagonal direction. -/
def Catalogue (S : Shape) (p : Fin 3 → Plank) : Prop :=
  (∃ l u, Presented S p (fun _ => false) l u ∧ CrossedQuadrilateralVerticalStack.Stack S l u) ∨
  (∃ l u, Presented S p mixedDirections l u ∧ Mixed S l u)

theorem oblique_zero (lo hi : ℝ) : oblique 0 lo hi = band true lo hi := by
  ext z
  simp [oblique,band,coord]

theorem all_vertical (S : Shape) (p : Fin 3 → Plank) (hp : ∀ i, (p i).lo < (p i).hi)
    (hy : ∀ i, (p i).u.2 = 0) (hR : (∑ i, relativeWidth S (p i)) < 1)
    (he : (volume (S.body \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, relativeWidth S (p i))^2*(volume S.body).toReal) : Catalogue S p := by
  choose l u ho hs hw using fun i => vertical_plank S (p i) (hp i) (hy i)
  have hb : CrossedQuadrilateralVerticalStack.total S l u = ∑ i, relativeWidth S (p i) := by
    unfold CrossedQuadrilateralVerticalStack.total
    exact Finset.sum_congr rfl (fun i _ => (hw i).symm)
  refine Or.inl ⟨l,u,fun i => ⟨ho i,hs i,hw i⟩,?_⟩
  apply (CrossedQuadrilateralVerticalStack.equality_iff_stack S l u ho (by rwa [hb])).mp
  rw [hb,← iUnion_congr hs]
  exact he

theorem transverse (S : Shape) (p : Fin 3 → Plank) (hp : ∀ i, (p i).lo < (p i).hi)
    (hy0 : (p 0).u.2 = 0) (hy1 : (p 1).u.2 = 0) (hy2 : (p 2).u.2 ≠ 0)
    (hR : (∑ i, relativeWidth S (p i)) < 1)
    (he : (volume (S.body \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, relativeWidth S (p i))^2*(volume S.body).toReal) : Catalogue S p := by
  obtain ⟨a,b,hab,hs0,hw0⟩ := vertical_plank S (p 0) (hp 0) hy0
  obtain ⟨c,d,hcd,hs1,hw1⟩ := vertical_plank S (p 1) (hp 1) hy1
  obtain ⟨k,lo,hi,ho,hs2,hw2,_⟩ := transverse_plank S (p 2) (hp 2) hy2
  have hb : CrossedQuadrilateralPairBudget.budget S k a b c d lo hi =
      ∑ i, relativeWidth S (p i) := by
    rw [Fin.sum_univ_three,hw0,hw1,hw2]
    rfl
  have hu : (⋃ i, (p i).set) = ((band false a b ∪ band false c d) ∪ oblique k lo hi) := by
    rw [CrossedQuadrilateralCommonPairSplit.union_three,hs0,hs1,hs2,← union_assoc]
  change (⋃ i, (p i).set) = ((UnimodalPlanarMerge.band a b ∪
    UnimodalPlanarMerge.band c d) ∪ oblique k lo hi) at hu
  have hc := (CrossedQuadrilateralVerticalPairCatalogue.equality_iff_catalogue S hab hcd ho
    (by rwa [hb])).mp (by rw [CrossedQuadrilateralPairBudget.gap,← hu,hb]; exact he)
  obtain ⟨hk,hcal⟩ := hc
  subst k
  rw [oblique_zero] at hs2
  rw [CrossedQuadrilateralObliquePhysical.oblique_range S
    (CrossedQuadrilateralVerticalPairCatalogue.zero_supports S)] at hw2
  refine Or.inr ⟨![a,c,lo],![b,d,hi],?_,hcal⟩
  intro i
  fin_cases i
  · exact ⟨hab,hs0,hw0⟩
  · exact ⟨hcd,hs1,hw1⟩
  · exact ⟨ho,hs2,hw2⟩

theorem equality_of_catalogue (S : Shape) (p : Fin 3 → Plank)
    (hR : (∑ i, relativeWidth S (p i)) < 1) (hc : Catalogue S p) :
    (volume (S.body \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, relativeWidth S (p i))^2*(volume S.body).toReal := by
  rcases hc with ⟨l,u,hp,hs⟩ | ⟨l,u,hp,hm⟩
  · have hb : CrossedQuadrilateralVerticalStack.total S l u = ∑ i, relativeWidth S (p i) :=
      Finset.sum_congr rfl (fun i _ => (hp i).2.2.symm)
    have he := (CrossedQuadrilateralVerticalStack.equality_iff_stack S l u
      (fun i => (hp i).1) (by rwa [hb])).mpr hs
    rw [hb,← iUnion_congr (fun i => (hp i).2.1)] at he
    exact he
  · have hb : CrossedQuadrilateralObliqueCatalogue.total S (l 0) (u 0) (l 1) (u 1) (l 2) (u 2) =
        ∑ i, relativeWidth S (p i) := by
      rw [Fin.sum_univ_three,(hp 0).2.2,(hp 1).2.2,(hp 2).2.2]
      rfl
    have he := (CrossedQuadrilateralObliqueCatalogue.horizontal_iff S
      (hp 0).1 (hp 1).1 (hp 2).1 (by rwa [hb])).mpr hm
    have hu : (⋃ i, (p i).set) = ((band false (l 0) (u 0) ∪ band false (l 1) (u 1)) ∪
        oblique 0 (l 2) (u 2)) := by
      rw [CrossedQuadrilateralCommonPairSplit.union_three,(hp 0).2.1,(hp 1).2.1,(hp 2).2.1,
        oblique_zero,← union_assoc]
      rfl
    change (⋃ i, (p i).set) = ((UnimodalPlanarMerge.band (l 0) (u 0) ∪
      UnimodalPlanarMerge.band (l 1) (u 1)) ∪ oblique 0 (l 2) (u 2)) at hu
    rw [hb,← hu] at he
    exact he

/-- The third positive plank has no direction or support restriction. -/
theorem equality_iff_catalogue (S : Shape) (p : Fin 3 → Plank)
    (hp : ∀ i, (p i).lo < (p i).hi) (hy0 : (p 0).u.2 = 0) (hy1 : (p 1).u.2 = 0)
    (hR : (∑ i, relativeWidth S (p i)) < 1) :
    (volume (S.body \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, relativeWidth S (p i))^2*(volume S.body).toReal ↔ Catalogue S p := by
  constructor
  · intro he
    by_cases hy2 : (p 2).u.2 = 0
    · exact all_vertical S p hp (by intro i; fin_cases i; exact hy0; exact hy1; exact hy2) hR he
    · exact transverse S p hp hy0 hy1 hy2 hR he
  · exact equality_of_catalogue S p hR

end Quant.CrossedQuadrilateralDiagonalPairCatalogue

/-- info: 'Quant.CrossedQuadrilateralDiagonalPairCatalogue.equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralDiagonalPairCatalogue.equality_iff_catalogue
