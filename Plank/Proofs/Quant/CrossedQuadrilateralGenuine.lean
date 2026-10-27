/- The overlap and cell-count restrictions for every genuine quadrilateral. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralNormalForm

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralGenuine
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarSevenCellArea PlanarDirectionDerivatives PlanarEqualityReductions
open Plank.Convex.DeficientHeightTilt

/-- Exactly four listed distinct extreme vertices generate the body. No
coordinate chart, diagonal ordering or affine independence is assumed. -/
def Genuine (K : Set Point) : Prop :=
  ∃ v : Fin 4 → Point, Function.Injective v ∧ K = convexHull ℝ (Set.range v) ∧
    ∀ i, v i ∈ K.extremePoints ℝ

theorem exists_model {K : Set Point} (hK : Genuine K) (hV : 0 < (volume K).toReal) :
    ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point),
      K = T '' CrossedQuadrilateralFormDirections.body S := by
  obtain ⟨v,hv,hbody,he⟩ := hK
  rw [hbody] at he hV ⊢
  exact CrossedQuadrilateralNormalForm.exists_model v hv he hV

/-- Seven nonempty closed exterior cells are strictly above the square bound
on every genuine quadrilateral, including all null-cell degeneracies. -/
theorem seven_nonempty_strict {K : Set Point} (hK : Genuine K) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1)
    (hcount : 7 ≤ (PlanarSevenNonemptyCells.nonemptyCells K f p).card) :
    (1-budget K f p)^2*(volume K).toReal < gapArea K f p := by
  obtain ⟨S,T,rfl⟩ := exists_model hK hV
  exact CrossedQuadrilateralImageStrata.seven_nonempty_strict S T f p hW ho hR hcount

theorem at_most_six_of_equality {K : Set Point} (hK : Genuine K) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) (he : Equality K f p) :
    (PlanarSevenNonemptyCells.nonemptyCells K f p).card ≤ 6 := by
  obtain ⟨S,T,rfl⟩ := exists_model hK hV
  exact CrossedQuadrilateralImageStrata.at_most_six_of_equality S T f p hW ho hR he

theorem contained_null_strict {K : Set Point} (hK : Genuine K) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (hc : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (ht : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0) :
    (1-budget K f p)^2*(volume K).toReal < gapArea K f p := by
  obtain ⟨S,T,rfl⟩ := exists_model hK hV
  exact CrossedQuadrilateralImageStrata.contained_null_strict S T f p hW ho hpairs hR hc ht

theorem contained_concurrent_strict {K : Set Point} (hK : Genuine K) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (hc : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (ha : CrossedQuadrilateralConcurrent.Concurrent K f p) :
    (1-budget K f p)^2*(volume K).toReal < gapArea K f p := by
  obtain ⟨S,T,rfl⟩ := exists_model hK hV
  exact CrossedQuadrilateralImageStrata.contained_concurrent_strict S T f p hW ho hpairs hR hc ha

/-- A proved necessary list of the remaining three-distinct-direction
possibilities. Neither alternative is asserted to attain equality. -/
theorem remaining_obstruction {K : Set Point} (hK : Genuine K) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (he : Equality K f p) :
    (∃ i j, i ≠ j ∧ ∃ x, x ∈ plank (f i) (p.1 i) (p.2 i) ∩
      plank (f j) (p.1 j) (p.2 j) ∧ x ∉ K) ∨
    (0 < volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∧
      ¬CrossedQuadrilateralConcurrent.Concurrent K f p) := by
  classical
  change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at he
  rw [max_eq_right (sub_pos.mpr hR).le] at he
  by_cases hc : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K
  · right
    constructor
    · apply pos_iff_ne_zero.mpr
      intro ht
      have hs := contained_null_strict hK hV f p hW ho hpairs hR hc ht
      linarith only [he,hs]
    · intro ha
      have hs := contained_concurrent_strict hK hV f p hW ho hpairs hR hc ha
      linarith only [he,hs]
  · left
    simp only [Set.subset_def] at hc
    push Not at hc
    exact hc

/-- For two positive windows with four nonempty cells, the normal form is
constructed from the actual body and both original forms align with its diagonals. -/
theorem two_four_cells_diagonal_model {K : Set Point} (hK : Genuine K) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) (hcell : ∀ s, (signCell K f p.1 p.2 s).Nonempty)
    (he : Equality K f p) :
    ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point),
      K = T '' CrossedQuadrilateralFormDirections.body S ∧
      ∀ i, (f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0 := by
  obtain ⟨S,T,rfl⟩ := exists_model hK hV
  exact ⟨S,T,rfl,CrossedQuadrilateralImageStrata.directions_of_four_cells S T f p hW ho hR hcell he⟩

end Quant.CrossedQuadrilateralGenuine

/-- info: 'Quant.CrossedQuadrilateralGenuine.remaining_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralGenuine.remaining_obstruction
