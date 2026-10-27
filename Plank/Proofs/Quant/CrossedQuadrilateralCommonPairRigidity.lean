/- A common-support positive pair and a transverse band force diagonal directions. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonPairReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCommonPairRigidity
open Set MeasureTheory
open CrossedQuadrilateralAttainment CrossedQuadrilateralDiagonalSplit
open CrossedQuadrilateralCommonSupport CrossedQuadrilateralCommonPairSplit
open CommonMiddleAffineTransport CommonMiddleNullWindow
open scoped BigOperators

/-- In this support sector, neither of the two initially arbitrary pair
directions can remain oblique in a three-positive-plank equality. -/
theorem parallel_of_equality (S : Shape) (p : Fin 2 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (hw : ∀ i, 0 < relativeWidth S (p i))
    (l u : ℝ) (ho : l < u) (hR : budget S p l u < 1)
    (he : (volume (S.body \ ⋃ i, (family p l u ho.le i).set)).toReal =
      (1-budget S p l u)^2*(volume S.body).toReal) :
    ∀ i, (p i).u.2 = 0 := by
  have hpair := CrossedQuadrilateralCommonPairReduction.pair_stack S p h hw l u ho hR he
  have hsmall : pairWidth S p < 1 := by
    have ht : 0 < (u-l)/(S.b+S.d) := div_pos (sub_pos.mpr ho) (add_pos S.hb S.hd)
    change pairWidth S p+(u-l)/(S.b+S.d) < 1 at hR
    linarith only [hR,ht]
  let Q := splitFamily (p 0) (p 1)
  have hc (i : Fin 3) : CommonSupports S (Q i) := by
    intro j
    fin_cases i
    · exact h 0 j
    · exact h 0 j
    · exact h 1 j
  have hsum (j : Bool) : (∑ i, (Q i).relWidth (half S j)) = pairWidth S p := by
    dsimp only [Q]
    rw [split_sum,relativeWidth_half S _ (h 0),relativeWidth_half S _ (h 1)]
    simp only [pairWidth,Fin.sum_univ_two]
  have hsumS : (∑ i, relativeWidth S (Q i)) = pairWidth S p := by
    calc
      _ = ∑ i, (Q i).relWidth (half S true) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (relativeWidth_half S _ (hc i) true).symm
      _ = _ := hsum true
  have hp (i : Fin 3) : 0 < relativeWidth S (Q i) := by
    rw [← relativeWidth_half S _ (hc i) true]
    fin_cases i
    · change 0 < (halfLo (p 0)).relWidth (half S true)
      rw [halfLo_relWidth,relativeWidth_half S _ (h 0)]
      exact half_pos (hw 0)
    · change 0 < (halfHi (p 0)).relWidth (half S true)
      rw [halfHi_relWidth,relativeWidth_half S _ (h 0)]
      exact half_pos (hw 0)
    · exact (relativeWidth_half S _ (h 1) true).symm ▸ hw 1
  have heh (j : Bool) : (volume ((half S j).set \ ⋃ i, (Q i).set)).toReal =
      (1-pairWidth S p)^2*(volume (half S j).set).toReal := by
    have hs := splitStack_of_pairStack (half S j) (p 0) (p 1) (h 0 j) (h 1 j) (hpair j)
    have hh := equality_of_orderedStack (half S j) Q (fun i => hc i j)
      (by rw [hsum]; exact hsmall) hs
    rwa [hsum] at hh
  have heQ : (volume (S.body \ ⋃ i, (Q i).set)).toReal =
      (1-∑ i, relativeWidth S (Q i))^2*(volume S.body).toReal := by
    rw [hsumS,gap_split S _ (MeasurableSet.iUnion
      (fun i => (Proofs.Quant.isClosed_plank_set _).measurableSet)),heh false,heh true,area_split]
    ring
  have hpQ := CrossedQuadrilateralCommonSupport.parallel_of_equality S Q hc hp
    (by rw [hsumS]; exact hsmall) heQ
  intro i
  fin_cases i
  · exact hpQ 0
  · exact hpQ 2

end Quant.CrossedQuadrilateralCommonPairRigidity

/-- info: 'Quant.CrossedQuadrilateralCommonPairRigidity.parallel_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCommonPairRigidity.parallel_of_equality
