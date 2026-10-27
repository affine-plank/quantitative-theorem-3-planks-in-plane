/- Equality forces calibration of the band transverse to a common-support pair. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonPairSplit

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCommonPairCalibration
open Set MeasureTheory
open CrossedQuadrilateralAttainment CrossedQuadrilateralDiagonalSplit
open CrossedQuadrilateralCommonSupport CrossedQuadrilateralCommonPairSplit
open scoped BigOperators

/-- Actual equality forces the two trimmed relative widths to agree.
The two common-support planks need not be parallel or positive. -/
theorem half_width_eq (S : Shape) (p : Fin 2 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (l u : ℝ) (ho : l ≤ u)
    (hR : budget S p l u < 1)
    (he : (volume (S.body \ ⋃ i, (family p l u ho i).set)).toReal =
      (1-budget S p l u)^2*(volume S.body).toReal) :
    ∀ j, halfWidth S j l u = (u-l)/(S.b+S.d) := by
  let w (j : Bool) := (volume (half S j).set).toReal
  let x (j : Bool) := 1-pairWidth S p-halfWidth S j l u
  have hw (j) : 0 < w j := half_area_pos S j
  have hm : 0 < 1-budget S p l u := sub_pos.mpr hR
  have hmean : (∑ j, w j*x j) = (1-budget S p l u)*(∑ j, w j) :=
    half_deficit_mean S p l u
  have hlow := CrossedQuadrilateralPlacement.weighted_hinge_lower_bound w x
    (fun j => (hw j).le) hm.le hmean
  have hb (j) : w j*(max 0 (x j))^2 ≤
      (volume ((half S j).set \ ⋃ i, (family p l u ho i).set)).toReal := by
    simpa only [w,x,mul_comm] using half_lower_bound S p h j l u ho
  have hs := gap_split S (⋃ i, (family p l u ho i).set)
    (MeasurableSet.iUnion (fun i => (Proofs.Quant.isClosed_plank_set _).measurableSet))
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Bool)) => hb j)
  have heq : (∑ j, w j*(max 0 (x j))^2) = (1-budget S p l u)^2*(∑ j, w j) := by
    apply le_antisymm _ hlow
    calc
      _ ≤ ∑ j : Bool, (volume ((half S j).set \ ⋃ i, (family p l u ho i).set)).toReal := hsum
      _ = (volume (S.body \ ⋃ i, (family p l u ho i).set)).toReal := by
        simpa only [Fintype.sum_bool,add_comm] using hs.symm
      _ = _ := by rw [he,area_split]; simp only [w,Fintype.sum_bool,add_comm]
  have hx := (CrossedQuadrilateralNecessity.weighted_hinge_equality w x hw hm hmean).mp heq
  intro j
  have hh := hx j
  dsimp [x,budget] at hh
  linarith only [hh]

/-- The transverse band must cross the diagonal intersection and use the
same fraction of the two remaining diagonals. No such placement is assumed. -/
theorem calibrated_of_equality (S : Shape) (p : Fin 2 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (l u : ℝ) (ho : l < u)
    (hR : budget S p l u < 1)
    (he : (volume (S.body \ ⋃ i, (family p l u ho.le i).set)).toReal =
      (1-budget S p l u)^2*(volume S.body).toReal) :
    l < 0 ∧ 0 < u ∧ u/S.b = (-l)/S.d := by
  have ht := half_width_eq S p h l u ho.le hR he
  have hp : 0 < (u-l)/(S.b+S.d) := div_pos (sub_pos.mpr ho) (add_pos S.hb S.hd)
  have hl : l < 0 := by
    by_contra hn
    have hl0 := le_of_not_gt hn
    have hu0 := hl0.trans ho.le
    have hh := ht false
    simp only [halfWidth,cut,Shape.Y,Bool.false_eq_true,if_false,min_eq_right hl0,
      min_eq_right hu0,sub_self,zero_div] at hh
    linarith only [hh,hp]
  have hu : 0 < u := by
    by_contra hn
    have hu0 := le_of_not_gt hn
    have hl0 := ho.le.trans hu0
    have hh := ht true
    simp only [halfWidth,cut,Shape.Y,if_true,max_eq_right hl0,max_eq_right hu0,
      sub_self,zero_div] at hh
    linarith only [hh,hp]
  refine ⟨hl,hu,?_⟩
  have hm := ht false
  have hp := ht true
  simp only [halfWidth,cut,Shape.Y,Bool.false_eq_true,if_false,if_true,
    min_eq_left hl.le,min_eq_right hu.le,max_eq_right hl.le,max_eq_left hu.le,
    sub_zero,zero_sub,abs_neg,abs_of_pos S.hb,abs_of_pos S.hd] at hm hp
  exact hp.trans hm.symm

theorem half_equality (S : Shape) (p : Fin 2 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (l u : ℝ) (ho : l ≤ u)
    (hR : budget S p l u < 1)
    (he : (volume (S.body \ ⋃ i, (family p l u ho i).set)).toReal =
      (1-budget S p l u)^2*(volume S.body).toReal) (j : Bool) :
    (volume ((half S j).set \ ⋃ i, (halfFamily p j l u ho i).set)).toReal =
      (1-budget S p l u)^2*(volume (half S j).set).toReal := by
  have ht := half_width_eq S p h l u ho hR he
  have hb (j) := half_lower_bound S p h j l u ho
  have hh (j) : 1-pairWidth S p-halfWidth S j l u = 1-budget S p l u := by
    rw [ht]
    dsimp [budget]
    ring
  simp only [hh,max_eq_right (sub_pos.mpr hR).le] at hb
  have hs := gap_split S (⋃ i, (family p l u ho i).set)
    (MeasurableSet.iUnion (fun i => (Proofs.Quant.isClosed_plank_set _).measurableSet))
  rw [he,area_split] at hs
  rw [clipped_gap]
  cases j <;> nlinarith only [hs,hb false,hb true]

end Quant.CrossedQuadrilateralCommonPairCalibration

/-- info: 'Quant.CrossedQuadrilateralCommonPairCalibration.calibrated_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCommonPairCalibration.calibrated_of_equality
