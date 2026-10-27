/- Calibrated half-triangle support removal for the common-support pair. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonPairCalibration
public import Plank.Proofs.Quant.CommonMiddleSupportReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCommonPairReduction
open Set MeasureTheory Proofs.Transport
open CrossedQuadrilateralAttainment CrossedQuadrilateralDiagonalSplit
open CrossedQuadrilateralCommonSupport CrossedQuadrilateralCommonPairSplit
open CommonMiddleAffineTransport CommonMiddleNullWindow
open scoped BigOperators

def level (S : Shape) (j : Bool) : Point →ᵃ[ℝ] ℝ :=
  ((S.Y j)⁻¹ • LinearMap.snd ℝ ℝ ℝ).toAffineMap

theorem level_apply (S : Shape) (j : Bool) (z : Point) : level S j z = z.2/S.Y j := by
  simp [level,div_eq_mul_inv,mul_comm]

theorem level_bounds (S : Shape) (j : Bool) {z : Point} (hz : z ∈ (half S j).set) :
    0 ≤ level S j z ∧ level S j z ≤ 1 := by
  rw [level_apply]
  refine ⟨half_sign S j hz,?_⟩
  obtain ⟨α,β,γ,hα,hβ,hγ,hs,rfl⟩ := hz
  have hγ1 : γ ≤ 1 := by linarith only [hα,hβ,hs]
  simpa [half,S.Y_ne j] using hγ1

theorem clipped_support (S : Shape) (l u : ℝ) (hl : l < 0) (hu : 0 < u)
    (j : Bool) (t : ℝ) (ht : halfWidth S j l u = t) :
    (clipped j l u (hl.trans hu).le).set = {z | 0 ≤ level S j z ∧ level S j z ≤ t} := by
  ext z
  change (cut j l ≤ 0*z.1+1*z.2 ∧ 0*z.1+1*z.2 ≤ cut j u) ↔
    (0 ≤ level S j z ∧ level S j z ≤ t)
  rw [level_apply]
  simp only [zero_mul,one_mul,zero_add]
  cases j
  · have ht' : (-l)/S.d = t := by
      simpa only [halfWidth,cut,Shape.Y,Bool.false_eq_true,if_false,
        min_eq_left hl.le,min_eq_right hu.le,zero_sub,abs_neg,abs_of_pos S.hd] using ht
    have htprod : t*(-S.d) = l := by
      have hh := (div_eq_iff S.hd.ne').mp ht'
      nlinarith only [hh]
    simp only [cut,Shape.Y,Bool.false_eq_true,if_false,min_eq_left hl.le,min_eq_right hu.le]
    rw [le_div_iff_of_neg (neg_lt_zero.mpr S.hd),div_le_iff_of_neg (neg_lt_zero.mpr S.hd)]
    simp only [zero_mul,htprod,and_comm]
  · have ht' : u/S.b = t := by
      simpa only [halfWidth,cut,Shape.Y,if_true,max_eq_right hl.le,max_eq_left hu.le,
        sub_zero,abs_of_pos S.hb] using ht
    have htprod : t*S.b = u := ((div_eq_iff S.hb.ne').mp ht').symm
    simp only [cut,Shape.Y,if_true,max_eq_right hl.le,max_eq_left hu.le]
    rw [le_div_iff₀ S.hb,div_le_iff₀ S.hb]
    simp only [zero_mul,htprod]

/-- After equality has calibrated the transverse band, support reduction
forces the original two planks to be an ordered stack on each half. -/
theorem pair_stack (S : Shape) (p : Fin 2 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (hw : ∀ i, 0 < relativeWidth S (p i))
    (l u : ℝ) (ho : l < u) (hR : budget S p l u < 1)
    (he : (volume (S.body \ ⋃ i, (family p l u ho.le i).set)).toReal =
      (1-budget S p l u)^2*(volume S.body).toReal) (j : Bool) :
    PairOrderedStack (half S j) (p 0) (p 1) := by
  obtain ⟨hl,hu,_⟩ := CrossedQuadrilateralCommonPairCalibration.calibrated_of_equality
    S p h l u ho hR he
  let t := (u-l)/(S.b+S.d)
  have ht : 0 < t := div_pos (sub_pos.mpr ho) (add_pos S.hb S.hd)
  have hwidth := CrossedQuadrilateralCommonPairCalibration.half_width_eq S p h l u ho.le hR he j
  have hs := clipped_support S l u hl hu j t hwidth
  have huSet : (⋃ i, (halfFamily p j l u ho.le i).set) =
      {z | 0 ≤ level S j z ∧ level S j z ≤ t} ∪ ⋃ i, (p i).set := by
    rw [union_three,CommonMiddleSupportReduction.union_two]
    change (p 0).set ∪ ((p 1).set ∪ (clipped j l u ho.le).set) = _
    rw [hs]
    ext z
    simp only [Set.mem_union]
    tauto
  have heh := CrossedQuadrilateralCommonPairCalibration.half_equality S p h l u ho.le hR he j
  rw [huSet] at heh
  have hbudget : 1-t-((p 0).relWidth (half S j)+(p 1).relWidth (half S j)) =
      1-budget S p l u := by
    rw [relativeWidth_half S _ (h 0),relativeWidth_half S _ (h 1)]
    simp only [budget,pairWidth,Fin.sum_univ_two,t]
    ring
  apply CommonMiddleSupportReduction.pair_stack_of_equality (half S j) (compact_half S j)
    (level S j)
    (by simp [level_apply,half,S.Y_ne j]) (by simp [level_apply,half])
    (fun z hz => level_bounds S j hz) p (fun i => h i j)
    (fun i => by rw [relativeWidth_half S _ (h i)]; exact hw i) t ht.le
  · rw [relativeWidth_half S _ (h 0),relativeWidth_half S _ (h 1)]
    simpa only [budget,pairWidth,Fin.sum_univ_two,t,add_comm] using hR
  · rw [hbudget]
    exact heh

end Quant.CrossedQuadrilateralCommonPairReduction

/-- info: 'Quant.CrossedQuadrilateralCommonPairReduction.pair_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCommonPairReduction.pair_stack
