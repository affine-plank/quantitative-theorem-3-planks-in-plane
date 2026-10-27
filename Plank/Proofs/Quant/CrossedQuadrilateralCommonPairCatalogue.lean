/- Complete geometric catalogue for a common-support pair and a transverse band. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonPairRigidity

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCommonPairCatalogue
open Set MeasureTheory
open CrossedQuadrilateralAttainment CrossedQuadrilateralDiagonalSplit
open CrossedQuadrilateralPlacement
open CrossedQuadrilateralCommonSupport CrossedQuadrilateralCommonPairSplit
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def left (p : Plank) : ℝ := p.lo/p.u.1
def right (p : Plank) : ℝ := p.hi/p.u.1

theorem x_positive (S : Shape) (p : Plank) (h : CommonSupports S p) : 0 < p.u.1 := by
  have hs := CommonMiddleAffineTransport.span_pos (half S true) p (h true)
  have hh : 0 < p.u.1*(S.a+S.c) := by
    simpa only [CommonMiddleAffineTransport.span,half,dot,mul_zero,add_zero,mul_neg,
      sub_neg_eq_add,← mul_add] using hs
  exact (mul_pos_iff_of_pos_right (add_pos S.ha S.hc)).mp hh

theorem x_width (S : Shape) (p : Plank) (h : CommonSupports S p) :
    relativeWidth S p = (right p-left p)/(S.a+S.c) := by
  have hx := (x_positive S p h).ne'
  simp only [relativeWidth,range_body S p h,CommonMiddleAffineTransport.span,half,dot,
    mul_zero,add_zero,left,right]
  field_simp [hx,(add_pos S.ha S.hc).ne']
  ring

theorem x_order (S : Shape) (p : Plank) (h : CommonSupports S p)
    (hw : 0 < relativeWidth S p) : left p < right p := by
  rw [x_width S p h] at hw
  exact sub_pos.mp ((div_pos_iff_of_pos_right (add_pos S.ha S.hc)).mp hw)

theorem x_set (S : Shape) (p : Plank) (h : CommonSupports S p) (hy : p.u.2 = 0) :
    p.set = band false (left p) (right p) := by
  ext z
  change (p.lo ≤ p.u.1*z.1+p.u.2*z.2 ∧ p.u.1*z.1+p.u.2*z.2 ≤ p.hi) ↔
    (p.lo/p.u.1 ≤ z.1 ∧ z.1 ≤ p.hi/p.u.1)
  simp only [hy,mul_zero,add_zero,div_le_iff₀ (x_positive S p h),
    le_div_iff₀ (x_positive S p h),mul_comm]

def Adjacent (S : Shape) (p : Fin 2 → Plank) : Prop :=
  (right (p 0) = left (p 1) ∧ right (p 1)/S.a = -left (p 0)/S.c) ∨
  (right (p 1) = left (p 0) ∧ right (p 0)/S.a = -left (p 1)/S.c)

def Catalogue (S : Shape) (p : Fin 2 → Plank) (l u : ℝ) : Prop :=
  (∀ i, (p i).u.2 = 0) ∧ Adjacent S p ∧ u/S.b = -l/S.d

theorem transverse_set (l u : ℝ) (ho : l ≤ u) : (transverse l u ho).set = band true l u := by
  ext z
  change (l ≤ 0*z.1+1*z.2 ∧ 0*z.1+1*z.2 ≤ u) ↔ (l ≤ z.2 ∧ z.2 ≤ u)
  simp only [zero_mul,one_mul,zero_add]

theorem axis_union (S : Shape) (p : Fin 2 → Plank) (h : ∀ i, CommonSupports S (p i))
    (hy : ∀ i, (p i).u.2 = 0) (l u : ℝ) (ho : l ≤ u) :
    (⋃ i, (family p l u ho i).set) =
      band false (left (p 0)) (right (p 0)) ∪ band false (left (p 1)) (right (p 1)) ∪
        band true l u := by
  rw [union_three]
  change (p 0).set ∪ ((p 1).set ∪ (transverse l u ho).set) = _
  rw [transverse_set,x_set S _ (h 0) (hy 0),x_set S _ (h 1) (hy 1),Set.union_assoc]

theorem axis_budget (S : Shape) (p : Fin 2 → Plank) (h : ∀ i, CommonSupports S (p i))
    (l u : ℝ) : budget S p l u =
      (right (p 0)-left (p 0))/(S.a+S.c)+(right (p 1)-left (p 1))/(S.a+S.c)+
        (u-l)/(S.b+S.d) := by
  simp only [budget,pairWidth,Fin.sum_univ_two,x_width S _ (h _)]

theorem diagonal_equality_iff (S : Shape) (p : Fin 2 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (hw : ∀ i, 0 < relativeWidth S (p i))
    (hy : ∀ i, (p i).u.2 = 0) (l u : ℝ) (ho : l < u) (hR : budget S p l u < 1) :
    (volume (S.body \ ⋃ i, (family p l u ho.le i).set)).toReal =
      (1-budget S p l u)^2*(volume S.body).toReal ↔ Adjacent S p ∧ u/S.b = -l/S.d := by
  have h0 := x_order S (p 0) (h 0) (hw 0)
  have h1 := x_order S (p 1) (h 1) (hw 1)
  rw [axis_union S p h hy,axis_budget S p h] at ⊢
  rw [axis_budget S p h] at hR
  rcases le_total (left (p 0)) (left (p 1)) with hl | hl
  · rw [CrossedQuadrilateralTwoDirections.equality_iff_adjacent S _ _ _ _ l u h0 h1 hl ho.le hR]
    change (_ ∧ _ ∧ (u=l ∨ u/S.b = -l/S.d)) ↔ _
    constructor
    · rintro ⟨ha,hc,ht⟩
      exact ⟨Or.inl ⟨ha,hc⟩,ht.resolve_left ho.ne'⟩
    · rintro ⟨ha,ht⟩
      rcases ha with ⟨ha,hc⟩ | ⟨ha,hc⟩
      · exact ⟨ha,hc,Or.inr ht⟩
      · exfalso
        linarith only [ha,hl,h1]
  · have hR' : (right (p 1)-left (p 1))/(S.a+S.c)+(right (p 0)-left (p 0))/(S.a+S.c)+
        (u-l)/(S.b+S.d) < 1 := by simpa only [add_comm] using hR
    rw [Set.union_comm (band false (left (p 0)) (right (p 0))),
      add_comm ((right (p 0)-left (p 0))/(S.a+S.c))]
    rw [CrossedQuadrilateralTwoDirections.equality_iff_adjacent S _ _ _ _ l u h1 h0 hl ho.le hR']
    constructor
    · rintro ⟨ha,hc,ht⟩
      exact ⟨Or.inr ⟨ha,hc⟩,ht.resolve_left ho.ne'⟩
    · rintro ⟨ha,ht⟩
      rcases ha with ⟨ha,hc⟩ | ⟨ha,hc⟩
      · exfalso
        linarith only [ha,hl,h0]
      · exact ⟨ha,hc,Or.inr ht⟩

/-- Complete iff in the explicit common-pair support sector. Initial
parallelism, clipping, overlap and calibration are all unrestricted. -/
theorem equality_iff_catalogue (S : Shape) (p : Fin 2 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (hw : ∀ i, 0 < relativeWidth S (p i))
    (l u : ℝ) (ho : l < u) (hR : budget S p l u < 1) :
    (volume (S.body \ ⋃ i, (family p l u ho.le i).set)).toReal =
      (1-∑ i, relativeWidth S (family p l u ho.le i))^2*(volume S.body).toReal ↔
        Catalogue S p l u := by
  rw [family_budget]
  constructor
  · intro he
    have hy := CrossedQuadrilateralCommonPairRigidity.parallel_of_equality S p h hw l u ho hR he
    exact ⟨hy,(diagonal_equality_iff S p h hw hy l u ho hR).mp he⟩
  · rintro ⟨hy,ha⟩
    exact (diagonal_equality_iff S p h hw hy l u ho hR).mpr ha

end Quant.CrossedQuadrilateralCommonPairCatalogue

/-- info: 'Quant.CrossedQuadrilateralCommonPairCatalogue.equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCommonPairCatalogue.equality_iff_catalogue
