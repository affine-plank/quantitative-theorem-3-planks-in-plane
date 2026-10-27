/- The unimodal cap profiles are actual vertical Lebesgue section lengths. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSectionProfile

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSectionGeometry
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralSectionProfile
open Plank.ConvexSections Plank.PlanarConvexSectionLength Plank.PlanarConvexSectionIntegral

theorem mem_body (S : Shape) (x y : ℝ) :
    (x,y) ∈ S.body ↔ -S.d*tent S x ≤ y ∧ y ≤ S.b*tent S x := by
  rw [mem_body_iff_support]
  constructor
  · intro h
    have hff := h false false
    have hft := h false true
    have htf := h true false
    have htt := h true true
    simp only [Shape.X,Shape.Y,Bool.false_eq_true,if_false,if_true,div_neg] at hff hft htf htt
    have hu : y/S.b ≤ tent S x :=
      le_min (by linarith only [hft]) (by linarith only [htt])
    have hl : -y/S.d ≤ tent S x := by
      rw [neg_div]
      exact le_min (by linarith only [hff]) (by linarith only [htf])
    have hlow := (div_le_iff₀ S.hd).mp hl
    have hhigh := (div_le_iff₀ S.hb).mp hu
    constructor <;> nlinarith only [hlow,hhigh]
  · rintro ⟨hl,hu⟩ i j
    have hyu : y/S.b ≤ tent S x := (div_le_iff₀ S.hb).mpr (by nlinarith only [hu])
    have hyl : -(y/S.d) ≤ tent S x := by
      rw [← neg_div]
      apply (div_le_iff₀ S.hd).mpr
      nlinarith only [hl]
    have hleft := min_le_left (1+x/S.c) (1-x/S.a)
    have hright := min_le_right (1+x/S.c) (1-x/S.a)
    change _ ≤ _ at hyu hyl
    unfold tent at hyu hyl
    cases i <;> cases j <;>
      simp only [Shape.X,Shape.Y,Bool.false_eq_true,if_false,if_true,div_neg] <;>
      linarith only [hyu,hyl,hleft,hright]

/-- Closed caps are convenient for Fubini; their boundary lines have zero area. -/
def above (S : Shape) (k hi : ℝ) : Set Point := S.body ∩ {z | hi ≤ k*z.1+z.2}
def below (S : Shape) (k lo : ℝ) : Set Point := S.body ∩ {z | k*z.1+z.2 ≤ lo}

theorem compact_above (S : Shape) (k hi : ℝ) : IsCompact (above S k hi) :=
  (compact_body S).inter_right (isClosed_le continuous_const (by fun_prop))

theorem compact_below (S : Shape) (k lo : ℝ) : IsCompact (below S k lo) :=
  (compact_body S).inter_right (isClosed_le (by fun_prop) continuous_const)

theorem fiber_above (S : Shape) (k hi x : ℝ) :
    fiber (above S k hi) x = Icc (max (-S.d*tent S x) (hi-k*x)) (S.b*tent S x) := by
  ext y
  change ((x,y) ∈ S.body ∧ hi ≤ k*x+y) ↔ _
  rw [mem_body]
  simp only [mem_Icc,max_le_iff]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor
  · exact ⟨h₁.1,by linarith only [h₂]⟩
  · exact h₁.2
  · exact ⟨h₁.1,h₂⟩
  · linarith only [h₁.2]

theorem fiber_below (S : Shape) (k lo x : ℝ) :
    fiber (below S k lo) x = Icc (-S.d*tent S x) (min (S.b*tent S x) (lo-k*x)) := by
  ext y
  change ((x,y) ∈ S.body ∧ k*x+y ≤ lo) ↔ _
  rw [mem_body]
  simp only [mem_Icc,le_min_iff]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor
  · exact h₁.1
  · exact ⟨h₁.2,by linarith only [h₂]⟩
  · exact ⟨h₁,h₂.1⟩
  · linarith only [h₂.2]

theorem length_above (S : Shape) (k hi x : ℝ) :
    length (above S k hi) x = capProfile S S.b k (-hi) x := by
  rw [length,fiber_above]
  change volume.real (Icc _ _) = _
  rw [Real.volume_real_Icc,max_comm]
  unfold capProfile
  congr 1
  rw [← min_sub_sub_left]
  congr 1 <;> ring

theorem length_below (S : Shape) (k lo x : ℝ) :
    length (below S k lo) x = capProfile S S.d (-k) lo x := by
  rw [length,fiber_below]
  change volume.real (Icc _ _) = _
  rw [Real.volume_real_Icc,max_comm]
  unfold capProfile
  congr 1
  rw [← min_sub_sub_right]
  congr 1 <;> ring

theorem residual_eq_lengths (S : Shape) (k lo hi x : ℝ) :
    residual S k lo hi x = length (above S k hi) x+length (below S k lo) x := by
  rw [length_above,length_below]
  rfl

def closedResidual (S : Shape) (k lo hi : ℝ) : Set Point :=
  above S k hi ∪ below S k lo

theorem compact_closedResidual (S : Shape) (k lo hi : ℝ) :
    IsCompact (closedResidual S k lo hi) :=
  (compact_above S k hi).union (compact_below S k lo)

theorem length_closedResidual (S : Shape) (k : ℝ) {lo hi : ℝ} (ho : lo < hi) (x : ℝ) :
    length (closedResidual S k lo hi) x = residual S k lo hi x := by
  have hs : fiber (closedResidual S k lo hi) x =
      fiber (above S k hi) x ∪ fiber (below S k lo) x := rfl
  have hd : Disjoint (fiber (above S k hi) x) (fiber (below S k lo) x) := by
    apply Set.disjoint_left.mpr
    intro y hy hz
    change (x,y) ∈ above S k hi at hy
    change (x,y) ∈ below S k lo at hz
    exact (not_le.mpr ho) (hy.2.trans hz.2)
  rw [residual_eq_lengths,length,hs,measure_union hd
    (compact_fiber (compact_below S k lo) x).measurableSet,
    ENNReal.toReal_add (compact_fiber (compact_above S k hi) x).measure_ne_top
      (compact_fiber (compact_below S k lo) x).measure_ne_top]
  rfl

def oblique (k lo hi : ℝ) : Set Point := {z | lo ≤ k*z.1+z.2 ∧ k*z.1+z.2 ≤ hi}

/-- Closing the two caps changes every remaining gap only on the two
boundary lines of the oblique plank. The additional removed set is arbitrary. -/
theorem gap_eq_closedResidual (S : Shape) (k lo hi : ℝ) (B : Set Point) :
    volume (S.body \ (B ∪ oblique k lo hi)) =
      volume (closedResidual S k lo hi \ B) := by
  have hn (t : ℝ) : volume {z : Point | k*z.1+z.2 = t} = 0 := by
    simpa [dot] using volume_line (by simp : ((k,1) : Point) ≠ 0) t
  apply measure_congr
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (hn lo),
    (measure_eq_zero_iff_ae_notMem).mp (hn hi)] with z hzlo hzhi
  apply propext
  change (z ∈ S.body ∧ ¬ (z ∈ B ∨ (lo ≤ k*z.1+z.2 ∧ k*z.1+z.2 ≤ hi))) ↔
    (((z ∈ S.body ∧ hi ≤ k*z.1+z.2) ∨ (z ∈ S.body ∧ k*z.1+z.2 ≤ lo)) ∧ z ∉ B)
  have hlo : (lo ≤ k*z.1+z.2) ↔ ¬ (k*z.1+z.2 ≤ lo) := by
    exact ⟨fun h₁ h₂ => hzlo (le_antisymm h₂ h₁),fun h => (lt_of_not_ge h).le⟩
  have hhi : (k*z.1+z.2 ≤ hi) ↔ ¬ (hi ≤ k*z.1+z.2) := by
    exact ⟨fun h₁ h₂ => hzhi (le_antisymm h₁ h₂),fun h => (lt_of_not_ge h).le⟩
  rw [hlo,hhi]
  tauto

end Quant.CrossedQuadrilateralSectionGeometry

/-- info: 'Quant.CrossedQuadrilateralSectionGeometry.residual_eq_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSectionGeometry.residual_eq_lengths
