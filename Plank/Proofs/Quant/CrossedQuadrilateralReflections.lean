/- Exact reflection transport of physical bands, widths and equality. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralAdjacentExclusion

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralReflections
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralAffine
open CrossedQuadrilateralSectionGeometry CrossedQuadrilateralPairBudget UnimodalPlanarMerge
open Plank.Convex.DeficientHeightTilt

def flipX : Point ≃ᵃ[ℝ] Point :=
  ((LinearEquiv.neg ℝ : ℝ ≃ₗ[ℝ] ℝ).prodCongr (LinearEquiv.refl ℝ ℝ)).toAffineEquiv

def antipode : Point ≃ᵃ[ℝ] Point := (LinearEquiv.neg ℝ : Point ≃ₗ[ℝ] Point).toAffineEquiv

@[simp] theorem flipX_apply (z : Point) : flipX z = (-z.1,z.2) := rfl
@[simp] theorem antipode_apply (z : Point) : antipode z = (-z.1,-z.2) := rfl
@[simp] theorem flipX_symm : flipX.symm = flipX := rfl
@[simp] theorem antipode_symm : antipode.symm = antipode := rfl

def flippedX (S : Shape) : Shape := ⟨S.c,S.b,S.a,S.d,S.hc,S.hb,S.ha,S.hd⟩
def opposite (S : Shape) : Shape := ⟨S.c,S.d,S.a,S.b,S.hc,S.hd,S.ha,S.hb⟩

theorem image_mem (T : Point ≃ᵃ[ℝ] Point) (A : Set Point) (z : Point) :
    z ∈ T '' A ↔ T.symm z ∈ A := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa only [T.symm_apply_apply] using hx
  · intro hz
    exact ⟨T.symm z,hz,T.apply_symm_apply z⟩

theorem body_flipX (S : Shape) : (flippedX S).body = flipX '' S.body := by
  rw [image_body S flipX]
  unfold Shape.body
  congr 1
  ext z
  simp [Shape.vertices,flippedX,or_left_comm]

theorem body_antipode (S : Shape) : (opposite S).body = antipode '' S.body := by
  rw [image_body S antipode]
  unfold Shape.body
  congr 1
  ext z
  simp [Shape.vertices,opposite,or_comm,or_left_comm,or_assoc]

theorem band_flipX (l u : ℝ) : flipX '' band l u = band (-u) (-l) := by
  ext z
  rw [image_mem]
  change (l ≤ -z.1 ∧ -z.1 ≤ u) ↔ (-u ≤ z.1 ∧ z.1 ≤ -l)
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]

theorem band_antipode (l u : ℝ) : antipode '' band l u = band (-u) (-l) := by
  ext z
  rw [image_mem]
  change (l ≤ -z.1 ∧ -z.1 ≤ u) ↔ (-u ≤ z.1 ∧ z.1 ≤ -l)
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]

theorem oblique_flipX (k lo hi : ℝ) : flipX '' oblique k lo hi = oblique (-k) lo hi := by
  ext z
  rw [image_mem]
  change (lo ≤ k*(-z.1)+z.2 ∧ k*(-z.1)+z.2 ≤ hi) ↔
    (lo ≤ (-k)*z.1+z.2 ∧ (-k)*z.1+z.2 ≤ hi)
  simp only [mul_neg,neg_mul]

theorem oblique_antipode (k lo hi : ℝ) :
    antipode '' oblique k lo hi = oblique k (-hi) (-lo) := by
  ext z
  rw [image_mem]
  change (lo ≤ k*(-z.1)+(-z.2) ∧ k*(-z.1)+(-z.2) ≤ hi) ↔
    (-hi ≤ k*z.1+z.2 ∧ k*z.1+z.2 ≤ -lo)
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith only [h₁,h₂]

theorem range_flipX (S : Shape) (k : ℝ) :
    rangeWidth (flippedX S).body (direction (-k,1)) = rangeWidth S.body (direction (k,1)) := by
  have he : pull flipX (direction (k,1)) = direction (-k,1) := by
    ext z
    change k*(-z.1)+1*z.2 = (-k)*z.1+1*z.2
    ring
  rw [body_flipX,← he,width_pull]

theorem range_antipode (S : Shape) (k : ℝ) :
    rangeWidth (opposite S).body (direction (k,1)) = rangeWidth S.body (direction (k,1)) := by
  have he : pull antipode (-(direction (k,1))) = direction (k,1) := by
    ext z
    change -(k*(-z.1)+1*(-z.2)) = k*z.1+1*z.2
    ring
  rw [body_antipode]
  conv_lhs => rw [← he,width_pull]
  exact Plank.Body.width_neg (compact_body S) ⟨0,zero_mem S⟩
    (direction (k,1)).continuous_of_finiteDimensional

theorem budget_flipX (S : Shape) (k a b c d lo hi : ℝ) :
    budget (flippedX S) (-k) (-b) (-a) (-d) (-c) lo hi = budget S k a b c d lo hi := by
  unfold budget
  rw [range_flipX]
  simp only [flippedX]
  ring

theorem budget_antipode (S : Shape) (k a b c d lo hi : ℝ) :
    budget (opposite S) k (-b) (-a) (-d) (-c) (-hi) (-lo) = budget S k a b c d lo hi := by
  unfold budget
  rw [range_antipode]
  simp only [opposite]
  ring

theorem equality_flipX (S : Shape) (k a b c d lo hi q : ℝ) :
    gap (flippedX S) (-k) (-b) (-a) (-d) (-c) lo hi = q*(volume (flippedX S).body).toReal ↔
      gap S k a b c d lo hi = q*(volume S.body).toReal := by
  have he : (band (-b) (-a) ∪ band (-d) (-c)) ∪ oblique (-k) lo hi =
      flipX '' ((band a b ∪ band c d) ∪ oblique k lo hi) := by
    rw [image_union,image_union,band_flipX,band_flipX,oblique_flipX]
  unfold gap
  rw [body_flipX,he]
  exact image_equality_iff flipX S.body _ q

theorem equality_antipode (S : Shape) (k a b c d lo hi q : ℝ) :
    gap (opposite S) k (-b) (-a) (-d) (-c) (-hi) (-lo) = q*(volume (opposite S).body).toReal ↔
      gap S k a b c d lo hi = q*(volume S.body).toReal := by
  have he : (band (-b) (-a) ∪ band (-d) (-c)) ∪ oblique k (-hi) (-lo) =
      antipode '' ((band a b ∪ band c d) ∪ oblique k lo hi) := by
    rw [image_union,image_union,band_antipode,band_antipode,oblique_antipode]
  unfold gap
  rw [body_antipode,he]
  exact image_equality_iff antipode S.body _ q

end Quant.CrossedQuadrilateralReflections

/-- info: 'Quant.CrossedQuadrilateralReflections.equality_antipode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralReflections.equality_antipode
