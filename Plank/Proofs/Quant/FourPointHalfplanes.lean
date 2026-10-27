/- Explicit twenty-row half-plane description of a four-point convex hull. -/
module

public import Plank.Proofs.Quant.ClosedLinearFeasibility
public import Plank.Proofs.Quant.PlanarStatement
public import Mathlib.Analysis.Convex.Combination

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FourPointHalfplanes

open Set PlanarQuantitative
open scoped BigOperators

/-- Three vertices are fixed at the standard triangle. The fourth point
is arbitrary, so triangles, repeated vertices and collinear sides occur. -/
def body (a b : ℝ) : Set Point := convexHull ℝ {![0,0],![1,0],![0,1],![a,b]}

def weightRegion (a b : ℝ) : Set Point :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ a*t ≤ x 0 ∧ b*t ≤ x 1 ∧
    (1-a-b)*t ≤ 1-x 0-x 1}

theorem convex_weightRegion (a b : ℝ) : Convex ℝ (weightRegion a b) := by
  rintro x ⟨t,ht,hxt,hyt,hzt⟩ y ⟨u,hu,hxu,hyu,hzu⟩ α β hα hβ hsum
  refine ⟨α*t+β*u,add_nonneg (mul_nonneg hα ht) (mul_nonneg hβ hu),?_,?_,?_⟩
  · change a*(α*t+β*u) ≤ α*x 0+β*y 0
    calc
      _ = α*(a*t)+β*(a*u) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hxt hα) (mul_le_mul_of_nonneg_left hxu hβ)
  · change b*(α*t+β*u) ≤ α*x 1+β*y 1
    calc
      _ = α*(b*t)+β*(b*u) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hyt hα) (mul_le_mul_of_nonneg_left hyu hβ)
  · change (1-a-b)*(α*t+β*u) ≤ 1-(α*x 0+β*y 0)-(α*x 1+β*y 1)
    calc
      _ = α*((1-a-b)*t)+β*((1-a-b)*u) := by ring
      _ ≤ α*(1-x 0-x 1)+β*(1-y 0-y 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hzt hα) (mul_le_mul_of_nonneg_left hzu hβ)
      _ = (α+β)-(α*x 0+β*y 0)-(α*x 1+β*y 1) := by ring
      _ = _ := by rw [hsum]

/-- One real weight suffices for exact membership, including boundary
points. All other convex weights are explicit affine expressions. -/
theorem body_eq_weightRegion (a b : ℝ) : body a b = weightRegion a b := by
  refine Subset.antisymm (convexHull_min ?_ (convex_weightRegion a b)) ?_
  · intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0,by norm_num,by norm_num,by norm_num,by norm_num⟩
    · exact ⟨0,by norm_num,by norm_num,by norm_num,by norm_num⟩
    · exact ⟨0,by norm_num,by norm_num,by norm_num,by norm_num⟩
    · exact ⟨1,by norm_num,by simp,by simp,by simp⟩
  · rintro x ⟨t,ht,hxt,hyt,hzt⟩
    let w : Fin 4 → ℝ := ![1-x 0-x 1-(1-a-b)*t,x 0-a*t,x 1-b*t,t]
    let v : Fin 4 → Point := ![![0,0],![1,0],![0,1],![a,b]]
    apply mem_convexHull_of_exists_fintype w v
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr hzt
      · exact sub_nonneg.mpr hxt
      · exact sub_nonneg.mpr hyt
      · exact ht
    · simp [w,Fin.sum_univ_four]
      ring
    · intro i
      fin_cases i <;> simp [v]
    · ext i
      fin_cases i <;> simp [w,v,Fin.sum_univ_four] <;> ring

def coefficients (a b : ℝ) : Fin 4 → ℝ := ![-1,a,b,1-a-b]

def offsets : Fin 4 → Point →ᵃ[ℝ] ℝ :=
  ![0,AffineMap.proj 0,AffineMap.proj 1,
    AffineMap.const ℝ Point 1-AffineMap.proj 0-AffineMap.proj 1]

abbrev Row := Fin 4 ⊕ (Fin 4 × Fin 4)

/-- All twenty rows are explicit affine expressions. Inactive rows are
constant tautologies, and no real feasibility variable remains. -/
def halfplanes (a b : ℝ) : Row → Point →ᵃ[ℝ] ℝ :=
  Quant.ClosedLinearFeasibility.eliminate (coefficients a b) offsets

/-- Exact half-plane representation for every value of the fourth
vertex, with no convex-position, distinctness or genericity assumption. -/
theorem mem_body_iff (a b : ℝ) (x : Point) :
    x ∈ body a b ↔ ∀ k : Row, 0 ≤ halfplanes a b k x := by
  rw [body_eq_weightRegion]
  change (∃ t : ℝ, 0 ≤ t ∧ a*t ≤ x 0 ∧ b*t ≤ x 1 ∧ (1-a-b)*t ≤ 1-x 0-x 1) ↔ _
  rw [halfplanes,Quant.ClosedLinearFeasibility.eliminate_iff]
  apply exists_congr
  intro t
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,coefficients,offsets,
    Matrix.cons_val_zero,and_true]
  change (0 ≤ t ∧ a*t ≤ x 0 ∧ b*t ≤ x 1 ∧ (1-a-b)*t ≤ 1-x 0-x 1) ↔
    (-1*t ≤ 0 ∧ a*t ≤ x 0 ∧ b*t ≤ x 1 ∧ (1-a-b)*t ≤ 1-x 0-x 1)
  simp only [neg_one_mul,neg_nonpos]

theorem body_eq_halfplanes (a b : ℝ) :
    body a b = {x | ∀ k : Row, 0 ≤ halfplanes a b k x} :=
  Set.ext (mem_body_iff a b)

end Plank.FourPointHalfplanes

/-- info: 'Plank.FourPointHalfplanes.body_eq_halfplanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.FourPointHalfplanes.body_eq_halfplanes
