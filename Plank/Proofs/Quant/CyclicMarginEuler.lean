module
/- The exact Euler identity for the cyclic scalar margin at a local minimum. -/
public import Plank.Proofs.Quant.PositivePartEuler
public import Plank.Proofs.Quant.CyclicDescentSymmetry

@[expose] public section
noncomputable section

namespace Quant.CyclicMarginEuler

open Filter CyclicGapCancellation CyclicVertexDescent CyclicThresholdCaps
  CyclicWeightedThresholdGeometry CyclicPairAreas
open scoped Topology

/-- The two raw cuts, four refunds, two vertex penalties, and two losses. -/
def argument (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : Fin 10 → ℝ :=
  ![lowPairSlack a b c l i,highPairSlack a b c h i,
    refundArgument a b c l h i 0,refundArgument a b c l h i 1,
    refundArgument a b c l h i 2,refundArgument a b c l h i 3,
    l i-direction a b c i,direction a b c i-h i,
    weight a b c i*windowWidth l h i-thresholdSlack a b c l,
    weight a b c i*windowWidth l h i+thresholdSlack a b c h]

def coefficient (a b c : ℝ) (i : Fin 3) : Fin 10 → ℝ :=
  let low := (direction a b c (i+1)*weight a b c (i+2))⁻¹
  let high := ((1-direction a b c i)*weight a b c (i+2))⁻¹
  let vertex := -(direction a b c i*(1-direction a b c i))⁻¹
  let loss := -(k0 b c*k1 a c*k2 a b)⁻¹
  ![low,high,low,low,high,high,vertex,vertex,loss,loss]

def radial (l L : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  fun i => l i+t*(l i-L i)

theorem radial_zero (l L : Fin 3 → ℝ) : radial l L 0 = l := by
  funext i
  simp [radial]

def anchorTerms (a b c : ℝ) (l h L H : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ s, coefficient a b c i s*argument a b c L H i s*
    max 0 (argument a b c l h i s)

theorem normalizedExpression_eq_sum (a b c : ℝ) (l h : Fin 3 → ℝ) :
    normalizedExpression a b c l h =
      ∑ i, ∑ s, coefficient a b c i s*squarePos (argument a b c l h i s) := by
  simp only [normalizedExpression,thresholdLoss,Finset.sum_div,
    ← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num [argument,coefficient,Fin.sum_univ_succ,refundArgument,
    Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem argument_radial (a b c : ℝ) (l h L H : Fin 3 → ℝ)
    (t : ℝ) (i : Fin 3) (s : Fin 10) :
    argument a b c (radial l L t) (radial h H t) i s =
      argument a b c l h i s+t*(argument a b c l h i s-argument a b c L H i s) := by
  fin_cases s <;> dsimp [argument,radial,refundArgument,windowWidth,
    lowPairSlack,highPairSlack,capSize,lowerCapSize,thresholdSlack] <;> ring

theorem deficit_radial (l h L H : Fin 3 → ℝ) (t : ℝ) :
    SixTriangleResidual.deficit (radial l L t) (radial h H t) =
      SixTriangleResidual.deficit l h+
        t*(SixTriangleResidual.deficit l h-SixTriangleResidual.deficit L H) := by
  dsimp [SixTriangleResidual.deficit,radial]
  ring

theorem localMin_anchor_identity (a b c : ℝ) (l h L H : Fin 3 → ℝ)
    (hmin : IsLocalMin (CyclicDescentSymmetry.jointMargin a b c) (l,h)) :
    margin a b c l h = anchorTerms a b c l h L H-
      SixTriangleResidual.deficit l h*SixTriangleResidual.deficit L H := by
  have ht : Tendsto (fun t : ℝ => (radial l L t,radial h H t)) (𝓝 0) (𝓝 (l,h)) := by
    have hcont : Continuous (fun t : ℝ => (radial l L t,radial h H t)) := by
      change Continuous (fun t : ℝ =>
        ((fun i => l i+t*(l i-L i)),fun i => h i+t*(h i-H i)))
      fun_prop
    have hh : Tendsto (fun t : ℝ => (radial l L t,radial h H t))
        (𝓝 0) (𝓝 (radial l L 0,radial h H 0)) := hcont.continuousAt
    simpa only [radial_zero] using hh
  have hnear := ht.eventually hmin
  have hid (t : ℝ) : margin a b c (radial l L t) (radial h H t) =
      (∑ v : Fin 3 × Fin 10, coefficient a b c v.1 v.2*
        squarePos (argument a b c l h v.1 v.2+
          t*(argument a b c l h v.1 v.2-argument a b c L H v.1 v.2)))-
        (SixTriangleResidual.deficit l h+
          t*(SixTriangleResidual.deficit l h-SixTriangleResidual.deficit L H))^2 := by
    simp only [margin,normalizedExpression_eq_sum,argument_radial,deficit_radial,
      Fintype.sum_prod_type]
  have hm : IsLocalMin (fun t : ℝ =>
      (∑ v : Fin 3 × Fin 10, coefficient a b c v.1 v.2*
        squarePos (argument a b c l h v.1 v.2+
          t*(argument a b c l h v.1 v.2-argument a b c L H v.1 v.2)))-
        (SixTriangleResidual.deficit l h+
          t*(SixTriangleResidual.deficit l h-SixTriangleResidual.deficit L H))^2) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, _ ≤ _
    filter_upwards [hnear] with t hh
    change margin a b c l h ≤ margin a b c (radial l L t) (radial h H t) at hh
    rw [← hid t,← hid 0]
    simpa only [radial_zero] using hh
  have he := PositivePartEuler.anchor_identity
    (fun v : Fin 3 × Fin 10 => coefficient a b c v.1 v.2)
    (fun v => argument a b c l h v.1 v.2)
    (fun v => argument a b c L H v.1 v.2)
    (SixTriangleResidual.deficit l h) (SixTriangleResidual.deficit L H) hm
  simpa only [margin,normalizedExpression_eq_sum,anchorTerms,Fintype.sum_prod_type] using he

end Quant.CyclicMarginEuler
