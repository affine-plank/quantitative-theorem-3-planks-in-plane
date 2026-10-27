module
public import Plank.Proofs.Quant.CyclicVertexDescent

@[expose] public section
noncomputable section

namespace Quant.CyclicDescentSymmetry

open CyclicVertexDescent CyclicGapCancellation CyclicSixTermCompensation
  CyclicThresholdCaps CyclicPairAreas CyclicWeightedThresholdGeometry
open Filter
open scoped Topology

def rotate (l : Fin 3 → ℝ) : Fin 3 → ℝ := ![l 1,l 2,l 0]
def unrotate (l : Fin 3 → ℝ) : Fin 3 → ℝ := ![l 2,l 0,l 1]
def jointMargin (a b c : ℝ) (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  margin a b c p.1 p.2

theorem rotate_unrotate (l : Fin 3 → ℝ) : rotate (unrotate l) = l := by
  ext i; fin_cases i <;> rfl

theorem unrotate_rotate (l : Fin 3 → ℝ) : unrotate (rotate l) = l := by
  ext i; fin_cases i <;> rfl

theorem reflectedLevels_involutive (l : Fin 3 → ℝ) :
    reflectedLevels (reflectedLevels l) = l := by
  ext i
  simp only [reflectedLevels,reflectionIndex_involutive]
  ring

theorem margin_rotate (a b c : ℝ) (l h : Fin 3 → ℝ) :
    margin b c a (rotate l) (rotate h) = margin a b c l h := by
  simp only [margin,normalizedExpression,thresholdLoss,Fin.sum_univ_three]
  dsimp [rotate,lowPairSlack,highPairSlack,capSize,lowerCapSize,windowWidth,
    direction,weight,thresholdSlack,k0,k1,k2,SixTriangleResidual.deficit]
  ring_nf

theorem margin_reflect (a b c : ℝ) (l h : Fin 3 → ℝ) :
    margin (1-b) (1-a) (1-c) (reflectedLevels h) (reflectedLevels l) =
      margin a b c l h := by
  simp only [margin,normalizedExpression,thresholdLoss,Fin.sum_univ_three]
  dsimp [reflectedLevels,reflectionIndex,lowPairSlack,highPairSlack,capSize,
    lowerCapSize,windowWidth,direction,weight,thresholdSlack,k0,k1,k2,
    SixTriangleResidual.deficit]
  ring_nf

theorem refundArgument_rotate (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) (j : Fin 4) :
    refundArgument b c a (rotate l) (rotate h) i j =
      refundArgument a b c l h (i+1) j := by
  fin_cases i <;> fin_cases j <;>
    dsimp [refundArgument,rotate,lowPairSlack,highPairSlack,capSize,
      lowerCapSize,windowWidth,direction]

theorem refundArgument_reflect (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) (j : Fin 4) :
    refundArgument (1-b) (1-a) (1-c) (reflectedLevels h) (reflectedLevels l) i j =
      refundArgument a b c l h (pairReflection i) (j+2) := by
  fin_cases i <;> fin_cases j <;>
    dsimp [refundArgument,reflectedLevels,reflectionIndex,pairReflection,
      lowPairSlack,highPairSlack,capSize,lowerCapSize,windowWidth,direction] <;> ring

theorem not_isLocalMin_lower_zero (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hl : a < l 0) (hargs : ∀ i j, refundArgument a b c l h i j < 0) :
    ¬ IsLocalMin (jointMargin a b c) (l,h) := by
  intro hmin
  let v := vertexDirection a b c
  have hzero : shift l v 0 = l := by ext i; simp [shift]
  have hcont : Continuous (fun t : ℝ => (shift l v t,h)) := by
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro i
    dsimp [shift]
    fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, margin a b c l h ≤ margin a b c (shift l v t) h := by
    have hh : IsLocalMin (jointMargin a b c) (shift l v 0,h) := by simpa only [hzero] using hmin
    simpa only [jointMargin,hzero] using hcont.continuousAt.eventually hh
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨t,ht,htr,hlt⟩ := exists_small_descent a b c l h ha hb hc hl hargs r hr
  have hp : t ∈ Metric.ball (0:ℝ) r := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htr
  have hm : -t ∈ Metric.ball (0:ℝ) r := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_neg,abs_of_pos ht] using htr
  rcases hlt with hh | hh
  · exact (not_lt_of_ge (hball hp)) hh
  · exact (not_lt_of_ge (hball hm)) hh

private theorem localMin_pullback {E : Type*} [TopologicalSpace E]
    (f g : E → ℝ) (T : E → E) (p q : E)
    (hT : Continuous T) (hp : T q = p) (he : ∀ x, f (T x) = g x)
    (hmin : IsLocalMin f p) : IsLocalMin g q := by
  rw [← hp] at hmin
  have hh := hT.continuousAt.eventually hmin
  change ∀ᶠ x in 𝓝 q, g q ≤ g x
  simpa only [he] using hh

theorem isLocalMin_rotate (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hmin : IsLocalMin (jointMargin a b c) (l,h)) :
    IsLocalMin (jointMargin b c a) (rotate l,rotate h) := by
  apply localMin_pullback (jointMargin a b c) (jointMargin b c a)
    (fun p => (unrotate p.1,unrotate p.2)) (l,h) (rotate l,rotate h) _ _ _ hmin
  · apply Continuous.prodMk <;> apply continuous_pi <;> intro i <;>
      fin_cases i <;> dsimp [unrotate] <;> fun_prop
  · simp only [unrotate_rotate]
  · intro p
    have he := margin_rotate a b c (unrotate p.1) (unrotate p.2)
    simpa only [jointMargin,rotate_unrotate] using he.symm

theorem lower_le_direction_of_isLocalMin (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hargs : ∀ i j, refundArgument a b c l h i j < 0)
    (hmin : IsLocalMin (jointMargin a b c) (l,h)) :
    ∀ i, l i ≤ direction a b c i := by
  have hr : ∀ i j, refundArgument b c a (rotate l) (rotate h) i j < 0 := by
    intro i j; rw [refundArgument_rotate]; exact hargs (i+1) j
  have hrr : ∀ i j, refundArgument c a b (rotate (rotate l)) (rotate (rotate h)) i j < 0 := by
    intro i j; rw [refundArgument_rotate]; exact hr (i+1) j
  have h0 : l 0 ≤ a := le_of_not_gt fun hh => not_isLocalMin_lower_zero a b c l h ha hb hc hh hargs hmin
  have h1 : l 1 ≤ b := le_of_not_gt fun hh =>
    not_isLocalMin_lower_zero b c a (rotate l) (rotate h) hb hc ha hh hr
      (isLocalMin_rotate a b c l h hmin)
  have h2 : l 2 ≤ c := le_of_not_gt fun hh =>
    not_isLocalMin_lower_zero c a b (rotate (rotate l)) (rotate (rotate h)) hc ha hb hh hrr
      (isLocalMin_rotate b c a _ _ (isLocalMin_rotate a b c l h hmin))
  intro i
  fin_cases i <;> first | exact h0 | exact h1 | exact h2

theorem isLocalMin_reflect (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hmin : IsLocalMin (jointMargin a b c) (l,h)) :
    IsLocalMin (jointMargin (1-b) (1-a) (1-c)) (reflectedLevels h,reflectedLevels l) := by
  apply localMin_pullback (jointMargin a b c) (jointMargin (1-b) (1-a) (1-c))
    (fun p => (reflectedLevels p.2,reflectedLevels p.1))
    (l,h) (reflectedLevels h,reflectedLevels l) _ _ _ hmin
  · apply Continuous.prodMk <;> apply continuous_pi <;> intro i <;>
      dsimp [reflectedLevels] <;> fun_prop
  · simp only [reflectedLevels_involutive]
  · intro p
    have he := margin_reflect a b c (reflectedLevels p.2) (reflectedLevels p.1)
    simpa only [jointMargin,reflectedLevels_involutive] using he.symm

/-- Every local minimum with strictly inactive refund hinges has zero vertex
penalty. This concerns the full scalar margin on the ambient level space. -/
theorem middle_windows_of_isLocalMin (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hargs : ∀ i j, refundArgument a b c l h i j < 0)
    (hmin : IsLocalMin (jointMargin a b c) (l,h)) :
    ∀ i, l i ≤ direction a b c i ∧ direction a b c i ≤ h i := by
  have hlo := lower_le_direction_of_isLocalMin a b c l h ha hb hc hargs hmin
  have ha' : 0 < 1-b ∧ 1-b < 1 := ⟨sub_pos.mpr hb.2,by linarith [hb.1]⟩
  have hb' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  have hc' : 0 < 1-c ∧ 1-c < 1 := ⟨sub_pos.mpr hc.2,by linarith [hc.1]⟩
  have hr : ∀ i j, refundArgument (1-b) (1-a) (1-c)
      (reflectedLevels h) (reflectedLevels l) i j < 0 := by
    intro i j
    rw [refundArgument_reflect]
    exact hargs _ _
  have hhi := lower_le_direction_of_isLocalMin (1-b) (1-a) (1-c)
    (reflectedLevels h) (reflectedLevels l) ha' hb' hc' hr (isLocalMin_reflect a b c l h hmin)
  intro i
  refine ⟨hlo i,?_⟩
  have hh := hhi (reflectionIndex i)
  fin_cases i <;> dsimp [reflectedLevels,reflectionIndex,direction] at hh ⊢ <;> linarith only [hh]


end Quant.CyclicDescentSymmetry
