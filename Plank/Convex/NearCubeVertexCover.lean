/- A boundary window in a whole-set three-coordinate cover costs at least
one in total. The homothetic remainder is covered by two windows, to which
the proved two-plank theorem applies. Quantitative window margins and a
near-cube-vertex bound follow without compactness or facet assumptions. -/
module
public import Plank.Convex.TwoAffineWindows
public import Plank.Convex.AffineBoundaryWindows
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.NearCubeVertexCover
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

private theorem sum_cyclic (v : Fin 3 → ℝ) (i : Fin 3) :
    ∑ j, v j = v i + v (i + 1) + v (i + 2) := by
  rw [Fin.sum_univ_three]
  fin_cases i
  · rfl
  · change v 0 + v 1 + v 2 = v 1 + v 2 + v 0
    ring
  · change v 0 + v 1 + v 2 = v 2 + v 0 + v 1
    ring

private theorem coordinate_cases (i j : Fin 3) : j = i ∨ j = i + 1 ∨ j = i + 2 := by
  fin_cases i <;> fin_cases j <;> decide

/-- If one of the three windows reaches a corresponding cube boundary,
the sum of their widths is at least one. Other windows need only be ordered. -/
theorem sum_ge_one_of_boundary (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (i : Fin 3) (hboundary : lo i = 0 ∨ hi i = 1) :
    1 ≤ ∑ j, (hi j - lo j) := by
  let c : Fin 2 → Fin 3 := ![i + 1, i + 2]
  have hcore : ∀ l h : Fin 2 → ℝ, (∀ j, l j ≤ h j) →
      (∀ x ∈ K, ∃ j, l j ≤ x (c j) ∧ x (c j) ≤ h j) →
      1 ≤ ∑ j, (h j - l j) := by
    intro l h horder hcov
    rw [Fin.sum_univ_two]
    apply TwoAffineWindows.width_bound K hconv (AffineMap.proj (c 0)) (AffineMap.proj (c 1))
      (fun x hx => ⟨hbox x hx (c 0), hbox x hx (c 1)⟩)
      (l 0) (h 0) (l 1) (h 1) (horder 0) (horder 1)
      (hmin (c 0)) (hmax (c 0)) (hmin (c 1)) (hmax (c 1))
    intro x hx
    obtain ⟨j, hj⟩ := hcov x hx
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr hj
  have hcov : ∀ x ∈ K, (lo i ≤ x i ∧ x i ≤ hi i) ∨
      ∃ j : Fin 2, lo (c j) ≤ x (c j) ∧ x (c j) ≤ hi (c j) := by
    intro x hx
    obtain ⟨j, hj⟩ := hcover x hx
    rcases coordinate_cases i j with rfl | rfl | rfl
    · exact Or.inl hj
    · exact Or.inr ⟨0, hj⟩
    · exact Or.inr ⟨1, hj⟩
  have hbound := AffineBoundaryWindows.width_bound K hconv (AffineMap.proj i)
    (fun j => AffineMap.proj (c j)) (fun x hx => hbox x hx i)
    (hmin i) (hmax i) hcore (lo i) (hi i) (hordered i)
    (fun j => lo (c j)) (fun j => hi (c j)) (fun j => hordered (c j)) hcov hboundary
  rw [sum_cyclic _ i]
  simpa only [Fin.sum_univ_two, c, Matrix.cons_val_zero, Matrix.cons_val_one, add_assoc]
    using hbound

private theorem lower_update_cost (lo hi : Fin 3 → ℝ) (i : Fin 3) :
    (∑ j, (hi j - Function.update lo i 0 j)) = (∑ j, (hi j - lo j)) + lo i := by
  classical
  calc
    _ = ∑ j, ((hi j - lo j) + if j = i then lo i else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

private theorem upper_update_cost (lo hi : Fin 3 → ℝ) (i : Fin 3) :
    (∑ j, (Function.update hi i 1 j - lo j)) = (∑ j, (hi j - lo j)) + (1 - hi i) := by
  classical
  calc
    _ = ∑ j, ((hi j - lo j) + if j = i then 1 - hi i else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- Extending any one clamped window to the lower cube face gives a
boundary cover and adds exactly its lower endpoint to the cost. -/
theorem sum_add_lower_ge_one (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j) (hlo : ∀ j, 0 ≤ lo j)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j) (i : Fin 3) :
    1 ≤ (∑ j, (hi j - lo j)) + lo i := by
  have ho (j : Fin 3) : Function.update lo i 0 j ≤ hi j := by
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (hlo i).trans (hordered i)
    · simpa only [Function.update_of_ne hji] using hordered j
  have hc : ∀ p ∈ K, ∃ j, Function.update lo i 0 j ≤ p j ∧ p j ≤ hi j := by
    intro p hp
    obtain ⟨j, hj⟩ := hcover p hp
    refine ⟨j, ?_, hj.2⟩
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (hbox p hp i).1
    · simpa only [Function.update_of_ne hji] using hj.1
  simpa only [lower_update_cost] using sum_ge_one_of_boundary K hconv hbox hmin hmax
    (Function.update lo i 0) hi ho hc i (Or.inl (Function.update_self i 0 lo))

/-- Extending one clamped window to the upper cube face adds its upper gap. -/
theorem sum_add_upper_gap_ge_one (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j) (hhi : ∀ j, hi j ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j) (i : Fin 3) :
    1 ≤ (∑ j, (hi j - lo j)) + (1 - hi i) := by
  have ho (j : Fin 3) : lo j ≤ Function.update hi i 1 j := by
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (hordered i).trans (hhi i)
    · simpa only [Function.update_of_ne hji] using hordered j
  have hc : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ Function.update hi i 1 j := by
    intro p hp
    obtain ⟨j, hj⟩ := hcover p hp
    refine ⟨j, hj.1, ?_⟩
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (hbox p hp i).2
    · simpa only [Function.update_of_ne hji] using hj.2
  simpa only [upper_update_cost] using sum_ge_one_of_boundary K hconv hbox hmin hmax
    lo (Function.update hi i 1) ho hc i (Or.inr (Function.update_self i 1 hi))

/-- A width deficit forces every covering window away from both cube faces. -/
theorem window_margins_of_deficit (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : ∀ j, 0 ≤ lo j) (hhi : ∀ j, hi j ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (γ : ℝ) (hdef : (∑ j, (hi j - lo j)) ≤ 1 - γ) :
    ∀ i, γ ≤ lo i ∧ hi i ≤ 1 - γ := by
  intro i
  have hl := sum_add_lower_ge_one K hconv hbox hmin hmax lo hi hordered hlo hcover i
  have hu := sum_add_upper_gap_ge_one K hconv hbox hmin hmax lo hi hordered hhi hcover i
  constructor <;> linarith only [hl, hu, hdef]

/-- Every covered point has some coordinate inside the uniform margin. -/
theorem covered_middle_of_deficit (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : ∀ j, 0 ≤ lo j) (hhi : ∀ j, hi j ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (γ : ℝ) (hdef : (∑ j, (hi j - lo j)) ≤ 1 - γ) :
    ∀ p ∈ K, ∃ i, γ ≤ p i ∧ p i ≤ 1 - γ := by
  have hm := window_margins_of_deficit K hconv hbox hmin hmax lo hi hordered hlo hhi hcover γ hdef
  intro p hp
  obtain ⟨i, hi⟩ := hcover p hp
  exact ⟨i, (hm i).1.trans hi.1, hi.2.trans (hm i).2⟩

/-- A covered point within `r` of any cube vertex forces total width at
least `1-r`. The corner is specified by real coordinates equal to zero or one. -/
theorem sum_ge_of_near_vertex (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : ∀ j, 0 ≤ lo j) (hhi : ∀ j, hi j ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (v : Point) (hv : ∀ j, v j = 0 ∨ v j = 1)
    (z : Point) (hz : z ∈ K) (r : ℝ) (hnear : ∀ j, |z j - v j| ≤ r) :
    1 - r ≤ ∑ j, (hi j - lo j) := by
  by_contra hbound
  have hdef := lt_of_not_ge hbound
  let S := ∑ j, (hi j - lo j)
  have hγ : r < 1 - S := by dsimp [S]; linarith only [hdef]
  obtain ⟨i, hi⟩ := covered_middle_of_deficit K hconv hbox hmin hmax lo hi hordered
    hlo hhi hcover (1 - S) (by dsimp [S]; linarith) z hz
  have hr := abs_le.mp (hnear i)
  rcases hv i with hv0 | hv1
  · rw [hv0, sub_zero] at hr
    linarith only [hr.2, hi.1, hγ]
  · rw [hv1] at hr
    linarith only [hr.1, hi.2, hγ]

end Plank.Convex.NearCubeVertexCover

/-- info: 'Plank.Convex.NearCubeVertexCover.sum_ge_one_of_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.NearCubeVertexCover.sum_ge_one_of_boundary

/-- info: 'Plank.Convex.NearCubeVertexCover.window_margins_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.NearCubeVertexCover.window_margins_of_deficit

/-- info: 'Plank.Convex.NearCubeVertexCover.covered_middle_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.NearCubeVertexCover.covered_middle_of_deficit

/-- info: 'Plank.Convex.NearCubeVertexCover.sum_ge_of_near_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.NearCubeVertexCover.sum_ge_of_near_vertex
