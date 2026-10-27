/- Objective coefficients and forced contacts at the original strict minimum. -/
module
public import Plank.Convex.LocalMinimumConstraints
public import Plank.Convex.SameSignCapMinimum
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace Plank.Convex.SameSignLocalMinimum
open SameSignCapMinimum

abbrev Index := Bool × Fin 3

/-- The numerator of the objective multiplier for a row; it uses only the other two slopes. -/
def numerator (r : Index → ℝ) (j : Index) : ℝ :=
  1 - r (succ (succ j)) + r (succ (succ j)) * r (succ j)

def rows (r : Index → ℝ) : Index → Walls →L[ℝ] ℝ :=
  row (fun i => r (true, i)) (fun i => r (false, i))

def motion (r : Index → ℝ) (j : Index) : Walls :=
  if j.1 then SameSignCapMinimum.motion (fun i => r (true, i)) (fun i => r (false, i)) j
  else -SameSignCapMinimum.motion (fun i => r (true, i)) (fun i => r (false, i)) j

theorem rows_apply (r : Index → ℝ) (j : Index) (B : Walls) :
    rows r j B = wall B j + r j * wall B (succ j) := row_eq r j B

theorem row_motion_other (r : Index → ℝ) (j k : Index) (hne : k ≠ j) :
    rows r k (motion r j) = 0 := by
  dsimp [motion, rows]
  split
  · exact SameSignCapMinimum.row_motion_other _ _ j k hne
  · rw [map_neg, SameSignCapMinimum.row_motion_other _ _ j k hne, neg_zero]

theorem row_motion_self (r : Index → ℝ) (j : Index) :
    rows r j (motion r j) = 1 + ∏ i : Fin 3, r (j.1, i) := by
  rcases j with ⟨s, i⟩
  cases s <;> fin_cases i <;>
    simp [rows, motion, SameSignCapMinimum.motion, direction, next, Fin.prod_univ_three] <;> ring

theorem motion_width (r : Index → ℝ) (j : Index) : width (motion r j) = numerator r j := by
  rcases j with ⟨s, i⟩
  cases s <;> fin_cases i <;>
    simp [motion, SameSignCapMinimum.motion, direction, numerator, succ, next,
      width_apply, Fin.sum_univ_three] <;> ring

theorem numerator_balance (r : Index → ℝ) (j : Index) :
    numerator r j + r (succ (succ j)) * numerator r (succ (succ j)) =
      1 + ∏ i : Fin 3, r (j.1, i) := by
  rcases j with ⟨s, i⟩
  fin_cases i <;> simp [numerator, succ, next, Fin.prod_univ_three] <;> ring

/-- At most one multiplier in either three-row cycle can vanish. -/
theorem eq_of_numerators_zero (r : Index → ℝ) (hr : ∀ j, 0 < r j)
    (s : Bool) (i j : Fin 3) (hi : numerator r (s, i) = 0)
    (hj : numerator r (s, j) = 0) : i = j := by
  have hD : 0 < 1 + ∏ k : Fin 3, r (s, k) :=
    add_pos zero_lt_one (Finset.prod_pos fun k _ => hr (s, k))
  by_contra hne
  have hc : i = next (next j) ∨ j = next (next i) := by
    fin_cases i <;> fin_cases j <;> first | exact False.elim (hne rfl) | decide
  rcases hc with hc | hc
  · have h := numerator_balance r (s, j)
    change numerator r (s, j) + r (s, next (next j)) * numerator r (s, next (next j)) = _ at h
    rw [← hc, hi, hj, mul_zero, zero_add] at h
    exact hD.ne' h.symm
  · have h := numerator_balance r (s, i)
    change numerator r (s, i) + r (s, next (next i)) * numerator r (s, next (next i)) = _ at h
    rw [← hc, hi, hj, mul_zero, zero_add] at h
    exact hD.ne' h.symm

/-- Every objective multiplier is nonnegative at the original strict minimum. -/
theorem numerator_nonneg_of_minimum (K : Set Point) (B : Walls)
    (hmin : IsMinOn width (wallSet K) B) (hstrict : B ∈ strictWalls)
    (r : Index → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, rows r j (x, x) ≤ rows r j B) :
    ∀ j, 0 ≤ numerator r j := by
  intro j
  have h := LocalMinimumConstraints.objective_nonneg (wallSet K) strictWalls B width
    hmin open_strictWalls hstrict (rows r) (fun k => rows r k B) (fun _ => le_rfl)
    (row_constraints_suffice K (fun i => r (true, i)) (fun i => r (false, i))
      (fun i => hr (true, i)) (fun i => hr (false, i)) (fun k => rows r k B) hs)
    (motion r j) (fun k => by
      by_cases hk : k = j
      · subst k
        rw [row_motion_self]
        exact (add_pos zero_lt_one (Finset.prod_pos fun i _ => hr (j.1, i))).le
      · rw [row_motion_other r j k hk])
  simpa only [motion_width] using h

/-- A missing corner has zero objective multiplier, even at a minimum that is not extreme. -/
theorem numerator_eq_zero_of_missing_corner (K : Set Point) (hcK : IsCompact K)
    (hK : Convex ℝ K) (B : Walls) (hmin : IsMinOn width (wallSet K) B)
    (hstrict : B ∈ strictWalls)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (r : Index → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, rows r j (x, x) ≤ rows r j B)
    (j : Index)
    (hmissing : ¬ ∃ x ∈ K, cut j x = wall B j ∧ cut (succ j) x = wall B (succ j)) :
    numerator r j = 0 := by
  classical
  have hB : B ∈ wallSet K := row_constraints_suffice K
    (fun i => r (true, i)) (fun i => r (false, i))
    (fun i => hr (true, i)) (fun i => hr (false, i)) (fun k => rows r k B) hs
    B hstrict (fun _ => le_rfl)
  obtain ⟨rj, hrj, cj, hlt, hsj⟩ := CompactPairSeparation.strict_support_of_no_corner
    K hcK hK (cut j) (cut (succ j)) (cut_continuous j) (cut_continuous (succ j))
    (wall B j) (wall B (succ j)) (cut_witness K B hstrict hL hU j)
    (cut_witness K B hstrict hL hU (succ j)) (cap_empty K B hB j) hmissing
  let r' := Function.update r j rj
  let c (k : Index) := if k = j then cj else rows r k B
  have hr' (k : Index) : 0 < r' k := by
    by_cases hk : k = j
    · subst k
      simpa [r'] using hrj
    · simpa [r', hk] using hr k
  have hcur (k : Index) : c k ≤ rows r' k B := by
    by_cases hk : k = j
    · subst k
      simpa [c, r', rows_apply] using hlt.le
    · simp [c, r', rows_apply, hk]
  have hs' (x : Point) (hx : x ∈ K) (k : Index) : rows r' k (x, x) ≤ c k := by
    by_cases hk : k = j
    · subst k
      simpa [c, r', rows_apply, wall_diagonal] using hsj x hx
    · simpa [c, r', rows_apply, hk] using hs x hx k
  have hzero := LocalMinimumConstraints.objective_eq_zero (wallSet K) strictWalls B width
    hmin open_strictWalls hstrict (rows r') c hcur
    (row_constraints_suffice K (fun i => r' (true, i)) (fun i => r' (false, i))
      (fun i => hr' (true, i)) (fun i => hr' (false, i)) c hs')
    (motion r j) (fun k hk => by
      have hkj : k ≠ j := by
        intro he
        subst k
        have he : cj = wall B j + rj * wall B (succ j) := by
          simpa [c, r', rows_apply] using hk
        exact hlt.ne he
      simpa [rows_apply, r', hkj] using row_motion_other r j k hkj)
  simpa only [motion_width] using hzero

/-- Positive objective multipliers force the corresponding actual pair contacts. -/
theorem contact_of_numerator_pos (K : Set Point) (hcK : IsCompact K)
    (hK : Convex ℝ K) (B : Walls) (hmin : IsMinOn width (wallSet K) B)
    (hstrict : B ∈ strictWalls)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (r : Index → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, rows r j (x, x) ≤ rows r j B)
    (j : Index) (hj : 0 < numerator r j) :
    ∃ x ∈ K, cut j x = wall B j ∧ cut (succ j) x = wall B (succ j) := by
  by_contra hn
  exact hj.ne' (numerator_eq_zero_of_missing_corner K hcK hK B hmin hstrict hL hU r hr hs j hn)

/-- At least two upper and two lower pair corners meet the body at the original strict minimum. -/
theorem missing_corners_unique (K : Set Point) (hcK : IsCompact K)
    (hK : Convex ℝ K) (B : Walls) (hmin : IsMinOn width (wallSet K) B)
    (hstrict : B ∈ strictWalls)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (r : Index → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, rows r j (x, x) ≤ rows r j B)
    (s : Bool) (i j : Fin 3)
    (hi : ¬ ∃ x ∈ K, cut (s, i) x = wall B (s, i) ∧
      cut (succ (s, i)) x = wall B (succ (s, i)))
    (hj : ¬ ∃ x ∈ K, cut (s, j) x = wall B (s, j) ∧
      cut (succ (s, j)) x = wall B (succ (s, j))) : i = j := by
  apply eq_of_numerators_zero r hr s i j
  · exact numerator_eq_zero_of_missing_corner K hcK hK B hmin hstrict hL hU r hr hs (s, i) hi
  · exact numerator_eq_zero_of_missing_corner K hcK hK B hmin hstrict hL hU r hr hs (s, j) hj

end Plank.Convex.SameSignLocalMinimum

/-- info: 'Plank.Convex.SameSignLocalMinimum.numerator_nonneg_of_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignLocalMinimum.numerator_nonneg_of_minimum

/-- info: 'Plank.Convex.SameSignLocalMinimum.numerator_eq_zero_of_missing_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignLocalMinimum.numerator_eq_zero_of_missing_corner

/-- info: 'Plank.Convex.SameSignLocalMinimum.contact_of_numerator_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignLocalMinimum.contact_of_numerator_pos

/-- info: 'Plank.Convex.SameSignLocalMinimum.missing_corners_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignLocalMinimum.missing_corners_unique
