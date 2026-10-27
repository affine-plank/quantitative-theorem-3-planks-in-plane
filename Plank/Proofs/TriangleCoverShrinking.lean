/- Delete a window meeting a normalized endpoint by shrinking toward the
opposite vertex and pulling the retained windows back to the original simplex. -/
module
public import Plank.Proofs.TriangleCoverData
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.TriangleNormalization
open scoped BigOperators

private theorem level_bounds {n : ℕ} (C : Cover n) (l : Fin 3 → ℝ)
    (hl0 : ∀ k, 0 ≤ l k) (hl1 : ∑ k, l k = 1) (i : Fin n) :
    0 ≤ ∑ k, l k * C.g i k ∧ (∑ k, l k * C.g i k) ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun k _ => mul_nonneg (hl0 k) (C.bounds i k).1), ?_⟩
  calc
    (∑ k, l k * C.g i k) ≤ ∑ k, l k :=
      Finset.sum_le_sum (fun k _ => mul_le_of_le_one_right (hl0 k) (C.bounds i k).2)
    _ = 1 := hl1

/-- A deficient cover with a window reaching `0` or `1` gives a deficient
cover with that row deleted. The retained normalized rows and endpoint
permutations are unchanged; only their window endpoints are pulled back. -/
theorem drop_bad_window {n : ℕ} (C : Cover (n+1)) (hsmall : C.width < 1)
    (j : Fin (n+1)) (hbad : C.lo j ≤ 0 ∨ 1 ≤ C.hi j) :
    ∃ D : Cover n, D.width < 1 := by
  let B := ∑ k : Fin n, (C.hi (j.succAbove k) - C.lo (j.succAbove k))
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun k _ => sub_nonneg.mpr (C.ordered _))
  have hsum : C.width = C.hi j - C.lo j + B :=
    Fin.sum_univ_succAbove (fun i => C.hi i - C.lo i) j
  have hB : B < 1 - (C.hi j - C.lo j) := by linarith only [hsum, hsmall]
  obtain ⟨r, hBr, hrw⟩ := exists_between hB
  have hr0 : 0 < r := hB0.trans_lt hBr
  have hr1 : r < 1 := by linarith only [hrw, C.ordered j]
  -- The chosen vertex makes the entire shrunken simplex miss the deleted window.
  obtain ⟨v, hv⟩ : ∃ v : Fin 3,
      (C.g j v = 1 ∧ C.hi j < 1-r) ∨ (C.g j v = 0 ∧ r < C.lo j) := by
    rcases hbad with hbad | hbad
    · exact ⟨C.σ j 2, Or.inl ⟨C.one j, by linarith only [hrw, hbad]⟩⟩
    · exact ⟨C.σ j 0, Or.inr ⟨C.zero j, by linarith only [hrw, hbad]⟩⟩
  let q (l : Fin 3 → ℝ) (k : Fin 3) := (if k=v then 1-r else 0) + r*l k
  have hq (l : Fin 3 → ℝ) (i : Fin (n+1)) :
      (∑ k, q l k * C.g i k) = (1-r)*C.g i v + r*(∑ k, l k*C.g i k) := by
    simp [q, add_mul, ite_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  refine ⟨{
    g := fun k => C.g (j.succAbove k)
    σ := fun k => C.σ (j.succAbove k)
    lo := fun k => (C.lo (j.succAbove k) - (1-r)*C.g (j.succAbove k) v)/r
    hi := fun k => (C.hi (j.succAbove k) - (1-r)*C.g (j.succAbove k) v)/r
    bounds := fun k => C.bounds (j.succAbove k)
    zero := fun k => C.zero (j.succAbove k)
    one := fun k => C.one (j.succAbove k)
    ordered := fun k => (div_le_div_iff_of_pos_right hr0).mpr
      (sub_le_sub_right (C.ordered (j.succAbove k)) _)
    covered := ?_ }, ?_⟩
  · intro l hl0 hl1
    have hq0 (k : Fin 3) : 0 ≤ q l k := by
      dsimp [q]
      exact add_nonneg (by split_ifs <;> linarith only [hr1]) (mul_nonneg hr0.le (hl0 k))
    have hq1 : ∑ k, q l k = 1 := by
      simp [q, Finset.sum_add_distrib, ← Finset.mul_sum, hl1]
    obtain ⟨i, hi⟩ := C.covered (q l) hq0 hq1
    rw [hq] at hi
    have hij : i ≠ j := by
      intro he
      subst i
      have hb := level_bounds C l hl0 hl1 j
      rcases hv with ⟨hv, hh⟩ | ⟨hv, hh⟩
      · rw [hv] at hi
        nlinarith only [hi.2, hh, mul_nonneg hr0.le hb.1]
      · rw [hv] at hi
        nlinarith only [hi.1, hh, mul_le_mul_of_nonneg_left hb.2 hr0.le]
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    refine ⟨k, ?_, ?_⟩
    · apply (div_le_iff₀ hr0).mpr
      linarith only [hi.1]
    · apply (le_div_iff₀ hr0).mpr
      linarith only [hi.2]
  · change (∑ k : Fin n,
      ((C.hi (j.succAbove k) - (1-r)*C.g (j.succAbove k) v)/r -
       (C.lo (j.succAbove k) - (1-r)*C.g (j.succAbove k) v)/r)) < 1
    calc
      _ = B/r := by
        dsimp [B]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ < 1 := (div_lt_one hr0).mpr hBr

/-- Windows missing all extreme vertex values need distinct owners for the
three vertices, hence at least three windows. -/
theorem Cover.three_le_of_interior {n : ℕ} (C : Cover n)
    (hlo : ∀ k, 0 < C.lo k) (hhi : ∀ k, C.hi k < 1) : 3 ≤ n := by
  have hvertices (i : Fin 3) : ∃ k, C.lo k ≤ C.g k i ∧ C.g k i ≤ C.hi k := by
    obtain ⟨k, hk⟩ := C.covered (fun j => if j = i then 1 else 0)
      (fun j => by split_ifs <;> norm_num) (by simp)
    exact ⟨k, by simpa using hk⟩
  have hmiddle (k : Fin n) (i : Fin 3)
      (hi : C.lo k ≤ C.g k i ∧ C.g k i ≤ C.hi k) : C.σ k 1 = i := by
    obtain ⟨j, rfl⟩ := (C.σ k).surjective i
    fin_cases j
    · exact ((not_le_of_gt (hlo k)) (hi.1.trans_eq (C.zero k))).elim
    · rfl
    · exact ((not_le_of_gt (hhi k)) ((C.one k).symm.trans_le hi.2)).elim
  choose owner howner using hvertices
  have hmid : Function.LeftInverse (fun k => C.σ k 1) owner :=
    fun i => hmiddle (owner i) i (howner i)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective owner hmid.injective

/-- The two-plank case follows entirely from shrinking: without an extreme
vertex, two windows cannot cover the three vertices. -/
theorem width_bound_two {n : ℕ} (C : Cover n) (hn : n ≤ 2) : 1 ≤ C.width := by
  induction n with
  | zero =>
    obtain ⟨i, _⟩ := C.covered (fun j => if j = 0 then 1 else 0)
      (fun j => by split_ifs <;> norm_num) (by simp)
    exact i.elim0
  | succ n ih =>
    by_contra hs
    by_cases hbad : ∃ j, C.lo j ≤ 0 ∨ 1 ≤ C.hi j
    · obtain ⟨j, hj⟩ := hbad
      obtain ⟨D, hD⟩ := drop_bad_window C (lt_of_not_ge hs) j hj
      exact (not_le_of_gt hD) (ih D (by omega))
    · simp only [not_exists, not_or, not_le] at hbad
      have := C.three_le_of_interior (fun i => (hbad i).1) (fun i => (hbad i).2)
      omega

end Plank.TriangleNormalization
