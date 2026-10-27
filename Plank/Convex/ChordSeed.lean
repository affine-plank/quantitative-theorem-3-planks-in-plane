/- A homothetic seed for every subset translation along finitely many chords.
The argument uses convexity alone and allows zero weights and empty families. -/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel

@[expose] public section

namespace Plank.Convex

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- A convex combination with the unused weight assigned to an additional point. -/
theorem convex_sum_mem_with_remainder {K : Set E} (hK : Convex ℝ K)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hsum : ∑ i, ρ i ≤ 1)
    (p : ι → E) (hp : ∀ i, p i ∈ K) {z : E} (hz : z ∈ K) :
    (1 - ∑ i, ρ i) • z + ∑ i, ρ i • p i ∈ K := by
  classical
  have h := hK.sum_mem (t := Finset.univ.insertNone)
    (w := fun i => i.elim (1 - ∑ i, ρ i) ρ) (z := fun i => i.elim z p)
    (by
      intro i _
      cases i with
      | none => exact sub_nonneg.mpr hsum
      | some i => exact hρ i)
    (by simp only [Finset.sum_insertNone, Option.elim_none, Option.elim_some,
      sub_add_cancel])
    (by
      intro i _
      cases i with
      | none => exact hz
      | some i => exact hp i)
  simpa only [Finset.sum_insertNone, Option.elim_none, Option.elim_some] using h

/-- A translate of the homothetic copy with ratio `1 - ∑ i, ρ i`, based at the
weighted lower endpoints of the chords. -/
def chordSeed (K : Set E) (ρ : ι → ℝ) (y : ι → E) : Set E :=
  (fun z => (∑ i, ρ i • y i) + (1 - ∑ i, ρ i) • z) '' K

/-- Every subset of the chord displacements translates the whole seed into the
convex set. No common chord midpoint or symmetry of the set is required. -/
theorem chordSeed_shift_mem {K : Set E} (hK : Convex ℝ K)
    (x y : ι → E) (hx : ∀ i, x i ∈ K) (hy : ∀ i, y i ∈ K)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hsum : ∑ i, ρ i ≤ 1)
    (s : Finset ι) {t : E} (ht : t ∈ chordSeed K ρ y) :
    t + ∑ i ∈ s, ρ i • (x i - y i) ∈ K := by
  classical
  obtain ⟨z, hz, rfl⟩ := ht
  have h := convex_sum_mem_with_remainder hK ρ hρ hsum
    (fun i => if i ∈ s then x i else y i)
    (fun i => by split_ifs <;> first | exact hx i | exact hy i) hz
  have hsplit : (∑ i, ρ i • (if i ∈ s then x i else y i)) =
      (∑ i, ρ i • y i) + ∑ i ∈ s, ρ i • (x i - y i) := by
    calc
      _ = ∑ i, (ρ i • y i + if i ∈ s then ρ i • (x i - y i) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs
        · rw [smul_sub]
          abel
        · simp only [add_zero]
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_mem_eq]
  rw [hsplit] at h
  simpa only [add_assoc, add_left_comm, add_comm] using h

end Plank.Convex
