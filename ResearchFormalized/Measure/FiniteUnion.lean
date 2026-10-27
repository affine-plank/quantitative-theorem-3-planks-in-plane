/- The second Bonferroni inequality, exact when distinct triple intersections
are null. The same induction proves both statements in any measure space. -/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace ResearchFormalized.FiniteUnion
open Set MeasureTheory
open scoped BigOperators

variable {α : Type*} [MeasurableSpace α]

/-- Each unordered pair is counted once. -/
def pairSum {n : ℕ} (μ : Measure α) (A : Fin n → Set α) : ℝ :=
  ∑ i, ∑ j, if i < j then μ.real (A i ∩ A j) else 0

/-- The second finite inclusion-exclusion bound, with its equality case.
Only the individual sets need finite measure. -/
theorem two_term {n : ℕ} (μ : Measure α) (A : Fin n → Set α)
    (hm : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, μ (A i) ≠ ⊤) :
    ((∑ i, μ.real (A i)) - pairSum μ A ≤ μ.real (⋃ i, A i)) ∧
    ((∀ i j k, i ≠ j → i ≠ k → j ≠ k → μ ((A i ∩ A j) ∩ A k) = 0) →
      (∑ i, μ.real (A i)) - pairSum μ A = μ.real (⋃ i, A i)) := by
  classical
  induction n with
  | zero => simp [pairSum]
  | succ n ih =>
    have hUf : μ (⋃ i : Fin n, A i.succ) ≠ ⊤ := by
      simpa only [mem_univ, iUnion_true] using
        measure_biUnion_ne_top (μ := μ) (s := Set.univ) (f := fun i : Fin n => A i.succ)
          (Set.toFinite _) (fun i _ => hfin i.succ)
    have htail := ih (fun i : Fin n => A i.succ) (fun i => hm i.succ)
      (fun i => hfin i.succ)
    have hadd := measureReal_union_add_inter (μ := μ) (s := A 0)
      (MeasurableSet.iUnion (fun i : Fin n => hm i.succ)) (hfin 0) hUf
    have hp : pairSum μ A = (∑ j : Fin n, μ.real (A 0 ∩ A j.succ)) +
        pairSum μ (fun i : Fin n => A i.succ) := by
      simp [pairSum, Fin.sum_univ_succ]
    have hu : (⋃ i, A i) = A 0 ∪ ⋃ i : Fin n, A i.succ := by
      ext x
      simp only [mem_iUnion, mem_union, Fin.exists_fin_succ]
    rw [Fin.sum_univ_succ, hp, hu]
    constructor
    · have hint := measureReal_iUnion_fintype_le (μ := μ)
        (fun i : Fin n => A 0 ∩ A i.succ)
      rw [← inter_iUnion] at hint
      linarith only [htail.1, hadd, hint]
    · intro htriple
      have heq := htail.2 (fun i j k hij hik hjk =>
        htriple i.succ j.succ k.succ (by simpa using hij) (by simpa using hik)
          (by simpa using hjk))
      have hdisj (i j : Fin n) (hij : i ≠ j) :
          AEDisjoint μ (A 0 ∩ A i.succ) (A 0 ∩ A j.succ) := by
        apply measure_mono_null _
          (htriple 0 i.succ j.succ (Fin.succ_ne_zero i).symm
            (Fin.succ_ne_zero j).symm (by simpa using hij))
        intro x hx
        exact ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩
      have hint := measureReal_biUnion_finset₀ (μ := μ) (s := Finset.univ)
        (f := fun i : Fin n => A 0 ∩ A i.succ)
        (fun i _ j _ hij => hdisj i j hij)
        (fun i _ => ((hm 0).inter (hm i.succ)).nullMeasurableSet)
        (fun i _ => measure_ne_top_of_subset inter_subset_left (hfin 0))
      simp only [Finset.mem_univ, iUnion_true] at hint
      rw [← inter_iUnion] at hint
      linarith only [heq, hadd, hint]

end ResearchFormalized.FiniteUnion
