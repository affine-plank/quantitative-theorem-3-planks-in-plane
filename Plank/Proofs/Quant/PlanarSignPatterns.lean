/- Finite sign-pattern consequences of retaining seven of eight vertices. -/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenCellGeometry

/-- Among at least seven of the eight sign patterns, any two different
patterns include one of the retained patterns. -/
theorem mem_or_mem_of_seven (S : Finset (Finset (Fin 3))) (hS : 7 ≤ S.card)
    (s t : Finset (Fin 3)) (hst : s ≠ t) : s ∈ S ∨ t ∈ S := by
  classical
  by_contra hn
  have hs : s ∉ S := fun h => hn (Or.inl h)
  have ht : t ∉ S := fun h => hn (Or.inr h)
  have his : s ∉ insert t S := by simp [hst, hs]
  have hh := (insert s (insert t S)).card_le_univ
  rw [Finset.card_insert_of_notMem his, Finset.card_insert_of_notMem ht] at hh
  simp only [Fintype.card_finset, Fintype.card_fin] at hh
  omega

/-- Seven patterns realize every choice of signs in any two coordinates. -/
theorem exists_pair_pattern (S : Finset (Finset (Fin 3))) (hS : 7 ≤ S.card)
    (i j : Fin 3) (hij : i ≠ j) (b c : Bool) :
    ∃ s ∈ S, (i ∈ s ↔ b = true) ∧ (j ∈ s ↔ c = true) := by
  classical
  have hex : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> simp_all <;> decide
  obtain ⟨k, hki, hkj⟩ := hex
  let s := Finset.univ.filter (fun r : Fin 3 => (r = i ∧ b = true) ∨ (r = j ∧ c = true))
  have hsi : i ∈ s ↔ b = true := by simp [s, hij]
  have hsj : j ∈ s ↔ c = true := by simp [s, hij.symm]
  have hks : k ∉ s := by simp [s, hki, hkj]
  have hne : s ≠ insert k s := by
    intro hh
    rw [hh] at hks
    exact hks (Finset.mem_insert_self k s)
  rcases mem_or_mem_of_seven S hS s (insert k s) hne with hs | ht
  · exact ⟨s, hs, hsi, hsj⟩
  · refine ⟨insert k s, ht, ?_, ?_⟩
    · simpa only [Finset.mem_insert, hki.symm, false_or] using hsi
    · simpa only [Finset.mem_insert, hkj.symm, false_or] using hsj

end Plank.PlanarSevenCellGeometry
