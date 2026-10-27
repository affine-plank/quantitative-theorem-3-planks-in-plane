/- Interior windows covering the three vertices have distinct owners.
With at most three rows, these owners give the cyclic three-window frame. -/
module
public import Plank.Proofs.TriangleCoverData
public import Plank.Proofs.TriangleSliding
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Choose
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.TriangleNormalization
open Finset

private theorem endpoints (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (hm : σ 1 = i) :
    (σ 0 = i+1 ∧ σ 2 = i+2) ∨ (σ 0 = i+2 ∧ σ 2 = i+1) := by
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have h : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      ((a = b+1 ∧ c = b+2) ∨ (a = b+2 ∧ c = b+1)) := by decide
  simpa only [hm] using h (σ 0) (σ 1) (σ 2) h01 h02 h12

/-- At most three normalized windows strictly inside `(0,1)` cannot cover
the barycentric triangle with total width less than one. Vertex values may tie;
only the two specified endpoint values are excluded by an interior window. -/
theorem interior_width_bound {n : ℕ} (C : Cover n) (hn : n ≤ 3)
    (hlo : ∀ i, 0 < C.lo i) (hhi : ∀ i, C.hi i < 1) : 1 ≤ C.width := by
  have hvertices (i : Fin 3) : ∃ k, C.lo k ≤ C.g k i ∧ C.g k i ≤ C.hi k := by
    obtain ⟨k, hk⟩ := C.covered (fun j => if j=i then 1 else 0)
      (fun j => by split_ifs <;> norm_num) (by simp)
    exact ⟨k, by simpa using hk⟩
  have hmiddle (k : Fin n) (i : Fin 3)
      (hi : C.lo k ≤ C.g k i ∧ C.g k i ≤ C.hi k) : C.σ k 1 = i := by
    obtain ⟨j, rfl⟩ := (C.σ k).surjective i
    fin_cases j
    · have hz : C.lo k ≤ C.g k (C.σ k 0) := hi.1
      rw [C.zero] at hz
      exact ((not_le_of_gt (hlo k)) hz).elim
    · rfl
    · have ho : C.g k (C.σ k 2) ≤ C.hi k := hi.2
      rw [C.one] at ho
      exact ((not_le_of_gt (hhi k)) ho).elim
  -- Choose each vertex's covering row once. Its middle label returns that vertex.
  choose owner howner using hvertices
  have hmid : Function.LeftInverse (fun k => C.σ k 1) owner :=
    fun i => hmiddle (owner i) i (howner i)
  have hthree : 3 ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective owner hmid.injective
  have hn3 : n = 3 := Nat.le_antisymm hn hthree
  subst n
  let π : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective owner (Finite.injective_iff_bijective.mp hmid.injective)
  have hπ (i : Fin 3) : C.σ (π i) 1 = i := hmid i
  have hown (i : Fin 3) : C.lo (π i) ≤ C.g (π i) i ∧ C.g (π i) i ≤ C.hi (π i) := howner i
  -- Reverse a row's scale when needed, so its next vertex is 0 and its previous is 1.
  let rev (i : Fin 3) : Prop := C.σ (π i) 0 = i+2
  let r (i j : Fin 3) := if rev i then 1-C.g (π i) j else C.g (π i) j
  let d (i : Fin 3) := r i i
  let a (i : Fin 3) := if rev i then 1-C.hi (π i) else C.lo (π i)
  let b (i : Fin 3) := if rev i then 1-C.lo (π i) else C.hi (π i)
  have hne (i : Fin 3) : i+1 ≠ i+2 := by fin_cases i <;> decide
  have hends (i : Fin 3) : r i (i+1) = 0 ∧ r i (i+2) = 1 := by
    rcases endpoints (C.σ (π i)) i (hπ i) with ⟨h0,h2⟩ | ⟨h0,h2⟩
    · have hz : C.g (π i) (i+1) = 0 := h0 ▸ C.zero (π i)
      have ho : C.g (π i) (i+2) = 1 := h2 ▸ C.one (π i)
      simp only [r, rev, h0, hne i, if_false, hz, ho, and_self]
    · have hz : C.g (π i) (i+2) = 0 := h0 ▸ C.zero (π i)
      have ho : C.g (π i) (i+1) = 1 := h2 ▸ C.one (π i)
      simp only [r, rev, h0, if_true, hz, ho, sub_self, sub_zero, and_self]
  have hlevels (i : Fin 3) (l : Fin 3 → ℝ) :
      (∑ j, l j*r i j) = d i*l i+l (i+2) := by
    rw [SixBoundaries.sum_cyclic _ i, (hends i).1, (hends i).2]
    change l i*d i+l (i+1)*0+l (i+2)*1 = _
    ring
  have hwindow (i : Fin 3) : 0 < a i ∧ a i ≤ d i ∧ d i ≤ b i ∧ b i < 1 := by
    dsimp [d, r, a, b]
    split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith only [hlo (π i), hhi (π i), (hown i).1, (hown i).2]
  have hcost : (∑ i, (b i-a i)) = C.width := by
    calc
      (∑ i, (b i-a i)) = ∑ i, (C.hi (π i)-C.lo (π i)) := by
        apply sum_congr rfl
        intro i _
        dsimp [a, b]; split_ifs <;> ring
      _ = C.width := Equiv.sum_comp π (fun i => C.hi i-C.lo i)
  have hcover (l : Fin 3 → ℝ) (hl0 : ∀ j, 0 ≤ l j) (hl1 : ∑ j, l j = 1) :
      ∃ i, a i ≤ d i*l i+l (i+2) ∧ d i*l i+l (i+2) ≤ b i := by
    obtain ⟨k, hk⟩ := C.covered l hl0 hl1
    obtain ⟨i, rfl⟩ := π.surjective k
    have hw : a i ≤ ∑ j, l j*r i j ∧ (∑ j, l j*r i j) ≤ b i := by
      dsimp [a, b, r]
      split_ifs
      · simp only [mul_sub, mul_one, sum_sub_distrib, hl1]
        exact ⟨by linarith only [hk.2], by linarith only [hk.1]⟩
      · exact hk
    exact ⟨i, by simpa only [hlevels] using hw⟩
  have h := SixBoundaries.canonical_interior_cover_width_bound d a b
    (fun i => (hwindow i).1.trans_le (hwindow i).2.1)
    (fun i => (hwindow i).2.2.1.trans_lt (hwindow i).2.2.2)
    (fun i => (hwindow i).1) (fun i => (hwindow i).2.1)
    (fun i => (hwindow i).2.2.1) (fun i => (hwindow i).2.2.2) hcover
  rwa [hcost] at h

end Plank.TriangleNormalization
