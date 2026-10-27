/- Lift the scalar triangle equality formula through the original row
permutation and independent changes of orientation. -/
module
public import Plank.Proofs.TriangleCoverInterior
public import Plank.Proofs.TriangleSliding.EqualityFamily
public import Plank.Convex.PlanarTight.OrientedCommonChord
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.StrictTriangleNormalization

def value (flip : Fin 3 → Bool) (g : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if flip i then 1 - g i j else g i j

private theorem endpoints (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (hm : σ 1 = i) :
    (σ 0 = i + 1 ∧ σ 2 = i + 2) ∨ (σ 0 = i + 2 ∧ σ 2 = i + 1) := by
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have h : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      ((a = b + 1 ∧ c = b + 2) ∨ (a = b + 2 ∧ c = b + 1)) := by decide
  simpa only [hm] using h (σ 0) (σ 1) (σ 2) h01 h02 h12

/-- The three positive widths determine all strict triangle windows and
all their vertex values, after a permutation and independent reflections. -/
theorem parameters (C : Plank.TriangleNormalization.Cover 3)
    (hlo : ∀ i, 0 < C.lo i) (hhi : ∀ i, C.hi i < 1)
    (hwidth : ∀ i, C.lo i < C.hi i) (hsum : C.width = 1) :
    ∃ (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (w : Fin 3 → ℝ),
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      ∀ i, value flip (fun k => C.g (π k)) i i = w (i + 1) / (1 - w i) ∧
        value flip (fun k => C.g (π k)) i (i + 1) = 0 ∧
        value flip (fun k => C.g (π k)) i (i + 2) = 1 ∧
        OrientedCommonChord.lower flip (fun k => C.lo (π k)) (fun k => C.hi (π k)) i = w (i + 1) ∧
        OrientedCommonChord.upper flip (fun k => C.lo (π k)) (fun k => C.hi (π k)) i = 1 - w (i + 2) := by
  classical
  have hvertices (i : Fin 3) : ∃ k, C.lo k ≤ C.g k i ∧ C.g k i ≤ C.hi k := by
    obtain ⟨k, hk⟩ := C.covered (fun j => if j = i then 1 else 0)
      (fun j => by split_ifs <;> norm_num) (by simp)
    exact ⟨k, by simpa using hk⟩
  have hmiddle (k i : Fin 3) (hi : C.lo k ≤ C.g k i ∧ C.g k i ≤ C.hi k) :
      C.σ k 1 = i := by
    obtain ⟨j, rfl⟩ := (C.σ k).surjective i
    fin_cases j
    · have hz : C.lo k ≤ C.g k (C.σ k 0) := hi.1
      rw [C.zero] at hz
      exact ((not_le_of_gt (hlo k)) hz).elim
    · rfl
    · have ho : C.g k (C.σ k 2) ≤ C.hi k := hi.2
      rw [C.one] at ho
      exact ((not_le_of_gt (hhi k)) ho).elim
  choose owner howner using hvertices
  have hmid : Function.LeftInverse (fun k => C.σ k 1) owner :=
    fun i => hmiddle (owner i) i (howner i)
  let π : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective owner (Finite.injective_iff_bijective.mp hmid.injective)
  have hπ (i : Fin 3) : C.σ (π i) 1 = i := hmid i
  have hown (i : Fin 3) : C.lo (π i) ≤ C.g (π i) i ∧ C.g (π i) i ≤ C.hi (π i) := howner i
  let flip : Fin 3 → Bool := fun i => decide (C.σ (π i) 0 = i + 2)
  let r := value flip (fun i => C.g (π i))
  let d (i : Fin 3) := r i i
  let L := OrientedCommonChord.lower flip (fun i => C.lo (π i)) (fun i => C.hi (π i))
  let H := OrientedCommonChord.upper flip (fun i => C.lo (π i)) (fun i => C.hi (π i))
  let G (i : Fin 3) := 1 - H i
  let w (i : Fin 3) := 1 - L i - G i
  have hne (i : Fin 3) : i + 1 ≠ i + 2 := by fin_cases i <;> decide
  have hends (i : Fin 3) : r i (i + 1) = 0 ∧ r i (i + 2) = 1 := by
    rcases endpoints (C.σ (π i)) i (hπ i) with ⟨h0, h2⟩ | ⟨h0, h2⟩
    · have hz : C.g (π i) (i + 1) = 0 := h0 ▸ C.zero (π i)
      have ho : C.g (π i) (i + 2) = 1 := h2 ▸ C.one (π i)
      simp only [r, value, flip, h0, hne i, decide_false, Bool.false_eq_true,
        if_false, hz, ho, and_self]
    · have hz : C.g (π i) (i + 2) = 0 := h0 ▸ C.zero (π i)
      have ho : C.g (π i) (i + 1) = 1 := h2 ▸ C.one (π i)
      simp only [r, value, flip, h0, decide_true, if_true, hz, ho, sub_self, sub_zero, and_self]
  have hlevels (i : Fin 3) (l : Fin 3 → ℝ) :
      (∑ j, l j * r i j) = d i * l i + l (i + 2) := by
    rw [SixBoundaries.sum_cyclic _ i, (hends i).1, (hends i).2]
    change l i * d i + l (i + 1) * 0 + l (i + 2) * 1 = _
    ring
  have hwindow (i : Fin 3) : 0 < L i ∧ L i ≤ d i ∧ d i ≤ H i ∧ H i < 1 := by
    dsimp [L, H, d, r, value, OrientedCommonChord.lower, OrientedCommonChord.upper]
    split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith only [hlo (π i), hhi (π i), (hown i).1, (hown i).2]
  have hwval (i : Fin 3) : w i = C.hi (π i) - C.lo (π i) := by
    dsimp [w, G, L, H, OrientedCommonChord.lower, OrientedCommonChord.upper]
    split_ifs <;> ring
  have hw (i : Fin 3) : 0 < w i := by rw [hwval]; exact sub_pos.mpr (hwidth _)
  have hwsum : ∑ i, w i = 1 := by
    have hs : (∑ i, (C.hi i - C.lo i)) = 1 := hsum
    simpa only [hwval, Equiv.sum_comp π (fun i => C.hi i - C.lo i)] using hs
  have hcover : SixBoundaries.covers d L G := by
    intro l hl
    obtain ⟨k, hk⟩ := C.covered l hl.1 hl.2
    obtain ⟨i, rfl⟩ := π.surjective k
    have hwl : L i ≤ ∑ j, l j * r i j ∧ (∑ j, l j * r i j) ≤ H i := by
      dsimp [L, H, r, value, OrientedCommonChord.lower, OrientedCommonChord.upper]
      split_ifs
      · simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hl.2]
        exact ⟨by linarith only [hk.2], by linarith only [hk.1]⟩
      · exact hk
    refine ⟨i, ?_⟩
    simpa only [SixBoundaries.level, G, sub_sub_cancel, hlevels] using hwl
  have hp := SixBoundaries.Rigidity.width_one_parameters
    (fun i => (hwindow i).1.trans_le (hwindow i).2.1)
    (fun i => (hwindow i).2.2.1.trans_lt (hwindow i).2.2.2)
    (fun i => (hwindow i).1) (fun i => (hwindow i).2.1)
    (fun i => sub_pos.mpr (hwindow i).2.2.2)
    (fun i => sub_le_sub_left (hwindow i).2.2.1 1) hw hcover hwsum
  refine ⟨π, flip, w, hw, hwsum, ?_⟩
  intro i
  have hden : 0 < 1 - w i := by
    have ht := (SixBoundaries.sum_cyclic w i).symm.trans hwsum
    linarith only [ht, hw (i + 1), hw (i + 2)]
  obtain ⟨hL, hG, hd⟩ := hp i
  refine ⟨(eq_div_iff hden.ne').mpr hd, (hends i).1, (hends i).2, hL, ?_⟩
  change H i = 1 - w (i + 2)
  change 1 - H i = w (i + 2) at hG
  linarith only [hG]

end Plank.Convex.PlanarTight.StrictTriangleNormalization

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleNormalization.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleNormalization.parameters
