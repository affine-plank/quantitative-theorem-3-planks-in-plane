/- Three positive windows in one direction tile its unit range. -/
module
public import Plank.Convex.ConvexCapWidth
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.ParallelClassification

/-- The interval covering property whose equality cases are classified. -/
def TightIntervals (lo hi : Fin 3 → ℝ) : Prop :=
  (∑ i, (hi i - lo i)) = 1 ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ i, lo i ≤ x ∧ x ≤ hi i

/-- A partition into three consecutive positive intervals, in arbitrary
label order. No restriction on the body's shape is imposed. -/
def Normal (lo hi : Fin 3 → ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (r s : ℝ), 0 < r ∧ r < s ∧ s < 1 ∧
    lo (σ 0) = 0 ∧ hi (σ 0) = r ∧ lo (σ 1) = r ∧ hi (σ 1) = s ∧
    lo (σ 2) = s ∧ hi (σ 2) = 1

private theorem sorted_touch (lo hi : Fin 3 → ℝ) (hsort : Monotone lo)
    (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1) (hw : ∀ i, lo i < hi i)
    (ht : TightIntervals lo hi) :
    lo 0 = 0 ∧ hi 0 = lo 1 ∧ hi 1 = lo 2 ∧ hi 2 = 1 := by
  have h01 : lo 0 ≤ lo 1 := hsort (by decide)
  have h12 : lo 1 ≤ lo 2 := hsort (by decide)
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  have hs := ht.1
  rw [Fin.sum_univ_three] at hs
  have hl0 : lo 0 = 0 := by
    obtain ⟨i, hi⟩ := ht.2 0 ⟨le_rfl, zero_le_one⟩
    fin_cases i <;> dsimp at hi <;> linarith only [hi.1, hlo 0, h01, h12]
  have hb1 : lo 1 ≤ hi 0 := by
    by_contra! hgap
    obtain ⟨i, hi⟩ := ht.2 ((hi 0 + lo 1) / 2) (by
      constructor <;> linarith only [hlo 0, h0, hlo 1, h1, hhi 1, hgap])
    fin_cases i <;> dsimp at hi <;> linarith only [hi.1, hi.2, hgap, h12]
  have hb2 : lo 2 ≤ max (hi 0) (hi 1) := by
    by_contra! hgap
    have hm0 := le_max_left (hi 0) (hi 1)
    have hm1 := le_max_right (hi 0) (hi 1)
    have hm : max (hi 0) (hi 1) ≤ 1 := max_le (hhi 0) (hhi 1)
    obtain ⟨i, hi⟩ := ht.2 ((max (hi 0) (hi 1) + lo 2) / 2) (by
      constructor <;> linarith only [hlo 0, h0, hm0, hlo 2, h2, hhi 2, hm])
    fin_cases i <;> dsimp at hi <;> linarith only [hi.1, hi.2, hgap, hm0, hm1]
  have hu2 : hi 2 = 1 := by
    obtain ⟨i, hi'⟩ := ht.2 1 ⟨zero_le_one, le_rfl⟩
    fin_cases i <;> dsimp at hi'
    · linarith only [hi'.2, hl0, hs, h1, h2]
    · linarith only [hi'.2, hl0, hs, hb1, h2]
    · exact le_antisymm (hhi 2) hi'.2
  have hh0 : hi 0 < lo 2 := by linarith only [hl0, hu2, hs, h1]
  have hb2' : lo 2 ≤ hi 1 := (le_max_iff.mp hb2).resolve_left (not_le_of_gt hh0)
  exact ⟨hl0, by linarith only [hl0, hu2, hs, hb1, hb2'],
    by linarith only [hl0, hu2, hs, hb1, hb2'], hu2⟩

/-- The complete positive equality classification for three clipped intervals. -/
theorem tight_intervals_iff (lo hi : Fin 3 → ℝ)
    (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1) (hw : ∀ i, lo i < hi i) :
    TightIntervals lo hi ↔ Normal lo hi := by
  constructor
  · intro ht
    let σ := Tuple.sort lo
    have hsort : Monotone (fun i => lo (σ i)) := Tuple.monotone_sort lo
    have ht' : TightIntervals (fun i => lo (σ i)) (fun i => hi (σ i)) := by
      refine ⟨?_, ?_⟩
      · simpa only [Equiv.sum_comp σ (fun i => hi i - lo i)] using ht.1
      · intro x hx
        obtain ⟨i, hi⟩ := ht.2 x hx
        exact ⟨σ.symm i, by simpa only [σ.apply_symm_apply] using hi⟩
    obtain ⟨h0, h01, h12, h2⟩ := sorted_touch (fun i => lo (σ i)) (fun i => hi (σ i))
      hsort (fun i => hlo (σ i)) (fun i => hhi (σ i)) (fun i => hw (σ i)) ht'
    refine ⟨σ, lo (σ 1), lo (σ 2), ?_, ?_, ?_, h0, h01, rfl, h12, rfl, h2⟩
    · have h := hw (σ 0); linarith only [h, h0, h01]
    · have h := hw (σ 1); linarith only [h, h12]
    · have h := hw (σ 2); linarith only [h, h2]
  · rintro ⟨σ, r, s, hr, hrs, hs, hl0, hu0, hl1, hu1, hl2, hu2⟩
    refine ⟨?_, ?_⟩
    · rw [← Equiv.sum_comp σ (fun i => hi i - lo i), Fin.sum_univ_three]
      rw [hl0, hu0, hl1, hu1, hl2, hu2]
      ring
    · intro x hx
      by_cases hxr : x ≤ r
      · exact ⟨σ 0, by rw [hl0, hu0]; exact ⟨hx.1, hxr⟩⟩
      by_cases hxs : x ≤ s
      · exact ⟨σ 1, by rw [hl1, hu1]; exact ⟨le_of_not_ge hxr, hxs⟩⟩
      · exact ⟨σ 2, by rw [hl2, hu2]; exact ⟨le_of_not_ge hxs, hx.2⟩⟩

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The parallel family on any convex body: after normalizing its attained
range, the three windows partition `[0,1]`. All convex body shapes are allowed. -/
theorem tight_iff (K : Set E) (hK : Convex ℝ K) (X : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ p ∈ K, 0 ≤ X p ∧ X p ≤ 1)
    (hL : ∃ p ∈ K, X p = 0) (hU : ∃ p ∈ K, X p = 1)
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hw : ∀ i, lo i < hi i) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ p ∈ K, ∃ i, lo i ≤ X p ∧ X p ≤ hi i) ↔
      Normal lo hi := by
  rw [← tight_intervals_iff lo hi hlo hhi hw]
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨hs, ?_⟩
    intro x hx
    obtain ⟨L, hL, hL0⟩ := hL
    obtain ⟨U, hU, hU1⟩ := hU
    have hmem := hK.lineMap_mem hL hU hx
    have he : X (AffineMap.lineMap L U x) = x := by
      rw [X.apply_lineMap, AffineMap.lineMap_apply_ring, hL0, hU1]
      ring
    simpa only [he] using hc (AffineMap.lineMap L U x) hmem
  · rintro ⟨hs, hc⟩
    exact ⟨hs, fun p hp => hc (X p) (hbox p hp)⟩

end Plank.Convex.PlanarTight.ParallelClassification

/-- info: 'Plank.Convex.PlanarTight.ParallelClassification.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ParallelClassification.tight_iff
