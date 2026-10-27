/- Exact elimination of one variable in a finite closed affine system. -/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.ClosedLinearFeasibility

variable {ι : Type*} [Fintype ι]

/-- The finite sign and pair tests for a system of weak inequalities. -/
def OneTest (b d : ι → ℝ) : Prop :=
  (∀ i, b i = 0 → 0 ≤ d i) ∧
    ∀ i j, b i < 0 → 0 < b j → 0 ≤ b j*d i-b i*d j

/-- Boundary contact is retained: weak feasibility uses weak pair
inequalities, with zero coefficients handled explicitly. -/
theorem oneTest_iff (b d : ι → ℝ) : OneTest b d ↔ ∃ y, ∀ i, b i*y ≤ d i := by
  classical
  constructor
  · rintro ⟨hz,hpair⟩
    let L := Finset.univ.filter (fun i => b i < 0)
    let U := Finset.univ.filter (fun i => 0 < b i)
    have hLU (i j : ι) (hi : i ∈ L) (hj : j ∈ U) : d i/b i ≤ d j/b j := by
      have hbi : b i < 0 := (Finset.mem_filter.mp hi).2
      have hbj : 0 < b j := (Finset.mem_filter.mp hj).2
      rw [div_le_iff_of_neg hbi,div_mul_eq_mul_div,div_le_iff₀ hbj]
      nlinarith only [hpair i j hbi hbj]
    have hbuild (y : ℝ) (hl : ∀ i ∈ L, d i/b i ≤ y)
        (hu : ∀ i ∈ U, y ≤ d i/b i) : ∀ i, b i*y ≤ d i := by
      intro i
      rcases lt_trichotomy (b i) 0 with hi | hi | hi
      · have hh := (div_le_iff_of_neg hi).mp (hl i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩))
        simpa only [mul_comm] using hh
      · simpa only [hi,zero_mul] using hz i hi
      · have hh := (le_div_iff₀ hi).mp (hu i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩))
        simpa only [mul_comm] using hh
    by_cases hL : L.Nonempty
    · obtain ⟨i,hi,hmax⟩ := L.exists_max_image (fun i => d i/b i) hL
      exact ⟨d i/b i,hbuild _ (fun k hk => hmax k hk) (fun k hk => hLU i k hi hk)⟩
    · by_cases hU : U.Nonempty
      · obtain ⟨j,hj,hmin⟩ := U.exists_min_image (fun i => d i/b i) hU
        exact ⟨d j/b j,hbuild _ (fun k hk => (hL ⟨k,hk⟩).elim) (fun k hk => hmin k hk)⟩
      · exact ⟨0,hbuild 0 (fun k hk => (hL ⟨k,hk⟩).elim) (fun k hk => (hU ⟨k,hk⟩).elim)⟩
  · rintro ⟨y,hy⟩
    refine ⟨fun i hi => by simpa only [hi,zero_mul] using hy i,?_⟩
    intro i j hi hj
    have h1 := mul_le_mul_of_nonneg_left (hy i) hj.le
    have h2 := mul_le_mul_of_nonneg_left (hy j) (neg_nonneg.mpr hi.le)
    nlinarith only [h1,h2]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Elimination produces only affine half-planes in the retained
parameters. The inactive rows are the tautology 0<=1. -/
def eliminate (b : ι → ℝ) (d : ι → E →ᵃ[ℝ] ℝ) : ι ⊕ (ι × ι) → E →ᵃ[ℝ] ℝ
  | .inl i => if b i = 0 then d i else AffineMap.const ℝ E 1
  | .inr (i,j) => if b i < 0 ∧ 0 < b j then b j • d i-b i • d j else AffineMap.const ℝ E 1

/-- Exact projection of a closed system, with no genericity or
nonzero-coefficient assumptions and no remaining real witness variable. -/
theorem eliminate_iff (b : ι → ℝ) (d : ι → E →ᵃ[ℝ] ℝ) (x : E) :
    (∀ k, 0 ≤ eliminate b d k x) ↔ ∃ y, ∀ i, b i*y ≤ d i x := by
  rw [← oneTest_iff]
  constructor
  · intro h
    refine ⟨fun i hi => ?_,fun i j hi hj => ?_⟩
    · simpa only [eliminate,if_pos hi] using h (.inl i)
    · have hh := h (.inr (i,j))
      simp only [eliminate,if_pos (And.intro hi hj)] at hh
      exact hh
  · rintro ⟨hz,hp⟩ (i | ⟨i,j⟩)
    · by_cases hi : b i = 0
      · simpa only [eliminate,if_pos hi] using hz i hi
      · simp [eliminate,hi]
    · by_cases hij : b i < 0 ∧ 0 < b j
      · simp only [eliminate,if_pos hij]
        exact hp i j hij.1 hij.2
      · simp [eliminate,hij]

end Quant.ClosedLinearFeasibility

/-- info: 'Quant.ClosedLinearFeasibility.eliminate_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.ClosedLinearFeasibility.eliminate_iff
