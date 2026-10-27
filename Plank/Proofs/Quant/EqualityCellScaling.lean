/- Simultaneous proportional motion of all positive cells at equality. -/
module

public import Plank.Proofs.Quant.EqualityCellRank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.EqualityCellScaling

open scoped BigOperators

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E] [Fintype ι]

/-- The finite-dimensional equality argument chooses a common relative
derivative for every cell, including the singular-gradient case. -/
theorem exists_proportional_direction (A : ι → ℝ) (g : ι → E →ₗ[ℝ] ℝ)
    (d : E →ₗ[ℝ] ℝ) (V q : ℝ) (hV : 0 < V) (hq : 0 < q)
    (hsum : ∑ i, A i = V*q^2) (hder : ∀ z, ∑ i, g i z = 2*V*q*d z)
    (hcard : Fintype.card ι ≤ Module.finrank ℝ E) :
    ∃ z : E, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ d z = q*c ∧ ∀ i, g i z = 2*A i*c := by
  apply EqualityCellRank.exists_weighted_proportional_direction
    (fun i => 2*A i) (fun _ => 1) g d q (2*V*q) hq.ne' (by positivity)
    ?_ (by simpa only [one_mul] using hder) hcard
  simp only [one_mul,← Finset.mul_sum,hsum]
  ring

/-- At a common proportional derivative, the global lower curvature bound
forces every individual Brunn--Minkowski curvature bound to be exact. -/
theorem curvature_eq_each (A g H : ι → ℝ) (V q c : ℝ)
    (hA : ∀ i, 0 < A i) (hsum : ∑ i, A i = V*q^2)
    (hg : ∀ i, g i = 2*A i*c)
    (hcurv : ∀ i, H i ≤ (g i)^2/(2*A i))
    (hmargin : 2*V*(q*c)^2 ≤ ∑ i, H i) : ∀ i, H i = 2*A i*c^2 := by
  classical
  have hi (i) : H i ≤ 2*A i*c^2 := by
    have hh := hcurv i
    rw [hg] at hh
    have he : (2*A i*c)^2/(2*A i) = 2*A i*c^2 := by field_simp [(hA i).ne']
    exact hh.trans_eq he
  have hs : ∑ i, 2*A i*c^2 = 2*V*(q*c)^2 := by
    calc
      ∑ i, 2*A i*c^2 = (∑ i, A i)*(2*c^2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2*V*(q*c)^2 := by rw [hsum]; ring
  have heq : (∑ i, H i) = ∑ i, 2*A i*c^2 := le_antisymm
    (Finset.sum_le_sum (fun i _ => hi i)) (by rwa [hs])
  have heach := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ Finset.univ) => hi i)).mp heq
  exact fun i => heach i (Finset.mem_univ i)

end Plank.EqualityCellScaling

/-- info: 'Plank.EqualityCellScaling.curvature_eq_each' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.EqualityCellScaling.curvature_eq_each
