/- The equality alternative in the cell-rank argument. Geometric curvature
and actual-area identities remain explicit inputs in this algebraic module. -/
module

public import Plank.Proofs.Quant.HomogeneousCellRank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.EqualityCellRank

open scoped BigOperators

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E] [Fintype ι]

/-- A weighted stationarity identity gives a common proportional direction.
The weights and target coordinates may have either sign or vanish. -/
theorem exists_weighted_proportional_direction (b w : ι → ℝ)
    (L : ι → E →ₗ[ℝ] ℝ) (d : E →ₗ[ℝ] ℝ) (q a : ℝ)
    (hq : q ≠ 0) (ha : a ≠ 0)
    (hsum : ∑ i, w i*b i = a*q) (hder : ∀ z, ∑ i, w i*L i z = a*d z)
    (hcard : Fintype.card ι ≤ Module.finrank ℝ E) :
    ∃ z : E, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ d z = q*c ∧ ∀ i, L i z = b i*c := by
  classical
  let G : E →ₗ[ℝ] (ι → ℝ) := LinearMap.pi L
  by_cases hinj : Function.Injective G
  · have hdim : Module.finrank ℝ E = Module.finrank ℝ (ι → ℝ) := by
      apply Nat.le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj)
      simpa only [Module.finrank_pi] using hcard
    obtain ⟨z,hz⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj b
    have hL (i) : L i z = b i := congrFun hz i
    have hd : d z = q := mul_left_cancel₀ ha (by
      rw [← hder]
      simpa only [hL] using hsum)
    have hzne : z ≠ 0 := by
      intro hz0
      exact hq (hd.symm.trans (by rw [hz0,map_zero]))
    exact ⟨z,hzne,1,zero_le_one,by simpa only [mul_one] using hd,
      fun i => by simpa only [mul_one] using hL i⟩
  · have hex : ∃ z : E, z ≠ 0 ∧ ∀ i, L i z = 0 := by
      by_contra hn
      apply hinj
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro z hz
      by_contra hzne
      exact hn ⟨z,hzne,fun i => congrFun hz i⟩
    obtain ⟨z,hzne,hL⟩ := hex
    have hd : d z = 0 := by
      have hh := hder z
      simp only [hL,mul_zero,Finset.sum_const_zero] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left ha
    exact ⟨z,hzne,0,le_rfl,by simpa only [mul_zero] using hd,
      fun i => by simpa only [mul_zero] using hL i⟩

/-- At equality the nonnegative margin curvature has a nonzero zero
direction whenever there are no more positive cells than parameters.
The direction can preserve or increase the affine deficit. -/
theorem exists_flat_direction (A : ι → ℝ) (g : ι → E →ₗ[ℝ] ℝ) (H : ι → E → ℝ)
    (d : E →ₗ[ℝ] ℝ) (V q : ℝ) (hV : 0 < V) (hq : 0 < q)
    (hA : ∀ i, 0 < A i) (hsum : ∑ i, A i = V*q^2)
    (hder : ∀ z, ∑ i, g i z = 2*V*q*d z)
    (hcurv : ∀ i z, H i z ≤ (g i z)^2/(2*A i))
    (hmargin : ∀ z, 2*V*(d z)^2 ≤ ∑ i, H i z)
    (hcard : Fintype.card ι ≤ Module.finrank ℝ E) :
    ∃ z : E, z ≠ 0 ∧ 0 ≤ d z ∧ ∑ i, H i z = 2*V*(d z)^2 := by
  obtain ⟨z,hzne,c,hc,hd,hg⟩ := exists_weighted_proportional_direction
    A (fun _ => 1) g d (q/2) (2*V*q) (by positivity) (by positivity)
    (by simpa only [one_mul] using hsum.trans (by ring))
    (by simpa only [one_mul] using hder) hcard
  have hle : (∑ i, H i z) ≤ (∑ i, A i)*(c^2/2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hh := hcurv i z
    rw [hg] at hh
    have he : (A i*c)^2/(2*A i) = A i*(c^2/2) := by field_simp [(hA i).ne']
    exact hh.trans_eq he
  refine ⟨z,hzne,by rw [hd]; positivity,le_antisymm ?_ (hmargin z)⟩
  rw [hsum] at hle
  rw [hd]
  nlinarith only [hle]

end Plank.EqualityCellRank

/-- info: 'Plank.EqualityCellRank.exists_flat_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.EqualityCellRank.exists_flat_direction
