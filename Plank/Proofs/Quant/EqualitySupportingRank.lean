/- The equality rank argument for affine square-root majorants. -/
module

public import Plank.Proofs.Quant.EqualityCellRank
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.EqualitySupportingRank

open Set
open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- One constraint for each inactive row leaves at least as many motion
dimensions as active rows. -/
theorem card_active_le_finrank_ker (S : Finset ι)
    (L : {i // i ∉ S} → E →ₗ[ℝ] ℝ)
    (hcard : Fintype.card ι ≤ Module.finrank ℝ E) :
    Fintype.card ↥S ≤ Module.finrank ℝ (LinearMap.ker (LinearMap.pi L)) := by
  classical
  let Z := LinearMap.pi L
  have hdim := Z.finrank_range_add_finrank_ker
  have hbound : Module.finrank ℝ Z.range ≤ Fintype.card {i // i ∉ S} := by
    simpa only [Module.finrank_pi] using Z.range.finrank_le
  have hcompl := Fintype.card_subtype_compl (fun i => i ∈ S)
  have hS := Fintype.card_subtype_le (fun i => i ∈ S)
  change Fintype.card {i // i ∈ S} ≤ Module.finrank ℝ Z.ker
  omega

omit [FiniteDimensional ℝ E] in
/-- Stationarity of affine powers at their touching local minimum. -/
theorem stationary_powers (b : ι → ℝ) (L : ι → E →L[ℝ] ℝ)
    (d : E →L[ℝ] ℝ) (V q : ℝ) (n : ℕ)
    (hmin : IsLocalMin (fun x : E => (∑ i, (b i+L i x)^n)-V*(q+d x)^n) 0) :
    ∀ z, (∑ i, (n : ℝ)*(b i)^(n-1)*(L i z)) = (n : ℝ)*V*q^(n-1)*d z := by
  have hpow (i) : HasFDerivAt (fun x : E => (b i+L i x)^n)
      (((n : ℝ)*(b i)^(n-1)) • L i) 0 := by
    simpa using (((L i).hasFDerivAt.const_add (b i)).pow n :
      HasFDerivAt (fun x : E => (b i+L i x)^n) _ 0)
  have hd : HasFDerivAt (fun x : E => (q+d x)^n) (((n : ℝ)*q^(n-1)) • d) 0 := by
    simpa using ((d.hasFDerivAt.const_add q).pow n :
      HasFDerivAt (fun x : E => (q+d x)^n) _ 0)
  have hzero := hmin.hasFDerivAt_eq_zero
    ((HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hpow i)).sub (hd.const_mul V))
  intro z
  have hh := congrArg (fun M : E →L[ℝ] ℝ => M z) hzero
  simpa [mul_assoc,mul_left_comm,mul_comm,sub_eq_zero] using hh

omit [FiniteDimensional ℝ E] in
/-- The square-power stationarity identity. -/
theorem stationary_majorants (b : ι → ℝ) (L : ι → E →L[ℝ] ℝ)
    (d : E →L[ℝ] ℝ) (V q : ℝ)
    (hmin : IsLocalMin (fun x : E => (∑ i, (b i+L i x)^2)-V*(q+d x)^2) 0) :
    ∀ z, (∑ i, 2*b i*(L i z)) = 2*V*q*d z := by
  simpa using stationary_powers b L d V q 2 hmin

/-- The same rank argument works for every positive integer power.
Individual affine roots need not be positive. All touching and minimum
hypotheses are explicit; this lemma supplies no geometric majorants. -/
theorem exists_proportional_direction_of_power (b : ι → ℝ) (L : ι → E →L[ℝ] ℝ)
    (d : E →L[ℝ] ℝ) (V q : ℝ) (hV : 0 < V) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (hsum : ∑ i, (b i)^n = V*q^n)
    (hmin : IsLocalMin (fun x : E => (∑ i, (b i+L i x)^n)-V*(q+d x)^n) 0)
    (hcard : Fintype.card ι ≤ Module.finrank ℝ E) :
    ∃ z : E, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ d z = q*c ∧ ∀ i, L i z = b i*c := by
  have hp (x : ℝ) : x^(n-1)*x = x^n := by
    rw [← pow_succ,Nat.sub_add_cancel hn]
  apply EqualityCellRank.exists_weighted_proportional_direction
    b (fun i => (n : ℝ)*(b i)^(n-1)) (fun i => (L i).toLinearMap) d.toLinearMap
    q ((n : ℝ)*V*q^(n-1)) hq.ne' (by positivity) ?_
    (stationary_powers b L d V q n hmin) hcard
  simp_rw [mul_assoc,hp,← Finset.mul_sum,hsum]

/-- A supporting-majorant minimum has a common proportional direction.
No area chart or Hessian is required. -/
theorem exists_proportional_direction (b : ι → ℝ) (L : ι → E →L[ℝ] ℝ)
    (d : E →L[ℝ] ℝ) (V q : ℝ) (hV : 0 < V) (hq : 0 < q)
    (hsum : ∑ i, (b i)^2 = V*q^2)
    (hmin : IsLocalMin (fun x : E => (∑ i, (b i+L i x)^2)-V*(q+d x)^2) 0)
    (hcard : Fintype.card ι ≤ Module.finrank ℝ E) :
    ∃ z : E, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ d z = q*c ∧ ∀ i, L i z = b i*c :=
  exists_proportional_direction_of_power b L d V q hV hq 2 (by decide) hsum hmin hcard

end Plank.EqualitySupportingRank

/-- info: 'Plank.EqualitySupportingRank.exists_proportional_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.EqualitySupportingRank.exists_proportional_direction
