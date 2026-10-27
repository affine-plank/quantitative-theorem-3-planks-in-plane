/- Finite-product monotonicity controls width budgets around a cycle. -/
module
public import Plank.Convex.WidthBudgets
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.FieldSimp
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.CyclicWidthBudgets

/-- Removing the highest-degree term leaves a polynomial with nonnegative coefficients. -/
theorem prod_one_add_sub_prod_mono {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i) :
    (∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, a i ≤
      (∏ i ∈ s, (1 + b i)) - ∏ i ∈ s, b i := by
  classical
  have he (f : ι → ℝ) : (∏ i ∈ s, (1 + f i)) - ∏ i ∈ s, f i =
      ∑ t ∈ s.powerset.erase s, ∏ i ∈ t, f i := by
    rw [Finset.prod_one_add, Finset.sum_erase_eq_sub (Finset.mem_powerset.mpr (Finset.Subset.refl s))]
  rw [he a, he b]
  apply Finset.sum_le_sum
  intro t ht
  have hts := Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2
  exact Finset.prod_le_prod₀ (fun i hi => ha i (hts hi)) (fun i hi => hab i (hts hi))

/-- Pair contractions and a bound on the two products control the products of deviations from one. -/
theorem prod_sub_one_le_prod_one_sub {ι : Type*} [Fintype ι] [Nonempty ι]
    (f r : ι → ℝ) (hf : ∀ i, 1 < f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r i ≤ 1) (hcycle : (∏ i, f i) + (∏ i, r i) ≤ 2) :
    (∏ i, (f i - 1)) ≤ ∏ i, (1 - r i) := by
  have hF (i : ι) : 0 < f i - 1 := sub_pos.mpr (hf i)
  have hR (i : ι) : 0 < 1 - r i := by
    apply sub_pos.mpr
    by_contra! h
    exact (not_lt_of_ge (hpair i)) (one_lt_mul_of_lt_of_le (hf i) h)
  have hX : 0 < ∏ i, (f i - 1) := Finset.prod_pos fun i _ => hF i
  have hY : 0 < ∏ i, (1 - r i) := Finset.prod_pos fun i _ => hR i
  have hmono := prod_one_add_sub_prod_mono Finset.univ
    (fun i => r i / (1 - r i)) (fun i => 1 / (f i - 1))
    (fun i _ => div_nonneg (hr i) (hR i).le)
    (fun i _ => (div_le_div_iff₀ (hR i) (hF i)).mpr (by nlinarith only [hpair i]))
  have heR (i : ι) : 1 + r i / (1 - r i) = 1 / (1 - r i) := by
    field_simp [(hR i).ne']
    ring
  have heF (i : ι) : 1 + 1 / (f i - 1) = f i / (f i - 1) := by
    field_simp [(hF i).ne']
    ring
  simp_rw [heR, heF] at hmono
  simp only [Finset.prod_div_distrib, Finset.prod_const_one, ← sub_div] at hmono
  have hcross := (div_le_div_iff₀ hY hX).mp hmono
  have hA : 0 < (∏ i, f i) - 1 := sub_pos.mpr (by
    simpa using (Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => (zero_lt_one : (0 : ℝ) < 1))
      (fun i _ => hf i) Finset.univ_nonempty))
  have hbound : ((∏ i, f i) - 1) * (∏ i, (f i - 1)) ≤
      (1 - ∏ i, r i) * (∏ i, (f i - 1)) :=
    mul_le_mul_of_nonneg_right (by linarith only [hcycle]) hX.le
  nlinarith only [hA, hbound, hcross]

/-- Above-one coefficients propagate around a cycle because opposite edges cannot both exceed one. -/
theorem cycle_of_pair_bounds {ι : Type*} (σ : ι ≃ ι) (f r : ι → ℝ)
    (hcycle : ∀ i j, ∃ n : ℕ, (σ : ι → ι)^[n] i = j)
    (hpair : ∀ i, f i * r (σ i) ≤ 1) (hout : ∀ i, 1 < f i ∨ 1 < r i) :
    (∀ i, 1 < f i) ∨ (∀ i, 1 < r i) := by
  by_cases h : ∃ i, 1 < f i
  · obtain ⟨i, hi⟩ := h
    have hnext (j : ι) (hj : 1 < f j) : 1 < f (σ j) :=
      (hout (σ j)).resolve_right fun hr =>
        (not_lt_of_ge (hpair j)) (one_lt_mul_of_lt_of_le hj hr.le)
    left
    intro j
    obtain ⟨n, rfl⟩ := hcycle i j
    induction n with
    | zero => exact hi
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hnext _ ih
  · right
    intro i
    exact (hout i).resolve_left fun hi => h ⟨i, hi⟩

/-- A consistently oriented family forces some vertex and its two neighbors to have width at least one. -/
theorem local_width_bound_of_forward {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι ≃ ι) (w f r : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, 1 < f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r (σ i) ≤ 1)
    (hcycle : (∏ i, f i) + (∏ i, r i) ≤ 2)
    (hbudget : ∀ i, 1 ≤ w i + f i * w (σ i) + r i * w (σ.symm i)) :
    ∃ i, 1 ≤ w i + w (σ i) + w (σ.symm i) := by
  by_contra! hdef
  have hR (i : ι) : 0 < 1 - r i := by
    have hp : f (σ.symm i) * r i ≤ 1 := by simpa using hpair (σ.symm i)
    apply sub_pos.mpr
    by_contra! h
    exact (not_lt_of_ge hp) (one_lt_mul_of_lt_of_le (hf _) h)
  have hstep (i : ι) : (1 - r i) * w (σ.symm i) < (f i - 1) * w (σ i) := by
    nlinarith only [hbudget i, hdef i]
  have hwp (i : ι) : 0 < w i := by
    have hs := hstep (σ.symm i)
    rw [σ.apply_symm_apply] at hs
    exact pos_of_mul_pos_right
      ((mul_nonneg (hR _).le (hw _)).trans_lt hs) (sub_nonneg.mpr (hf _).le)
  have hprod := Finset.prod_lt_prod_of_nonempty₀
    (fun i _ => mul_pos (hR i) (hwp (σ.symm i))) (fun i _ => hstep i) Finset.univ_nonempty
  simp only [Finset.prod_mul_distrib, Equiv.prod_comp] at hprod
  have hdiff := prod_sub_one_le_prod_one_sub f (fun i => r (σ i)) hf
    (fun i => hr (σ i)) hpair (by simpa only [Equiv.prod_comp] using hcycle)
  rw [Equiv.prod_comp σ (fun i => 1 - r i)] at hdiff
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_right hdiff
    (Finset.prod_nonneg fun i _ => hw i))) hprod

/-- The two-product criterion controls a sum of three neighboring widths on any finite cycle. -/
theorem local_width_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι ≃ ι) (w f r : ι → ℝ)
    (hcycle : ∀ i j, ∃ n : ℕ, (σ : ι → ι)^[n] i = j)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r (σ i) ≤ 1)
    (hproducts : (∏ i, f i) + (∏ i, r i) ≤ 2)
    (hbudget : ∀ i, 1 ≤ w i + f i * w (σ i) + r i * w (σ.symm i)) :
    ∃ i, 1 ≤ w i + w (σ i) + w (σ.symm i) := by
  by_contra! hdef
  have hout (i : ι) : 1 < f i ∨ 1 < r i := by
    by_contra! h
    have hF := mul_le_mul_of_nonneg_right h.1 (hw (σ i))
    have hR := mul_le_mul_of_nonneg_right h.2 (hw (σ.symm i))
    nlinarith only [hbudget i, hdef i, hF, hR]
  rcases cycle_of_pair_bounds σ f r hcycle hpair hout with hF | hR
  · obtain ⟨i, hi⟩ := local_width_bound_of_forward σ w f r hw hF hr hpair hproducts hbudget
    exact (not_le_of_gt (hdef i)) hi
  · obtain ⟨i, hi⟩ := local_width_bound_of_forward σ.symm w r f hw hR hf
      (fun i => by simpa only [σ.apply_symm_apply, mul_comm] using hpair (σ.symm i))
      (by linarith only [hproducts])
      (fun i => by simpa only [Equiv.symm_symm, add_right_comm] using hbudget i)
    exact (not_le_of_gt (hdef i)) (by simpa only [Equiv.symm_symm, add_right_comm] using hi)

/-- The local bound gives the original total-width estimate for consistently oriented budgets. -/
theorem width_bound_of_forward {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι ≃ ι) (w f r : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, 1 < f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r (σ i) ≤ 1)
    (hcycle : (∏ i, f i) + (∏ i, r i) ≤ 2)
    (hlocal : ∀ i, w i + w (σ i) + w (σ.symm i) ≤ ∑ j, w j)
    (hbudget : ∀ i, 1 ≤ w i + f i * w (σ i) + r i * w (σ.symm i)) :
    1 ≤ ∑ i, w i := by
  obtain ⟨i, hi⟩ := local_width_bound_of_forward σ w f r hw hf hr hpair hcycle hbudget
  exact hi.trans (hlocal i)

/-- The two-product criterion works for budgets around any finite cycle.
The local sum hypothesis is automatic when each vertex and its two neighbors are distinct. -/
theorem width_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι ≃ ι) (w f r : ι → ℝ)
    (hcycle : ∀ i j, ∃ n : ℕ, (σ : ι → ι)^[n] i = j)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r (σ i) ≤ 1)
    (hproducts : (∏ i, f i) + (∏ i, r i) ≤ 2)
    (hlocal : ∀ i, w i + w (σ i) + w (σ.symm i) ≤ ∑ j, w j)
    (hbudget : ∀ i, 1 ≤ w i + f i * w (σ i) + r i * w (σ.symm i)) :
    1 ≤ ∑ i, w i := by
  obtain ⟨i, hi⟩ := local_width_bound σ w f r hcycle hw hf hr hpair hproducts hbudget
  exact hi.trans (hlocal i)

/-- The sum over a vertex and two distinct neighbors is bounded by the total nonnegative weight. -/
theorem local_sum_le {ι : Type*} [Fintype ι] (σ : ι ≃ ι) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hnext : ∀ i, σ i ≠ i) (hnext2 : ∀ i, σ (σ i) ≠ i)
    (i : ι) : w i + w (σ i) + w (σ.symm i) ≤ ∑ j, w j := by
  classical
  have hip : i ≠ σ.symm i := fun h => hnext i (by simpa using congrArg σ h)
  have hnp : σ i ≠ σ.symm i := fun h => hnext2 i (by simpa using congrArg σ h)
  have hsum : (∑ j ∈ ({i, σ i, σ.symm i} : Finset ι), w j) ≤ ∑ j, w j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hw j)
  simpa [hip, hnp, (hnext i).symm, add_assoc] using hsum

/-- A finite cycle of length at least three satisfies the two-product budget criterion. -/
theorem width_bound_of_distinct_neighbors {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι ≃ ι) (w f r : ι → ℝ)
    (hcycle : ∀ i j, ∃ n : ℕ, (σ : ι → ι)^[n] i = j)
    (hnext : ∀ i, σ i ≠ i) (hnext2 : ∀ i, σ (σ i) ≠ i)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r (σ i) ≤ 1)
    (hproducts : (∏ i, f i) + (∏ i, r i) ≤ 2)
    (hbudget : ∀ i, 1 ≤ w i + f i * w (σ i) + r i * w (σ.symm i)) :
    1 ≤ ∑ i, w i :=
  width_bound σ w f r hcycle hw hf hr hpair hproducts
    (local_sum_le σ w hw hnext hnext2) hbudget

end Plank.Convex.CyclicWidthBudgets

/-- info: 'Plank.Convex.CyclicWidthBudgets.local_width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CyclicWidthBudgets.local_width_bound

/-- info: 'Plank.Convex.CyclicWidthBudgets.prod_sub_one_le_prod_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CyclicWidthBudgets.prod_sub_one_le_prod_one_sub

/-- info: 'Plank.Convex.CyclicWidthBudgets.width_bound_of_distinct_neighbors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CyclicWidthBudgets.width_bound_of_distinct_neighbors
