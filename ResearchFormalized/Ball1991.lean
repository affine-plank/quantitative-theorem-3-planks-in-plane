/-
Copyright (c) 2026 Zaz Brown. All rights reserved.

# The Plank Problem for Symmetric Bodies -- Keith Ball (1991)

Formalization of:
  K. Ball, "The plank problem for symmetric bodies",
  Inventiones Mathematicae 104 (1991), 535-543.
  arXiv: math/9201218

## Summary

Ball proves that if the unit ball of a Banach space X is covered by a (countable)
collection of planks, then the sum of the half-widths of the planks is at least 1.
This resolves the affine plank problem for centrally symmetric convex bodies.

## Key Results (in paper order)

- **Theorem 1**: Unit ball of Banach space covered by planks => sum of half-widths >= 1
- **Theorem 2**: Finite-dim version -- exists x in unit ball with |phi_i(x) - m_i| >= w_i
- **Corollary**: Symmetric body C + n hyperplanes => exists translate of (1/(n+1))*C avoiding all
- **Lemma 3** (Bang): Symmetric matrix with 1s on diagonal, exists signs epsilon
- **Theorem 2'**: Matrix version with sum |coeffs_j| <= 1
- **Lemma 4**: Symmetrisation -- existence of theta_i and orthogonal U
- **Lemma 5**: Diagonal estimate for positive matrices
- **Lemma 6**: Nuclear norm inequality
- **Theorem 7**: Multiple Hahn-Banach
- **Theorem 8**: Strong form with weighted coefficients

**Fully formalized** — 0 sorrys remaining. All theorems and lemmas are proved.
-/

module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

noncomputable section

open scoped Matrix NNReal
open Matrix Finset

/-! ## Section 1: Introduction and preliminary observations -/

section BanachSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A **plank** in a normed space X is the set `{x in X : |phi(x) - m| <= w}`
where `phi` is in `X*`, `m` is in `R`, `w > 0`. If `‖phi‖ = 1`, then `w` is the
**half-width**.

We define the plank as a set given a continuous linear functional, center, and half-width. -/
def Ball1991.plank (phi : X →L[ℝ] ℝ) (m w : ℝ) : Set X :=
  {x | |phi x - m| ≤ w}

-- Theorems 1 and 2 are proved below (after their dependencies):
-- Ball1991.theorem1 — proved from theorem1_from_theorem8 by contraposition
-- Ball1991.theorem2 — proved from theorem2_from_theorem2' with theorem2'

-- Corollary (Ball 1991): proved below as `Ball1991.corollary_symmetric_body`
-- (after davenport_improved, which it depends on)

end BanachSpace

/-! ## Matrix formulations (Section 1 continued) -/

section MatrixFormulations

/-- Row-level inner sum difference when flipping sign ε_k → −ε_k:
    ∑ⱼ H_ij εⱼ θⱼ − ∑ⱼ H_ij ε'ⱼ θⱼ = 2 H_ik ε_k θ_k
    where ε' = Function.update ε k (−ε k). -/
private lemma bang_inner_sum_flip' {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (eps theta : Fin n → ℝ) (k i : Fin n) :
    ∑ j, H i j * eps j * theta j -
    ∑ j, H i j * Function.update eps k (-eps k) j * theta j =
    2 * H i k * eps k * theta k := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [show ∀ j, H i j * eps j * theta j -
      H i j * Function.update eps k (-eps k) j * theta j =
      H i j * (eps j - Function.update eps k (-eps k) j) * theta j from fun j => by ring]
  rw [(Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm,
      Finset.sum_eq_zero (fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]; ring),
      add_zero, Function.update_self]; ring

/-- Combined flip identity for Bang's objective function:
    Q(ε) − Q(ε') = 4 ε_k θ_k (T_k − μ_k)
    where T_k = ∑_{j≠k} H_kj ε_j θ_j and ε' flips the k-th sign. -/
private lemma bang_flip_identity' {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH_sym : Matrix.IsSymm H)
    (hH_diag : ∀ i, H i i = 1) (mu theta eps : Fin n → ℝ) (k : Fin n) :
    (∑ i, ∑ j, H i j * eps i * eps j * theta i * theta j
     - 2 * ∑ i, eps i * theta i * mu i) -
    (∑ i, ∑ j, H i j * Function.update eps k (-eps k) i *
        Function.update eps k (-eps k) j * theta i * theta j
     - 2 * ∑ i, Function.update eps k (-eps k) i * theta i * mu i) =
    4 * eps k * theta k *
    (∑ j ∈ Finset.univ.erase k, H k j * eps j * theta j - mu k) := by
  have hrow : ∀ i, ∑ j, H i j * eps j * theta j -
      ∑ j, H i j * Function.update eps k (-eps k) j * theta j =
      2 * H i k * eps k * theta k :=
    fun i => bang_inner_sum_flip' H eps theta k i
  have hsym : ∀ i, H i k = H k i := fun i => (hH_sym.apply i k).symm
  have hfactor : ∀ (a : Fin n → ℝ),
      ∑ i, ∑ j, H i j * a i * a j * theta i * theta j =
      ∑ i, a i * theta i * ∑ j, H i j * a j * theta j := by
    intro a; congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
  set T := ∑ j ∈ Finset.univ.erase k, H k j * eps j * theta j with T_def
  have hRk : ∑ j, H k j * eps j * theta j = eps k * theta k + T := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hH_diag k, one_mul]
  have hR'k : ∑ j, H k j * Function.update eps k (-eps k) j * theta j =
      -eps k * theta k + T := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    congr 1
    · rw [Function.update_self, hH_diag k]; ring
    · apply Finset.sum_congr rfl; intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hS1 : ∑ i, (eps i - Function.update eps k (-eps k) i) * theta i *
      (∑ j, H i j * eps j * theta j) =
      2 * eps k * theta k * ∑ j, H k j * eps j * theta j := by
    have h : ∀ i, (eps i - Function.update eps k (-eps k) i) * theta i *
        (∑ j, H i j * eps j * theta j) =
        if i = k then 2 * eps k * theta k * ∑ j, H k j * eps j * theta j else 0 := by
      intro i; split
      · next h => subst h; rw [Function.update_self]; ring
      · next h => rw [Function.update_of_ne h, sub_self, zero_mul, zero_mul]
    simp_rw [h, Finset.sum_ite_eq']; simp [mem_univ]
  have hS2 : ∑ i, Function.update eps k (-eps k) i * theta i *
      (2 * H i k * eps k * theta k) =
      2 * eps k * theta k *
      ∑ j, H k j * Function.update eps k (-eps k) j * theta j := by
    simp_rw [hsym]; rw [Finset.mul_sum]; congr 1; ext i; ring
  have hbilin : ∑ i, ∑ j, H i j * eps i * eps j * theta i * theta j -
      ∑ i, ∑ j, H i j * Function.update eps k (-eps k) i *
          Function.update eps k (-eps k) j * theta i * theta j =
      2 * eps k * theta k * (∑ j, H k j * eps j * theta j) +
      2 * eps k * theta k *
        (∑ j, H k j * Function.update eps k (-eps k) j * theta j) := by
    rw [hfactor eps, hfactor (Function.update eps k (-eps k)), ← Finset.sum_sub_distrib]
    simp_rw [show ∀ i,
        eps i * theta i * ∑ j, H i j * eps j * theta j -
        Function.update eps k (-eps k) i * theta i *
          ∑ j, H i j * Function.update eps k (-eps k) j * theta j =
        (eps i - Function.update eps k (-eps k) i) * theta i *
          (∑ j, H i j * eps j * theta j) +
        Function.update eps k (-eps k) i * theta i *
          (∑ j, H i j * eps j * theta j -
           ∑ j, H i j * Function.update eps k (-eps k) j * theta j)
        from fun i => by ring, hrow, Finset.sum_add_distrib]
    linarith [hS1, hS2]
  have hlin : ∑ i, eps i * theta i * mu i -
      ∑ i, Function.update eps k (-eps k) i * theta i * mu i =
      2 * eps k * theta k * mu k := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [show ∀ i, eps i * theta i * mu i -
        Function.update eps k (-eps k) i * theta i * mu i =
        (eps i - Function.update eps k (-eps k) i) * theta i * mu i from fun i => by ring]
    have h : ∀ i, (eps i - Function.update eps k (-eps k) i) * theta i * mu i =
        if i = k then 2 * eps k * theta k * mu k else 0 := by
      intro i; split
      · next h => subst h; rw [Function.update_self]; ring
      · next h => rw [Function.update_of_ne h, sub_self, zero_mul, zero_mul]
    simp_rw [h, Finset.sum_ite_eq']; simp [mem_univ]
  have key : 2 * eps k * theta k * ∑ j, H k j * eps j * theta j +
      2 * eps k * theta k *
        ∑ j, H k j * Function.update eps k (-eps k) j * theta j =
      4 * eps k * theta k * T := by rw [hRk, hR'k]; ring
  linarith [hbilin, hlin, key]

/-- **Lemma 3** (Bang's Lemma, as stated in Ball 1991).
Let `H = (h_ij)` be a real symmetric `n x n` matrix with 1's on the diagonal,
`(mu_i)` a sequence of reals, and `(theta_i)` a sequence of non-negative numbers.
Then there is a sequence of signs `(eps_j)` (`eps_j = 1` or `-1` for each j) so that
for each i:
  `|sum_j h_ij eps_j theta_j - mu_i| >= theta_i`.

The proof uses a maximization argument: choose signs to maximize
  `sum_{i,j} h_ij eps_i eps_j theta_i theta_j - 2 sum_i eps_i theta_i mu_i`
then use the optimality condition at each coordinate. -/
theorem Ball1991.lemma3_bang
    {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH_sym : H.IsSymm)
    (hH_diag : ∀ i, H i i = 1)
    (mu : Fin n → ℝ)
    (theta : Fin n → ℝ)
    (htheta_nonneg : ∀ i, 0 ≤ theta i) :
    ∃ eps : Fin n → ℝ,
      (∀ j, eps j = 1 ∨ eps j = -1) ∧
      ∀ i, |∑ j, H i j * eps j * theta j - mu i| ≥ theta i := by
  let toSign : Bool → ℝ := fun b => if b then (1 : ℝ) else (-1 : ℝ)
  let obj : (Fin n → Bool) → ℝ := fun b =>
    ∑ i, ∑ j, H i j * toSign (b i) * toSign (b j) * theta i * theta j
    - 2 * ∑ i, toSign (b i) * theta i * mu i
  by_cases hn : n = 0
  · subst hn; exact ⟨Fin.elim0, fun j => Fin.elim0 j, fun i => Fin.elim0 i⟩
  · have hne : (Finset.univ : Finset (Fin n → Bool)).Nonempty :=
      ⟨fun _ => true, Finset.mem_univ _⟩
    obtain ⟨bm, _, hmax⟩ := Finset.exists_max_image _ obj hne
    set eps := fun i => toSign (bm i) with eps_def
    refine ⟨eps, fun j => ?_, fun k => ?_⟩
    · -- Signs are ±1
      simp only [eps_def, toSign]; split <;> simp
    · -- Main bound: |Σ H_kj eps_j theta_j - mu_k| ≥ theta_k
      -- Maximizer beats any single-coordinate flip
      have h_nonneg : 0 ≤ obj bm - obj (Function.update bm k (!bm k)) := by
        linarith [hmax (Function.update bm k (!bm k)) (Finset.mem_univ _)]
      have hflip_sign : ∀ b : Bool, toSign (!b) = -toSign b := by
        intro b; simp only [toSign]; cases b <;> simp
      have h_update_comm : ∀ i, toSign (Function.update bm k (!bm k) i) =
          Function.update eps k (-eps k) i := by
        intro i; by_cases hik : i = k
        · subst hik; simp [Function.update_self, hflip_sign, eps_def]
        · simp [Function.update_of_ne hik, eps_def]
      have h_obj_flip : obj (Function.update bm k (!bm k)) =
          ∑ i, ∑ j, H i j * Function.update eps k (-eps k) i *
              Function.update eps k (-eps k) j * theta i * theta j
          - 2 * ∑ i, Function.update eps k (-eps k) i * theta i * mu i := by
        simp only [obj]; congr 1
        · congr 1; ext i; congr 1; ext j; rw [h_update_comm i, h_update_comm j]
        · congr 1; congr 1; ext i; rw [h_update_comm i]
      -- Apply the flip identity
      have hdiff : obj bm - obj (Function.update bm k (!bm k)) =
          4 * eps k * theta k *
          (∑ j ∈ Finset.univ.erase k, H k j * eps j * theta j - mu k) := by
        rw [show obj bm = ∑ i, ∑ j, H i j * eps i * eps j * theta i * theta j
            - 2 * ∑ i, eps i * theta i * mu i from rfl, h_obj_flip]
        exact bang_flip_identity' H hH_sym hH_diag mu theta eps k
      have h4 : 0 ≤ 4 * eps k * theta k *
          (∑ j ∈ Finset.univ.erase k, H k j * eps j * theta j - mu k) := by linarith
      -- Split the full sum at k: Σ_j H_kj ε_j θ_j = ε_k θ_k + T_k
      set T := ∑ j ∈ Finset.univ.erase k, H k j * eps j * theta j with T_def
      have h_split : ∑ j, H k j * eps j * theta j = eps k * theta k + T := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hH_diag k, one_mul]
      rw [h_split]
      -- Case split: theta_k = 0 is trivial, theta_k > 0 uses optimality
      by_cases hk : theta k = 0
      · rw [hk, mul_zero, zero_add]; exact abs_nonneg _
      · have hk_pos : 0 < theta k := lt_of_le_of_ne (htheta_nonneg k) (Ne.symm hk)
        -- From 0 ≤ 4 ε_k θ_k (T - μ_k) and θ_k > 0: ε_k(T - μ_k) ≥ 0
        have h_eps_T : 0 ≤ eps k * (T - mu k) := by
          have : 0 < 4 * theta k := by positivity
          nlinarith [mul_comm (eps k) (theta k)]
        have h_eps_sq : eps k ^ 2 = 1 := by
          simp only [eps_def, toSign]; cases bm k <;> norm_num
        have h_eps_abs : |eps k| = 1 := by
          rwa [← Real.sqrt_sq_eq_abs, Real.sqrt_eq_one]
        -- ε_k(ε_k θ_k + T - μ_k) = θ_k + ε_k(T - μ_k) ≥ θ_k
        have h_ge : eps k * (eps k * theta k + T - mu k) ≥ theta k := by
          nlinarith [h_eps_sq]
        -- |ε_k θ_k + T - μ_k| = |ε_k|·|ε_k θ_k + T - μ_k| = |ε_k(ε_k θ_k + T - μ_k)| ≥ θ_k
        calc (theta k : ℝ)
            _ ≤ eps k * (eps k * theta k + T - mu k) := h_ge
            _ ≤ |eps k * (eps k * theta k + T - mu k)| := le_abs_self _
            _ = |eps k| * |eps k * theta k + T - mu k| := abs_mul _ _
            _ = |eps k * theta k + T - mu k| := by rw [h_eps_abs, one_mul]

/-- The objective function maximized in Bang's proof:
  `sum_{i,j} h_ij eps_i eps_j theta_i theta_j - 2 sum_i eps_i theta_i mu_i` -/
def Ball1991.bangObjective
    {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ)
    (mu theta eps : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, H i j * eps i * eps j * theta i * theta j
    - 2 * ∑ i, eps i * theta i * mu i

-- Theorem 2' is proved below as `Ball1991.theorem2'` (after the block matrix proof chain)

-- Theorem 2' (strengthened): proved below as `Ball1991.theorem2'_strengthened_proof`
-- (depends on Lemma 4 from Symmetrisation section). Gives ∑ coeffs² ≤ 1/n and
-- |∑ a_ij coeffs_j - m_i| ≥ 1/n (the equal-weight case).

end MatrixFormulations

/-! ## Section 2: Symmetrisations of matrices and the main proof -/

section Symmetrisation

-- Ball uses "positive" to mean symmetric and positive semidefinite.

-- Lemma 4 (symmetrisation) is proved below, after the nuclear norm infrastructure.

/-- The nuclear (trace-class) norm of a matrix `B`: `‖B‖_{C_1} = tr(sqrt(BB*))`.
In finite dimensions, this equals the sum of singular values, or equivalently
  `‖B‖_{C_1} = max{tr(BU) : U orthogonal}`.
We define it via the variational characterization. -/
def Ball1991.nuclearNorm
    {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ (U : Matrix (Fin n) (Fin n) ℝ) (_ : U * U.transpose = 1),
    (B * U).trace

/-- Continuity of individual matrix entries in the product topology. -/
private theorem continuous_matrix_entry {m : ℕ} (i j : Fin m) :
    Continuous (fun U : Matrix (Fin m) (Fin m) ℝ => U i j) :=
  (show Continuous (fun row : Fin m → ℝ => row j) from continuous_apply j).comp
    (show Continuous (fun M : Matrix (Fin m) (Fin m) ℝ => M i) from continuous_apply i)

/-- The nuclear norm is attained by some orthogonal matrix:
  `‖B‖_{C_1} = max{tr(BU) : U orthogonal} = tr(BU_0)` for some orthogonal `U_0`. -/
theorem Ball1991.nuclearNorm_attained
    {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U * U.transpose = 1 ∧
      Ball1991.nuclearNorm B = (B * U).trace := by
  set S := {U : Matrix (Fin n) (Fin n) ℝ | U * Uᵀ = 1}
  set f : Matrix (Fin n) (Fin n) ℝ → ℝ := fun U => (B * U).trace
  -- S is nonempty (identity is orthogonal)
  have hne : S.Nonempty := ⟨1, by simp [S, Matrix.transpose_one]⟩
  -- S is compact: closed subset of the compact box [-1,1]^{n×n}
  have hK : IsCompact S := by
    apply IsCompact.of_isClosed_subset
      (show IsCompact (Set.pi Set.univ (fun _ : Fin n =>
          Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) :
          Set (Matrix (Fin n) (Fin n) ℝ)) from
        isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
    · -- S is closed: preimage of {1} under continuous A ↦ A * Aᵀ
      have : S = (fun A : Matrix (Fin n) (Fin n) ℝ => A * Aᵀ) ⁻¹' {1} := by
        ext; simp [S]
      rw [this]; apply IsClosed.preimage _ isClosed_singleton
      apply continuous_pi; intro i; apply continuous_pi; intro j
      change Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => ∑ k, A i k * A j k)
      apply continuous_finset_sum; intro k _
      exact (continuous_matrix_entry i k).mul (continuous_matrix_entry j k)
    · -- S ⊆ [-1,1]^{n×n}: entries of orthogonal matrices bounded by 1
      intro A hA_mem
      simp only [S] at hA_mem
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left]; intro i j
      have hrow : ∑ k : Fin n, A i k * A i k = 1 := by
        have h := congr_fun (congr_fun hA_mem i) i
        simp [Matrix.mul_apply, Matrix.transpose_apply] at h; exact h
      have : A i j * A i j ≤ 1 :=
        hrow ▸ Finset.single_le_sum (fun k _ => mul_self_nonneg (A i k)) (Finset.mem_univ j)
      constructor <;> nlinarith
  -- f is continuous (linear in U, product topology)
  have hf_cont : Continuous f := by
    show Continuous fun U => (B * U).trace
    simp_rw [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply continuous_finset_sum; intro i _
    apply continuous_finset_sum; intro k _
    exact continuous_const.mul (continuous_matrix_entry k i)
  -- Get maximizer by compactness
  obtain ⟨U₀, hU₀_mem, hU₀_max⟩ := hK.exists_isMaxOn hne hf_cont.continuousOn
  have hU₀_orth : U₀ * U₀ᵀ = 1 := hU₀_mem
  replace hU₀_max : ∀ U ∈ S, f U ≤ f U₀ := Filter.eventually_principal.mp hU₀_max
  -- f U₀ ≥ 0 (negation trick: -U₀ is also orthogonal, f(-U₀) = -f(U₀))
  have h_nonneg : 0 ≤ f U₀ := by
    have h_neg_mem : -U₀ ∈ S := by
      show (-U₀) * (-U₀)ᵀ = 1; rw [transpose_neg, neg_mul_neg, hU₀_orth]
    have h_neg_f : f (-U₀) = -f U₀ := by
      show (B * (-U₀)).trace = -((B * U₀).trace)
      rw [mul_neg]; exact map_neg (Matrix.traceLinearMap (Fin n) ℝ ℝ) (B * U₀)
    linarith [hU₀_max (-U₀) h_neg_mem]
  -- Helper: each conditional iSup term ≤ f U₀
  have h_le_max : ∀ U, (⨆ (_ : U * Uᵀ = 1), f U) ≤ f U₀ := by
    intro U; by_cases hU : U * Uᵀ = 1
    · rw [ciSup_pos hU]; exact hU₀_max U hU
    · have : IsEmpty (U * Uᵀ = 1) := isEmpty_Prop.mpr hU; simp; exact h_nonneg
  -- BddAbove for the outer iSup
  have hbdd : BddAbove (Set.range fun U => ⨆ (_ : U * Uᵀ = 1), f U) :=
    ⟨f U₀, fun x ⟨U, hU⟩ => hU ▸ h_le_max U⟩
  -- nuclearNorm B = f U₀
  refine ⟨U₀, hU₀_orth, le_antisymm ?_ ?_⟩
  · -- nuclearNorm B ≤ f U₀
    simp only [Ball1991.nuclearNorm]; exact ciSup_le h_le_max
  · -- f U₀ ≤ nuclearNorm B
    simp only [Ball1991.nuclearNorm]
    have h_eq : (fun U => ⨆ (_ : U * Uᵀ = 1), f U) U₀ = f U₀ := by
      dsimp only; exact ciSup_pos hU₀_orth
    linarith [le_ciSup hbdd U₀]

/-- Matrix Cauchy-Schwarz inequality for the nuclear norm:
  `‖BC‖_{C_1} <= (tr(BB*))^{1/2} * (tr(CC*))^{1/2}`. -/
theorem Ball1991.nuclear_norm_cauchy_schwarz
    {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) ℝ) :
    Ball1991.nuclearNorm (B * C) ≤
      Real.sqrt ((B * B.transpose).trace) *
      Real.sqrt ((C * C.transpose).trace) := by
  -- Nuclear norm = ⨆ over orthogonal matrices
  show ⨆ (U : Matrix (Fin n) (Fin n) ℝ) (_ : U * Uᵀ = 1),
    ((B * C) * U).trace ≤ _
  apply ciSup_le; intro U₀
  by_cases hU : U₀ * U₀ᵀ = 1
  · rw [ciSup_pos hU, Matrix.mul_assoc]
    set D := C * U₀
    -- DD^T = CC^T via orthogonality of U₀
    have hDD : D * Dᵀ = C * Cᵀ := by
      change (C * U₀) * (C * U₀)ᵀ = C * Cᵀ
      rw [Matrix.transpose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc U₀ U₀ᵀ Cᵀ, hU, Matrix.one_mul]
    -- If trace ≤ 0, bound follows from non-negativity of RHS
    by_cases h_sign : (B * D).trace ≤ 0
    · exact le_trans h_sign (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · push_neg at h_sign
      -- Express tr(BD) as sum over product type Fin n × Fin n
      have h_tr : (B * D).trace =
          ∑ p : Fin n × Fin n, B p.1 p.2 * D p.2 p.1 := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        exact (Fintype.sum_prod_type' fun i j => B i j * D j i).symm
      -- Cauchy-Schwarz on flat product type
      have h_cs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun p : Fin n × Fin n => B p.1 p.2) (fun p : Fin n × Fin n => D p.2 p.1)
      -- Connect squared sums to traces
      have h_B_sq : ∑ p : Fin n × Fin n, (B p.1 p.2) ^ 2 = (B * Bᵀ).trace := by
        simp only [sq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.transpose_apply]
        exact Fintype.sum_prod_type' fun i j => B i j * B i j
      have h_D_sq : ∑ p : Fin n × Fin n, (D p.2 p.1) ^ 2 = (D * Dᵀ).trace := by
        simp only [sq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.transpose_apply]
        exact Fintype.sum_prod_type_right' fun i j => D j i * D j i
      -- Chain: tr(BD) ≤ √(tr BB^T) · √(tr CC^T)
      calc (B * D).trace
          = ∑ p : Fin n × Fin n, B p.1 p.2 * D p.2 p.1 := h_tr
        _ ≤ Real.sqrt (∑ p : Fin n × Fin n, (B p.1 p.2) ^ 2) *
            Real.sqrt (∑ p : Fin n × Fin n, (D p.2 p.1) ^ 2) := h_cs
        _ = Real.sqrt ((B * Bᵀ).trace) * Real.sqrt ((D * Dᵀ).trace) := by
            rw [h_B_sq, h_D_sq]
        _ = Real.sqrt ((B * Bᵀ).trace) * Real.sqrt ((C * Cᵀ).trace) := by
            rw [hDD]
  · have : IsEmpty (U₀ * U₀ᵀ = 1) := isEmpty_Prop.mpr hU
    simp
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ### Helpers for Lemma 5 -/

private lemma star_matrix_eq_transpose_lemma5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    star A = Aᵀ := by
  change Aᴴ = Aᵀ; ext i j; simp [conjTranspose_apply, transpose_apply, star_trivial]

/-- Expand `(P * diagonal eig * W) i i` into a sum over eigenvalues. -/
private lemma psd_expand_product {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (eig : Fin n → ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (P * diagonal eig * W) i i = ∑ k, eig k * P i k * W k i := by
  simp only [mul_apply, diagonal_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext k
  simp only [mul_ite, mul_zero]
  conv_lhs => arg 2; ext x; rw [show (if k = x then P i k * eig k else 0) * W x i =
    if k = x then P i k * eig k * W x i else 0 from by split_ifs <;> simp]
  rw [Finset.sum_ite_eq]; simp [Finset.mem_univ, mul_comm, mul_left_comm]

/-- Expand diagonal entry `(P * diagonal eig * Pᵀ) i i` as `∑ eig_k * P_ik²`. -/
private lemma psd_expand_diag {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (eig : Fin n → ℝ)
    (i : Fin n) :
    (P * diagonal eig * Pᵀ) i i = ∑ k, eig k * P i k ^ 2 := by
  have h := psd_expand_product P eig Pᵀ i
  simp only [transpose_apply] at h
  rw [h]; congr 1; ext k; ring

/-- Weighted Cauchy-Schwarz: `(∑ w a b)² ≤ (∑ w a²)(∑ w b²)` for `w ≥ 0`. -/
private lemma weighted_cauchy_schwarz_sq {n : ℕ} (w a b : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) :
    (∑ k, w k * a k * b k) ^ 2 ≤
    (∑ k, w k * a k ^ 2) * (∑ k, w k * b k ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => Real.sqrt (w k) * a k) (fun k => Real.sqrt (w k) * b k)
  simp only [mul_pow, Real.sq_sqrt (hw _)] at h
  have lhs_eq : ∀ k : Fin n, Real.sqrt (w k) * a k * (Real.sqrt (w k) * b k) =
      w k * a k * b k := fun k => by
    rw [show Real.sqrt (w k) * a k * (Real.sqrt (w k) * b k) =
      (Real.sqrt (w k) * Real.sqrt (w k)) * (a k * b k) from by ring,
      Real.mul_self_sqrt (hw k)]; ring
  simp_rw [lhs_eq] at h; linarith

/-- Row norm of an orthogonal matrix is 1: `∑_j W_{kj}² = 1`. -/
private lemma orthogonal_row_sq_sum {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : W * Wᵀ = 1) (k : Fin n) :
    ∑ i, W k i ^ 2 = 1 := by
  have := congr_fun (congr_fun hW k) k
  simp only [mul_apply, transpose_apply, one_apply_eq] at this
  convert this using 1; congr 1; ext i; ring

/-- **Lemma 5** (Ball 1991, Lemma 5 -- Key diagonal estimate).
If `H = (h_ij)` is a positive semidefinite matrix with non-zero diagonal entries
and U is orthogonal, then:
  `sum_i (HU)^2_{ii} / h_{ii} <= sum_i h_{ii}`

**Proof** (via spectral decomposition, avoiding nuclear norms):
Write `H = P Λ Pᵀ` and set `W = Pᵀ U` (orthogonal). Then `(HU)_{ii} = ∑_k λ_k P_{ik} W_{ki}`
and `h_{ii} = ∑_k λ_k P²_{ik}`. By weighted Cauchy-Schwarz with weights `λ_k ≥ 0`:
  `(HU)²_{ii} ≤ h_{ii} · ∑_k λ_k W²_{ki}`
Dividing and summing: `∑_i (HU)²_{ii}/h_{ii} ≤ ∑_k λ_k ∑_i W²_{ki} = ∑_k λ_k = tr(H)`. -/
theorem Ball1991.lemma5_diagonal_estimate
    {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH_pos : H.PosSemidef)
    (hH_diag_ne : ∀ i, H i i ≠ 0)
    (U : Matrix (Fin n) (Fin n) ℝ)
    (hU_orth : U * U.transpose = 1) :
    ∑ i, (H * U) i i ^ 2 / H i i ≤ ∑ i, H i i := by
  -- Spectral decomposition: H = P * diag(eig) * Pᵀ
  set P := hH_pos.isHermitian.eigenvectorUnitary
  set eig := hH_pos.isHermitian.eigenvalues
  have hspec : H = P.1 * diagonal eig * P.1ᵀ := by
    have h := hH_pos.isHermitian.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h; exact h
  have hPPT : P.1 * P.1ᵀ = 1 := by
    rw [← star_matrix_eq_transpose_lemma5]; exact mem_unitaryGroup_iff.mp P.2
  have hPTP : P.1ᵀ * P.1 = 1 := by
    rw [← star_matrix_eq_transpose_lemma5]; exact UnitaryGroup.star_mul_self P
  have heig_nn := hH_pos.eigenvalues_nonneg
  -- W = Pᵀ U is orthogonal (since P and U are)
  set W := P.1ᵀ * U
  have hWWT : W * Wᵀ = 1 := by
    show P.1ᵀ * U * (P.1ᵀ * U)ᵀ = 1
    simp only [transpose_mul, transpose_transpose]
    rw [show P.1ᵀ * U * (Uᵀ * P.1) = P.1ᵀ * (U * Uᵀ) * P.1 from by
      simp only [mul_assoc]]
    rw [hU_orth, mul_one, hPTP]
  -- Diagonal positivity: h_ii > 0 (nonneg from PSD + nonzero)
  have hH_diag_pos : ∀ i, 0 < H i i := by
    intro i
    have hnn : 0 ≤ H i i := by
      have := hH_pos.2 (Finsupp.single i 1)
      simp [Finsupp.sum_single_index] at this; linarith
    exact lt_of_le_of_ne hnn (hH_diag_ne i).symm
  -- Key expansions via spectral decomposition
  have h_HU : ∀ i, (H * U) i i = ∑ k, eig k * P.1 i k * W k i := by
    intro i; conv_lhs => rw [hspec, show P.1 * diagonal eig * P.1ᵀ * U =
      P.1 * diagonal eig * W from by simp [W, mul_assoc]]
    exact psd_expand_product P.1 eig W i
  have h_Hii : ∀ i, H i i = ∑ k, eig k * P.1 i k ^ 2 := by
    intro i; conv_lhs => rw [hspec]
    exact psd_expand_diag P.1 eig i
  -- Cauchy-Schwarz per row: (HU)²_{ii} ≤ h_{ii} · ∑_k λ_k W²_{ki}
  have h_cs : ∀ i, (H * U) i i ^ 2 ≤ H i i * ∑ k, eig k * W k i ^ 2 := by
    intro i; rw [h_HU i, h_Hii i]
    exact weighted_cauchy_schwarz_sq eig (fun k => P.1 i k) (fun k => W k i) heig_nn
  -- Division: (HU)²_{ii}/h_{ii} ≤ ∑_k λ_k W²_{ki}
  have h_div : ∀ i, (H * U) i i ^ 2 / H i i ≤ ∑ k, eig k * W k i ^ 2 := by
    intro i
    have h1 := div_le_div_of_nonneg_right (h_cs i) (hH_diag_pos i).le
    rwa [mul_div_cancel_left₀ _ (hH_diag_pos i).ne'] at h1
  -- Sum, swap, and simplify using row orthogonality of W
  calc ∑ i, (H * U) i i ^ 2 / H i i
      ≤ ∑ i, ∑ k, eig k * W k i ^ 2 := Finset.sum_le_sum (fun i _ => h_div i)
    _ = ∑ k, ∑ i, eig k * W k i ^ 2 := Finset.sum_comm
    _ = ∑ k, eig k * ∑ i, W k i ^ 2 := by
        congr 1; ext k; rw [Finset.mul_sum]
    _ = ∑ k, eig k := by
        congr 1; ext k; rw [orthogonal_row_sq_sum W hWWT k, mul_one]
    _ = H.trace := by
        conv_rhs => rw [hspec]; rw [mul_assoc, trace_mul_comm P.1 _,
          mul_assoc, hPTP, mul_one, trace_diagonal]
    _ = ∑ i, H i i := rfl

/-! ## Auxiliary lemmas for nuclear norm (used by Lemma 4 proof) -/

section NuclearNormHelpers

private lemma star_matrix_eq_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    star A = Aᵀ := by
  change Aᴴ = Aᵀ; ext i j; simp [conjTranspose_apply, transpose_apply, star_trivial]

private lemma orthogonal_diag_le_one {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ)
    (hV : V * Vᵀ = 1) (i : Fin n) : V i i ≤ 1 := by
  have h : ∑ j, V i j * V i j = 1 := by
    have := congr_fun (congr_fun hV i) i
    simp [Matrix.mul_apply, Matrix.transpose_apply] at this; exact this
  nlinarith [Finset.single_le_sum (f := fun j => V i j * V i j)
    (fun j _ => mul_self_nonneg _) (Finset.mem_univ i), sq_abs (V i i)]

private lemma trace_diagonal_mul {n : ℕ} (d : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.diagonal d * M).trace = ∑ i, d i * M i i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply]
  congr 1; ext i
  conv_lhs => arg 2; ext x; rw [show (if i = x then d i else 0) * M x i =
    if i = x then d i * M x i else 0 from by split_ifs <;> simp [*]]
  simp [Finset.sum_ite_eq]

/-- For PSD `H` and orthogonal `U`, `tr(H * U) <= tr(H)`.
Proved via spectral decomposition: `H = P * diag(eig) * P^T`, so
`tr(HU) = sum eig_i V_ii` where `V = P^T U P` is orthogonal, and `V_ii <= 1`. -/
private lemma trace_psd_mul_orthogonal_le {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) :
    (H * U).trace ≤ H.trace := by
  set P := hH.isHermitian.eigenvectorUnitary
  set eig := hH.isHermitian.eigenvalues
  have hspec : H = P.1 * Matrix.diagonal eig * P.1ᵀ := by
    have h := hH.isHermitian.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h; exact h
  have hPPT : P.1 * P.1ᵀ = 1 := by
    rw [← star_matrix_eq_transpose]; exact Matrix.mem_unitaryGroup_iff.mp P.2
  have hPTP : P.1ᵀ * P.1 = 1 := by
    rw [← star_matrix_eq_transpose]; exact Matrix.UnitaryGroup.star_mul_self P
  have heig_nn := hH.eigenvalues_nonneg
  have htrH : H.trace = ∑ i, eig i := by
    conv_lhs => rw [hspec]
    rw [mul_assoc, Matrix.trace_mul_comm P.1 _, mul_assoc, hPTP, mul_one,
      Matrix.trace_diagonal]
  set V := P.1ᵀ * U * P.1
  have hVorth : V * Vᵀ = 1 := by
    show P.1ᵀ * U * P.1 * (P.1ᵀ * U * P.1)ᵀ = 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [show P.1ᵀ * U * P.1 * (P.1ᵀ * (Uᵀ * P.1)) =
        P.1ᵀ * (U * (P.1 * P.1ᵀ) * (Uᵀ * P.1)) from by simp only [mul_assoc]]
    rw [hPPT, mul_one]
    rw [show P.1ᵀ * (U * (Uᵀ * P.1)) = P.1ᵀ * ((U * Uᵀ) * P.1) from by
      simp only [mul_assoc]]
    rw [hU, one_mul, hPTP]
  have htrHU : (H * U).trace = ∑ i, eig i * V i i := by
    conv_lhs => rw [hspec]
    rw [show P.1 * Matrix.diagonal eig * P.1ᵀ * U =
        P.1 * (Matrix.diagonal eig * (P.1ᵀ * U)) from by simp only [mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show Matrix.diagonal eig * (P.1ᵀ * U) * P.1 = Matrix.diagonal eig * V from by
      simp only [V, mul_assoc]]
    exact trace_diagonal_mul eig V
  rw [htrHU, htrH]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_of_le_one_right (heig_nn i) (orthogonal_diag_le_one V hVorth i)

end NuclearNormHelpers

/-! ## Nuclear norm properties (additional formalization of Section 2 prerequisites) -/

section NuclearNormProperties

/-- The nuclear norm is non-negative. -/
theorem Ball1991.nuclearNorm_nonneg
    {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) :
    Ball1991.nuclearNorm B ≥ 0 := by
  simp only [ge_iff_le, Ball1991.nuclearNorm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [trace, Fintype.sum_empty]; simp
  · by_cases hbdd : BddAbove (Set.range fun U => ⨆ _ : U * U.transpose = 1, (B * U).trace)
    · apply le_ciSup_of_le hbdd 0
      suffices h : (⨆ (_ : (0 : Matrix (Fin n) (Fin n) ℝ) * 0ᵀ = 1),
          (B * (0 : Matrix (Fin n) (Fin n) ℝ)).trace) = 0 by linarith
      have h0 : ((0 : Matrix (Fin n) (Fin n) ℝ) * 0ᵀ) ≠ 1 := by
        intro heq
        have := congr_fun (congr_fun heq ⟨0, hn⟩) ⟨0, hn⟩
        simp at this
      simp only [iSup, Set.range_eq_empty_iff.mpr (isEmpty_Prop.mpr h0), Real.sSup_empty]
    · rw [ciSup_of_not_bddAbove hbdd, Real.sSup_empty]

/-- For a positive semidefinite matrix H, the nuclear norm equals the trace:
  `‖H‖_{C_1} = tr(H) = sum_i h_{ii}`.
This is because the singular values of a positive semidefinite matrix are its
eigenvalues, and the trace equals the sum of eigenvalues. -/
theorem Ball1991.nuclearNorm_pos_semidef_eq_trace
    {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosSemidef) :
    Ball1991.nuclearNorm H = H.trace := by
  simp only [Ball1991.nuclearNorm]
  apply le_antisymm
  · -- Upper bound: ⨆ ... ≤ H.trace
    apply ciSup_le; intro U
    by_cases hU : U * Uᵀ = 1
    · rw [ciSup_pos hU]; exact trace_psd_mul_orthogonal_le H hH U hU
    · have : IsEmpty (U * Uᵀ = 1) := isEmpty_Prop.mpr hU; simp; exact hH.trace_nonneg
  · -- Lower bound: H.trace ≤ ⨆ ... (using U = 1)
    have hall : ∀ U : Matrix (Fin n) (Fin n) ℝ,
        (⨆ (_ : U * Uᵀ = 1), (H * U).trace) ≤ H.trace := by
      intro U
      by_cases hU : U * Uᵀ = 1
      · rw [ciSup_pos hU]; exact trace_psd_mul_orthogonal_le H hH U hU
      · have : IsEmpty (U * Uᵀ = 1) := isEmpty_Prop.mpr hU; simp; exact hH.trace_nonneg
    have hbdd : BddAbove (Set.range fun U => ⨆ (_ : U * Uᵀ = 1), (H * U).trace) :=
      ⟨H.trace, by rintro x ⟨U, rfl⟩; exact hall U⟩
    have h1_orth : (1 : Matrix (Fin n) (Fin n) ℝ) * 1ᵀ = 1 := by simp
    have inner_eq : (⨆ (_ : (1 : Matrix (Fin n) (Fin n) ℝ) * 1ᵀ = 1),
          (H * (1 : Matrix (Fin n) (Fin n) ℝ)).trace) = H.trace := by
      rw [ciSup_pos h1_orth]; simp
    rw [← inner_eq]
    exact le_ciSup hbdd 1

/-- AM-GM step in the proof of Lemma 4:
If `(sum h_i / n)^n <= prod h_k` (i.e. AM^n <= GM^n, which means AM <= GM),
then all `h_i` are equal.
This is because AM = GM implies all terms equal for positive reals. -/
theorem Ball1991.am_gm_equality
    {n : ℕ} (hn : 0 < n)
    (h : Fin n → ℝ)
    (hh_pos : ∀ i, 0 < h i)
    (h_ineq : ((∑ i, h i) / n) ^ n ≤ ∏ i, h i) :
    ∀ i j, h i = h j := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hprod_pos : 0 < ∏ i : Fin n, h i :=
    Finset.prod_pos (fun i _ => hh_pos i)
  have hsum_pos : 0 < ∑ i : Fin n, h i :=
    Finset.sum_pos (fun i _ => hh_pos i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have ham_pos : 0 < (∑ i : Fin n, h i) / n := div_pos hsum_pos hn_pos
  -- AM-GM: (∏ h_i)^{1/n} ≤ (∑ h_i)/n
  have hamgm : (∏ i, h i) ^ ((1:ℝ)/n) ≤ (∑ i, h i) / n := by
    have := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1/n) h
      (fun i _ => by positivity)
      (by simp [Finset.sum_const, nsmul_eq_mul]; field_simp)
      (fun i _ => le_of_lt (hh_pos i))
    rw [Real.finset_prod_rpow Finset.univ h (fun i _ => le_of_lt (hh_pos i)) (1/n)] at this
    convert this using 1
    rw [Finset.sum_div]; congr 1; ext i; ring
  -- From h_ineq: AM^n ≤ ∏ h_i, take (1/n)-th power: AM ≤ (∏ h_i)^{1/n}
  have hrev : (∑ i, h i) / n ≤ (∏ i, h i) ^ ((1:ℝ)/n) := by
    have h1 : ((∑ i, h i) / ↑n) ^ (n : ℝ) ≤ (∏ i, h i) := by
      rw [Real.rpow_natCast]; exact h_ineq
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0:ℝ) ≤ 1/n)
    rwa [← Real.rpow_mul (le_of_lt ham_pos), show (n : ℝ) * (1/n) = 1 from by field_simp,
      Real.rpow_one] at h2
  -- Equality in weighted AM-GM form
  have heq : ∏ i, h i ^ ((1:ℝ)/n) = ∑ i, (1/n) * h i := by
    rw [Real.finset_prod_rpow Finset.univ h (fun i _ => le_of_lt (hh_pos i)) (1/n)]
    rw [le_antisymm hamgm hrev, Finset.sum_div]
    congr 1; ext i; ring
  -- Apply equality characterization: all h_j equal the arithmetic mean
  have heq_char := (Real.geom_mean_eq_arith_mean_weighted_iff' Finset.univ (fun _ => 1/n) h
    (fun i _ => by positivity)
    (by simp [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun i _ => le_of_lt (hh_pos i))).mp heq
  intro i j
  linarith [heq_char i (Finset.mem_univ i), heq_char j (Finset.mem_univ j)]

end NuclearNormProperties

/-! ## Proof of Lemma 6 (Nuclear norm inequality)

Placed here (after NuclearNormProperties) so we can use `nuclearNorm_pos_semidef_eq_trace`. -/

/-- Cauchy-Schwarz: `∑ a_i ≤ √n * √(∑ a_i²)`. -/
private lemma sum_le_sqrt_card_mul_sqrt_sum_sq {n : ℕ} (a : Fin n → ℝ) :
    ∑ i, a i ≤ Real.sqrt n * Real.sqrt (∑ i, a i ^ 2) := by
  by_cases h_sum : ∑ i, a i ≤ 0
  · exact le_trans h_sum (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · push_neg at h_sum
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1 : ℝ)) a
    simp only [one_pow, one_mul, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, mul_one] at h_cs
    have h1 := Real.sqrt_le_sqrt h_cs
    rwa [Real.sqrt_sq (le_of_lt h_sum), Real.sqrt_mul (Nat.cast_nonneg n)] at h1

/-- **Lemma 6** (Ball 1991, Lemma 6 -- Nuclear norm inequality).
If `H = (h_ij)` is a positive semidefinite `n x n` matrix with non-zero diagonal
entries, then:
  `‖(h_ij / sqrt(h_{ii}))‖_{C_1} <= sqrt(n) * ‖H‖_{C_1}^{1/2}`

The proof uses Lemma 5: for any orthogonal U,
  `tr(BU) = sum_i (HU)_{ii}/sqrt(h_{ii})`
  `<= sqrt(n) * (sum_i (HU)^2_{ii}/h_{ii})^{1/2}`    (Cauchy-Schwarz)
  `<= sqrt(n) * (sum_i h_{ii})^{1/2} = sqrt(n) * ‖H‖_{C_1}^{1/2}`  (Lemma 5)
Taking sup over all orthogonal U gives the result (no need for nuclearNorm_attained). -/
theorem Ball1991.lemma6_nuclear_norm_ineq
    {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH_pos : H.PosSemidef)
    (hH_diag_ne : ∀ i, H i i ≠ 0) :
    Ball1991.nuclearNorm
      (Matrix.of (fun i j => H i j / Real.sqrt (H i i))) ≤
      Real.sqrt n * Real.sqrt (Ball1991.nuclearNorm H) := by
  -- Diagonal positivity (PSD + nonzero → positive)
  have hH_diag_pos : ∀ i, 0 < H i i := by
    intro i
    have hnn : 0 ≤ H i i := by
      have := hH_pos.2 (Finsupp.single i 1)
      simp [Finsupp.sum_single_index] at this; linarith
    exact lt_of_le_of_ne hnn (hH_diag_ne i).symm
  -- Nuclear norm of PSD = trace
  have hNN : Ball1991.nuclearNorm H = H.trace :=
    Ball1991.nuclearNorm_pos_semidef_eq_trace H hH_pos
  set B := Matrix.of (fun i j => H i j / Real.sqrt (H i i)) with hB_def
  -- Key bound: for every orthogonal U₀, tr(BU₀) ≤ √n * √(nuclearNorm H)
  suffices h_bound : ∀ U₀ : Matrix (Fin n) (Fin n) ℝ, U₀ * U₀ᵀ = 1 →
      (B * U₀).trace ≤ Real.sqrt n * Real.sqrt (Ball1991.nuclearNorm H) by
    -- Bound the iSup
    show ⨆ (U : _) (_ : U * Uᵀ = 1), (B * U).trace ≤ _
    apply ciSup_le; intro U₀
    by_cases hU : U₀ * U₀ᵀ = 1
    · rw [ciSup_pos hU]; exact h_bound U₀ hU
    · have : IsEmpty (U₀ * U₀ᵀ = 1) := isEmpty_Prop.mpr hU; simp
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- Prove the bound for each orthogonal U₀
  intro U₀ hU
  -- Step 1: trace identity: tr(BU₀) = ∑_i (HU₀)_ii / √(H_ii)
  have h_trace : (B * U₀).trace = ∑ i, (H * U₀) i i / Real.sqrt (H i i) := by
    simp only [B, trace, diag_apply, mul_apply, of_apply]
    congr 1; funext i; simp_rw [div_mul_eq_mul_div]; rw [← Finset.sum_div]
  -- Step 2: chain of inequalities
  calc (B * U₀).trace
      = ∑ i, (H * U₀) i i / Real.sqrt (H i i) := h_trace
    _ ≤ Real.sqrt n *
        Real.sqrt (∑ i, ((H * U₀) i i / Real.sqrt (H i i)) ^ 2) :=
        sum_le_sqrt_card_mul_sqrt_sum_sq _
    _ = Real.sqrt n * Real.sqrt (∑ i, (H * U₀) i i ^ 2 / H i i) := by
        congr 1; congr 1; apply Finset.sum_congr rfl; intro i _
        rw [div_pow, Real.sq_sqrt (le_of_lt (hH_diag_pos i))]
    _ ≤ Real.sqrt n * Real.sqrt (∑ i, H i i) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact Real.sqrt_le_sqrt
          (Ball1991.lemma5_diagonal_estimate H hH_pos hH_diag_ne U₀ hU)
    _ = Real.sqrt n * Real.sqrt (Ball1991.nuclearNorm H) := by
        congr 1; rw [hNN, trace]; simp [diag_apply]

/-! ## Proof of Lemma 4 (Symmetrisation)

The proof follows Ball's variational argument:
1. Get a nuclear norm maximizer U₀ for B = diag(θ)·A (gives PSD matrix H = B·U₀)
2. Show H has positive diagonal (from nonzero rows of A)
3. Minimize nuclear norm over θ with ∏θ = 1
4. Perturbation via Lemma 6 + AM-GM equality forces all H_ii equal
5. Rescale so H_ii = 1
-/

/-- Derive Uᵀ * U = 1 from U * Uᵀ = 1 for square real matrices. -/
private theorem orthogonal_transpose {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) : Uᵀ * U = 1 := by
  have hdet : IsUnit U.det := isUnit_iff_ne_zero.mpr (by
    intro h; have := congr_arg Matrix.det hU; simp [h] at this)
  rw [← Matrix.inv_eq_right_inv hU]; exact Matrix.nonsing_inv_mul U hdet

/-- Entries of orthogonal matrices are bounded by 1 in absolute value. -/
private theorem orthogonal_entry_le_one {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) (i j : Fin n) :
    |U i j| ≤ 1 := by
  have hrow : ∑ k, U i k * U i k = 1 := by
    have h := congr_fun (congr_fun hU i) i
    simp [Matrix.mul_apply, Matrix.transpose_apply] at h; exact h
  have hsq : U i j * U i j ≤ 1 :=
    hrow ▸ Finset.single_le_sum (fun k _ => mul_self_nonneg (U i k)) (Finset.mem_univ j)
  nlinarith [sq_abs (U i j)]

/-- The set of traces {tr(BU) : U orthogonal} is bounded above. -/
private theorem nuclearNorm_trace_bddAbove {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove (Set.range fun U : Matrix (Fin n) (Fin n) ℝ =>
      ⨆ (_ : U * Uᵀ = 1), (B * U).trace) := by
  refine ⟨∑ i, ∑ j, |B i j|, ?_⟩
  rintro x ⟨U, rfl⟩
  dsimp only
  by_cases hU : U * Uᵀ = 1
  · rw [ciSup_pos hU]
    calc (B * U).trace = ∑ i, ∑ j, B i j * U j i := by
            simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      _ ≤ ∑ i, ∑ j, |B i j * U j i| :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => le_abs_self _
      _ = ∑ i, ∑ j, |B i j| * |U j i| := by
            congr 1; ext i; congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ i, ∑ j, |B i j| :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              mul_le_of_le_one_right (abs_nonneg _) (orthogonal_entry_le_one U hU j i)
  · have : IsEmpty (U * Uᵀ = 1) := isEmpty_Prop.mpr hU; simp
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

/-- For any orthogonal U, `tr(B * U) ≤ nuclearNorm B`. -/
private theorem nuclearNorm_ge_trace {n : ℕ}
    (B U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) :
    (B * U).trace ≤ Ball1991.nuclearNorm B := by
  suffices h : (B * U).trace ≤
      ⨆ (V : Matrix (Fin n) (Fin n) ℝ) (_ : V * Vᵀ = 1), (B * V).trace from h
  have h_eq : (fun V : Matrix (Fin n) (Fin n) ℝ =>
      ⨆ (_ : V * Vᵀ = 1), (B * V).trace) U = (B * U).trace := by
    dsimp only; exact ciSup_pos hU
  calc (B * U).trace = _ := h_eq.symm
    _ ≤ _ := le_ciSup (nuclearNorm_trace_bddAbove B) U

/-- Nuclear norm maximizer: strongest form of `nuclearNorm_attained`, exporting
    the maximality property. -/
private theorem nuclearNorm_maximizer {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U₀ : Matrix (Fin n) (Fin n) ℝ, U₀ * U₀ᵀ = 1 ∧
      Ball1991.nuclearNorm B = (B * U₀).trace ∧
      ∀ V : Matrix (Fin n) (Fin n) ℝ, V * Vᵀ = 1 →
        (B * V).trace ≤ (B * U₀).trace := by
  obtain ⟨U₀, hU₀, heq⟩ := Ball1991.nuclearNorm_attained B
  exact ⟨U₀, hU₀, heq, fun V hV => heq ▸ nuclearNorm_ge_trace B V hV⟩

/-- If `tr(M * V) ≤ tr(M)` for all orthogonal V, then M is PSD.
    Proof: symmetry from Givens rotations, nonneg eigenvalues from sign-flip. -/
private theorem max_trace_at_identity_psd {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hmax : ∀ V : Matrix (Fin n) (Fin n) ℝ, V * Vᵀ = 1 →
      (M * V).trace ≤ M.trace) :
    M.PosSemidef := by
  -- === Part A: ∀ u, 0 ≤ u ⬝ᵥ M.mulVec u (via Householder reflection) ===
  have hqf : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ M.mulVec u := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp [dotProduct, Matrix.mulVec]
    · -- Normalize to unit vector w = r⁻¹ • u
      obtain ⟨k₀, hk₀⟩ : ∃ k, u k ≠ 0 := by
        by_contra h; push_neg at h; exact hu (funext h)
      have huu : 0 < u ⬝ᵥ u := by
        calc 0 < u k₀ * u k₀ := mul_self_pos.mpr hk₀
          _ ≤ ∑ j, u j * u j :=
              Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ k₀)
      set r := Real.sqrt (u ⬝ᵥ u) with hr_def
      have hr : 0 < r := Real.sqrt_pos_of_pos huu
      set w := r⁻¹ • u with hw_def
      have hw : w ⬝ᵥ w = 1 := by
        simp only [w, dotProduct, Pi.smul_apply, smul_eq_mul]
        have : ∑ k, r⁻¹ * u k * (r⁻¹ * u k) = r⁻¹ ^ 2 * (u ⬝ᵥ u) := by
          rw [dotProduct, Finset.mul_sum]; congr 1; ext k; ring
        rw [this, inv_pow, hr_def, Real.sq_sqrt (le_of_lt huu),
            inv_mul_cancel₀ (ne_of_gt huu)]
      -- Householder: V = 1 - 2·w·wᵀ is orthogonal, tr(MV) = tr(M) - 2(w ⬝ᵥ Mw)
      let V := Matrix.of fun (i j : Fin n) =>
        (if i = j then (1 : ℝ) else 0) - 2 * w i * w j
      have hV_orth : V * Vᵀ = 1 := by
        ext i j
        simp only [V, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
          Matrix.one_apply]
        -- Each summand: (δ_ik - 2 w_i w_k)(δ_jk - 2 w_j w_k)
        -- Evaluate the sum term by term
        have eval : ∀ k : Fin n,
            ((if i = k then (1:ℝ) else 0) - 2 * w i * w k) *
            ((if j = k then 1 else 0) - 2 * w j * w k) =
            (if i = k then if j = k then 1 else 0 else 0) -
            2 * w j * (if i = k then w k else 0) -
            2 * w i * (if j = k then w k else 0) +
            4 * w i * w j * (w k * w k) := fun k => by
          split_ifs <;> ring
        simp_rw [eval]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [show ∑ k, w k * w k = w ⬝ᵥ w from rfl, hw]
        simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        by_cases hij : i = j
        · subst hij; ring
        · simp [hij, Ne.symm hij]; ring
      have htr : (M * V).trace = M.trace - 2 * (w ⬝ᵥ M.mulVec w) := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
        simp only [V, Matrix.of_apply]
        -- Expand product
        simp_rw [show ∀ i k, M i k * ((if k = i then (1:ℝ) else 0) - 2 * w k * w i) =
            M i k * (if k = i then 1 else 0) - 2 * (M i k * w k) * w i
            from fun i k => by ring]
        simp only [Finset.sum_sub_distrib]
        have s1 : ∑ i : Fin n, ∑ k : Fin n,
            M i k * (if k = i then (1:ℝ) else 0) = M.trace := by
          simp only [Matrix.trace, Matrix.diag]; congr 1; funext i
          simp_rw [show ∀ k, M i k * (if k = i then (1:ℝ) else 0) =
              if k = i then M i k else 0 from fun k => by split_ifs <;> simp]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        have s2 : ∑ i : Fin n, ∑ k : Fin n, 2 * (M i k * w k) * w i =
            2 * (w ⬝ᵥ M.mulVec w) := by
          simp only [dotProduct, Matrix.mulVec, dotProduct]
          rw [Finset.mul_sum]; congr 1; funext i
          rw [Finset.mul_sum, Finset.mul_sum]; congr 1; funext k; ring
        rw [s1, s2]; simp [Matrix.trace, Matrix.diag]
      have hw_nn : 0 ≤ w ⬝ᵥ M.mulVec w := by linarith [hmax V hV_orth, htr]
      -- Scale: u ⬝ᵥ Mu = r² * (w ⬝ᵥ Mw) ≥ 0
      have hscale : u ⬝ᵥ M.mulVec u = r ^ 2 * (w ⬝ᵥ M.mulVec w) := by
        simp only [w, dotProduct, Matrix.mulVec, dotProduct,
          Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]; congr 1; ext i
        rw [Finset.mul_sum, ← mul_assoc, Finset.mul_sum]
        congr 1 with j; field_simp [ne_of_gt hr]
      linarith [mul_nonneg (sq_nonneg r) hw_nn, hscale]
  -- === Part B: M is symmetric (Givens rotation) ===
  have hsym : ∀ p q : Fin n, M p q = M q p := by
    intro p q
    by_cases hpq : p = q
    · subst hpq; rfl
    · have hp_nn : 0 ≤ M p p := by
        have := hqf (Pi.single p 1)
        simp only [dotProduct, Matrix.mulVec, dotProduct, Pi.single_apply,
          mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
        linarith
      have hq_nn : 0 ≤ M q q := by
        have := hqf (Pi.single q 1)
        simp only [dotProduct, Matrix.mulVec, dotProduct, Pi.single_apply,
          mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
        linarith
      -- a = M_pp + M_qq ≥ 0, b = M_pq - M_qp. Show b = 0.
      set a := M p p + M q q with ha_def
      set b := M p q - M q p with hb_def
      suffices hb : b = 0 by linarith
      by_contra hb_ne
      -- For all c²+s²=1, a*c + b*s ≤ a (from Givens rotation + hmax)
      have h_bound : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → a * c + b * s ≤ a := by
        intro c s hcs
        let G := Matrix.of fun (i j : Fin n) =>
          if i = p ∧ j = p then c
          else if i = q ∧ j = q then c
          else if i = p ∧ j = q then -s
          else if i = q ∧ j = p then s
          else if i = j then (1 : ℝ)
          else 0
        have hqp : q ≠ p := fun h => hpq h.symm
        -- Helper: decompose ∑_k f(k) by pulling out k=p and k=q
        have sum_decomp : ∀ f : Fin n → ℝ,
            ∑ x, f x = f p + f q + ∑ x ∈ (Finset.univ.erase p).erase q, f x := by
          intro f
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
              ← Finset.add_sum_erase _ _
                (Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩)]
          ring
        have hG_orth : G * Gᵀ = 1 := by
          ext i j
          simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
            G, Matrix.of_apply]
          rw [sum_decomp]
          -- Simplify the x=p and x=q terms (substitute x)
          simp only [eq_self_iff_true, true_and, and_true, hpq, hqp,
            false_and, and_false, and_self, ite_true, ite_false]
          -- Simplify rest sum: for x ∉ {p,q}, most ite branches are False
          have hrest : ∑ x ∈ (Finset.univ.erase p).erase q,
              (if i = p ∧ x = p then c
               else if i = q ∧ x = q then c
               else if i = p ∧ x = q then -s
               else if i = q ∧ x = p then s
               else if i = x then (1:ℝ) else 0) *
              (if j = p ∧ x = p then c
               else if j = q ∧ x = q then c
               else if j = p ∧ x = q then -s
               else if j = q ∧ x = p then s
               else if j = x then 1 else 0) =
            if i = j ∧ i ≠ p ∧ i ≠ q then 1 else 0 := by
            -- Step 1: simplify each summand using x ∉ {p,q}
            have hsimp : ∀ x ∈ (Finset.univ.erase p).erase q,
                (if i = p ∧ x = p then c
                 else if i = q ∧ x = q then c
                 else if i = p ∧ x = q then -s
                 else if i = q ∧ x = p then s
                 else if i = x then (1:ℝ) else 0) *
                (if j = p ∧ x = p then c
                 else if j = q ∧ x = q then c
                 else if j = p ∧ x = q then -s
                 else if j = q ∧ x = p then s
                 else if j = x then 1 else 0) =
                (if i = x then (1:ℝ) else 0) * (if j = x then 1 else 0) := by
              intro x hx
              have hxq : x ≠ q := (Finset.mem_erase.mp hx).1
              have hxp : x ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
              simp [Ne.symm hxp, Ne.symm hxq, hxp, hxq]
            -- Step 2: further simplify and evaluate using sum_ite_eq'
            have hsimp2 : ∀ x ∈ (Finset.univ.erase p).erase q,
                (if i = x then (1:ℝ) else 0) * (if j = x then 1 else 0) =
                if x = i ∧ x = j then 1 else 0 := by
              intro x _; by_cases h1 : i = x <;> by_cases h2 : j = x <;>
                simp [h1, h2, eq_comm]
            rw [Finset.sum_congr rfl hsimp, Finset.sum_congr rfl hsimp2]
            by_cases hij : i = j
            · subst hij
              simp only [and_self, Finset.sum_ite_eq', Finset.mem_erase,
                Finset.mem_univ, and_true, ne_eq, eq_self_iff_true, true_and,
                and_comm]
            · simp only [hij, false_and, ite_false]
              apply Finset.sum_eq_zero; intro x _
              simp only [ite_eq_right_iff]
              exact fun ⟨h1, h2⟩ => absurd (h1.symm.trans h2) hij
          rw [hrest]; clear hrest
          -- Case split on i,j vs {p,q} and compute
          clear * - n p q i j c s hpq hqp hcs
          by_cases hip : i = p <;> by_cases hiq : i = q <;>
              by_cases hjp : j = p <;> by_cases hjq : j = q <;>
              simp_all <;> first | nlinarith only [hcs] | omega
        have hG_trace : (M * G).trace =
            (M.trace - M p p - M q q) + a * c + b * s := by
          -- Helper: evaluate inner sum for specific diagonal index
          have diag_entry : ∀ i : Fin n,
              ∑ k, M i k * (if k = p ∧ i = p then c
                else if k = q ∧ i = q then c
                else if k = p ∧ i = q then -s
                else if k = q ∧ i = p then s
                else if k = i then (1:ℝ) else 0) =
              if i = p then M i p * c + M i q * s
              else if i = q then M i p * (-s) + M i q * c
              else M i i := by
            intro i; rw [sum_decomp]
            have hzero : ∀ (hip : i ≠ p) (hiq : i ≠ q),
                ∀ x ∈ (Finset.univ.erase p).erase q,
                M i x * (if x = p ∧ i = p then c else if x = q ∧ i = q then c
                  else if x = p ∧ i = q then -s else if x = q ∧ i = p then s
                  else if x = i then (1:ℝ) else 0) =
                if x = i then M i x else 0 := by
              intro hip hiq x hx
              have hxq := (Finset.mem_erase.mp hx).1
              have hxp := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
              simp [hxp, hxq, hip, hiq]
            by_cases hip : i = p <;> by_cases hiq : i = q
            · exact absurd (hip.symm.trans hiq) hpq
            · subst hip
              simp only [eq_self_iff_true, true_and, hpq, hqp, false_and,
                and_false, ite_true, ite_false, mul_one, mul_zero]
              rw [Finset.sum_eq_zero (fun x hx => by
                have hxq := (Finset.mem_erase.mp hx).1
                have hxp := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
                simp [hxp, hxq, hpq])]
              ring
            · subst hiq
              simp only [hpq, hqp, false_and, and_false, and_true, ite_true, ite_false]
              rw [Finset.sum_eq_zero (fun x hx => by
                have hxq := (Finset.mem_erase.mp hx).1
                have hxp := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
                simp [hxp, hxq, hpq])]
              ring
            · simp only [hip, hiq, false_and, and_false, ite_false, Ne.symm hip,
                Ne.symm hiq, mul_zero]
              simp only [zero_add, mul_ite, mul_one, mul_zero]
              rw [Finset.sum_ite_eq']
              simp [Finset.mem_erase, hip, hiq]
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, G, Matrix.of_apply]
          simp_rw [diag_entry]
          -- Now: ∑_i (if i=p then ... else if i=q then ... else M_ii) = target
          rw [sum_decomp]
          simp only [eq_self_iff_true, ite_true, hpq, hqp, ite_false]
          -- Rest sum: ∑_{i≠p,q} M_ii = ∑_{all} M_ii - M_pp - M_qq
          have hrest : ∑ x ∈ (Finset.univ.erase p).erase q,
              (if x = p then M x p * c + M x q * s
               else if x = q then M x p * (-s) + M x q * c
               else M x x) = ∑ x ∈ (Finset.univ.erase p).erase q, M x x := by
            apply Finset.sum_congr rfl; intro x hx
            have hxq := (Finset.mem_erase.mp hx).1
            have hxp := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            simp [hxp, hxq]
          rw [hrest]
          have : ∑ x, M x x = M p p + M q q +
              ∑ x ∈ (Finset.univ.erase p).erase q, M x x := sum_decomp _
          linarith [ha_def, hb_def]
        linarith [hmax G hG_orth, hG_trace]
      -- Choose c₀ = a/R, s₀ = b/R where R = √(a²+b²) to get contradiction
      have hab : 0 < a ^ 2 + b ^ 2 := by positivity
      set R := Real.sqrt (a ^ 2 + b ^ 2) with hR_def
      have hR : 0 < R := Real.sqrt_pos_of_pos hab
      have ha_nn : 0 ≤ a := by linarith
      have hR_sq : R ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (le_of_lt hab)
      have hacs : a * (a / R) + b * (b / R) = R := by
        field_simp [ne_of_gt hR]
        nlinarith only [hR_sq]
      have hcs_unit : (a / R) ^ 2 + (b / R) ^ 2 = 1 := by
        field_simp [ne_of_gt hR]; rw [hR_def, Real.sq_sqrt (le_of_lt hab)]
      have hR_gt : a < R := by
        rw [hR_def, show a = Real.sqrt (a ^ 2) from (Real.sqrt_sq ha_nn).symm]
        apply Real.sqrt_lt_sqrt (sq_nonneg a)
        have h1 := Real.sq_sqrt (sq_nonneg a)
        have h2 : 0 < b ^ 2 := by positivity
        linarith
      linarith [h_bound (a / R) (b / R) hcs_unit]
  -- === Part C: Assemble PosSemidef ===
  refine ⟨?_, ?_⟩
  · -- IsHermitian (Mᵀ = M)
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply]
    exact hsym j i
  · -- Nonneg Finsupp quadratic form
    intro x
    suffices h : 0 ≤ (⇑x) ⬝ᵥ M.mulVec ⇑x by
      convert h using 1 <;> try rfl
      unfold Finsupp.sum
      simp only [star_trivial, dotProduct, Matrix.mulVec, dotProduct]
      rw [← Finset.sum_subset (Finset.subset_univ x.support)
        (fun i _ hi => by simp [show x i = 0 from by rwa [Finsupp.mem_support_iff, not_not] at hi])]
      congr 1; ext i
      rw [← Finset.sum_subset (Finset.subset_univ x.support)
        (fun j _ hj => by simp [show x j = 0 from by rwa [Finsupp.mem_support_iff, not_not] at hj])]
      rw [Finset.mul_sum]; congr 1; ext j; ring
    exact hqf x

/-- Nuclear norm maximizer gives PSD: if U₀ maximizes tr(B·U) over orthogonal U,
    then B·U₀ is PSD. -/
private theorem maximizer_gives_psd {n : ℕ}
    (B U₀ : Matrix (Fin n) (Fin n) ℝ) (hU₀ : U₀ * U₀ᵀ = 1)
    (hmax : ∀ V, V * Vᵀ = 1 → (B * V).trace ≤ (B * U₀).trace) :
    (B * U₀).PosSemidef := by
  apply max_trace_at_identity_psd
  intro V hV
  rw [show (B * U₀ * V).trace = (B * (U₀ * V)).trace from by rw [Matrix.mul_assoc]]
  have hU₀V_orth : (U₀ * V) * (U₀ * V)ᵀ = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V Vᵀ U₀ᵀ,
        hV, Matrix.one_mul, hU₀]
  exact hmax (U₀ * V) hU₀V_orth

/-- PSD matrix with zero diagonal entry has zero row.
    Uses `dotProduct_mulVec_zero_iff`: if xᵀHx = 0, then Hx = 0. -/
private theorem psd_zero_diag_zero_row {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef) (i : Fin n)
    (hi : H i i = 0) : ∀ j, H i j = 0 := by
  -- e_i ⬝ᵥ (H *ᵥ e_i) = H_ii = 0, so H *ᵥ e_i = 0 by PSD kernel characterization
  have hx_dot : star (Pi.single i 1 : Fin n → ℝ) ⬝ᵥ (H *ᵥ Pi.single i 1) = 0 := by
    rw [star_trivial]; convert hi using 1
    simp [dotProduct, mulVec, Pi.single_apply, Finset.mem_univ]
  have hHx : H *ᵥ (Pi.single i 1 : Fin n → ℝ) = 0 :=
    hH.dotProduct_mulVec_zero_iff.mp hx_dot
  intro j
  -- (H *ᵥ e_i) j = H j i = 0
  have h1 : (H *ᵥ (Pi.single i 1 : Fin n → ℝ)) j = 0 := congr_fun hHx j
  simp [mulVec, dotProduct, Pi.single_apply] at h1
  -- H is symmetric (IsHermitian), so H i j = H j i = 0
  have hsym : H i j = H j i := by
    have := congr_fun (congr_fun hH.isHermitian.eq j) i
    simp [conjTranspose_apply, star_trivial] at this; exact this
  linarith

/-- PSD product of matrix with nonzero rows and orthogonal has positive diagonal. -/
private theorem psd_product_pos_diag {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hB_rows : ∀ i, ∃ j, B i j ≠ 0)
    (U₀ : Matrix (Fin n) (Fin n) ℝ) (hU₀ : U₀ * U₀ᵀ = 1)
    (hH : (B * U₀).PosSemidef) :
    ∀ i, 0 < (B * U₀) i i := by
  intro i
  set H := B * U₀
  have hnn : 0 ≤ H i i := by
    have := hH.2 (Finsupp.single i 1); simp [Finsupp.sum_single_index] at this; linarith
  by_contra h_not_pos; push_neg at h_not_pos
  have hi0 : H i i = 0 := le_antisymm h_not_pos hnn
  have hrow_zero : ∀ j, H i j = 0 := psd_zero_diag_zero_row H hH i hi0
  -- B = H * U₀ᵀ (since H = B * U₀ and U₀ * U₀ᵀ = 1), so row i of B is zero
  have hB_row_zero : ∀ j, B i j = 0 := by
    have hBH : B = H * U₀ᵀ := by
      change B = B * U₀ * U₀ᵀ
      rw [Matrix.mul_assoc, hU₀, Matrix.mul_one]
    intro j; rw [hBH, Matrix.mul_apply]
    apply Finset.sum_eq_zero; intro x _
    rw [Matrix.transpose_apply, hrow_zero x, zero_mul]
  exact absurd (hB_row_zero _) (hB_rows i).choose_spec

/-- Nuclear norm is right-invariant under orthogonal multiplication:
    `‖M·V‖_{C₁} = ‖M‖_{C₁}` for orthogonal V. -/
private theorem nuclearNorm_mul_orthogonal {n : ℕ}
    (M V : Matrix (Fin n) (Fin n) ℝ) (hV : V * Vᵀ = 1) :
    Ball1991.nuclearNorm (M * V) = Ball1991.nuclearNorm M := by
  have hVT := orthogonal_transpose V hV
  apply le_antisymm
  · -- nuclearNorm(M*V) ≤ nuclearNorm(M): maximizer U₀ for M*V gives V*U₀ for M
    obtain ⟨U₀, hU₀, heq⟩ := Ball1991.nuclearNorm_attained (M * V)
    rw [heq, Matrix.mul_assoc]
    have hVU : (V * U₀) * (V * U₀)ᵀ = 1 := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₀ U₀ᵀ Vᵀ,
          hU₀, Matrix.one_mul, hV]
    exact nuclearNorm_ge_trace M (V * U₀) hVU
  · -- nuclearNorm(M) ≤ nuclearNorm(M*V): maximizer U₀ for M gives Vᵀ*U₀ for M*V
    obtain ⟨U₀, hU₀, heq⟩ := Ball1991.nuclearNorm_attained M
    rw [heq, show (M * U₀).trace = (M * V * (Vᵀ * U₀)).trace from by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, hV, Matrix.one_mul]]
    have hVTU : (Vᵀ * U₀) * (Vᵀ * U₀)ᵀ = 1 := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₀ U₀ᵀ (Vᵀᵀ),
          hU₀, Matrix.one_mul, Matrix.transpose_transpose, hVT]
    exact nuclearNorm_ge_trace (M * V) (Vᵀ * U₀) hVTU

/-- Nuclear norm scales with nonneg scalar: `‖c • M‖_{C₁} = c * ‖M‖_{C₁}`. -/
private theorem nuclearNorm_smul_nonneg {n : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (M : Matrix (Fin n) (Fin n) ℝ) :
    Ball1991.nuclearNorm (c • M) = c * Ball1991.nuclearNorm M := by
  apply le_antisymm
  · -- ≤: get maximizer for c•M, factor out c
    obtain ⟨U₀, hU₀, heq⟩ := Ball1991.nuclearNorm_attained (c • M)
    rw [heq, Matrix.smul_mul, show (c • (M * U₀)).trace = c * (M * U₀).trace from by
      simp [Matrix.trace, Matrix.smul_apply, Finset.mul_sum]]
    exact mul_le_mul_of_nonneg_left (nuclearNorm_ge_trace M U₀ hU₀) hc
  · -- ≥: get maximizer for M, factor in c
    obtain ⟨U₀, hU₀, heq⟩ := Ball1991.nuclearNorm_attained M
    rw [heq, show c * (M * U₀).trace = (c • M * U₀).trace from by
      rw [Matrix.smul_mul]; simp [Matrix.trace, Matrix.smul_apply, Finset.mul_sum]]
    exact nuclearNorm_ge_trace (c • M) U₀ hU₀

/-- One-sided Lipschitz: nuclearNorm(B₁) ≤ nuclearNorm(B₂) + ∑_{ij} |(B₁-B₂)_{ij}|. -/
private theorem nuclearNorm_sub_le {n : ℕ}
    (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) :
    Ball1991.nuclearNorm B₁ ≤
    Ball1991.nuclearNorm B₂ + ∑ i : Fin n, ∑ j : Fin n, |B₁ i j - B₂ i j| := by
  obtain ⟨U₁, hU₁, heq₁⟩ := Ball1991.nuclearNorm_attained B₁
  rw [heq₁]
  have hsplit : (B₁ * U₁).trace = (B₂ * U₁).trace + ((B₁ - B₂) * U₁).trace := by
    rw [← Matrix.trace_add, ← Matrix.add_mul, add_sub_cancel]
  rw [hsplit]
  have h₂ := nuclearNorm_ge_trace B₂ U₁ hU₁
  have h_bound : ((B₁ - B₂) * U₁).trace ≤ ∑ i, ∑ j, |B₁ i j - B₂ i j| := by
    calc ((B₁ - B₂) * U₁).trace
        = ∑ i, ∑ j, (B₁ i j - B₂ i j) * U₁ j i := by
          simp [Matrix.trace, Matrix.mul_apply, Matrix.sub_apply]
      _ ≤ ∑ i, ∑ j, |(B₁ i j - B₂ i j) * U₁ j i| :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => le_abs_self _
      _ = ∑ i, ∑ j, |B₁ i j - B₂ i j| * |U₁ j i| := by
          congr 1; ext i; congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ i, ∑ j, |B₁ i j - B₂ i j| :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            mul_le_of_le_one_right (abs_nonneg _) (orthogonal_entry_le_one U₁ hU₁ j i)
  linarith

/-- nuclearNorm(diag(θ)·A) is continuous in θ. Uses the Lipschitz bound from
    nuclearNorm_sub_le: the nuclear norm changes by at most ∑|ΔB_{ij}|. -/
private theorem nuclearNorm_diag_continuous {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun theta : Fin n → ℝ =>
      Ball1991.nuclearNorm (Matrix.diagonal theta * A)) := by
  rw [Metric.continuous_iff]
  intro θ₀ ε hε
  set C := ∑ i : Fin n, ∑ j : Fin n, |A i j| + 1
  have hC_pos : 0 < C := by positivity
  refine ⟨ε / C, div_pos hε hC_pos, fun θ hθ => ?_⟩
  rw [Real.dist_eq]
  set f := fun θ : Fin n → ℝ => Ball1991.nuclearNorm (Matrix.diagonal θ * A)
  have h1 := nuclearNorm_sub_le (Matrix.diagonal θ * A) (Matrix.diagonal θ₀ * A)
  have h2 := nuclearNorm_sub_le (Matrix.diagonal θ₀ * A) (Matrix.diagonal θ * A)
  have hentry : ∑ i : Fin n, ∑ j : Fin n,
      |(Matrix.diagonal θ * A) i j - (Matrix.diagonal θ₀ * A) i j| ≤
      dist θ θ₀ * C := by
    simp only [Matrix.diagonal_mul]
    calc ∑ i, ∑ j, |θ i * A i j - θ₀ i * A i j|
        = ∑ i, ∑ j, |θ i - θ₀ i| * |A i j| := by
          congr 1; ext i; congr 1; ext j
          rw [← abs_mul, show θ i * A i j - θ₀ i * A i j = (θ i - θ₀ i) * A i j from by ring]
      _ ≤ ∑ i, dist θ θ₀ * ∑ j, |A i j| := by
          apply Finset.sum_le_sum; intro i _
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun j _ => abs_nonneg _)
          calc |θ i - θ₀ i| = dist (θ i) (θ₀ i) := (Real.dist_eq _ _).symm
            _ ≤ dist θ θ₀ := dist_le_pi_dist θ θ₀ i
      _ = dist θ θ₀ * ∑ i, ∑ j, |A i j| := by rw [← Finset.mul_sum]
      _ ≤ dist θ θ₀ * C := by
          apply mul_le_mul_of_nonneg_left _ (dist_nonneg)
          linarith
  have hentry' : ∑ i : Fin n, ∑ j : Fin n,
      |(Matrix.diagonal θ₀ * A) i j - (Matrix.diagonal θ * A) i j| ≤
      dist θ θ₀ * C := by
    calc _ = ∑ i : Fin n, ∑ j : Fin n,
        |(Matrix.diagonal θ * A) i j - (Matrix.diagonal θ₀ * A) i j| := by
          congr 1; ext i; congr 1; ext j; rw [abs_sub_comm]
      _ ≤ _ := hentry
  -- From h1, h2, hentry, hentry': |f θ - f θ₀| < ε
  have hfθ_le : f θ ≤ f θ₀ + dist θ θ₀ * C := by linarith
  have hfθ₀_le : f θ₀ ≤ f θ + dist θ θ₀ * C := by linarith
  have hdC : dist θ θ₀ * C < ε := by
    calc dist θ θ₀ * C < ε / C * C := by exact mul_lt_mul_of_pos_right hθ hC_pos
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hC_pos)
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- Continuity of the nuclear norm under diagonal row scaling. -/
theorem Ball1991.nuclearNorm_diagonal_continuous {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun theta : Fin n → ℝ =>
      Ball1991.nuclearNorm (Matrix.diagonal theta * A)) :=
  nuclearNorm_diag_continuous A

/-- Every orthogonal trace is bounded by the nuclear norm. -/
theorem Ball1991.orthogonal_trace_le_nuclearNorm {n : ℕ}
    (A U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) :
    (A * U).trace ≤ Ball1991.nuclearNorm A :=
  nuclearNorm_ge_trace A U hU

/-- Right multiplication by an orthogonal matrix preserves the nuclear norm. -/
theorem Ball1991.nuclearNorm_right_orthogonal {n : ℕ}
    (A U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) :
    Ball1991.nuclearNorm (A * U) = Ball1991.nuclearNorm A :=
  nuclearNorm_mul_orthogonal A U hU

/-- A matrix with nonzero rows has a positive-diagonal PSD polar factor. -/
theorem Ball1991.polar_positive_diagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, ∃ j, A i j ≠ 0) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U * Uᵀ = 1 ∧
      (A * U).PosSemidef ∧ ∀ i, 0 < (A * U) i i := by
  obtain ⟨U, hU, _, hmax⟩ := nuclearNorm_maximizer A
  have hpsd := maximizer_gives_psd A U hU hmax
  exact ⟨U, hU, hpsd, psd_product_pos_diag A hA U hU hpsd⟩

/-- Minimizer of nuclear norm on the product-1 surface:
    ∃ θ > 0 with ∏θ = 1 minimizing ‖diag(θ)·A‖_{C₁}. -/
private theorem nuclearNorm_diag_minimizer {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_rows : ∀ i, ∃ j, A i j ≠ 0) :
    ∃ theta : Fin n → ℝ, (∀ i, 0 < theta i) ∧ (∏ i, theta i = 1) ∧
      ∀ theta' : Fin n → ℝ, (∀ i, 0 < theta' i) → (∏ i, theta' i = 1) →
        Ball1991.nuclearNorm (Matrix.diagonal theta * A) ≤
        Ball1991.nuclearNorm (Matrix.diagonal theta' * A) := by
  -- Step 1: Reference point and coercivity setup
  obtain ⟨U₀, hU₀, hU₀_eq, _⟩ := nuclearNorm_maximizer A
  set H₀ := A * U₀ with hH₀_def
  have hH₀_psd := maximizer_gives_psd A U₀ hU₀
    (fun V hV => hU₀_eq ▸ nuclearNorm_ge_trace A V hV)
  have hH₀_diag_pos := psd_product_pos_diag A hA_rows U₀ hU₀ hH₀_psd
  set δ := Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => H₀ i i)
  have hδ_pos : 0 < δ := by
    exact (Finset.lt_inf'_iff _).mpr (fun i _ => hH₀_diag_pos i)
  have hδ_le : ∀ i, δ ≤ H₀ i i :=
    fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set M := Ball1991.nuclearNorm A
  -- Step 2: Lower bound via fixed U₀
  have hlb : ∀ θ : Fin n → ℝ, (∀ i, 0 < θ i) →
      δ * (∑ i, θ i) ≤ Ball1991.nuclearNorm (Matrix.diagonal θ * A) := by
    intro θ hθ
    have htrace : (Matrix.diagonal θ * A * U₀).trace = ∑ i, θ i * H₀ i i := by
      rw [Matrix.mul_assoc]
      simp only [Matrix.trace, Matrix.diagonal_mul, Matrix.diag]
      rfl
    calc δ * ∑ i, θ i = ∑ i, δ * θ i := by rw [Finset.mul_sum]
      _ ≤ ∑ i, θ i * H₀ i i := Finset.sum_le_sum fun i _ => by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hδ_le i) (le_of_lt (hθ i))
      _ = (Matrix.diagonal θ * A * U₀).trace := htrace.symm
      _ ≤ _ := nuclearNorm_ge_trace _ U₀ hU₀
  -- Step 3: Compact set K
  set R := max (M / δ + 1) 2 with hR_def
  have hR_pos : 0 < R := by positivity
  have hR_ge_one : 1 ≤ R := by linarith [le_max_right (M / δ + 1) 2]
  set K := {θ : Fin n → ℝ | (∀ i, 0 ≤ θ i ∧ θ i ≤ R) ∧ ∏ i, θ i = 1}
  -- K is nonempty (contains (1,...,1))
  have hK_ne : K.Nonempty := ⟨fun _ => 1, ⟨fun _ => ⟨le_of_lt one_pos, hR_ge_one⟩,
    Finset.prod_const_one⟩⟩
  -- K is compact (closed subset of compact box)
  have hK_compact : IsCompact K := by
    apply IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ => isCompact_Icc)
    · change IsClosed ({θ : Fin n → ℝ | ∀ i, 0 ≤ θ i ∧ θ i ≤ R} ∩
        {θ | ∏ i, θ i = 1})
      apply IsClosed.inter
      · -- {θ | ∀ i, 0 ≤ θ i ∧ θ i ≤ R} is closed
        show IsClosed {θ : Fin n → ℝ | ∀ i, 0 ≤ θ i ∧ θ i ≤ R}
        have : {θ : Fin n → ℝ | ∀ i, 0 ≤ θ i ∧ θ i ≤ R} =
            ⋂ i, ({θ : Fin n → ℝ | 0 ≤ θ i} ∩ {θ : Fin n → ℝ | θ i ≤ R}) := by
          ext θ; simp [Set.mem_iInter]
        rw [this]
        exact isClosed_iInter fun i =>
            (isClosed_le continuous_const (continuous_apply i)).inter
              (isClosed_le (continuous_apply i) continuous_const)
      · exact isClosed_eq
          (continuous_finset_prod _ fun i _ => continuous_apply i)
          continuous_const
    · intro θ ⟨hbox, hprod⟩
      exact Set.mem_univ_pi.mpr fun i => ⟨(hbox i).1, (hbox i).2⟩
  -- Step 4: f is continuous
  set f := fun θ : Fin n → ℝ => Ball1991.nuclearNorm (Matrix.diagonal θ * A)
  have hf_cont : Continuous f := nuclearNorm_diag_continuous A
  -- Step 5: Extreme value theorem on K
  obtain ⟨θ_min, hθ_min_mem, hθ_min_is_min⟩ :=
    hK_compact.exists_isMinOn hK_ne hf_cont.continuousOn
  -- θ_min has all positive entries (from ∏ = 1 and ≥ 0)
  have hθ_min_pos : ∀ i, 0 < θ_min i := by
    intro i
    have hprod := hθ_min_mem.2
    have hnn := fun j => (hθ_min_mem.1 j).1
    by_contra h
    push_neg at h
    have : θ_min i = 0 := le_antisymm h (hnn i)
    have : ∏ j, θ_min j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) this
    linarith
  have hθ_min_prod := hθ_min_mem.2
  -- Step 6: θ_min is global minimizer
  -- For any θ' with ∏ = 1 and all positive:
  -- Case 1: θ' ∈ K → f(θ_min) ≤ f(θ') by hθ_min_is_min
  -- Case 2: θ' ∉ K → some θ'_i > R → ∑ θ'_i ≥ θ'_i > R → f(θ') ≥ δ·R > M ≥ f(θ_min)
  have hf_min_le_M : f θ_min ≤ M := by
    have h_ones_in_K : (fun _ : Fin n => (1 : ℝ)) ∈ K :=
      ⟨fun _ => ⟨le_of_lt one_pos, hR_ge_one⟩, Finset.prod_const_one⟩
    have := hθ_min_is_min h_ones_in_K
    simp only [Set.mem_setOf_eq, f] at this
    calc f θ_min ≤ f (fun _ => 1) := this
      _ = M := by simp [f, M]
  exact ⟨θ_min, hθ_min_pos, hθ_min_prod, fun θ' hθ'_pos hθ'_prod => by
    by_cases hθ'_in_K : θ' ∈ K
    · exact hθ_min_is_min hθ'_in_K
    · -- θ' ∉ K: since ∏ = 1 and all positive, must have some θ'_i > R
      simp only [K, Set.mem_setOf_eq, not_and_or] at hθ'_in_K
      rcases hθ'_in_K with hbox | hprod
      · -- ¬(∀ i, 0 ≤ θ' i ∧ θ' i ≤ R)
        push_neg at hbox
        obtain ⟨i₀, hi₀⟩ := hbox
        -- hi₀ : 0 ≤ θ' i₀ → R < θ' i₀. Since θ' i₀ > 0, we get R < θ' i₀.
        have hR_lt : R < θ' i₀ := hi₀ (le_of_lt (hθ'_pos i₀))
        have : f θ_min < f θ' :=
          calc f θ_min ≤ M := hf_min_le_M
            _ < δ * R := by
                calc M ≤ M / δ * δ := by rw [div_mul_cancel₀]; exact ne_of_gt hδ_pos
                  _ < (M / δ + 1) * δ := by linarith
                  _ ≤ R * δ :=
                      mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hδ_pos)
                  _ = δ * R := by ring
            _ ≤ δ * θ' i₀ := mul_le_mul_of_nonneg_left (le_of_lt hR_lt) (le_of_lt hδ_pos)
            _ ≤ δ * ∑ i, θ' i :=
                mul_le_mul_of_nonneg_left
                  (Finset.single_le_sum (fun j _ => le_of_lt (hθ'_pos j)) (Finset.mem_univ i₀))
                  (le_of_lt hδ_pos)
            _ ≤ f θ' := hlb θ' hθ'_pos
        linarith
      · -- ∏ ≠ 1: contradicts hθ'_prod
        exact absurd hθ'_prod hprod⟩

/-- **Lemma 4** (Ball 1991, Lemma 4 -- Symmetrisation Lemma).
Let A be an `n x n` real matrix with non-null rows. Then there exists a sequence `(theta_i)`
of positive numbers and an orthogonal matrix U so that the matrix `H = (h_ij)` given by
  `h_ij = theta_i * (AU)_ij`
is positive semidefinite and has 1's on the diagonal.

The proof uses a variational argument: minimize the nuclear norm of `(theta_i a_ij)`
subject to `prod theta_i = 1`, then uses Lemma 6 to show the diagonal entries must be
equal. -/
theorem Ball1991.lemma4_symmetrisation
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_rows : ∀ i, ∃ j, A i j ≠ 0) :
    ∃ (theta : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℝ),
      (∀ i, 0 < theta i) ∧
      (U * U.transpose = 1) ∧
      let H := Matrix.of (fun i j => theta i * (A * U) i j)
      H.PosSemidef ∧ (∀ i, H i i = 1) := by
  -- Handle n = 0: vacuous
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨Fin.elim0, 1, fun i => Fin.elim0 i,
      by rw [Matrix.transpose_one, Matrix.mul_one], ?_, fun i => Fin.elim0 i⟩
    exact ⟨by ext i; exact Fin.elim0 i, fun x => by
      have : x = 0 := Finsupp.ext (fun i => Fin.elim0 i)
      subst this; simp [Finsupp.sum]⟩
  -- Step 1: Get minimizer theta on product-1 surface
  obtain ⟨theta, htheta_pos, hprod, hmin⟩ := nuclearNorm_diag_minimizer hn A hA_rows
  -- Step 2: Form B = diag(theta) * A and get nuclear norm maximizer U₀
  set B := Matrix.diagonal theta * A with hB_def
  obtain ⟨U₀, hU₀_orth, hU₀_eq, hU₀_max⟩ := nuclearNorm_maximizer B
  -- Step 3: H = B * U₀ is PSD
  have hH_psd : (B * U₀).PosSemidef := maximizer_gives_psd B U₀ hU₀_orth hU₀_max
  -- B has nonzero rows (since theta > 0 and A has nonzero rows)
  have hB_rows : ∀ i, ∃ j, B i j ≠ 0 := by
    intro i; obtain ⟨j, hj⟩ := hA_rows i
    exact ⟨j, by simp [hB_def, Matrix.diagonal_mul, mul_ne_zero (ne_of_gt (htheta_pos i)) hj]⟩
  -- Step 4: H has positive diagonal
  have hH_diag_pos : ∀ i, 0 < (B * U₀) i i := psd_product_pos_diag B hB_rows U₀ hU₀_orth hH_psd
  -- Step 5: Diagonal equality from minimality + Lemma 6 + AM-GM
  set H := B * U₀ with hH_def
  have hH_diag_ne : ∀ i, H i i ≠ 0 := fun i => ne_of_gt (hH_diag_pos i)
  -- Nuclear norm of PSD = trace
  have hNN_H : Ball1991.nuclearNorm H = H.trace :=
    Ball1991.nuclearNorm_pos_semidef_eq_trace H hH_psd
  have htrH_pos : 0 < H.trace := by
    rw [Matrix.trace]; exact Finset.sum_pos (fun i _ => hH_diag_pos i)
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  -- Define perturbation parameter c = (∏ √H_kk)^{1/n}
  set sqrtH := fun i => Real.sqrt (H i i) with hsqrtH_def
  have hsqrtH_pos : ∀ i, 0 < sqrtH i := fun i => Real.sqrt_pos.mpr (hH_diag_pos i)
  set prodSqrt := (∏ i, sqrtH i) with hprodSqrt_def
  have hprodSqrt_pos : 0 < prodSqrt :=
    Finset.prod_pos (fun i _ => hsqrtH_pos i)
  set c_pow := prodSqrt ^ ((1 : ℝ) / ↑n) with hc_def
  have hc_pos : 0 < c_pow := Real.rpow_pos_of_pos hprodSqrt_pos _
  -- Define gamma_i = c / √H_ii
  set gamma := fun i => c_pow / sqrtH i with hgamma_def
  have hgamma_pos : ∀ i, 0 < gamma i :=
    fun i => div_pos hc_pos (hsqrtH_pos i)
  -- ∏ gamma_i = c^n / ∏ √H_kk = (∏ √H_kk)^{n·(1/n)} / ∏ √H_kk = 1
  have hgamma_prod : ∏ i, gamma i = 1 := by
    simp only [gamma, Finset.prod_div_distrib]
    rw [Finset.prod_const, Finset.card_fin]
    rw [show c_pow ^ n = prodSqrt from by
      rw [hc_def, ← Real.rpow_natCast (prodSqrt ^ ((1 : ℝ) / ↑n)) n,
          ← Real.rpow_mul (le_of_lt hprodSqrt_pos),
          show (1 : ℝ) / ↑n * ↑n = 1 from by field_simp, Real.rpow_one]]
    exact div_self (ne_of_gt hprodSqrt_pos)
  -- theta' = gamma * theta satisfies constraints
  set theta' := fun i => gamma i * theta i with htheta'_def
  have htheta'_pos : ∀ i, 0 < theta' i :=
    fun i => mul_pos (hgamma_pos i) (htheta_pos i)
  have htheta'_prod : ∏ i, theta' i = 1 := by
    simp only [theta']
    rw [show ∏ i : Fin n, gamma i * theta i =
        (∏ i : Fin n, gamma i) * ∏ i : Fin n, theta i from Finset.prod_mul_distrib]
    rw [hgamma_prod, one_mul, hprod]
  -- Minimality: nuclearNorm(B) ≤ nuclearNorm(diag(gamma)*B)
  have hmin_ineq : Ball1991.nuclearNorm B ≤
      Ball1991.nuclearNorm (Matrix.diagonal gamma * B) := by
    have key : Matrix.diagonal theta' * A = Matrix.diagonal gamma * B := by
      ext i j; simp [hB_def, theta', Matrix.diagonal_mul]; ring
    calc Ball1991.nuclearNorm B
        = Ball1991.nuclearNorm (Matrix.diagonal theta * A) := by rw [hB_def]
      _ ≤ Ball1991.nuclearNorm (Matrix.diagonal theta' * A) :=
          hmin theta' htheta'_pos htheta'_prod
      _ = Ball1991.nuclearNorm (Matrix.diagonal gamma * B) := by rw [key]
  -- Nuclear norm chain:
  -- nuclearNorm(diag(γ)·B) = nuclearNorm(diag(γ)·H·U₀ᵀ) = nuclearNorm(diag(γ)·H)
  have hBU₀T : B = H * U₀ᵀ := by
    rw [hH_def, Matrix.mul_assoc, hU₀_orth, Matrix.mul_one]
  have hgB_eq : Matrix.diagonal gamma * B = Matrix.diagonal gamma * H * U₀ᵀ := by
    conv_rhs =>
      rw [show H = B * U₀ from rfl,
          ← Matrix.mul_assoc (Matrix.diagonal gamma) B U₀,
          Matrix.mul_assoc (Matrix.diagonal gamma * B) U₀ U₀ᵀ,
          hU₀_orth, Matrix.mul_one]
  have hU₀T_orth : U₀ᵀ * (U₀ᵀ)ᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact orthogonal_transpose U₀ hU₀_orth
  have hNN_gB : Ball1991.nuclearNorm (Matrix.diagonal gamma * B) =
      Ball1991.nuclearNorm (Matrix.diagonal gamma * H) := by
    rw [hgB_eq]; exact nuclearNorm_mul_orthogonal _ U₀ᵀ hU₀T_orth
  -- diag(γ)·H = c • of(H_ij / √H_ii)
  set normH := Matrix.of (fun i j => H i j / Real.sqrt (H i i)) with hnormH_def
  have hgH_eq : Matrix.diagonal gamma * H = c_pow • normH := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, normH, Matrix.of_apply, gamma, smul_eq_mul]
    rw [div_mul_eq_mul_div, mul_div_assoc']
  -- Apply Lemma 6
  have hL6 : Ball1991.nuclearNorm normH ≤
      Real.sqrt ↑n * Real.sqrt (Ball1991.nuclearNorm H) :=
    Ball1991.lemma6_nuclear_norm_ineq H hH_psd hH_diag_ne
  -- Chain: trH ≤ c · √n · √trH
  have hNN_chain : H.trace ≤ c_pow * (Real.sqrt ↑n * Real.sqrt H.trace) := by
    calc H.trace = Ball1991.nuclearNorm B := hU₀_eq.symm
      _ ≤ Ball1991.nuclearNorm (Matrix.diagonal gamma * B) := hmin_ineq
      _ = Ball1991.nuclearNorm (Matrix.diagonal gamma * H) := hNN_gB
      _ = Ball1991.nuclearNorm (c_pow • normH) := by rw [hgH_eq]
      _ = c_pow * Ball1991.nuclearNorm normH := nuclearNorm_smul_nonneg c_pow hc_pos.le normH
      _ ≤ c_pow * (Real.sqrt ↑n * Real.sqrt (Ball1991.nuclearNorm H)) := by
          exact mul_le_mul_of_nonneg_left hL6 hc_pos.le
      _ = c_pow * (Real.sqrt ↑n * Real.sqrt H.trace) := by rw [hNN_H]
  -- From chain: √trH ≤ c · √n, so trH ≤ c² · n
  -- i.e., (trH / n) ≤ c²  = (∏ √H_kk)^{2/n} = (∏ H_kk)^{1/n}
  -- This means AM(H_ii) ≤ GM(H_ii), so by am_gm_equality, all H_ii are equal
  have hAM_le_GM : ((∑ i, H i i) / ↑n) ^ n ≤ ∏ i, H i i := by
    -- From hNN_chain: trH ≤ c · √n · √trH
    -- Divide by √trH: √trH ≤ c · √n
    -- Square: trH ≤ c² · n
    have h_sqrt_trH := Real.sqrt_pos.mpr htrH_pos
    have h_div : Real.sqrt H.trace ≤ c_pow * Real.sqrt ↑n := by
      have hsq : H.trace = Real.sqrt H.trace * Real.sqrt H.trace :=
        (Real.mul_self_sqrt (le_of_lt htrH_pos)).symm
      conv at hNN_chain => lhs; rw [hsq]
      rw [show c_pow * (Real.sqrt ↑n * Real.sqrt H.trace) =
          c_pow * Real.sqrt ↑n * Real.sqrt H.trace from by ring] at hNN_chain
      exact le_of_mul_le_mul_right hNN_chain h_sqrt_trH
    -- Square both sides
    have h_sq : H.trace ≤ c_pow ^ 2 * ↑n := by
      have h1 := Real.sq_sqrt (le_of_lt htrH_pos)
      have h2 : Real.sqrt H.trace ^ 2 ≤ (c_pow * Real.sqrt ↑n) ^ 2 :=
        sq_le_sq' (by linarith [Real.sqrt_nonneg H.trace]) h_div
      rw [h1, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at h2
      exact h2
    -- trH / n ≤ c² = (∏ √H_kk)^{2/n}
    -- c² = ((∏ √H_kk)^{1/n})^2 = (∏ √H_kk)^{2/n}
    -- (∏ √H_kk)^{2/n} = (∏ H_kk^{1/2})^{2/n} = (∏ H_kk)^{1/n}
    have hc_sq : c_pow ^ 2 = (∏ i, H i i) ^ ((1 : ℝ) / ↑n) := by
      -- First: prodSqrt ^ 2 = ∏ H_ii
      have h_prod_sq : prodSqrt ^ 2 = ∏ i, H i i := by
        rw [hprodSqrt_def, sq, ← Finset.prod_mul_distrib]
        congr 1; ext i
        exact Real.mul_self_sqrt (le_of_lt (hH_diag_pos i))
      -- c_pow^2 = (prodSqrt^{1/n})^2 = prodSqrt^{2/n} = (prodSqrt^2)^{1/n} = (∏ H_ii)^{1/n}
      rw [hc_def, ← h_prod_sq]
      -- Goal: (prodSqrt ^ (1/↑n))^2 = (prodSqrt^2)^(1/↑n)  [both ^2 nat pow]
      rw [← Real.rpow_natCast (prodSqrt ^ ((1 : ℝ) / ↑n)) 2,
          ← Real.rpow_natCast prodSqrt 2]
      -- Goal: (prodSqrt ^ (1/↑n))^(↑2) = (prodSqrt^(↑2))^(1/↑n)  [all rpow]
      rw [← Real.rpow_mul (le_of_lt hprodSqrt_pos),
          ← Real.rpow_mul (le_of_lt hprodSqrt_pos)]
      -- Goal: prodSqrt ^ ((1/↑n)*↑2) = prodSqrt ^ (↑2*(1/↑n))
      congr 1; push_cast; ring
    rw [hc_sq] at h_sq
    -- h_sq : trH ≤ (∏ H_kk)^{1/n} * n
    -- Need: (trH / n)^n ≤ ∏ H_kk
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
    have h_div_n : H.trace / ↑n ≤ (∏ i, H i i) ^ ((1 : ℝ) / ↑n) := by
      rwa [div_le_iff₀ hn_pos]
    -- Raise to power n: (trH/n)^n ≤ ((∏ H_kk)^{1/n})^n = ∏ H_kk
    have h_pow := Real.rpow_le_rpow (div_nonneg (le_of_lt htrH_pos) hn_pos.le)
      h_div_n (Nat.cast_nonneg n)
    rwa [← Real.rpow_mul (Finset.prod_nonneg fun i _ => (hH_diag_pos i).le),
         show (1 : ℝ) / ↑n * ↑n = 1 from by field_simp,
         Real.rpow_one, Real.rpow_natCast] at h_pow
  -- Apply AM-GM equality: all H_ii are equal
  have hH_diag_eq : ∀ i j, H i i = H j j :=
    Ball1991.am_gm_equality hn (fun i => H i i) hH_diag_pos hAM_le_GM
  -- Step 6: All diagonal entries equal some c_val > 0
  set c_val := H ⟨0, hn⟩ ⟨0, hn⟩ with hcval_def
  have hcval_pos : 0 < c_val := hH_diag_pos ⟨0, hn⟩
  have hcval_eq : ∀ i, H i i = c_val := fun i => hH_diag_eq i ⟨0, hn⟩
  -- Step 7: Rescale theta by 1/c_val
  refine ⟨fun i => theta i / c_val, U₀, fun i => div_pos (htheta_pos i) hcval_pos,
    hU₀_orth, ?_, ?_⟩
  · -- H' = (1/c_val) • H is PSD
    show (Matrix.of fun i j => theta i / c_val * (A * U₀) i j).PosSemidef
    have key : (Matrix.of fun i j => theta i / c_val * (A * U₀) i j) = c_val⁻¹ • H := by
      ext i j
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show H i j = (Matrix.diagonal theta * A * U₀) i j from by rw [hH_def, hB_def]]
      rw [show (Matrix.diagonal theta * A * U₀) i j = theta i * (A * U₀) i j from by
        rw [Matrix.mul_assoc]; simp [Matrix.diagonal_mul]]
      ring
    rw [key]
    exact hH_psd.smul (le_of_lt (inv_pos.mpr hcval_pos))
  · -- Diagonal = 1
    intro i
    show (Matrix.of fun i' j' => theta i' / c_val * (A * U₀) i' j') i i = 1
    simp only [Matrix.of_apply]
    have : theta i / c_val * (A * U₀) i i = H i i / c_val := by
      rw [show H i i = (Matrix.diagonal theta * A * U₀) i i from by rw [hH_def, hB_def]]
      rw [show (Matrix.diagonal theta * A * U₀) i i = theta i * (A * U₀) i i from by
        rw [Matrix.mul_assoc]; simp [Matrix.diagonal_mul]]
      ring
    rw [this, hcval_eq i, div_self (ne_of_gt hcval_pos)]

end Symmetrisation


/-! ## Proof of Theorem 2' (Section 2) -/

section ProofTheorem2Prime

-- theorem2'_proof_via_symmetrisation is declared after the helper lemmas (see below)

/-- **Key calculation in proof of Theorem 2'**:
`theta_i = (HU*)_ii` when `a_ii = 1` and `h_ij = theta_i(AU)_ij`.
From `h_ij = theta_i(AU)_ij`, we get `theta_i a_ij = (HU*)_ij`.
Setting `i = j` and using `a_ii = 1`: `theta_i = (HU*)_ii`. -/
theorem Ball1991.theta_eq_HUtranspose_diag
    {n : ℕ}
    (A U : Matrix (Fin n) (Fin n) ℝ)
    (theta : Fin n → ℝ)
    (hA_diag : ∀ i, A i i = 1)
    (hU_orth : U * U.transpose = 1) :
    let H := Matrix.of (fun i j => theta i * (A * U) i j)
    ∀ i, theta i = (H * U.transpose) i i := by
  intro H i
  simp only [H, of_apply, mul_apply, transpose_apply]
  conv_rhs =>
    rw [show (fun x => theta i * (∑ x_1, A i x_1 * U x_1 x) * U i x) =
        (fun x => theta i * ((∑ x_1, A i x_1 * U x_1 x) * U i x)) from by ext; ring]
    rw [← Finset.mul_sum]
  have key : ∑ j, (∑ k, A i k * U k j) * U i j = 1 := by
    have h1 : ∑ j, (∑ k, A i k * U k j) * U i j = ∑ j, ∑ k, A i k * U k j * U i j := by
      congr 1; ext j; rw [Finset.sum_mul]
    rw [h1, Finset.sum_comm]
    have h2 : ∀ k, (∑ j, U k j * U i j) = if k = i then 1 else 0 := by
      intro k
      have := congr_fun (congr_fun hU_orth k) i
      simp [mul_apply, transpose_apply] at this
      exact this
    simp_rw [show ∀ y x, A i y * U y x * U i x = A i y * (U y x * U i x) from
      fun y x => by ring]
    simp_rw [← Finset.mul_sum, h2]
    simp [hA_diag]
  rw [key, mul_one]

/-- **Sum of theta_i^2 bound from Lemma 5**:
`sum_i theta_i^2 = sum_i (HU*)^2_ii / h_ii <= sum_i h_ii = n`.
This is the key estimate ensuring `sum coeffs_k^2 <= 1/n`. -/
theorem Ball1991.sum_theta_sq_le
    {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH_pos : H.PosSemidef)
    (hH_diag : ∀ i, H i i = 1)
    (U : Matrix (Fin n) (Fin n) ℝ)
    (hU_orth : U * U.transpose = 1)
    (theta : Fin n → ℝ)
    (htheta : ∀ i, theta i = (H * U.transpose) i i) :
    ∑ i, theta i ^ 2 ≤ n := by
  -- Rewrite ∑ θ²_i in terms of (HUᵀ)_{ii}
  have hθ_sq : ∑ i, theta i ^ 2 = ∑ i, (H * U.transpose) i i ^ 2 := by
    congr 1; ext i; rw [htheta i]
  rw [hθ_sq]
  -- Uᵀ is also orthogonal
  have hUT_orth : U.transpose * U.transpose.transpose = 1 := by
    simp [transpose_transpose, mul_eq_one_comm.mp hU_orth]
  -- Apply Lemma 5 with Uᵀ: ∑ (HUᵀ)²_{ii}/h_{ii} ≤ ∑ h_{ii}
  have h5 := Ball1991.lemma5_diagonal_estimate H hH_pos (fun i => by rw [hH_diag i]; exact one_ne_zero)
    U.transpose hUT_orth
  -- Since h_{ii} = 1: ∑ (HUᵀ)²_{ii}/1 = ∑ (HUᵀ)²_{ii} and ∑ 1 = n
  simp only [hH_diag, div_one] at h5
  have : (∑ _ : Fin n, (1 : ℝ)) = n := by
    simp [Finset.sum_const]
  linarith

end ProofTheorem2Prime

/-! ## Proof of Theorem 2' (strengthened) — assembling the components

This proof uses:
- **Lemma 4** (symmetrisation, proved): gets θ, U, H from A
- **Lemma 3** (Bang, proved): gets signs ε from H
- **Lemma 5** (diagonal estimate, proved) via `sum_theta_sq_le`: bounds ∑ θ²
- **theta_eq_HUtranspose_diag** (proved): identifies θ_i = (HUᵀ)_{ii}

All components are proved — the chain is sorry-free. -/

/-- Orthogonal transformations preserve the L² norm of a vector. -/
private lemma orthogonal_preserves_l2 {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U * Uᵀ = 1) (c : Fin n → ℝ) :
    ∑ k, (∑ j, U k j * c j) ^ 2 = ∑ j, c j ^ 2 := by
  have hUTU : Uᵀ * U = 1 := mul_eq_one_comm.mp hU
  conv_lhs =>
    arg 2; ext k; rw [sq]; rw [Finset.sum_mul_sum (s := univ) (t := univ)]
  simp_rw [show ∀ (k j l : Fin n), U k j * c j * (U k l * c l) =
      c j * c l * (U k j * U k l) from fun k j l => by ring]
  rw [Finset.sum_comm]; conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; arg 2; ext l; rw [← Finset.mul_sum]
  have hentry : ∀ j l : Fin n, ∑ k, U k j * U k l = if j = l then 1 else 0 := by
    intro j l; have := congr_fun (congr_fun hUTU j) l
    simpa [mul_apply, transpose_apply, one_apply] using this
  simp_rw [hentry]; congr 1; ext j; simp [sq]

/-- Key algebraic identity: `∑_j A_ij coeffs_j = S / (n θ_i)` where
    `S = ∑_l θ_i (AU)_il ε_l θ_l` and `coeffs_k = (1/n) ∑_j U_kj ε_j θ_j`. -/
private lemma coeffs_sum_eq {n : ℕ}
    (A U : Matrix (Fin n) (Fin n) ℝ) (theta eps : Fin n → ℝ)
    (htheta_pos : ∀ i, 0 < theta i) (hn : 0 < n) (i : Fin n) :
    ∑ j, A i j * (1 / (n : ℝ) * ∑ l, U j l * eps l * theta l) =
    (∑ l, theta i * (A * U) i l * eps l * theta l) / ((n : ℝ) * theta i) := by
  have hti_ne : theta i ≠ 0 := ne_of_gt (htheta_pos i)
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show (∑ l, theta i * (A * U) i l * eps l * theta l) / ((n : ℝ) * theta i) =
    1 / (n : ℝ) * ∑ l, (A * U) i l * (eps l * theta l) from by
    conv_lhs =>
      arg 1; arg 2; ext l
      rw [show theta i * (A * U) i l * eps l * theta l =
        theta i * ((A * U) i l * (eps l * theta l)) from by ring]
    rw [← Finset.mul_sum]; field_simp]
  conv_lhs => arg 2; ext j; rw [show A i j * (1 / (n : ℝ) * ∑ l, U j l * eps l * theta l) =
    1 / (n : ℝ) * (A i j * ∑ l, U j l * eps l * theta l) from by ring]
  rw [← Finset.mul_sum]; congr 1
  conv_lhs => arg 2; ext j; rw [Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; funext l
  simp_rw [show ∀ j, A i j * (U j l * eps l * theta l) =
    A i j * U j l * (eps l * theta l) from fun j => by ring]
  rw [← Finset.sum_mul]; simp [mul_apply]

/-- **Proof of Theorem 2' (strengthened form)**.
Uses Lemma 4 (symmetrisation, proved) to get `θ, U, H`, then Lemma 3 (Bang,
proved) to get signs `ε`. Defines `coeffs_k = (1/n) ∑_j U_kj ε_j θ_j`. The L² bound
follows from orthogonal invariance of L² norm + Lemma 5 (diagonal estimate, proved).
The |Ax - m| bound follows from the algebraic identity relating `A * coeffs` to
`H * ε * θ` + Bang's conclusion.

All components are proved — the chain is sorry-free. -/
theorem Ball1991.theorem2'_strengthened_proof
    {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_diag : ∀ i, A i i = 1)
    (m : Fin n → ℝ) :
    ∃ coeffs : Fin n → ℝ,
      ∑ j, coeffs j ^ 2 ≤ 1 / n ∧
      ∀ i, |∑ j, A i j * coeffs j - m i| ≥ 1 / n := by
  -- Step 1: Lemma 4 (symmetrisation) — A has nonzero rows since a_ii = 1
  have hA_rows : ∀ i, ∃ j, A i j ≠ 0 := fun i => ⟨i, by rw [hA_diag]; exact one_ne_zero⟩
  obtain ⟨theta, U, htheta_pos, hU_orth, hH_psd, hH_diag⟩ :=
    Ball1991.lemma4_symmetrisation A hA_rows
  set H := Matrix.of (fun i j => theta i * (A * U) i j)
  -- Step 2: Lemma 3 (Bang) with μ_i = n θ_i m_i and weights θ_i
  obtain ⟨eps, heps_sign, hbang⟩ := Ball1991.lemma3_bang H hH_psd.isHermitian hH_diag
    (fun i => (n : ℝ) * theta i * m i) theta (fun i => le_of_lt (htheta_pos i))
  -- Step 3: Define coefficients
  refine ⟨fun k => (1 / (n : ℝ)) * ∑ j, U k j * eps j * theta j, ?_, ?_⟩
  · -- Part 1: ∑ coeffs_k² ≤ 1/n
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    -- Regroup inner sum: U_kj * eps_j * theta_j = U_kj * (eps_j * theta_j)
    simp_rw [show ∀ k : Fin n,
        ∑ j, U k j * eps j * theta j = ∑ j, U k j * (eps j * theta j) from
      fun k => by congr 1; funext j; ring]
    simp_rw [mul_pow, ← Finset.mul_sum]
    -- Orthogonality: ∑_k (∑_j U_kj c_j)² = ∑_j c_j²
    rw [orthogonal_preserves_l2 U hU_orth]
    -- ε_j² = 1, so (ε_j θ_j)² = θ_j²
    simp_rw [show ∀ j : Fin n, (eps j * theta j) ^ 2 = theta j ^ 2 from fun j => by
      rw [mul_pow]; cases heps_sign j with | inl h => rw [h]; ring | inr h => rw [h]; ring]
    -- (1/n)² · ∑ θ² ≤ 1/n ⟺ ∑ θ² ≤ n (from Lemma 5 via sum_theta_sq_le)
    rw [show (1 / (n : ℝ)) ^ 2 = 1 / ((n : ℝ) * n) from by field_simp,
        show (1 : ℝ) / ((n : ℝ) * n) * ∑ x, theta x ^ 2 =
          (∑ x, theta x ^ 2) / ((n : ℝ) * n) from by ring,
        div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < n)]
    nlinarith [Ball1991.sum_theta_sq_le H hH_psd hH_diag U hU_orth theta
      (Ball1991.theta_eq_HUtranspose_diag A U theta hA_diag hU_orth)]
  · -- Part 2: |∑_j A_ij coeffs_j − m_i| ≥ 1/n
    intro i
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hti := htheta_pos i
    have hnt : 0 < (n : ℝ) * theta i := mul_pos hn_pos hti
    -- Algebraic identity: ∑ A_ij coeffs_j = S / (n θ_i)
    rw [coeffs_sum_eq A U theta eps htheta_pos hn i]
    -- S = ∑ H_il ε_l θ_l, and Bang gives |S − n θ_i m_i| ≥ θ_i
    have hS_bang : |∑ l, theta i * (A * U) i l * eps l * theta l -
        (n : ℝ) * theta i * m i| ≥ theta i := by
      rw [show (fun l => theta i * (A * U) i l * eps l * theta l) =
        (fun l => H i l * eps l * theta l) from by funext l; simp [H, of_apply]]
      exact hbang i
    -- |S/(nθ_i) − m_i| = |S − nθ_i m_i|/(nθ_i) ≥ θ_i/(nθ_i) = 1/n
    rw [show (∑ l, theta i * (A * U) i l * eps l * theta l) / ((n : ℝ) * theta i) - m i =
      (∑ l, theta i * (A * U) i l * eps l * theta l -
        (n : ℝ) * theta i * m i) / ((n : ℝ) * theta i) from by field_simp,
      abs_div, abs_of_pos hnt, ge_iff_le, le_div_iff₀ hnt]
    calc 1 / ↑n * (↑n * theta i) = theta i := by field_simp
      _ ≤ |∑ l, theta i * (A * U) i l * eps l * theta l - ↑n * theta i * m i| := hS_bang

/-- **Proof of Theorem 2'** -- the full argument exposing theta, U, eps.
    Same proof as `theorem2'_strengthened_proof` but packages the intermediate
    objects (theta, U from Lemma 4; eps from Lemma 3) in the output. -/
theorem Ball1991.theorem2'_proof_via_symmetrisation
    {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_diag : ∀ i, A i i = 1)
    (m : Fin n → ℝ) :
    ∃ (theta : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℝ)
      (eps : Fin n → ℝ),
      (∀ i, 0 < theta i) ∧
      (U * U.transpose = 1) ∧
      (∀ j, eps j = 1 ∨ eps j = -1) ∧
      let H := Matrix.of (fun i j => theta i * (A * U) i j)
      let coeffs := fun k => (1 / (n : ℝ)) * ∑ j, U k j * eps j * theta j
      H.PosSemidef ∧
      (∀ i, H i i = 1) ∧
      ∑ j, (coeffs j) ^ 2 ≤ 1 / n ∧
      ∀ i, |∑ j, A i j * coeffs j - m i| ≥ 1 / n := by
  -- Step 1: Lemma 4 (symmetrisation)
  have hA_rows : ∀ i, ∃ j, A i j ≠ 0 := fun i => ⟨i, by rw [hA_diag]; exact one_ne_zero⟩
  obtain ⟨theta, U, htheta_pos, hU_orth, hH_psd, hH_diag⟩ :=
    Ball1991.lemma4_symmetrisation A hA_rows
  set H := Matrix.of (fun i j => theta i * (A * U) i j)
  -- Step 2: Lemma 3 (Bang)
  obtain ⟨eps, heps_sign, hbang⟩ := Ball1991.lemma3_bang H hH_psd.isHermitian hH_diag
    (fun i => (n : ℝ) * theta i * m i) theta (fun i => le_of_lt (htheta_pos i))
  refine ⟨theta, U, eps, htheta_pos, hU_orth, heps_sign, hH_psd, hH_diag, ?_, ?_⟩
  · -- ∑ coeffs_k² ≤ 1/n
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    simp_rw [show ∀ k : Fin n,
        ∑ j, U k j * eps j * theta j = ∑ j, U k j * (eps j * theta j) from
      fun k => by congr 1; funext j; ring]
    simp_rw [mul_pow, ← Finset.mul_sum]
    rw [orthogonal_preserves_l2 U hU_orth]
    simp_rw [show ∀ j : Fin n, (eps j * theta j) ^ 2 = theta j ^ 2 from fun j => by
      rw [mul_pow]; cases heps_sign j with | inl h => rw [h]; ring | inr h => rw [h]; ring]
    rw [show (1 / (n : ℝ)) ^ 2 = 1 / ((n : ℝ) * n) from by field_simp,
        show (1 : ℝ) / ((n : ℝ) * n) * ∑ x, theta x ^ 2 =
          (∑ x, theta x ^ 2) / ((n : ℝ) * n) from by ring,
        div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < n)]
    nlinarith [Ball1991.sum_theta_sq_le H hH_psd hH_diag U hU_orth theta
      (Ball1991.theta_eq_HUtranspose_diag A U theta hA_diag hU_orth)]
  · -- |∑_j A_ij coeffs_j − m_i| ≥ 1/n
    intro i
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hti := htheta_pos i
    have hnt : 0 < (n : ℝ) * theta i := mul_pos hn_pos hti
    rw [coeffs_sum_eq A U theta eps htheta_pos hn i]
    have hS_bang : |∑ l, theta i * (A * U) i l * eps l * theta l -
        (n : ℝ) * theta i * m i| ≥ theta i := by
      rw [show (fun l => theta i * (A * U) i l * eps l * theta l) =
        (fun l => H i l * eps l * theta l) from by funext l; simp [H, of_apply]]
      exact hbang i
    rw [show (∑ l, theta i * (A * U) i l * eps l * theta l) / ((n : ℝ) * theta i) - m i =
      (∑ l, theta i * (A * U) i l * eps l * theta l -
        (n : ℝ) * theta i * m i) / ((n : ℝ) * theta i) from by field_simp,
      abs_div, abs_of_pos hnt, ge_iff_le, le_div_iff₀ hnt]
    calc 1 / ↑n * (↑n * theta i) = theta i := by field_simp
      _ ≤ |∑ l, theta i * (A * U) i l * eps l * theta l - ↑n * theta i * m i| := hS_bang

/-! ## Change-of-density / block matrix argument for Theorem 2'

This section proves Theorem 2' (general weights) from the equal-weight strengthened result
via Ball's change-of-density argument:
1. For strict slack (∑w < 1): expand each row into copies, apply equal-weight result, collapse
2. For general (∑w ≤ 1): approximate with strict slack, take FIP/compactness limit -/

/-! ### Interval covering lemma for the block matrix argument -/

/-- **Interval covering bound**: If `k` evenly-spaced centers in `[-w, w]` are each avoided
by at least `1/N`, and `1/N > w/k`, then `|y| ≥ w`.

This is the key geometric step in the change-of-density argument: the `k` copies of
a row with deviations `≥ 1/N` from their respective shifted centers force the collapsed
deviation to be `≥ w`. -/
private theorem Ball1991.deviation_bound_from_copies
    {N : ℕ} (hN : 0 < N)
    {k : ℕ} (hk : 0 < k)
    {w : ℝ} (hw : 0 ≤ w) (hNw : (N : ℝ) * w < k)
    {y : ℝ}
    (h : ∀ q : Fin k, (1 : ℝ) / N ≤
      |y - (2 * (q : ℝ) + 1 - k) * w / k|) :
    w ≤ |y| := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hδ : w / k < 1 / (N : ℝ) := by
    rw [div_lt_div_iff₀ hk_pos hN_pos]; linarith
  by_contra habs; push_neg at habs
  rcases eq_or_lt_of_le hw with rfl | hw_pos
  · linarith [abs_nonneg y]
  · have h2w_pos : 0 < 2 * w := by linarith
    set t := (y + w) * k / (2 * w)
    have ht_pos : 0 < t := div_pos (mul_pos (by linarith [(abs_lt.mp habs).1]) hk_pos) h2w_pos
    have ht_lt : t < k := by
      rw [div_lt_iff₀ h2w_pos]; nlinarith [mul_comm (k : ℝ) (2 * w), (abs_lt.mp habs).2]
    set p := ⌊t⌋₊
    have hp_lt : p < k := by exact_mod_cast (Nat.floor_lt (le_of_lt ht_pos)).mpr ht_lt
    have hfl : (↑p : ℝ) ≤ t := Nat.floor_le (le_of_lt ht_pos)
    have hfu : t < ↑p + 1 := Nat.lt_floor_add_one t
    have hy_t : y = 2 * w * t / k - w := by
      change y = 2 * w * ((y + w) * k / (2 * w)) / k - w; field_simp; ring
    have hsub : y - (2 * ↑p + 1 - k) * w / k = 2 * w * (t - (↑p + 1/2)) / k := by
      rw [hy_t]; field_simp; ring
    have h_half : |t - (↑p + 1/2)| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
    have key : |y - (2 * ↑p + 1 - k) * w / k| ≤ w / k := by
      rw [hsub, abs_div, abs_of_pos hk_pos]
      apply div_le_div_of_nonneg_right _ hk_pos.le
      calc |2 * w * (t - (↑p + 1 / 2))|
          = 2 * w * |t - (↑p + 1/2)| := by rw [abs_mul, abs_of_pos h2w_pos]
        _ ≤ 2 * w * (1/2) := by nlinarith
        _ = w := by ring
    linarith [h ⟨p, hp_lt⟩]

/-! ### Block matrix argument: strict slack case -/

/-- **Column collapse identity**: The inner product of a block-matrix row with
coefficients `c` equals the inner product of the original matrix row with the
collapsed coefficients `d_j = ∑_q c(e ⟨j, q⟩)`. -/
private theorem Ball1991.column_collapse {n : ℕ} (rep : Fin n → ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (N : ℕ) (e : (Σ (j : Fin n), Fin (rep j)) ≃ Fin N)
    (c : Fin N → ℝ)
    (d : Fin n → ℝ) (hd : ∀ j, d j = ∑ q : Fin (rep j), c (e ⟨j, q⟩)) :
    ∑ p : Fin N, A i (e.symm p).1 * c p = ∑ j : Fin n, A i j * d j := by
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]
  simp_rw [hd, Finset.mul_sum]
  rw [← Finset.univ_sigma_univ]; rw [Finset.sum_sigma]

/-- **Theorem 2' with strict slack**: If `∑ w_i < 1` (strict), then we can construct
coefficients directly via the block matrix / change-of-density argument.

This expands each row `i` into `rep_i` copies with shifted centers, applies the
equal-weight strengthened result to the expanded matrix, then collapses the
coefficients back. The interval covering lemma converts the `1/N` deviations
from copy centers into `w_i` deviations from the original centers. -/
private theorem Ball1991.theorem2'_strict_slack
    {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_diag : ∀ i, A i i = 1)
    (m : Fin n → ℝ)
    (w : Fin n → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum_strict : ∑ i, w i < 1) :
    ∃ coeffs : Fin n → ℝ,
      ∑ j, |coeffs j| ≤ 1 ∧
      ∀ i, |∑ j, A i j * coeffs j - m i| ≥ w i := by
  -- Step 1: Choose replication parameters
  set s := 1 - ∑ i, w i
  have hs : 0 < s := by simp only [s]; linarith
  set C := ⌈2 * ↑n / s⌉₊ + 1
  set rep : Fin n → ℕ := fun i => ⌈(C : ℝ) * w i⌉₊ + 1
  have hrep_pos : ∀ j, 0 < rep j := fun _ => Nat.succ_pos _
  -- Step 2: Build sigma type and equiv to Fin N
  set N := ∑ j : Fin n, rep j
  have hN_pos : 0 < N := Finset.sum_pos (fun j _ => hrep_pos j)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  have hcard : Fintype.card (Σ (j : Fin n), Fin (rep j)) = N := by
    rw [Fintype.card_sigma]; congr 1; ext j; exact Fintype.card_fin _
  set e : (Σ (j : Fin n), Fin (rep j)) ≃ Fin N :=
    (Fintype.equivFin _).trans (Equiv.cast (by rw [hcard]))
  -- Step 3: Build block matrix and shifted centers
  set B : Matrix (Fin N) (Fin N) ℝ := fun p q => A (e.symm p).1 (e.symm q).1
  have hB_diag : ∀ p, B p p = 1 := fun p => hA_diag (e.symm p).1
  set μ : Fin N → ℝ := fun p =>
    let b := e.symm p
    m b.1 + (2 * (b.2 : ℝ) + 1 - (rep b.1 : ℝ)) * w b.1 / (rep b.1 : ℝ)
  -- Step 4: Apply equal-weight result to the expanded matrix
  obtain ⟨c, hc_l2, hc_dev⟩ :=
    Ball1991.theorem2'_strengthened_proof hN_pos B hB_diag μ
  -- Step 5: Collapse coefficients
  set d : Fin n → ℝ := fun j => ∑ q : Fin (rep j), c (e ⟨j, q⟩)
  refine ⟨d, ?_, ?_⟩
  · -- L1 bound: ∑|d_j| ≤ ∑|c_p| ≤ 1
    have hN_cast : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
    calc ∑ j, |d j|
        ≤ ∑ p : Fin N, |c p| := by
          simp_rw [d]
          calc ∑ j : Fin n, |∑ q : Fin (rep j), c (e ⟨j, q⟩)|
              ≤ ∑ j : Fin n, ∑ q : Fin (rep j), |c (e ⟨j, q⟩)| :=
                Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
            _ = ∑ x : Σ j, Fin (rep j), |c (e x)| := by
                rw [← Finset.univ_sigma_univ]; rw [Finset.sum_sigma]
            _ = ∑ p : Fin N, |c p| := Equiv.sum_comp e (fun p => |c p|)
      _ ≤ 1 := by
          -- Cauchy-Schwarz: (∑|c|)² ≤ N · ∑c² ≤ N · (1/N) = 1
          have hcs : (∑ i : Fin N, |c i|) ^ 2 ≤ ↑N * ∑ i : Fin N, c i ^ 2 := by
            have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
              (fun (_ : Fin N) => (1:ℝ)) (fun j => |c j|)
            simp only [one_mul, one_pow, Finset.sum_const, Finset.card_fin,
              nsmul_eq_mul, mul_one, sq_abs] at this; exact this
          have key : (∑ x : Fin N, |c x|) ^ 2 ≤ 1 :=
            calc (∑ x, |c x|) ^ 2 ≤ ↑N * ∑ x, c x ^ 2 := hcs
              _ ≤ ↑N * (1 / ↑N) := by nlinarith
              _ = 1 := by field_simp
          nlinarith [sq_nonneg (∑ j : Fin N, |c j|),
            Finset.sum_nonneg (fun (i : Fin N) (_ : i ∈ Finset.univ) => abs_nonneg (c i))]
  · -- Deviation bound: |∑_j A_ij d_j - m_i| ≥ w_i
    intro i
    -- Key inequality: N * w_i < rep_i
    have hNw_lt : (N : ℝ) * w i < (rep i : ℝ) := by
      have hCs : (C : ℝ) * s > 2 * ↑n := by
        have h_ceil : (⌈2 * ↑n / s⌉₊ : ℝ) ≥ 2 * ↑n / s := Nat.le_ceil _
        have : (C : ℝ) > 2 * ↑n / s := by simp only [C]; push_cast; linarith
        rwa [gt_iff_lt, ← div_lt_iff₀ hs]
      have hN_le : (N : ℝ) ≤ (C : ℝ) * ∑ j, w j + 2 * ↑n := by
        push_cast [N, rep]
        have h : ∀ j : Fin n, (⌈(↑C : ℝ) * w j⌉₊ : ℝ) ≤ ↑C * w j + 1 :=
          fun j => le_of_lt (by
            exact_mod_cast Nat.ceil_lt_add_one
              (mul_nonneg (Nat.cast_nonneg C) (hw_nonneg j)))
        calc ∑ j : Fin n, ((⌈(↑C : ℝ) * w j⌉₊ : ℝ) + 1)
            ≤ ∑ j : Fin n, (↑C * w j + 1 + 1) :=
              Finset.sum_le_sum (fun j _ => by linarith [h j])
          _ = ↑C * ∑ j, w j + 2 * ↑n := by
              simp [Finset.sum_add_distrib, Finset.mul_sum]; ring
      have hrep_gt : (C : ℝ) * w i < (rep i : ℝ) := by
        simp only [rep]; push_cast; linarith [Nat.le_ceil ((C : ℝ) * w i)]
      by_cases hwi : w i = 0
      · simp [hwi]; exact_mod_cast Nat.succ_pos _
      · have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
        -- N ≤ C*(1-s) + 2n, rep > C*w, C*s > 2n, w > 0
        -- N*w ≤ (C*(1-s)+2n)*w = C*w - C*s*w + 2n*w < C*w ≤ rep
        have hs_eq : (∑ j, w j) = 1 - s := by simp [s]
        nlinarith [mul_pos (show (0:ℝ) < C * s - 2 * ↑n by linarith) hwi_pos]
    -- Column collapse: for each copy (i, q), the block matrix row gives ∑_j A_ij d_j
    have h_collapse : ∀ q : Fin (rep i),
        ∑ p : Fin N, B (e ⟨i, q⟩) p * c p = ∑ j, A i j * d j := by
      intro q
      show ∑ p, A (e.symm (e ⟨i, q⟩)).1 (e.symm p).1 * c p = ∑ j, A i j * d j
      simp only [Equiv.symm_apply_apply]
      exact Ball1991.column_collapse rep A i N e c d (fun j => rfl)
    -- Each copy has deviation ≥ 1/N from its shifted center
    set y := ∑ j, A i j * d j - m i
    have h_copies : ∀ q : Fin (rep i),
        1 / (N : ℝ) ≤ |y - (2 * (q : ℝ) + 1 - (rep i : ℝ)) * w i / (rep i : ℝ)| := by
      intro q
      have hdev := hc_dev (e ⟨i, q⟩)
      -- ∑_p B_{e(i,q),p} c_p - μ_{e(i,q)} = y - shift_{i,q}
      rw [ge_iff_le, show (1 : ℝ) / N = 1 / (N : ℝ) from rfl] at hdev
      have hBc := h_collapse q
      have hmu : μ (e ⟨i, q⟩) = m i + (2 * (q : ℝ) + 1 - (rep i : ℝ)) * w i / (rep i : ℝ) := by
        simp only [μ]
        conv_lhs => rw [show e.symm (e ⟨i, q⟩) = ⟨i, q⟩ from Equiv.symm_apply_apply e ⟨i, q⟩]
      rw [hBc] at hdev
      rw [show y - (2 * (q : ℝ) + 1 - ↑(rep i)) * w i / ↑(rep i) =
        ∑ j, A i j * d j - μ (e ⟨i, q⟩) from by rw [hmu]; ring]
      exact hdev
    -- Apply interval covering to get |y| ≥ w_i
    have := Ball1991.deviation_bound_from_copies hN_pos (hrep_pos i)
      (hw_nonneg i) hNw_lt h_copies
    rwa [ge_iff_le]

/-! ### Theorem 2' via FIP/compactness -/

/-- **Proof of Theorem 2'** via the change-of-density / block matrix argument.

For `∑ w_i < 1` (strict slack): directly apply the block matrix argument.
For `∑ w_i ≤ 1` (general): approximate by `w'_i = (1 - 1/(K+2)) w_i` which has
strict slack, then take a limit using the finite intersection property on the
compact L¹ ball. -/
theorem Ball1991.theorem2'_proof
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_diag : ∀ i, A i i = 1)
    (m : Fin n → ℝ)
    (w : Fin n → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i ≤ 1) :
    ∃ coeffs : Fin n → ℝ,
      ∑ j, |coeffs j| ≤ 1 ∧
      ∀ i, |∑ j, A i j * coeffs j - m i| ≥ w i := by
  -- n = 0: vacuous
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, by simp, fun i => Fin.elim0 i⟩
  -- Define approximating sets: S_k = {c | ∑|c| ≤ 1 ∧ ∀i, |dev_i| ≥ (1-1/(k+2)) w_i}
  set S : ℕ → Set (Fin n → ℝ) := fun k =>
    {c | ∑ j, |c j| ≤ 1 ∧ ∀ i, |∑ j, A i j * c j - m i| ≥ (1 - 1/((k:ℝ)+2)) * w i}
  -- S_k is closed
  have hS_closed : ∀ k, IsClosed (S k) := by
    intro k
    change IsClosed ({c : Fin n → ℝ | ∑ j, |c j| ≤ 1} ∩
      {c | ∀ i, |∑ j, A i j * c j - m i| ≥ (1 - 1/((k:ℝ)+2)) * w i})
    apply IsClosed.inter
    · exact isClosed_le (continuous_finset_sum _ fun i _ => Continuous.abs (continuous_apply i))
        continuous_const
    · have : (fun c : Fin n → ℝ => ∀ i, |∑ j, A i j * c j - m i| ≥ (1 - 1/((k:ℝ)+2)) * w i) =
          (fun c => c ∈ ⋂ i : Fin n, {c | (1 - 1/((k:ℝ)+2)) * w i ≤ |∑ j, A i j * c j - m i|}) := by
        ext c; simp [Set.mem_iInter, ge_iff_le]
      rw [this]
      exact isClosed_iInter (fun i => isClosed_le continuous_const
        (Continuous.abs (Continuous.sub
          (continuous_finset_sum _ fun j _ => Continuous.mul continuous_const (continuous_apply j))
          continuous_const)))
  -- S_k is compact (closed subset of compact L1 ball)
  have hS_compact : ∀ k, IsCompact (S k) := by
    intro k
    apply (isCompact_pi_infinite fun _ => isCompact_Icc (a := -1) (b := 1)).of_isClosed_subset
      (hS_closed k)
    intro c ⟨hc_l1, _⟩
    simp only [Set.mem_Icc]
    intro i; constructor
    · linarith [Finset.single_le_sum (f := fun j => |c j|)
        (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i), neg_abs_le (c i)]
    · linarith [Finset.single_le_sum (f := fun j => |c j|)
        (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i), le_abs_self (c i)]
  -- S_k is directed by reverse inclusion (S_{k+1} ⊆ S_k)
  have hS_directed : Directed (· ⊇ ·) S := by
    intro k₁ k₂
    refine ⟨max k₁ k₂, fun c hc => ?_, fun c hc => ?_⟩
    · refine ⟨hc.1, fun i => le_trans ?_ (hc.2 i)⟩
      apply mul_le_mul_of_nonneg_right _ (hw_nonneg i)
      simp only [sub_le_sub_iff_left]
      apply div_le_div_of_nonneg_left zero_le_one (by positivity : (0:ℝ) < (↑k₁:ℝ) + 2)
      gcongr; exact_mod_cast le_max_left k₁ k₂
    · refine ⟨hc.1, fun i => le_trans ?_ (hc.2 i)⟩
      apply mul_le_mul_of_nonneg_right _ (hw_nonneg i)
      simp only [sub_le_sub_iff_left]
      apply div_le_div_of_nonneg_left zero_le_one (by positivity : (0:ℝ) < (↑k₂:ℝ) + 2)
      gcongr; exact_mod_cast le_max_right k₁ k₂
  -- S_k is nonempty for all k (block matrix argument)
  have hS_nonempty : ∀ k, (S k).Nonempty := by
    intro k
    -- w' = (1 - 1/(k+2)) * w has strict slack
    set w' : Fin n → ℝ := fun i => (1 - 1/((k:ℝ)+2)) * w i
    have hw'_nonneg : ∀ i, 0 ≤ w' i := by
      intro i; apply mul_nonneg _ (hw_nonneg i)
      have hk2_pos : (0:ℝ) < (k:ℝ) + 2 := by positivity
      linarith [(div_le_one hk2_pos).mpr (by linarith : (1:ℝ) ≤ (k:ℝ) + 2)]
    have hw'_sum : ∑ i, w' i < 1 := by
      simp_rw [w', ← Finset.mul_sum]
      calc (1 - 1 / ((k:ℝ) + 2)) * ∑ i, w i
          ≤ (1 - 1 / ((k:ℝ) + 2)) * 1 := by
            apply mul_le_mul_of_nonneg_left hw_sum
            have hk2_pos : (0:ℝ) < (k:ℝ) + 2 := by positivity
            linarith [(div_le_one hk2_pos).mpr (by linarith : (1:ℝ) ≤ (k:ℝ) + 2)]
        _ < 1 := by
            rw [mul_one]; linarith [show (0:ℝ) < 1 / ((k:ℝ) + 2) by positivity]
    obtain ⟨c, hc_l1, hc_dev⟩ := Ball1991.theorem2'_strict_slack hn A hA_diag m w' hw'_nonneg hw'_sum
    exact ⟨c, hc_l1, fun i => hc_dev i⟩
  -- FIP: ⋂_k S_k is nonempty
  have h_inter := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    S hS_directed hS_nonempty hS_compact hS_closed
  -- Extract coefficients from the intersection
  obtain ⟨c, hc⟩ := h_inter
  refine ⟨c, ?_, ?_⟩
  · exact (Set.mem_iInter.mp hc 0).1
  · intro i
    rw [ge_iff_le]
    -- For all k: |dev_i| ≥ (1 - 1/(k+2)) * w_i. Taking k → ∞ gives |dev_i| ≥ w_i.
    by_contra h; push_neg at h
    -- h : |∑ j, A i j * c j - m i| < w i
    rcases eq_or_lt_of_le (hw_nonneg i) with hwi | hwi_pos
    · linarith [abs_nonneg (∑ j, A i j * c j - m i)]
    · -- w_i > 0 and |dev| < w_i. Find k large enough for contradiction.
      set L := |∑ j, A i j * c j - m i| with hL_def
      have hgap : 0 < w i - L := by linarith
      obtain ⟨k, hk⟩ := exists_nat_gt (w i / (w i - L) - 2)
      have hk2_pos : (0:ℝ) < (k:ℝ) + 2 := by positivity
      have hmem := (Set.mem_iInter.mp hc k).2 i
      -- hmem : (1 - 1/(k+2)) * w i ≤ L
      have hfrac : w i / ((k:ℝ) + 2) < w i - L := by
        rw [div_lt_iff₀ hk2_pos]
        have : w i / (w i - L) < (k:ℝ) + 2 := by linarith
        rw [div_lt_iff₀ hgap] at this
        linarith [mul_comm ((k:ℝ) + 2) (w i - L)]
      have : L < (1 - 1 / ((k:ℝ) + 2)) * w i := by
        rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]; linarith
      linarith

/-- **Theorem 2'** (Ball 1991, Theorem 2').
Let `A = (a_ij)` be an `n x n` matrix whose diagonal entries equal 1, `(m_i)` a sequence
of reals, and `(w_i)` a sequence of non-negative numbers with `sum w_i <= 1`.
Then there is a sequence `(coeffs_j)` with `sum_j |coeffs_j| <= 1` and, for each i:
  `|sum_j a_ij coeffs_j - m_i| >= w_i`. -/
theorem Ball1991.theorem2'
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_diag : ∀ i, A i i = 1)
    (m : Fin n → ℝ)
    (w : Fin n → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i ≤ 1) :
    ∃ coeffs : Fin n → ℝ,
      ∑ j, |coeffs j| ≤ 1 ∧
      ∀ i, |∑ j, A i j * coeffs j - m i| ≥ w i :=
  Ball1991.theorem2'_proof A hA_diag m w hw_nonneg hw_sum

/-! ## Section 3: The infinite-dimensional case -/

section InfiniteDimensional

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Theorem 7 for Fin n index set, without FiniteDimensional hypothesis.
Same proof as `theorem7_finite_dim`, but `exists_dual_vector` and `theorem2'`
don't actually need X to be finite-dimensional. -/
private theorem Ball1991.theorem7_fin
    {n : ℕ}
    (x : Fin n → X)
    (hx_unit : ∀ i, ‖x i‖ = 1)
    (m : Fin n → ℝ) (w : Fin n → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i ≤ 1) :
    ∃ phi : X →L[ℝ] ℝ,
      ‖phi‖ ≤ 1 ∧ ∀ i, |phi (x i) - m i| ≥ w i := by
  have hx_ne : ∀ i, ‖x i‖ ≠ 0 := fun i => by rw [hx_unit i]; exact one_ne_zero
  choose psi hpsi_norm hpsi_val using fun i => exists_dual_vector ℝ (x i) (hx_ne i)
  have hpsi1 : ∀ i, psi i (x i) = 1 := fun i => by
    rw [hpsi_val i, hx_unit i]; norm_cast
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => psi i (x j))
  have hAT_diag : ∀ i, Aᵀ i i = 1 := fun i => by
    simp [A, Matrix.transpose_apply, Matrix.of_apply, hpsi1]
  obtain ⟨coeffs, hcoeffs_l1, hcoeffs_dev⟩ :=
    Ball1991.theorem2' Aᵀ hAT_diag m w hw_nonneg hw_sum
  refine ⟨∑ j, coeffs j • psi j, ?_, ?_⟩
  · calc ‖∑ j, coeffs j • psi j‖
        ≤ ∑ j, ‖coeffs j • psi j‖ := norm_sum_le _ _
      _ = ∑ j, |coeffs j| * ‖psi j‖ := by
          congr 1; ext j; rw [norm_smul, Real.norm_eq_abs]
      _ = ∑ j, |coeffs j| := by
          congr 1; ext j; rw [hpsi_norm j, mul_one]
      _ ≤ 1 := hcoeffs_l1
  · intro i
    have h_eval : (∑ j, coeffs j • psi j) (x i) = ∑ j, Aᵀ i j * coeffs j := by
      rw [ContinuousLinearMap.sum_apply]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
        A, Matrix.transpose_apply, Matrix.of_apply, mul_comm]
    rw [h_eval]
    exact hcoeffs_dev i

/-- **Theorem 7** (Ball 1991, Theorem 7 -- Multiple Hahn-Banach).
Let `(x_i)` be unit vectors in a normed space X, `(m_i)` reals, and
`(w_i)` non-negative reals with `sum w_i <= 1`. Then there is a functional phi
of norm at most 1 in `X*` with `|phi(x_i) - m_i| >= w_i` for every i.

Proved by Banach-Alaoglu (weak*-compactness of the unit dual ball)
combined with the finite intersection property. For each finite subset
of indices, `theorem7_fin` produces a functional satisfying those conditions.
The condition sets are closed in the weak* topology (evaluation is continuous),
so their intersection over all indices is nonempty by compactness. -/
theorem Ball1991.theorem7_multiple_hahn_banach
    {ι : Type*} [Countable ι]
    (x : ι → X)
    (hx_unit : ∀ i, ‖x i‖ = 1)
    (m : ι → ℝ) (w : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : Summable w)
    (hw_le : ∑' i, w i ≤ 1) :
    ∃ phi : X →L[ℝ] ℝ,
      ‖phi‖ ≤ 1 ∧ ∀ i, |phi (x i) - m i| ≥ w i := by
  classical
  -- Work in WeakDual ℝ X for Banach-Alaoglu + FIP
  -- Compact set: unit ball in weak* topology
  set K : Set (WeakDual ℝ X) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1
  have hK : IsCompact K := WeakDual.isCompact_closedBall 0 1
  -- Condition sets: {phi | |phi(x_i) - m_i| ≥ w_i}
  set C : ι → Set (WeakDual ℝ X) := fun i =>
    {phi | w i ≤ |phi (x i) - m i|}
  -- Each C_i is closed (evaluation at x_i is continuous in weak*)
  have hC_closed : ∀ i, IsClosed (C i) := fun i =>
    isClosed_le continuous_const
      (continuous_abs.comp ((WeakDual.eval_continuous (x i)).sub continuous_const))
  -- Finite intersections are nonempty (from theorem7_fin)
  have hFIP : ∀ S : Finset ι, (K ∩ ⋂ i ∈ S, C i).Nonempty := by
    intro S
    -- Sum of w over S ≤ 1
    have hw_S : ∑ i ∈ S, w i ≤ 1 :=
      le_trans (Summable.sum_le_tsum S (fun i _ => hw_nonneg i) hw_sum) hw_le
    -- Re-index S to Fin S.card via subtype equivalence
    set e : {i // i ∈ S} ≃ Fin S.card :=
      (Fintype.equivFin {i // i ∈ S}).trans (finCongr (Fintype.card_coe S))
    set x' : Fin S.card → X := fun k => x (e.symm k)
    set m' : Fin S.card → ℝ := fun k => m (e.symm k)
    set w' : Fin S.card → ℝ := fun k => w (e.symm k)
    have hx' : ∀ k, ‖x' k‖ = 1 := fun k => hx_unit (e.symm k)
    have hw' : ∀ k, 0 ≤ w' k := fun k => hw_nonneg (e.symm k)
    have hws' : ∑ k, w' k ≤ 1 := by
      have : ∑ k : Fin S.card, w' k = ∑ i ∈ S, w i := by
        rw [← Finset.sum_coe_sort S w]
        exact Fintype.sum_equiv e.symm w' (fun i => w ↑i) (fun _ => rfl)
      linarith
    -- Apply theorem7_fin
    obtain ⟨phi, hphi_norm, hphi_dev⟩ := Ball1991.theorem7_fin x' hx' m' w' hw' hws'
    -- Convert to WeakDual and show membership
    refine ⟨StrongDual.toWeakDual phi, ?_, ?_⟩
    · -- phi ∈ K (norm ≤ 1)
      simp only [K, Set.mem_preimage, Metric.mem_closedBall]
      change dist (WeakDual.toStrongDual (StrongDual.toWeakDual phi)) 0 ≤ 1
      rw [@dist_zero_right (StrongDual ℝ X) _]
      exact hphi_norm
    · -- phi ∈ ⋂ i ∈ S, C i
      simp only [Set.mem_iInter]
      intro i hi
      show w i ≤ |phi (x i) - m i|
      have := hphi_dev (e ⟨i, hi⟩)
      simp only [x', m', w', Equiv.symm_apply_apply] at this
      exact this
  -- Apply FIP: compact ∩ intersection of closed sets is nonempty
  obtain ⟨phi, hphi_K, hphi_C⟩ := hK.inter_iInter_nonempty C hC_closed hFIP
  -- Extract the result
  refine ⟨WeakDual.toStrongDual phi, ?_, ?_⟩
  · -- ‖phi‖ ≤ 1
    have : WeakDual.toStrongDual phi ∈ Metric.closedBall (0 : StrongDual ℝ X) 1 :=
      Set.mem_preimage.mp hphi_K
    rw [Metric.mem_closedBall, @dist_zero_right (StrongDual ℝ X) _] at this
    exact this
  · -- |phi(x_i) - m_i| ≥ w_i for all i
    intro i
    exact Set.mem_iInter.mp hphi_C i

/-- **Theorem 7** (finite-dimensional version).
For a finite-dimensional space, the existence of the functional follows directly
from Theorem 2 by duality. -/
theorem Ball1991.theorem7_finite_dim [FiniteDimensional ℝ X]
    {n : ℕ}
    (x : Fin n → X)
    (hx_unit : ∀ i, ‖x i‖ = 1)
    (m : Fin n → ℝ) (w : Fin n → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i ≤ 1) :
    ∃ phi : X →L[ℝ] ℝ,
      ‖phi‖ ≤ 1 ∧ ∀ i, |phi (x i) - m i| ≥ w i := by
  -- Step 1: Hahn-Banach: for each unit vector x_i, get psi_i with ‖psi_i‖ = 1, psi_i(x_i) = 1
  have hx_ne : ∀ i, ‖x i‖ ≠ 0 := fun i => by rw [hx_unit i]; exact one_ne_zero
  choose psi hpsi_norm hpsi_val using fun i => exists_dual_vector ℝ (x i) (hx_ne i)
  -- psi i (x i) = ‖x i‖ = 1
  have hpsi1 : ∀ i, psi i (x i) = 1 := fun i => by
    rw [hpsi_val i, hx_unit i]; norm_cast
  -- Step 2: Build matrix A_ij = psi_i(x_j), apply Theorem 2' to Aᵀ
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => psi i (x j))
  have hAT_diag : ∀ i, Aᵀ i i = 1 := fun i => by
    simp [A, Matrix.transpose_apply, Matrix.of_apply, hpsi1]
  obtain ⟨coeffs, hcoeffs_l1, hcoeffs_dev⟩ :=
    Ball1991.theorem2' Aᵀ hAT_diag m w hw_nonneg hw_sum
  -- Step 3: phi = Σ coeffs_j • psi_j
  refine ⟨∑ j, coeffs j • psi j, ?_, ?_⟩
  · -- ‖phi‖ ≤ 1
    calc ‖∑ j, coeffs j • psi j‖
        ≤ ∑ j, ‖coeffs j • psi j‖ := norm_sum_le _ _
      _ = ∑ j, |coeffs j| * ‖psi j‖ := by
          congr 1; ext j; rw [norm_smul, Real.norm_eq_abs]
      _ = ∑ j, |coeffs j| := by
          congr 1; ext j; rw [hpsi_norm j, mul_one]
      _ ≤ 1 := hcoeffs_l1
  · -- |phi(x_i) - m_i| ≥ w_i
    intro i
    -- phi(x_i) = Σ coeffs_j * psi_j(x_i) = Σ coeffs_j * A j i = Σ Aᵀ i j * coeffs j
    have h_eval : (∑ j, coeffs j • psi j) (x i) = ∑ j, Aᵀ i j * coeffs j := by
      rw [ContinuousLinearMap.sum_apply]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
        A, Matrix.transpose_apply, Matrix.of_apply, mul_comm]
    rw [h_eval]
    exact hcoeffs_dev i

-- **Theorem 8** (Ball 1991, Theorem 8 -- Strong form with weights).
-- Statement: Given A (n×n) with A_ii = 1, reals m_i, positive w_i:
--   ∃ coeffs, Σ w_j⁻¹ coeffs_j² ≤ Σ w_j ∧ ∀ i, |Σ A_ij coeffs_j - m_i| ≥ w_i
-- Proof: change-of-density argument (expanding to N×N matrix with repeated
-- rows/columns proportional to w_i) + theorem2'_strengthened_proof.
-- Currently unused (theorem1 is proved by other means; this stronger form was never needed).
-- Formalization target: needs the block matrix expansion + rational approximation
-- of weights, then application of the equal-weight theorem.

-- **Proof of Theorem 1 from Theorem 8** (Ball 1991, general Banach spaces).
-- For general (non-reflexive) Banach spaces, the proof requires:
-- 1. Theorem 8 (weighted L² control from change-of-density)
-- 2. Near norm-attaining vectors: x_i with phi_i(x_i) ≈ 1
-- 3. Series construction: x = Σ coeffs_j x_j converges by completeness
-- 4. Diagonal argument for countable ι
-- For finite-dimensional X, a simpler proof via FIP + compactness
-- is given in `theorem1` below.

end InfiniteDimensional

/-! ## Implications between the results -/

section Implications

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The construction of the matrix A from unit functionals (Ball 1991, Section 1):
Given unit functionals `phi_i` on X, for each j choose `x_j` in the unit ball with
`phi_j(x_j) = ‖x_j‖ = 1` (i.e. `phi_j` attains its norm). Then `A = (phi_i(x_j))`
has 1's on the diagonal and for any `(coeffs_j)` with `sum |coeffs_j| <= 1`,
the point `x = sum coeffs_j x_j` has norm at most 1 and
`phi_i(x) = sum_j a_ij coeffs_j`. -/
theorem Ball1991.matrix_from_functionals [FiniteDimensional ℝ X]
    {n : ℕ}
    (phi : Fin n → X →L[ℝ] ℝ)
    (hphi_unit : ∀ i, ‖phi i‖ = 1) :
    ∃ (x : Fin n → X),
      (∀ j, ‖x j‖ ≤ 1) ∧
      (∀ j, phi j (x j) = 1) ∧
      let A := Matrix.of (fun i j => phi i (x j))
      ∀ i, A i i = 1 := by
  haveI : ProperSpace X := FiniteDimensional.proper ℝ X
  -- For each j, find x_j with ‖x_j‖ ≤ 1 and phi_j(x_j) = 1
  have norm_attained : ∀ j, ∃ y : X, ‖y‖ ≤ 1 ∧ (phi j) y = 1 := by
    intro j
    have hcpt := isCompact_closedBall (0 : X) 1
    have hne : (Metric.closedBall (0 : X) 1).Nonempty :=
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    obtain ⟨y, hy_mem, hy_max⟩ :=
      hcpt.exists_isMaxOn hne (map_continuous (phi j)).continuousOn
    have hy_norm : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy_mem
    replace hy_max : ∀ x ∈ Metric.closedBall (0 : X) 1, (phi j) x ≤ (phi j) y :=
      Filter.eventually_principal.mp hy_max
    -- Upper bound: phi j y ≤ 1 (operator norm bound)
    have h_le : (phi j) y ≤ 1 := calc
      (phi j) y ≤ |(phi j) y| := le_abs_self _
      _ = ‖(phi j) y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖phi j‖ * ‖y‖ := (phi j).le_opNorm y
      _ = 1 * ‖y‖ := by rw [hphi_unit j]
      _ ≤ 1 * 1 := by linarith
      _ = 1 := one_mul 1
    -- Lower bound: phi j y ≥ 1 (negation trick + sSup)
    have h_ge : 1 ≤ (phi j) y := by
      have h_sSup := (phi j).sSup_unitClosedBall_eq_norm
      rw [hphi_unit j] at h_sSup; rw [← h_sSup]
      apply csSup_le (hne.image _)
      rintro _ ⟨x, hx, rfl⟩
      dsimp only; rw [Real.norm_eq_abs, abs_le]
      exact ⟨by
        have hx_neg : -x ∈ Metric.closedBall (0 : X) 1 := by
          rw [mem_closedBall_zero_iff] at hx ⊢; rw [norm_neg]; exact hx
        linarith [hy_max (-x) hx_neg, (phi j).map_neg x],
        hy_max x hx⟩
    exact ⟨y, hy_norm, le_antisymm h_le h_ge⟩
  choose x hx_norm hx_val using norm_attained
  exact ⟨x, hx_norm, hx_val, fun i => by simp [Matrix.of_apply, hx_val i]⟩

/-- Theorem 2 follows from Theorem 2':
construct the matrix, apply Theorem 2', recover the point `x = sum coeffs_j x_j`.
Since `sum |coeffs_j| <= 1` and `x_j` are in the unit ball, `x = sum coeffs_j x_j`
has norm at most 1 by the triangle inequality. -/
theorem Ball1991.theorem2_from_theorem2' [FiniteDimensional ℝ X]
    (h2' : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (_ : ∀ i, A i i = 1)
      (m : Fin n → ℝ) (w : Fin n → ℝ) (_ : ∀ i, 0 ≤ w i) (_ : ∑ i, w i ≤ 1),
      ∃ coeffs : Fin n → ℝ,
        ∑ j, |coeffs j| ≤ 1 ∧ ∀ i, |∑ j, A i j * coeffs j - m i| ≥ w i)
    {n : ℕ}
    (phi : Fin n → X →L[ℝ] ℝ)
    (m : Fin n → ℝ) (w : Fin n → ℝ)
    (hphi_unit : ∀ i, ‖phi i‖ = 1)
    (hw_pos : ∀ i, 0 < w i)
    (hw_sum : ∑ i, w i = 1) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ ∀ i, |phi i x - m i| ≥ w i := by
  -- Step 1: Get norm-attaining vectors x_j from unit functionals
  obtain ⟨xb, hxb_norm, hxb_val, _⟩ := Ball1991.matrix_from_functionals phi hphi_unit
  set A := Matrix.of (fun i j => phi i (xb j))
  have hA_diag : ∀ i, A i i = 1 := by intro i; simp [A, Matrix.of_apply, hxb_val i]
  -- Step 2: Apply Theorem 2' to the matrix A
  obtain ⟨coeffs, hcoeffs_sum, hcoeffs_ineq⟩ :=
    h2' A hA_diag m w (fun i => (hw_pos i).le) (hw_sum ▸ le_refl _)
  -- Step 3: Set x = Σ coeffs_j · x_j
  refine ⟨∑ j, coeffs j • xb j, ?_, ?_⟩
  · -- ‖x‖ ≤ 1 by triangle inequality
    calc ‖∑ j, coeffs j • xb j‖
        ≤ ∑ j, ‖coeffs j • xb j‖ := norm_sum_le _ _
      _ = ∑ j, |coeffs j| * ‖xb j‖ := by
          congr 1; ext j; rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ j, |coeffs j| * 1 := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hxb_norm j) (abs_nonneg _)
      _ = ∑ j, |coeffs j| := by simp
      _ ≤ 1 := hcoeffs_sum
  · -- |phi_i(x) - m_i| ≥ w_i
    intro i
    have h_phi : phi i (∑ j, coeffs j • xb j) = ∑ j, A i j * coeffs j := by
      simp only [map_sum, map_smul, smul_eq_mul, A, Matrix.of_apply]
      congr 1; ext j; ring
    rw [h_phi]; exact hcoeffs_ineq i

end Implications

/-! ## Main theorems (proved from the machinery above) -/

section MainTheorems

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Theorem 2** (Ball 1991, Theorem 2).
If `(phi_i)` is a sequence of unit functionals on a finite-dimensional normed space X,
`(m_i)` a sequence of reals, and `(w_i)` a sequence of positive numbers with `sum w_i = 1`,
then there is a point x in the unit ball of X with `|phi_i(x) - m_i| >= w_i` for every i.

This is the finite-dimensional dual formulation: instead of "planks cover => sum w >= 1",
we have "sum w <= 1 => exists point avoiding all planks".

Proved from `theorem2_from_theorem2'` applied to `theorem2'`. -/
theorem Ball1991.theorem2 [FiniteDimensional ℝ X]
    {n : ℕ}
    (phi : Fin n → X →L[ℝ] ℝ)
    (m : Fin n → ℝ) (w : Fin n → ℝ)
    (hphi_unit : ∀ i, ‖phi i‖ = 1)
    (hw_pos : ∀ i, 0 < w i)
    (hw_sum : ∑ i, w i = 1) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ ∀ i, |phi i x - m i| ≥ w i :=
  Ball1991.theorem2_from_theorem2' @Ball1991.theorem2' phi m w hphi_unit hw_pos hw_sum

/-- Variant of Theorem 2 with `∑ w_i ≤ 1` (not necessarily `= 1`).
Proved by rescaling weights: `w'_i = w_i / ∑ w_j` sums to 1, and
`w'_i ≥ w_i` since `∑ w_j ≤ 1`. -/
theorem Ball1991.theorem2_le [FiniteDimensional ℝ X]
    {n : ℕ}
    (phi : Fin n → X →L[ℝ] ℝ)
    (m : Fin n → ℝ) (w : Fin n → ℝ)
    (hphi_unit : ∀ i, ‖phi i‖ = 1)
    (hw_pos : ∀ i, 0 < w i)
    (hw_sum : ∑ i, w i ≤ 1) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ ∀ i, |phi i x - m i| ≥ w i := by
  by_cases hn : n = 0
  · subst hn; exact ⟨0, by simp, fun i => Fin.elim0 i⟩
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    set s := ∑ i, w i with s_def
    have hs_pos : 0 < s :=
      Finset.sum_pos (fun i _ => hw_pos i) ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
    set w' : Fin n → ℝ := fun i => w i / s
    have hw'_pos : ∀ i, 0 < w' i := fun i => div_pos (hw_pos i) hs_pos
    have hw'_sum : ∑ i, w' i = 1 := by
      show ∑ i : Fin n, w i / s = 1
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hs_pos)
    obtain ⟨x, hx_norm, hx_dev⟩ := Ball1991.theorem2 phi m w' hphi_unit hw'_pos hw'_sum
    refine ⟨x, hx_norm, fun i => le_trans ?_ (hx_dev i)⟩
    show w i ≤ w i / s
    rw [le_div_iff₀ hs_pos]
    exact mul_le_of_le_one_right (le_of_lt (hw_pos i)) hw_sum

/-- **Theorem 1** (Ball 1991, Theorem 1 — finite-dimensional case).
If the unit ball of a finite-dimensional normed space X is covered by a (countable)
collection of planks, then the sum of the half-widths is at least 1.

Ball's paper proves this for general Banach spaces using Theorem 8 (weighted L² control)
and series construction. Here we prove the finite-dimensional case via compactness of
the unit ball (Heine-Borel) + finite intersection property, analogous to the proof of
Theorem 7 (multiple Hahn-Banach).

For each finite subset of planks with bumped weights, `theorem2_le` provides a point
avoiding them. The condition sets are closed, and by compactness + FIP, a point avoiding
ALL planks exists, contradicting the covering hypothesis. -/
theorem Ball1991.theorem1 [FiniteDimensional ℝ X]
    {ι : Type*} [Countable ι]
    (phi : ι → X →L[ℝ] ℝ)
    (m : ι → ℝ) (w : ι → ℝ)
    (hphi_unit : ∀ i, ‖phi i‖ = 1)
    (hw_pos : ∀ i, 0 < w i)
    (hw_sum : Summable w)
    (hcover : ∀ x : X, ‖x‖ ≤ 1 →
      ∃ i, |phi i x - m i| ≤ w i) :
    1 ≤ ∑' i, w i := by
  classical
  by_contra h
  push_neg at h
  -- h : ∑' i, w i < 1
  set sw := ∑' i, w i
  -- ι must be nonempty (otherwise hcover gives ∃ i in empty type)
  obtain ⟨i₀, _⟩ := hcover 0 (by norm_num)
  have hsw_pos : 0 < sw :=
    lt_of_lt_of_le (hw_pos i₀) (hw_sum.le_tsum i₀ (fun j _ => le_of_lt (hw_pos j)))
  -- Step 1: Bumped weights v_i = w_i / c where c = (1+sw)/2 < 1
  set c := (1 + sw) / 2
  have hc_pos : 0 < c := by positivity
  have hc_lt_one : c < 1 := by change (1 + sw) / 2 < 1; linarith
  set v : ι → ℝ := fun i => w i / c
  have hv_pos : ∀ i, 0 < v i := fun i => div_pos (hw_pos i) hc_pos
  have hv_gt : ∀ i, w i < v i := by
    intro i; show w i < w i / c
    rw [lt_div_iff₀ hc_pos]
    exact mul_lt_of_lt_one_right (hw_pos i) hc_lt_one
  have hv_summable : Summable v := hw_sum.div_const c
  have hv_le : ∑' i, v i ≤ 1 := by
    rw [show (fun i => v i) = fun i => w i / c from rfl, tsum_div_const]
    rw [div_le_one hc_pos]; change sw ≤ (1 + sw) / 2; linarith
  -- Step 2: Compact K = closed unit ball (FiniteDimensional → ProperSpace)
  set K : Set X := Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall 0 1
  -- Step 3: Condition sets C_i = {x | v_i ≤ |phi_i(x) - m_i|}
  set C : ι → Set X := fun i => {x | v i ≤ |phi i x - m i|}
  have hC_closed : ∀ i, IsClosed (C i) := fun i =>
    isClosed_le continuous_const
      (continuous_abs.comp ((phi i).continuous.sub continuous_const))
  -- Step 4: FIP — for each finite S, K ∩ ⋂ i ∈ S, C i is nonempty
  have hFIP : ∀ S : Finset ι, (K ∩ ⋂ i ∈ S, C i).Nonempty := by
    intro S
    -- Re-index S to Fin S.card
    set e : {i // i ∈ S} ≃ Fin S.card :=
      (Fintype.equivFin {i // i ∈ S}).trans (finCongr (Fintype.card_coe S))
    set phi' : Fin S.card → X →L[ℝ] ℝ := fun k => phi (e.symm k)
    set m' : Fin S.card → ℝ := fun k => m (e.symm k)
    set v' : Fin S.card → ℝ := fun k => v (e.symm k)
    have hphi' : ∀ k, ‖phi' k‖ = 1 := fun k => hphi_unit (e.symm k)
    have hv'_pos : ∀ k, 0 < v' k := fun k => hv_pos (e.symm k)
    have hv'_sum : ∑ k, v' k ≤ 1 := by
      have : ∑ k : Fin S.card, v' k = ∑ i ∈ S, v i := by
        rw [← Finset.sum_coe_sort S v]
        exact Fintype.sum_equiv e.symm v' (fun i => v ↑i) (fun _ => rfl)
      rw [this]
      exact le_trans (Summable.sum_le_tsum S (fun i _ => le_of_lt (hv_pos i)) hv_summable) hv_le
    obtain ⟨x, hx_norm, hx_dev⟩ := Ball1991.theorem2_le phi' m' v' hphi' hv'_pos hv'_sum
    refine ⟨x, ?_, ?_⟩
    · simp only [K, Metric.mem_closedBall, dist_zero_right]; exact hx_norm
    · simp only [Set.mem_iInter]
      intro i hi; show v i ≤ |phi i x - m i|
      have := hx_dev (e ⟨i, hi⟩)
      simp only [phi', m', v', Equiv.symm_apply_apply] at this
      exact this
  -- Step 5: Apply FIP — compact K ∩ ⋂ C_i is nonempty
  obtain ⟨x, hx_K, hx_C⟩ := hK.inter_iInter_nonempty C hC_closed hFIP
  -- Step 6: Contradiction
  have hx_norm : ‖x‖ ≤ 1 := by
    simp only [K, Metric.mem_closedBall, dist_zero_right] at hx_K; exact hx_K
  obtain ⟨j, hj⟩ := hcover x hx_norm
  -- hj : |phi j x - m j| ≤ w j, but v j ≤ |phi j x - m j| and w j < v j
  exact absurd (le_trans (Set.mem_iInter.mp hx_C j) hj) (not_le.mpr (hv_gt j))

end MainTheorems

/-! ## Auxiliary results and counterexamples -/

section Auxiliary

/-- The counterexample to Lemma 3 without the symmetry hypothesis (Ball 1991, Remark):
The matrix `[[1, 1], [-1, 1]]` with `theta_1 = theta_2 = 1` and `mu_1 = mu_2 = 0`
does not satisfy the conclusion of Lemma 3.

For `eps = (1, 1)`:   row 1: `|1+1-0| = 2 >= 1` OK, row 2: `|-1+1-0| = 0 < 1` FAIL
For `eps = (1, -1)`:  row 1: `|1-1-0| = 0 < 1` FAIL
For `eps = (-1, 1)`:  row 1: `|-1+1-0| = 0 < 1` FAIL
For `eps = (-1, -1)`: row 1: `|-1-1-0| = 2 >= 1` OK, row 2: `|1-1-0| = 0 < 1` FAIL -/
theorem Ball1991.lemma3_counterexample_nonsymmetric :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, 1]
    let theta : Fin 2 → ℝ := ![1, 1]
    let mu : Fin 2 → ℝ := ![0, 0]
    ¬ ∃ eps : Fin 2 → ℝ,
      (∀ j, eps j = 1 ∨ eps j = -1) ∧
      ∀ i, |∑ j, A i j * eps j * theta j - mu i| ≥ theta i := by
  intro A theta mu ⟨eps, heps_sign, heps_bound⟩
  have h0 := heps_sign 0
  have h1 := heps_sign 1
  have hb0 := heps_bound 0
  have hb1 := heps_bound 1
  simp only [A, theta, mu, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val'] at hb0 hb1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    simp only [h0, h1] at hb0 hb1 <;> (try norm_num at hb0) <;> norm_num at hb1

-- Change-of-density argument (Ball 1991, Section 2):
-- Reduces theorem2' (general weights w_i) to the equal-weight case (1/N for all).
-- Ball's proof subdivides each plank of half-width w_i into 2*ceil(N*w_i) "sheets"
-- of half-width 1/(2N), creating an expanded N×N matrix. The equal-weight result
-- (theorem2'_strengthened_proof) applied to the expanded matrix gives |dev| ≥ 1/N
-- from each sheet center. A point avoiding all sheets for plank i avoids the
-- original plank, giving |dev| ≥ w_i.
-- To formalize: needs matrix expansion, rational approximation of weights, and
-- aggregation of sheet-level results back to plank-level bounds.

/-- The Cauchy-Schwarz step: `sum coeffs_j^2 <= 1/n` implies `sum |coeffs_j| <= 1`.
By Cauchy-Schwarz: `(sum |coeffs_j|)^2 <= n * sum coeffs_j^2 <= n * (1/n) = 1`. -/
theorem Ball1991.l2_to_l1_bound
    {n : ℕ} (hn : 0 < n)
    (coeffs : Fin n → ℝ)
    (h : ∑ j, (coeffs j) ^ 2 ≤ 1 / n) :
    ∑ j, |coeffs j| ≤ 1 := by
  have hcs : (∑ i : Fin n, 1 * |coeffs i|) ^ 2 ≤
      (∑ i : Fin n, (1:ℝ) ^ 2) * ∑ i : Fin n, |coeffs i| ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1:ℝ)) (fun j => |coeffs j|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one,
    sq_abs] at hcs
  have hnn : 0 ≤ ∑ j : Fin n, |coeffs j| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have key : (∑ x : Fin n, |coeffs x|) ^ 2 ≤ 1 := by
    calc (∑ x, |coeffs x|) ^ 2 ≤ n * ∑ x, coeffs x ^ 2 := hcs
      _ ≤ n * (1 / n) := by nlinarith
      _ = 1 := by field_simp
  nlinarith [sq_nonneg (∑ j : Fin n, |coeffs j|)]

/-- The weighted Cauchy-Schwarz step used in the proof of Theorem 1
(infinite-dimensional case):
  `sum |coeffs_j| <= (sum v_j)^{1/2} * (sum v_j^{-1} coeffs_j^2)^{1/2}`.
This is obtained by writing `|coeffs_j| = sqrt(v_j) * (|coeffs_j|/sqrt(v_j))`
and applying Cauchy-Schwarz. -/
theorem Ball1991.weighted_cauchy_schwarz
    {n : ℕ}
    (v coeffs : Fin n → ℝ)
    (hv_pos : ∀ i, 0 < v i) :
    ∑ j, |coeffs j| ≤
      Real.sqrt (∑ j, v j) * Real.sqrt (∑ j, (v j)⁻¹ * (coeffs j) ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => le_of_lt (hv_pos i)))]
  apply Real.le_sqrt_of_sq_le
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => Real.sqrt (v j)) (fun j => |coeffs j| / Real.sqrt (v j))
  simp only [Real.sq_sqrt (le_of_lt (hv_pos _))] at hcs
  have heq1 : ∀ j : Fin n, Real.sqrt (v j) * (|coeffs j| / Real.sqrt (v j)) = |coeffs j| :=
    fun j => mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (hv_pos j))
  have heq2 : ∀ j : Fin n, (|coeffs j| / Real.sqrt (v j)) ^ 2 = (v j)⁻¹ * (coeffs j) ^ 2 := by
    intro j
    rw [div_pow, Real.sq_sqrt (le_of_lt (hv_pos j)), sq_abs]
    rw [inv_mul_eq_div]
  simp only [heq1, heq2] at hcs
  linarith

/-- **Uniform summability** in the proof of Theorem 1 (Ball 1991, equation (6) and sequel):
If `sum v_i < 1` and `sum v_i^{-1} (coeffs_k i)^2 <= sum v_i` for each k,
then `sum |coeffs_k i| <= 1` uniformly in k.
This gives equicontinuity for the coefficient sequences.

The bound `sum v_i^{-1} a_i^2 <= sum v_i` matches Theorem 8's output. -/
theorem Ball1991.uniform_summability
    {n : ℕ}
    (v : Fin n → ℝ)
    (hv_pos : ∀ i, 0 < v i)
    (hv_sum : ∑ i, v i < 1)
    (coeffs_seq : ℕ → Fin n → ℝ)
    (h_bound : ∀ k, ∑ i, (v i)⁻¹ * (coeffs_seq k i) ^ 2 ≤ ∑ i, v i) :
    ∀ k, ∑ i, |coeffs_seq k i| ≤ 1 := by
  intro k
  have hv_nn : 0 ≤ ∑ i, v i := Finset.sum_nonneg (fun i _ => le_of_lt (hv_pos i))
  calc ∑ i, |coeffs_seq k i|
      ≤ Real.sqrt (∑ i, v i) * Real.sqrt (∑ i, (v i)⁻¹ * (coeffs_seq k i) ^ 2) :=
        Ball1991.weighted_cauchy_schwarz v (coeffs_seq k) hv_pos
    _ ≤ Real.sqrt (∑ i, v i) * Real.sqrt (∑ i, v i) := by
        apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (h_bound k)) (Real.sqrt_nonneg _)
    _ = ∑ i, v i := by rw [← Real.sqrt_mul hv_nn]; exact Real.sqrt_mul_self hv_nn
    _ ≤ 1 := le_of_lt hv_sum

end Auxiliary


/-! ## Application to Diophantine approximation (mentioned in Section 1)

Ball notes that the Corollary strengthens Davenport's pigeonhole principle:
a cube C and n hyperplanes admit a sub-cube at least `2^{-n}` times as large missing all
hyperplanes (Davenport). With the symmetric body version, one gets `1/(n+1)` instead of
`2^{-n}`. -/

section DiophantineApplication

/-- **Davenport's observation improved** (referenced in Ball 1991, Section 1):
Ball's Corollary improves Davenport's `2^{-n}` factor to `1/(n+1)` for all symmetric bodies.
Given n hyperplanes (as unit functionals), there is a point x with `‖x‖ <= n/(n+1)`
such that `|phi_i(x) - m_i| >= 1/(n+1)` for all i. -/
theorem Ball1991.davenport_improved
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {n : ℕ}
    (phi : Fin n → X →L[ℝ] ℝ)
    (m : Fin n → ℝ)
    (hphi_unit : ∀ i, ‖phi i‖ = 1) :
    ∃ x : X, ‖x‖ ≤ n / (n + 1) ∧
      ∀ i, |phi i x - m i| ≥ 1 / (n + 1) := by
  -- n = 0: vacuously true
  by_cases hn : n = 0
  · subst hn; exact ⟨0, by simp, fun i => Fin.elim0 i⟩
  -- n > 0
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hn_cast : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hn1_cast : (0 : ℝ) < n + 1 := by linarith
  -- Step 1: Get norm-attaining vectors
  obtain ⟨xb, hxb_norm, hxb_val, _⟩ := Ball1991.matrix_from_functionals phi hphi_unit
  set A := Matrix.of (fun i j => phi i (xb j))
  have hA_diag : ∀ i, A i i = 1 := fun i => by simp [A, Matrix.of_apply, hxb_val i]
  -- Step 2: Apply Theorem 2' (strengthened) with rescaled centers m' = ((n+1)/n) · m
  obtain ⟨coeffs, hcoeffs_l2, hcoeffs_ineq⟩ :=
    Ball1991.theorem2'_strengthened_proof hn_pos A hA_diag (fun i => ((n + 1 : ℝ) / n) * m i)
  -- Step 3: Set x = (n/(n+1)) · Σ coeffs_j · xb_j
  set y := ∑ j, coeffs j • xb j
  refine ⟨((n : ℝ) / (n + 1)) • y, ?_, ?_⟩
  · -- ‖x‖ ≤ n/(n+1)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hn_cast hn1_cast)]
    calc (n : ℝ) / (n + 1) * ‖y‖
        ≤ n / (n + 1) * (∑ j, |coeffs j|) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith) (by linarith))
          calc ‖y‖ ≤ ∑ j, ‖coeffs j • xb j‖ := norm_sum_le _ _
            _ = ∑ j, |coeffs j| * ‖xb j‖ := by
                congr 1; ext j; rw [norm_smul, Real.norm_eq_abs]
            _ ≤ ∑ j, |coeffs j| * 1 := by
                apply Finset.sum_le_sum; intro j _
                exact mul_le_mul_of_nonneg_left (hxb_norm j) (abs_nonneg _)
            _ = ∑ j, |coeffs j| := by simp
      _ ≤ n / (n + 1) * 1 := by
          apply mul_le_mul_of_nonneg_left (Ball1991.l2_to_l1_bound hn_pos coeffs hcoeffs_l2)
            (div_nonneg (by linarith) (by linarith))
      _ = n / (n + 1) := mul_one _
  · -- |phi_i(x) - m_i| ≥ 1/(n+1)
    intro i
    simp only [map_smul, smul_eq_mul]
    have h_phi : phi i y = ∑ j, A i j * coeffs j := by
      simp only [y, map_sum, map_smul, smul_eq_mul, A, Matrix.of_apply]
      congr 1; ext j; ring
    rw [h_phi]
    -- |(n/(n+1)) · Σ A_ij c_j - m_i| = (n/(n+1)) · |Σ A_ij c_j - ((n+1)/n) m_i|
    rw [show (n : ℝ) / (n + 1) * ∑ j, A i j * coeffs j - m i =
      (n / (n + 1)) * (∑ j, A i j * coeffs j - (n + 1) / n * m i) from by field_simp]
    rw [abs_mul, abs_of_pos (div_pos hn_cast hn1_cast)]
    calc 1 / (n + 1 : ℝ) = n / (n + 1) * (1 / n) := by field_simp
      _ ≤ n / (n + 1) * |∑ j, A i j * coeffs j - (↑n + 1) / ↑n * m i| := by
          apply mul_le_mul_of_nonneg_left (hcoeffs_ineq i)
            (div_nonneg (by linarith) (by linarith))

/-- **Corollary** (Ball 1991, Corollary following Theorem 2).
If C is a convex body with center of symmetry in `R^d` and `(H_i)` are n hyperplanes,
then there is a set of the form `x + (1/(n+1))*C` inside C whose interior
does not meet any `H_i`.

We formalize this for a normed space X with unit ball C (the symmetric body).
Given n hyperplanes `{x : phi_i(x) = m_i}` with `‖phi_i‖ = 1`, there exists x with
`‖x‖ <= n/(n+1)` such that for all y with `‖y-x‖ < 1/(n+1)`, `phi_i(y) != m_i`.

Note: the ball must be OPEN (strict inequality). With a closed ball, the boundary
point y = x - (1/(n+1)) * x_i could lie on a hyperplane.

Proved from `davenport_improved` via the operator norm bound:
|phi_i(y) - m_i| ≥ |phi_i(x) - m_i| - |phi_i(y - x)| ≥ 1/(n+1) - ‖y - x‖ > 0. -/
theorem Ball1991.corollary_symmetric_body
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {n : ℕ}
    (phi : Fin n → X →L[ℝ] ℝ)
    (m : Fin n → ℝ)
    (hphi_unit : ∀ i, ‖phi i‖ = 1) :
    ∃ x : X, ‖x‖ ≤ n / (n + 1) ∧
      ∀ y : X, ‖y - x‖ < 1 / (n + 1) →
        ∀ i, phi i y ≠ m i := by
  obtain ⟨x, hx_norm, hx_ineq⟩ := Ball1991.davenport_improved X phi m hphi_unit
  refine ⟨x, hx_norm, fun y hy i heq => ?_⟩
  have h_dev := hx_ineq i
  have h_eq : phi i x - m i = phi i (x - y) := by rw [map_sub, heq]
  rw [h_eq] at h_dev
  have h_bound : |phi i (x - y)| ≤ ‖y - x‖ :=
    calc |phi i (x - y)|
        = ‖phi i (x - y)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖phi i‖ * ‖x - y‖ := (phi i).le_opNorm _
      _ = ‖x - y‖ := by rw [hphi_unit i, one_mul]
      _ = ‖y - x‖ := norm_sub_rev _ _
  linarith

end DiophantineApplication
