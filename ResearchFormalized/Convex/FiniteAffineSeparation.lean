/- Separation of a convex set from finitely many simultaneous strict affine
inequalities. Work in the finite-dimensional space of cut values; the original
space needs no topology, and the convex set need not be compact. -/
module
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace ResearchFormalized.FiniteAffineSeparation
open scoped BigOperators
open Set

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [Nonempty ι]

/-- An empty strict affine cell on any convex set has a normalized nonnegative
separator valid on the entire set. No finite generation or continuity is assumed. -/
theorem exists_weights (K : Set E) (hK : Convex ℝ K) (g : ι → E →ᵃ[ℝ] ℝ)
    (he : ¬ ∃ x ∈ K, ∀ i, 0 < g i x) :
    ∃ m : ι → ℝ, (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 1 ∧
      ∀ x ∈ K, ∑ i, m i * g i x ≤ 0 := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hne
  · let i : ι := Classical.arbitrary ι
    exact ⟨fun j => if j = i then 1 else 0, by intro j; positivity, by simp, by simp⟩
  let O : Set (ι → ℝ) := Set.pi Set.univ fun _ => Set.Ici 0
  let G : E →ᵃ[ℝ] (ι → ℝ) := AffineMap.pi g
  have hInt : interior O = {x | ∀ i, 0 < x i} := by
    rw [show O = Set.pi Set.univ (fun _ => Set.Ici 0) from rfl,
      interior_pi_set Set.finite_univ]
    ext x
    simp [Set.mem_pi]
  have hdis : Disjoint (interior O) (G '' K) := by
    rw [hInt]
    apply Set.disjoint_left.mpr
    rintro _ ho ⟨x, hx, rfl⟩
    exact he ⟨x, hx, ho⟩
  obtain ⟨f, u, hfn, hO, hG⟩ := geometric_hahn_banach_of_nonempty_interior
    (show Convex ℝ O from convex_pi fun _ _ => convex_Ici (0 : ℝ))
    (Convex.affine_image G hK) hdis
    (by rw [hInt]; exact ⟨fun _ => 1, fun _ => zero_lt_one⟩) (hne.image G)
  let e (i : ι) : ι → ℝ := fun j => if i = j then 1 else 0
  let m : ι → ℝ := fun i => -f (e i)
  have hf (x : ι → ℝ) : f x = -∑ i, m i * x i := by
    simpa [m, e, mul_comm] using
      LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) x
  have hu : 0 ≤ u := by simpa using hO 0 (fun _ _ => (show (0 : ℝ) ≤ 0 from le_rfl))
  have hm (i : ι) : 0 ≤ m i := by
    by_contra hn
    have hi : 0 < f (e i) := neg_lt_zero.mp (lt_of_not_ge hn)
    let t := (u + 1) / f (e i)
    have ht : 0 ≤ t := div_nonneg (by linarith) hi.le
    have hb := hO (t • e i) (by
      intro j _; change 0 ≤ t * (if i = j then 1 else 0)
      split_ifs <;> positivity)
    simp only [map_smul, smul_eq_mul] at hb
    rw [show t * f (e i) = u + 1 from div_mul_cancel₀ _ hi.ne'] at hb
    linarith
  have hs : 0 < ∑ i, m i := by
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hm i)
    by_contra hn
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hm i)).mp
      (le_antisymm (le_of_not_gt hn) hsum)
    apply hfn
    ext x
    simp [hf, fun i => hz i (Finset.mem_univ i)]
  refine ⟨fun i => m i / ∑ j, m j, fun i => div_nonneg (hm i) hs.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hs.ne']
  · intro x hx
    have hb := hu.trans (hG _ ⟨x, hx, rfl⟩)
    rw [hf] at hb
    have hb' : ∑ i, m i * g i x ≤ 0 := neg_nonneg.mp hb
    simpa only [Finset.sum_div, div_mul_eq_mul_div] using
      div_nonpos_of_nonpos_of_nonneg hb' hs.le

end ResearchFormalized.FiniteAffineSeparation

/-- info: 'ResearchFormalized.FiniteAffineSeparation.exists_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResearchFormalized.FiniteAffineSeparation.exists_weights
