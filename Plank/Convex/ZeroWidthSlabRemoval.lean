/-
# Removing a zero-width slab from a finite convex cover

A convex set with a point off a hyperplane cannot need that hyperplane in
addition to a closed covering set. Applying this to the remaining slabs
reduces a three-slab cover with a zero width to the sharp two-plank bound.
No global coordinate bounds or compactness of the original set are needed.
-/
module

public import Plank.Convex.ThreePlankParallelChord
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
noncomputable section

namespace Plank.Convex.ZeroWidthSlabRemoval
open Filter Topology
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A hyperplane is redundant in a closed cover of a convex set containing
one point outside that hyperplane. -/
theorem closed_cover_remove_hyperplane (K C : Set E) (hK : Convex ℝ K)
    (hC : IsClosed C) (f : E →L[ℝ] ℝ) (a : ℝ) (p : E)
    (hp : p ∈ K) (hpa : f p ≠ a)
    (hcov : ∀ x ∈ K, x ∈ C ∨ f x = a) : K ⊆ C := by
  intro x hx
  rcases hcov x hx with hxC | hxa
  · exact hxC
  let t : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  let q : ℕ → E := fun m => (1 - t m) • x + t m • p
  have ht (m) : 0 < t m := by dsimp [t]; positivity
  have ht1 (m) : t m ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hqC (m) : q m ∈ C := by
    have hqK : q m ∈ K := hK hx hp (sub_nonneg.mpr (ht1 m)) (ht m).le (by ring)
    rcases hcov (q m) hqK with hmem | heq
    · exact hmem
    · have hid : f (q m) - a = t m * (f p - a) := by
        simp only [q, map_add, map_smul, smul_eq_mul, hxa]
        ring
      have hz : t m * (f p - a) = 0 := by rw [← hid, heq]; ring
      exact False.elim (hpa (sub_eq_zero.mp
        ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (ht m)))))
  have hlim : Tendsto q atTop (𝓝 x) := by
    have htlim : Tendsto t atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hf : Continuous (fun r : ℝ => (1 - r) • x + r • p) := by fun_prop
    have hh := hf.continuousAt.tendsto.comp htlim
    simpa [q, Function.comp_def] using hh
  exact hC.mem_of_tendsto hlim (Filter.Eventually.of_forall hqC)

/-- Every remaining slab is closed, so one zero-width slab may be removed
from any finite cover when the covered convex set has an off-plane point. -/
theorem cover_without_zero {I : Type*} [Fintype I]
    (K : Set E) (hK : Convex ℝ K) (f : I → E →L[ℝ] ℝ)
    (lo hi : I → ℝ) (k : I) (hz : lo k = hi k)
    (p : E) (hp : p ∈ K) (hpa : f k p ≠ lo k)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) :
    ∀ x ∈ K, ∃ j, j ≠ k ∧ lo j ≤ f j x ∧ f j x ≤ hi j := by
  classical
  let C : Set E := ⋃ j : {j : I // j ≠ k}, (f j.1) ⁻¹' Set.Icc (lo j.1) (hi j.1)
  have hC : IsClosed C :=
    isClosed_iUnion_of_finite fun j => isClosed_Icc.preimage (f j.1).continuous
  have hcov : K ⊆ C := by
    apply closed_cover_remove_hyperplane K C hK hC (f k) (lo k) p hp hpa
    intro x hx
    obtain ⟨j, hj0, hj1⟩ := hcover x hx
    by_cases hjk : j = k
    · subst j
      exact Or.inr (by rw [← hz] at hj1; exact le_antisymm hj1 hj0)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨j, hjk⟩, hj0, hj1⟩)
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hx)
  exact ⟨j.1, j.2, hj⟩

/-- Unit contacts and a degenerate last slab reduce directly to two coordinates. -/
theorem width_bound_last (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →L[ℝ] ℝ)
    (hcontacts : ∀ (j : Fin 3) (side : Bool),
      ∃ x ∈ K, f j x = (if side then 1 else 0))
    (lo hi : Fin 3 → ℝ) (hle : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j)
    (hz : hi 2 - lo 2 = 0) : 1 ≤ ∑ j, (hi j - lo j) := by
  classical
  have hlast : Fin.last 2 = (2 : Fin 3) := rfl
  obtain ⟨p, hp, hpa⟩ : ∃ p ∈ K, f 2 p ≠ lo 2 := by
    by_cases ha : lo 2 = 0
    · obtain ⟨p, hp, hp1⟩ := hcontacts 2 true
      exact ⟨p, hp, by simpa [hp1, ha] using (one_ne_zero : (1 : ℝ) ≠ 0)⟩
    · obtain ⟨p, hp, hp0⟩ := hcontacts 2 false
      exact ⟨p, hp, by simpa [hp0] using Ne.symm ha⟩
  have hremaining := cover_without_zero K hK f lo hi 2 (sub_eq_zero.mp hz).symm
    p hp hpa hcover
  have hcover2 : ∀ x ∈ K, ∃ j : Fin 2,
      lo j.castSucc ≤ f j.castSucc x ∧ f j.castSucc x ≤ hi j.castSucc := by
    intro x hx
    obtain ⟨r, hr, hr0, hr1⟩ := hremaining x hx
    have hr' : r ≠ Fin.last 2 := by simpa only [hlast] using hr
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hr'
    exact ⟨j, hr0, hr1⟩
  have hb := ThreePlankParallelChord.two_coordinate_width_bound K hK
    (fun j => f j.castSucc) (fun j side => hcontacts j.castSucc side)
    (fun j => lo j.castSucc) (fun j => hi j.castSucc)
    (fun j => hle j.castSucc) hcover2
  rw [Fin.sum_univ_castSucc]
  simpa only [hlast, hz, add_zero] using hb

/-- Any zero width in a three-slab cover forces the sharp total bound.
The original convex set may be unbounded or lower-dimensional. -/
theorem width_bound (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →L[ℝ] ℝ)
    (hcontacts : ∀ (j : Fin 3) (side : Bool),
      ∃ x ∈ K, f j x = (if side then 1 else 0))
    (lo hi : Fin 3 → ℝ) (hle : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j)
    (k : Fin 3) (hz : hi k - lo k = 0) : 1 ≤ ∑ j, (hi j - lo j) := by
  classical
  let p : Equiv.Perm (Fin 3) := Equiv.swap k 2
  have hp2 : p 2 = k := Equiv.swap_apply_right k 2
  have hcover' : ∀ x ∈ K, ∃ j, lo (p j) ≤ f (p j) x ∧ f (p j) x ≤ hi (p j) := by
    intro x hx
    obtain ⟨j, hj⟩ := hcover x hx
    exact ⟨p.symm j, by simpa only [p.apply_symm_apply] using hj⟩
  have hb := width_bound_last K hK (fun j => f (p j))
    (fun j side => hcontacts (p j) side) (fun j => lo (p j)) (fun j => hi (p j))
    (fun j => hle (p j)) hcover' (by simpa only [hp2] using hz)
  simpa only [Equiv.sum_comp p (fun j => hi j - lo j)] using hb

end Plank.Convex.ZeroWidthSlabRemoval
