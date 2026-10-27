/- Exterior orthant witnesses force box containment and full affine rank. -/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Range
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace ResearchFormalized.OrthantWitnesses

open Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A convex set meeting every weak exterior orthant of a box contains the
whole box. No closedness assumption is needed: finitely many witnesses suffice. -/
theorem box_subset {K : Set (ι → ℝ)} (hK : Convex ℝ K) (lo hi : ι → ℝ)
    (hwitness : ∀ s : Finset ι, ∃ x ∈ K,
      ∀ i, if i ∈ s then hi i ≤ x i else x i ≤ lo i) : Icc lo hi ⊆ K := by
  classical
  choose w hwK hw using hwitness
  let C := convexHull ℝ (range w)
  have hCK : C ⊆ K := convexHull_min (range_subset_iff.mpr hwK) hK
  intro y hy
  apply hCK
  by_contra hn
  obtain ⟨L, u, hC, hyu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (range w)) ((finite_range w).isClosed_convexHull ℝ) hn
  let a : ι → ℝ := fun i => L (Pi.single i 1)
  have hL (x : ι → ℝ) : L x = ∑ i, a i * x i := by
    simpa [a, map_sum, Pi.basisFun_apply, Pi.basisFun_repr, mul_comm] using
      (congrArg L ((Pi.basisFun ℝ ι).sum_repr x)).symm
  let s := Finset.univ.filter fun i => 0 ≤ a i
  have hxy : L y ≤ L (w s) := by
    rw [hL, hL]
    apply Finset.sum_le_sum
    intro i _
    have hx := hw s i
    by_cases ha : 0 ≤ a i
    · simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, ha, ite_true] at hx
      exact mul_le_mul_of_nonneg_left ((hy.2 i).trans hx) ha
    · simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, ha, ite_false] at hx
      exact mul_le_mul_of_nonpos_left (hx.trans (hy.1 i)) (le_of_not_ge ha)
  exact hyu.not_ge (hxy.trans (hC (w s) (subset_convexHull ℝ _ (mem_range_self s))).le)

/-- Injective affine coordinates transfer the box conclusion back to the
original convex set. The domain needs no topology or dimension assumption. -/
theorem preimage_box_subset {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E →ᵃ[ℝ] (ι → ℝ)) (hF : Function.Injective F)
    {K : Set E} (hK : Convex ℝ K) (lo hi : ι → ℝ)
    (hwitness : ∀ s : Finset ι, ∃ x ∈ K,
      ∀ i, if i ∈ s then hi i ≤ F x i else F x i ≤ lo i) :
    F ⁻¹' Icc lo hi ⊆ K := by
  have hbox : Icc lo hi ⊆ F '' K := box_subset (hK.affine_image F) lo hi fun s => by
    obtain ⟨x, hx, hs⟩ := hwitness s
    exact ⟨F x, ⟨x, hx, rfl⟩, hs⟩
  intro x hx
  obtain ⟨y, hy, heq⟩ := hbox hx
  exact hF heq ▸ hy

/-- Exterior witnesses for a box with strictly positive side lengths force
the affine coordinate map to be onto. The domain may have arbitrary dimension. -/
theorem surjective_of_witnesses {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E →ᵃ[ℝ] (ι → ℝ)) (lo hi : ι → ℝ) (hwidth : ∀ i, lo i < hi i)
    (hwitness : ∀ s : Finset ι, ∃ x,
      ∀ i, if i ∈ s then hi i ≤ F x i else F x i ≤ lo i) :
    Function.Surjective F := by
  have hbox : Icc lo hi ⊆ (F.range : Set (ι → ℝ)) :=
    box_subset F.range.convex lo hi fun s => by
      obtain ⟨x, hx⟩ := hwitness s
      exact ⟨F x, F.mem_range_self x, hx⟩
  have hint : (interior (Icc lo hi)).Nonempty := by
    rw [show Icc lo hi = Set.pi Set.univ (fun i => Icc (lo i) (hi i)) by
      ext x; simp [Set.mem_Icc, Pi.le_def]]
    rw [interior_pi_set Set.finite_univ]
    simp_rw [interior_Icc]
    refine ⟨fun i => (lo i + hi i) / 2, ?_⟩
    intro i _
    constructor <;> linarith [hwidth i]
  apply F.range_eq_top_iff_surjective.mp
  simpa only [AffineSubspace.affineSpan_coe] using
    F.range.convex.interior_nonempty_iff_affineSpan_eq_top.mp
      (hint.mono (interior_mono hbox))

end ResearchFormalized.OrthantWitnesses
