/- Every deficient normalized three-plank cover has an actual point of
the covered body common to all three planks. A quantitative deficit also
places this point uniformly away from all six cube faces. -/
module
public import Plank.Convex.DisconnectedPlankCover
public import Plank.Convex.ThreeSetCoverIntersection
public import Plank.Convex.NearCubeVertexCover
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.CommonPointOfDeficit
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

/-- A whole-set cover of total width below one has a common point in `K`.
The coordinate ranges of `K` are exactly `[0,1]`. No compactness, facet,
affine-dimension, or positive-window-width assumption is needed. -/
theorem exists_common (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : ∀ j, 0 ≤ lo j) (hhi : ∀ j, hi j ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hdef : (∑ j, (hi j - lo j)) < 1) :
    ∃ p ∈ K, ∀ j, lo j ≤ p j ∧ p j ≤ hi j := by
  let P (j : Fin 3) : Set Point := {p | lo j ≤ p j ∧ p j ≤ hi j}
  have hPc (j : Fin 3) : IsClosed (P j) :=
    (isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_le (continuous_apply j) continuous_const)
  have hPv (j : Fin 3) : Convex ℝ (P j) :=
    (convex_Icc (lo j) (hi j)).linear_preimage (LinearMap.proj j : Point →ₗ[ℝ] ℝ)
  have hpair := DisconnectedPlankCover.pairwise_intersect_of_deficit K hconv
    hbox hmin hmax lo hi hordered hlo hhi hcover hdef
  have hpair' (i j : Fin 3) (hij : i ≠ j) : (K ∩ P i ∩ P j).Nonempty := by
    obtain ⟨p, hp, hpi, hpj⟩ := hpair i j hij
    exact ⟨p, ⟨hp, hpi⟩, hpj⟩
  have hcov : K ⊆ P 0 ∪ P 1 ∪ P 2 := by
    intro p hp
    obtain ⟨j, hj⟩ := hcover p hp
    fin_cases j
    · exact Or.inl (Or.inl hj)
    · exact Or.inl (Or.inr hj)
    · exact Or.inr hj
  obtain ⟨p, ⟨⟨hp, hp0⟩, hp1⟩, hp2⟩ :=
    ThreeSetCoverIntersection.triple_nonempty K (P 0) (P 1) (P 2) hconv
      (hPv 0) (hPv 1) (hPv 2) (hPc 0) (hPc 1) (hPc 2) hcov
      (hpair' 0 1 (by decide)) (hpair' 0 2 (by decide)) (hpair' 1 2 (by decide))
  refine ⟨p, hp, ?_⟩
  intro j
  fin_cases j
  · exact hp0
  · exact hp1
  · exact hp2

/-- A deficit of at least `γ > 0` gives a common point with every coordinate
in `[γ, 1-γ]`. This is interior to the cube, not necessarily to `K` or a plank. -/
theorem exists_common_with_margin (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : ∀ j, 0 ≤ lo j) (hhi : ∀ j, hi j ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (γ : ℝ) (hγ : 0 < γ) (hdef : (∑ j, (hi j - lo j)) ≤ 1 - γ) :
    ∃ p ∈ K, (∀ j, lo j ≤ p j ∧ p j ≤ hi j) ∧
      ∀ j, γ ≤ p j ∧ p j ≤ 1 - γ := by
  obtain ⟨p, hp, hpall⟩ := exists_common K hconv hbox hmin hmax lo hi
    hordered hlo hhi hcover (by linarith only [hdef, hγ])
  have hm := NearCubeVertexCover.window_margins_of_deficit K hconv hbox
    hmin hmax lo hi hordered hlo hhi hcover γ hdef
  exact ⟨p, hp, hpall, fun j =>
    ⟨(hm j).1.trans (hpall j).1, (hpall j).2.trans (hm j).2⟩⟩

end Plank.Convex.CommonPointOfDeficit

/-- info: 'Plank.Convex.CommonPointOfDeficit.exists_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CommonPointOfDeficit.exists_common

/-- info: 'Plank.Convex.CommonPointOfDeficit.exists_common_with_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CommonPointOfDeficit.exists_common_with_margin
