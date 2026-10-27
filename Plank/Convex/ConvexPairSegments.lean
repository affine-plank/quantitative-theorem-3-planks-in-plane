/- A segment between two disjoint strict cuts bounds their cross product. -/
module
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ConvexCellSeparation
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A segment joining the two strict cuts cannot pass through their intersection. -/
theorem cross_bound (K : Set E) (hK : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (p q : E) (hp : p ∈ K) (hq : q ∈ K) (hgp : 0 < g p) (hhq : 0 < h q)
    (he : ¬ ∃ x ∈ K, 0 < g x ∧ 0 < h x) :
    g p * h q ≤ g q * h p := by
  have hhp : h p ≤ 0 := le_of_not_gt (fun hh => he ⟨p, hp, hgp, hh⟩)
  have hgq : g q ≤ 0 := le_of_not_gt (fun hg => he ⟨q, hq, hg, hhq⟩)
  let D := g p - h p + h q - g q
  have hD : 0 < D := by dsimp [D]; linarith only [hgp, hhq, hhp, hgq]
  let t := (g p - h p) / D
  have ht : 0 ≤ t := div_nonneg (by linarith only [hgp, hhp]) hD.le
  have ht1 : t ≤ 1 := (div_le_one hD).mpr (by dsimp [D]; linarith only [hhq, hgq])
  have hx : AffineMap.lineMap p q t ∈ K := by
    rw [AffineMap.lineMap_apply_module]
    exact hK hp hq (sub_nonneg.mpr ht1) ht (sub_add_cancel 1 t)
  have hvals :
      g (AffineMap.lineMap p q t) = (g p * h q - g q * h p) / D ∧
      h (AffineMap.lineMap p q t) = (g p * h q - g q * h p) / D := by
    constructor <;> rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring] <;>
      dsimp [t] <;> field_simp <;> dsimp [D] <;> ring
  by_contra! hn
  exact he ⟨_, hx, hvals.1 ▸ div_pos (sub_pos.mpr hn) hD,
    hvals.2 ▸ div_pos (sub_pos.mpr hn) hD⟩

end Plank.Convex.ConvexCellSeparation
