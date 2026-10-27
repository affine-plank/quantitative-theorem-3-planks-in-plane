/- A hyperplane containing no relative neighborhood of a convex set can
be removed from a closed cover. No continuity of the affine functional is needed. -/
module
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace Plank.Convex.ClosedCover

theorem closed_cover_remove_affine {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (K C : Set E) (hK : Convex ℝ K) (hC : IsClosed C) (f : E →ᵃ[ℝ] ℝ)
    (a : ℝ) (p : E) (hp : p ∈ K) (hpa : f p ≠ a)
    (hcov : ∀ x ∈ K, x ∈ C ∨ f x = a) : K ⊆ C := by
  intro x hx
  rcases hcov x hx with hxC | hxa
  · exact hxC
  have hpath : Continuous (fun t : ℝ => AffineMap.lineMap x p t) := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hlim : Tendsto (AffineMap.lineMap x p) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa only [AffineMap.lineMap_apply_zero] using
      (hpath.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply hC.mem_of_tendsto hlim
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with t ht
  rcases hcov _ (hK.lineMap_mem hx hp ⟨ht.1.le, ht.2⟩) with hm | he
  · exact hm
  · have hzero : t * (f p - a) = 0 := by
      simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring', hxa] at he
      linarith only [he]
    exact False.elim ((mul_ne_zero ht.1.ne' (sub_ne_zero.mpr hpa)) hzero)

end Plank.Convex.ClosedCover
