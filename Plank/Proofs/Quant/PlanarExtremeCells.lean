/- Extreme points of homothetic convex cells lie on cuts or at their center. -/
module

public import Plank.Proofs.Quant.PlanarExtremeHomothety
public import Plank.Proofs.Quant.PlanarCellArea

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarExtremeCells

open Set PlanarQuantitative PlanarCellArea

variable {ι : Type*} [Fintype ι]

/-- At an extreme point strictly inside all terminal half-plane cuts,
an exact cell homothety toward a point of the opposite cell must fix the
point. The hypotheses are only convexity, finite cuts and exact set data. -/
theorem extreme_fixed_of_strict_cuts {K : Set Point} (hK : Convex ℝ K)
    (f : ι → Point →L[ℝ] ℝ) (u v : ι → ℝ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (y : Point) (hy : y ∈ cell K f v)
    (hcopy : cell K f (r • u+(1-r) • v) = AffineMap.homothety y r '' cell K f u)
    (x : Point) (hx : x ∈ K.extremePoints ℝ) (hs : ∀ i, f i x < u i) : x = y := by
  let O : Set Point := ⋂ i, {z | f i z < (r • u+(1-r) • v) i}
  have hO : IsOpen O := isOpen_iInter_of_finite fun i =>
    isOpen_lt (f i).continuous continuous_const
  apply PlanarExtremeHomothety.extreme_fixed_of_local_homothety hK hO x y hx hy.1 r hr hr1
  · apply mem_iInter.mpr
    intro i
    have hfi : f i (AffineMap.homothety y r x) = r*f i x+(1-r)*f i y := by
      simp only [AffineMap.homothety_apply,vadd_eq_add,vsub_eq_sub,map_add,map_smul,map_sub,
        smul_eq_mul]
      ring
    have hp := mul_pos hr (sub_pos.mpr (hs i))
    have hn := mul_nonneg (sub_pos.mpr hr1).le (sub_nonneg.mpr (mem_iInter.mp hy.2 i))
    change f i (AffineMap.homothety y r x) < r*u i+(1-r)*v i
    rw [hfi]
    nlinarith only [hp,hn]
  · intro z hz
    have hcell : z ∈ cell K f (r • u+(1-r) • v) := by
      refine ⟨hz.1,mem_iInter.mpr fun i => ?_⟩
      have hs : f i z < (r • u+(1-r) • v) i := mem_iInter.mp hz.2 i
      exact hs.le
    rw [hcopy] at hcell
    obtain ⟨w,hw,he⟩ := hcell
    exact ⟨w,hw.1,he⟩

/-- Every extreme point in a terminal cell lies either at its critical
center or on one of the terminal cutting hyperplanes. -/
theorem extreme_on_cut_or_center {K : Set Point} (hK : Convex ℝ K)
    (f : ι → Point →L[ℝ] ℝ) (u v : ι → ℝ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (y : Point) (hy : y ∈ cell K f v)
    (hcopy : cell K f (r • u+(1-r) • v) = AffineMap.homothety y r '' cell K f u)
    (x : Point) (hx : x ∈ K.extremePoints ℝ) (hxu : x ∈ cell K f u) :
    x = y ∨ ∃ i, f i x = u i := by
  by_cases hcut : ∃ i, f i x = u i
  · exact Or.inr hcut
  · exact Or.inl (extreme_fixed_of_strict_cuts hK f u v r hr hr1 y hy hcopy x hx
      (fun i => lt_of_le_of_ne (mem_iInter.mp hxu.2 i) (fun he => hcut ⟨i,he⟩)))

end Plank.PlanarExtremeCells

/-- info: 'Plank.PlanarExtremeCells.extreme_on_cut_or_center' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarExtremeCells.extreme_on_cut_or_center
