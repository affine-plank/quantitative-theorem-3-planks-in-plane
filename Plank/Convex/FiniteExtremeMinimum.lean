/- Finite-dimensional extreme minima by a squared-coordinate tie-breaker,
and the active constraints of a local affine model. Neither argument
requires a convex feasible set. -/
module
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators Topology
namespace Plank.Convex.ExtremeMinimum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem square_gap (x y a b : ℝ) (hab : a + b = 1) :
    a * x ^ 2 + b * y ^ 2 - (a * x + b * y) ^ 2 = a * b * (x - y) ^ 2 := by
  obtain rfl := eq_sub_of_add_eq hab
  ring

private theorem strictConvex_coordinates {ι : Type*} [Fintype ι]
    (c : E →L[ℝ] (ι → ℝ)) (hc : Function.Injective c) :
    StrictConvexOn ℝ univ (fun x => ∑ i, (c x i) ^ 2) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro i _
    have h := mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (c x i - c y i))
    linarith only [h, square_gap (c x i) (c y i) a b hab]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp (hc.ne hxy)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    have h := mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hi))
    linarith only [h, square_gap (c x i) (c y i) a b hab]

/-- A squared-coordinate tie-breaker selects an extreme minimizer. -/
theorem exists_finite_extreme_minimizer [FiniteDimensional ℝ E]
    (s : Set E) (hs : IsCompact s) (hne : s.Nonempty) (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s.extremePoints ℝ, IsMinOn f s x := by
  let c := (Module.finBasis ℝ E).equivFunL
  let q : E → ℝ := fun x => ∑ i, (c x i) ^ 2
  have hq : StrictConvexOn ℝ univ q := strictConvex_coordinates c.toContinuousLinearMap c.injective
  have hcont : Continuous q := by fun_prop
  let t := (-f).toExposed s
  have he : IsExposed ℝ s t := ContinuousLinearMap.toExposed.isExposed
  obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hne f.continuous.continuousOn
  have hne' : t.Nonempty := ⟨x, hx, fun y hy => neg_le_neg (hmin hy)⟩
  obtain ⟨y, hy, hmax⟩ := (he.isCompact hs).exists_isMaxOn hne' hcont.continuousOn
  have hyext : y ∈ t.extremePoints ℝ := by
    refine ⟨hy, ?_⟩
    intro u hu v hv hseg
    by_cases huv : u = v
    · simpa only [← huv, openSegment_same, mem_singleton_iff, eq_comm] using hseg
    · exact False.elim ((hq.lt_on_openSegment (mem_univ _) (mem_univ _) huv hseg).not_ge
        (max_le (hmax hu) (hmax hv)))
  refine ⟨y, he.isExtreme.extremePoints_subset_extremePoints hyext, ?_⟩
  intro z hz
  exact neg_le_neg_iff.mp (hy.2 z hz)

theorem extreme_no_two_sided_motion (s : Set E) (x : E)
    (hx : x ∈ s.extremePoints ℝ) (d : E) (hd : d ≠ 0)
    (hm : x - d ∈ s) (hp : x + d ∈ s) : False := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have he := hx.2 hm hp (mem_openSegment_sub_add (𝕜 := ℝ) x d)
  exact hd (sub_eq_self.mp he)

theorem extreme_no_motion (s : Set E) (x : E) (hx : x ∈ s.extremePoints ℝ)
    (d : E) (hd : d ≠ 0) (hm : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ s) : False := by
  have hm' : ∀ᶠ t : ℝ in 𝓝 0, x - t • d ∈ s := by
    have hn : Filter.Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
    simpa only [neg_smul, ← sub_eq_add_neg] using hn.eventually hm
  obtain ⟨t, ht, hp, hn⟩ := (hm.and hm').exists_gt
  exact extreme_no_two_sided_motion s x hx (t • d) (smul_ne_zero ht.ne' hd) hn hp

theorem eventual_constraints {ι : Type*} [Fintype ι]
    (f : ι → E →L[ℝ] ℝ) (c : ι → ℝ) (x d : E)
    (hx : ∀ i, c i ≤ f i x) (hd : ∀ i, c i = f i x → f i d = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ i, c i ≤ f i (x + t • d) := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases he : c i = f i x
  · exact Filter.Eventually.of_forall fun t => by
      rw [map_add, map_smul, hd i he, smul_zero, add_zero]
      exact hx i
  · have hh : c i < f i (x + (0 : ℝ) • d) := by
      simpa only [zero_smul, add_zero] using (hx i).lt_of_ne he
    have hcont : Continuous (fun t : ℝ => f i (x + t • d)) := by fun_prop
    exact (hcont.continuousAt.eventually (lt_mem_nhds hh)).mono fun _ h => h.le

/-- If a feasible set locally contains an affine constraint region through an
extreme point, the active constraint forms have trivial common kernel. -/
theorem extreme_active_kernel {ι : Type*} [Fintype ι]
    (s U : Set E) (x : E) (hx : x ∈ s.extremePoints ℝ)
    (hU : IsOpen U) (hxU : x ∈ U)
    (f : ι → E →L[ℝ] ℝ) (c : ι → ℝ)
    (hcur : ∀ i, c i ≤ f i x)
    (hlocal : ∀ y ∈ U, (∀ i, c i ≤ f i y) → y ∈ s)
    (d : E) (hd : ∀ i, c i = f i x → f i d = 0) : d = 0 := by
  by_contra hn
  apply extreme_no_motion s x hx d hn
  have hcont : Continuous (fun t : ℝ => x + t • d) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ U := by
    have ht : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := 0)).tendsto
    exact ht.eventually (hU.mem_nhds hxU)
  filter_upwards [hnear, eventual_constraints f c x d hcur hd] with t ht hc
  exact hlocal _ ht hc

end Plank.Convex.ExtremeMinimum
