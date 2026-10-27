/- Compact extreme-point selection excludes two-sided motions, including
for nonconvex feasible sets. -/
module
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators Topology
namespace Plank.Convex.FiniteMinimumMotion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If a point admits no symmetric displacement, a line locally contained
in the feasible set must have zero direction. -/
theorem eq_zero_of_eventually_line_mem {s : Set E} {p z : E}
    (hnomotion : ∀ d, p-d ∈ s → p+d ∈ s → d = 0)
    (hline : ∀ᶠ t : ℝ in 𝓝 0, p+t • z ∈ s) : z = 0 := by
  have hn : Filter.Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
  obtain ⟨t,ht,hp,hm⟩ := (hline.and (hn.eventually hline)).exists_gt
  have hz := hnomotion (t • z) (by simpa only [neg_smul,← sub_eq_add_neg] using hm) hp
  exact (smul_eq_zero.mp hz).resolve_left ht.ne'

/-- A minimum can be chosen so that no nonzero displacement is feasible
in both directions. The feasible set need not be convex. -/
theorem exists_minimizer_no_motion
    (s : Set E) (hs : IsCompact s) (hne : s.Nonempty) (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s, IsMinOn f s x ∧ ∀ d, x - d ∈ s → x + d ∈ s → d = 0 := by
  obtain ⟨a, ha, hmin⟩ := hs.exists_isMinOn hne f.continuous.continuousOn
  have he : IsExposed ℝ s ((-f).toExposed s) := ContinuousLinearMap.toExposed.isExposed
  obtain ⟨x, hx⟩ := (he.isCompact hs).extremePoints_nonempty
    ⟨a, ha, fun y hy => neg_le_neg (hmin hy)⟩
  refine ⟨x, hx.1.1, fun y hy => neg_le_neg_iff.mp (hx.1.2 y hy), ?_⟩
  intro d hm hp
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hxS := he.isExtreme.extremePoints_subset_extremePoints hx
  exact sub_eq_self.mp (hxS.2 hm hp (mem_openSegment_sub_add (𝕜 := ℝ) x d))

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

/-- The active row map is injective: a vector in its kernel would give
small feasible displacements in both directions. -/
theorem active_kernel {ι : Type*} [Fintype ι]
    (s U : Set E) (x : E) (hnomotion : ∀ d, x - d ∈ s → x + d ∈ s → d = 0)
    (hU : IsOpen U) (hxU : x ∈ U)
    (f : ι → E →L[ℝ] ℝ) (c : ι → ℝ)
    (hcur : ∀ i, c i ≤ f i x)
    (hlocal : ∀ y ∈ U, (∀ i, c i ≤ f i y) → y ∈ s)
    (d : E) (hd : ∀ i, c i = f i x → f i d = 0) : d = 0 := by
  have hcont : Continuous (fun t : ℝ => x + t • d) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ U := by
    have ht : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := 0)).tendsto
    exact ht.eventually (hU.mem_nhds hxU)
  have hp : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ s := by
    filter_upwards [hnear, eventual_constraints f c x d hcur hd] with t ht hc
    exact hlocal _ ht hc
  exact eq_zero_of_eventually_line_mem hnomotion hp

/-- A local affine model has at least as many active rows as dimensions. -/
theorem card_active_ge_finrank [FiniteDimensional ℝ E] {J : Type*} [Fintype J]
    (s U : Set E) (x : E) (hnomotion : ∀ d, x - d ∈ s → x + d ∈ s → d = 0)
    (hU : IsOpen U) (hxU : x ∈ U)
    (f : J → E →L[ℝ] ℝ) (c : J → ℝ)
    (hcur : ∀ j, c j ≤ f j x)
    (hlocal : ∀ y ∈ U, (∀ j, c j ≤ f j y) → y ∈ s) :
    Module.finrank ℝ E ≤ Nat.card {j : J // c j = f j x} := by
  classical
  let F : E →ₗ[ℝ] ({j : J // c j = f j x} → ℝ) :=
    LinearMap.pi fun j => (f j.val).toLinearMap
  have hinj : Function.Injective F := by
    intro u v huv
    apply sub_eq_zero.mp
    apply active_kernel s U x hnomotion hU hxU f c hcur hlocal (u - v)
    intro j hj
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun huv ⟨j, hj⟩)
  simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using F.finrank_le_finrank_of_injective hinj

end Plank.Convex.FiniteMinimumMotion

/-- info: 'Plank.Convex.FiniteMinimumMotion.exists_minimizer_no_motion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.FiniteMinimumMotion.exists_minimizer_no_motion
/-- info: 'Plank.Convex.FiniteMinimumMotion.card_active_ge_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.FiniteMinimumMotion.card_active_ge_finrank
