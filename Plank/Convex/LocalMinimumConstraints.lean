/- The objective at a local linear constraint model of a minimum. -/
module
public import Plank.Convex.ExtremeMinimum
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped Topology
namespace Plank.Convex.LocalMinimumConstraints
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A direction that increases every sufficient constraint cannot decrease the objective. -/
theorem objective_nonneg {ι : Type*}
    (s U : Set E) (x : E) (F : E →L[ℝ] ℝ) (hmin : IsMinOn F s x)
    (hU : IsOpen U) (hxU : x ∈ U) (f : ι → E →L[ℝ] ℝ) (c : ι → ℝ)
    (hcur : ∀ i, c i ≤ f i x)
    (hlocal : ∀ y ∈ U, (∀ i, c i ≤ f i y) → y ∈ s)
    (d : E) (hd : ∀ i, 0 ≤ f i d) : 0 ≤ F d := by
  have hcont : Continuous (fun t : ℝ => x + t • d) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ U := by
    have ht : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := 0)).tendsto
    exact ht.eventually (hU.mem_nhds hxU)
  obtain ⟨t, ht, htU⟩ := hnear.exists_gt
  have hc (i : ι) : c i ≤ f i (x + t • d) := by
    rw [map_add, map_smul, smul_eq_mul]
    exact (hcur i).trans (le_add_of_nonneg_right (mul_nonneg ht.le (hd i)))
  have h : F x ≤ F (x + t • d) := hmin (hlocal _ htU hc)
  rw [map_add, map_smul, smul_eq_mul] at h
  nlinarith only [h, ht]

/-- A direction preserving the active rows has zero objective at a minimum. -/
theorem objective_eq_zero {ι : Type*} [Fintype ι]
    (s U : Set E) (x : E) (F : E →L[ℝ] ℝ) (hmin : IsMinOn F s x)
    (hU : IsOpen U) (hxU : x ∈ U) (f : ι → E →L[ℝ] ℝ) (c : ι → ℝ)
    (hcur : ∀ i, c i ≤ f i x)
    (hlocal : ∀ y ∈ U, (∀ i, c i ≤ f i y) → y ∈ s)
    (d : E) (hd : ∀ i, c i = f i x → f i d = 0) : F d = 0 := by
  have hcont : Continuous (fun t : ℝ => x + t • d) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ U := by
    have ht : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := 0)).tendsto
    exact ht.eventually (hU.mem_nhds hxU)
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t * F d := by
    filter_upwards [hnear, ExtremeMinimum.eventual_constraints f c x d hcur hd] with t ht hc
    have h : F x ≤ F (x + t • d) := hmin (hlocal _ ht hc)
    simpa only [map_add, map_smul, smul_eq_mul, le_add_iff_nonneg_right] using h
  have hneg : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ -t * F d := by
    have hn : Filter.Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
    exact hn.eventually hpos
  obtain ⟨t, ht, hp, hn⟩ := (hpos.and hneg).exists_gt
  nlinarith only [ht, hp, hn]

end Plank.Convex.LocalMinimumConstraints

/-- info: 'Plank.Convex.LocalMinimumConstraints.objective_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.LocalMinimumConstraints.objective_nonneg

/-- info: 'Plank.Convex.LocalMinimumConstraints.objective_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.LocalMinimumConstraints.objective_eq_zero
