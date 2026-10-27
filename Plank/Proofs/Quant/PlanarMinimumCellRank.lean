/- A compact zero set forces more nonempty cells than endpoint parameters. -/
module

public import Plank.Proofs.Quant.PlanarMinimumCellScaling
public import Plank.Convex.FiniteMinimumMotion
public import Plank.Proofs.Quant.FiniteDimensionalMinimumCellRank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarMinimumCellRank

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarFewCellScaling
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

variable {m : ℕ}

/-- Actual closed exterior cells, including nonempty cells of zero area. -/
def nonemptyCells (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) :
    Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter (fun s => (signCell K f p.1 p.2 s).Nonempty)

/-- The common upper bounds become exact locally at an actual zero minimum.
This uses only that local minimum, including for negative times. -/
theorem exists_local_zero_motion {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (C : Finset (Finset (Fin m))) (hC : C.card ≤ 2*m)
    (B : ℝ) (p : Endpoints m) (hp : p ∈ interior (domain K f))
    (hreg : p ∈ region K f C) (hR : budget K f p < B)
    (hz : PlanarShiftedDomain.margin K f B p = 0)
    (hmin : IsLocalMin (PlanarShiftedDomain.margin K f B) p) :
    ∃ z : Endpoints m, z ≠ 0 ∧ ∀ᶠ t : ℝ in 𝓝 0,
      p+t • z ∈ interior (domain K f) ∧
        PlanarShiftedDomain.margin K f B (p+t • z) = 0 := by
  have ho := PlanarShiftedDomain.strict_windows_of_interior K f B
    (PlanarShiftedDomain.mem_interior_of_lt K f B hp hR)
  obtain ⟨z,hzne,c,_,hline⟩ :=
    FiniteDimensionalFewCellScaling.exists_common_upper_scaling_at_minimum
      hK hc hne hV f hW C hC B p ho hreg (sub_pos.mpr hR) hz hmin
  have ht : Filter.Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
    have hcont : Continuous (fun t : ℝ => p+t • z) := by fun_prop
    simpa only [zero_smul,add_zero] using
      (hcont.continuousAt (x := (0 : ℝ))).tendsto
  refine ⟨z,hzne,?_⟩
  filter_upwards [hline,ht.eventually (isOpen_interior.mem_nhds hp)] with t he hD
  exact ⟨hD,he.2.2⟩

/-- A nonempty compact zero set of the actual shifted margin contains a
zero with at least `2*m+1` nonempty closed exterior cells. Degenerate cells
are counted. Nonnegative margin and a strict boundary barrier
are explicit hypotheses; this does not assert them for arbitrary plank counts. -/
theorem exists_many_of_shifted_barrier {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (B : ℝ)
    (hzero : ∃ p ∈ PlanarShiftedDomain.domain K f B, PlanarShiftedDomain.margin K f B p = 0)
    (hminimum : ∀ p ∈ PlanarShiftedDomain.domain K f B, 0 ≤ PlanarShiftedDomain.margin K f B p)
    (hboundary : ∀ p ∈ PlanarShiftedDomain.domain K f B,
      p ∉ interior (PlanarShiftedDomain.domain K f B) → 0 < PlanarShiftedDomain.margin K f B p) :
    ∃ p ∈ interior (PlanarShiftedDomain.domain K f B),
      PlanarShiftedDomain.margin K f B p = 0 ∧
      2*m+1 ≤ (nonemptyCells K f p).card := by
  classical
  have hinside (p : Endpoints m) (hpD : p ∈ PlanarShiftedDomain.domain K f B)
      (hz : PlanarShiftedDomain.margin K f B p = 0) :
      p ∈ interior (PlanarShiftedDomain.domain K f B) := by
    by_contra hn
    have hh := hboundary p hpD hn
    rw [hz] at hh
    exact lt_irrefl 0 hh
  by_cases hm : m = 0
  · subst m
    obtain ⟨p,hp,hz⟩ := hzero
    have hcell (s : Finset (Fin 0)) : (signCell K f p.1 p.2 s).Nonempty := by
      obtain ⟨x,hx⟩ := hne
      exact ⟨x,hx,fun i => Fin.elim0 i⟩
    refine ⟨p,hinside p hp hz,hz,?_⟩
    simp [nonemptyCells,hcell]
  apply FiniteDimensionalMinimumCellRank.exists_many_of_compact_zero_domain
    hK hc hne hV f hW B (PlanarShiftedDomain.domain K f B)
    (PlanarShiftedDomain.isCompact_domain K f B) hzero hminimum
  intro p hpD hz
  have hpI := hinside p hpD hz
  refine ⟨hpI,PlanarShiftedDomain.strict_windows_of_interior K f B hpI,?_⟩
  apply sub_pos.mpr
  change budget K f p < B
  let i : Fin m := ⟨0,Nat.pos_of_ne_zero hm⟩
  let L := -(PlanarShiftedDomain.budgetLinear K f)
  have hL : Function.Surjective L := by
    intro r
    refine ⟨(0,Pi.single i (-r*rangeWidth K (f i))),?_⟩
    simpa [L,budget,Pi.single_apply,ite_div,neg_div] using
      (mul_div_cancel_right₀ r (hW i).ne')
  have hsub : PlanarShiftedDomain.domain K f B ⊆ L ⁻¹' Ici (-B) := by
    intro q hq
    simpa only [mem_preimage,mem_Ici,L,LinearMap.neg_apply,
      PlanarShiftedDomain.budgetLinear_apply] using neg_le_neg hq.2
  simpa only [L,LinearMap.neg_apply,PlanarShiftedDomain.budgetLinear_apply,
    neg_lt_neg_iff] using
      PlanarShiftedDomain.strict_linear_lower_of_interior L hL hsub hpI

/-- The three-plank specialization counts at least seven nonempty closed cells. -/
theorem exists_seven_of_shifted_barrier {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (B : ℝ)
    (hzero : ∃ p ∈ PlanarShiftedDomain.domain K f B, PlanarShiftedDomain.margin K f B p = 0)
    (hminimum : ∀ p ∈ PlanarShiftedDomain.domain K f B, 0 ≤ PlanarShiftedDomain.margin K f B p)
    (hboundary : ∀ p ∈ PlanarShiftedDomain.domain K f B,
      p ∉ interior (PlanarShiftedDomain.domain K f B) → 0 < PlanarShiftedDomain.margin K f B p) :
    ∃ p ∈ interior (PlanarShiftedDomain.domain K f B),
      PlanarShiftedDomain.margin K f B p = 0 ∧
      7 ≤ (nonemptyCells K f p).card := by
  exact exists_many_of_shifted_barrier hK hc hne hV f hW B hzero hminimum hboundary

/-- Without a positivity input, a counterexample has an actual negative
root-margin minimizer which either has zero gap or has at least2n+1 cells.
The body and directions stay fixed, and the original minimum is retained. -/
theorem exists_minimum_zero_or_many {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p₀ : Endpoints (m+1)} (hp₀ : p₀ ∈ domain K f)
    (hbad : gapArea K f p₀ < (max 0 (1-budget K f p₀))^2*(volume K).toReal) :
    ∃ p ∈ interior (domain K f), rootMargin K f p < 0 ∧
      (∀ e ∈ domain K f, rootMargin K f p ≤ rootMargin K f e) ∧
      (gapArea K f p = 0 ∨ ∃ B, 0 < B ∧ B < 1 ∧
        p ∈ interior (PlanarShiftedDomain.domain K f B) ∧
        PlanarShiftedDomain.margin K f B p = 0 ∧
        2*(m+1)+1 ≤ (nonemptyCells K f p).card) := by
  have hcost (e : Endpoints (m+1)) :
      FiniteDimensionalMinimumCellRank.rootCost K f e = rootMargin K f e + 1 := by
    change (gapArea K f e / (volume K).toReal) ^ ((2 : ℝ)⁻¹) + budget K f e =
      Real.sqrt (gapArea K f e / (volume K).toReal) + budget K f e - 1 + 1
    rw [Real.sqrt_eq_rpow,one_div]
    ring
  have hbad' : FiniteDimensionalMinimumCellRank.rootCost K f p₀ < 1 := by
    rw [hcost]
    have hh := (rootMargin_neg_iff hV f p₀ hp₀.2).mpr hbad
    linarith only [hh]
  obtain ⟨p,hp,hneg,hmin,hcases⟩ :=
    FiniteDimensionalParameterDomain.exists_minimum_zero_or_many
      hm hK hc hne hV f hW hnorm hp₀ hbad'
  rw [hcost] at hneg
  refine ⟨p,hp,by linarith only [hneg],?_,?_⟩
  · intro e he
    have hh := hmin e he
    rw [hcost,hcost] at hh
    linarith only [hh]
  · rcases hcases with hz | ⟨B,hB0,hB,hRp,hz,hcount⟩
    · exact Or.inl hz
    · exact Or.inr ⟨B,hB0,hB,
        PlanarShiftedDomain.mem_interior_of_lt K f B hp hRp,hz,hcount⟩

/-- Explicit subcritical positivity removes the zero-gap branch. -/
theorem exists_many_of_counterexample_of_gap {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hgap : ∀ e : Endpoints (m+1), (∀ i, e.1 i ≤ e.2 i) →
      budget K f e < 1 → 0 < gapArea K f e)
    {p₀ : Endpoints (m+1)} (hp₀ : p₀ ∈ domain K f)
    (hbad : gapArea K f p₀ < (max 0 (1-budget K f p₀))^2*(volume K).toReal) :
    ∃ B, 0 < B ∧ B < 1 ∧ ∃ p ∈ interior (PlanarShiftedDomain.domain K f B),
      PlanarShiftedDomain.margin K f B p = 0 ∧
      2*(m+1)+1 ≤ (nonemptyCells K f p).card := by
  obtain ⟨p,hp,hneg,_,hcases⟩ := exists_minimum_zero_or_many
    hm hK hc hne hV f hW hnorm hp₀ hbad
  rcases hcases with hz | ⟨B,hB0,hB,hpB,hz,hcount⟩
  · have hG := hgap p (fun i => ((interior_subset hp).1 i).2.1)
      (PlanarGapPositivity.budget_lt_one_of_rootMargin_neg f p hneg)
    exact False.elim (hG.ne' hz)
  · exact ⟨B,hB0,hB,p,hpB,hz,hcount⟩

/-- A strict normalized three-plank counterexample supplies seven cells.
Qualitative positivity is supplied explicitly to direct root-minimum selection;
the three-plank quantitative theorem and global shifted barrier are not used. -/
theorem exists_seven_of_counterexample (h2 : SharpPlanarBound 2)
    {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p₀ : Endpoints 3} (hp₀ : p₀ ∈ domain K f)
    (hbad : gapArea K f p₀ < (max 0 (1-budget K f p₀))^2*(volume K).toReal) :
    ∃ B, 0 < B ∧ B < 1 ∧ ∃ p ∈ interior (PlanarShiftedDomain.domain K f B),
      PlanarShiftedDomain.margin K f B p = 0 ∧
      7 ≤ (nonemptyCells K f p).card := by
  exact exists_many_of_counterexample_of_gap h2 hK hc hne hV f hW hnorm
    (fun e he hR => PlanarGapPositivity.gapArea_pos_of_le_three (by decide : 2+1 ≤ 3)
      hK hc hne hV f e he hW hR) hp₀ hbad

end Plank.PlanarMinimumCellRank

/-- info: 'Plank.PlanarMinimumCellRank.exists_seven_of_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarMinimumCellRank.exists_seven_of_counterexample

/-- info: 'Plank.PlanarMinimumCellRank.exists_many_of_shifted_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarMinimumCellRank.exists_many_of_shifted_barrier
