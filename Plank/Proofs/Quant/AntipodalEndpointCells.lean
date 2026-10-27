/- Contact counts from affine cell majorants and linear algebra.
The historical module/namespace is retained for compatibility. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalMinimumCellRank
public import Plank.Proofs.Quant.FiniteDimensionalNormalizedDomain

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace Plank.AntipodalEndpointCells

open FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling FiniteDimensionalMinimumCellRank
  FiniteDimensionalMinimumContactRank

variable {n m : ℕ}

/-- The full contact count follows from affine cell majorants and linear algebra. -/
theorem contact_counts_at_minimum
    {K : Set (Point n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point n →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (D : Set (Endpoints (Fin m))) (p : Endpoints (Fin m))
    (hp : p ∈ interior D) (ho : ∀ i, p.1 i < p.2 i)
    (hmin : ∀ e ∈ D, rootCost K f p ≤ rootCost K f e)
    (hnomotion : ∀ z, p-z ∈ D ∩ (rootCost K f) ⁻¹' {rootCost K f p} →
      p+z ∈ D ∩ (rootCost K f) ⁻¹' {rootCost K f p} → z = 0) :
    2*m ≤ (nonemptyCells K f p).card ∧
      (0 < gapVolume K f p → 2*m+1 ≤ (nonemptyCells K f p).card) := by
  classical
  let C := nonemptyCells K f p
  have hreg : p ∈ region K f C := by
    intro s hs
    apply not_nonempty_iff_eq_empty.mp
    intro h
    exact hs (by simpa only [C, nonemptyCells, Finset.mem_filter,
      Finset.mem_univ, true_and] using h)
  have hlocal : IsLocalMin (rootCost K f) p := by
    filter_upwards [isOpen_interior.mem_nhds hp] with e he
    exact hmin e (interior_subset he)
  have no_line (z : Endpoints (Fin m))
      (hz : ∀ᶠ t : ℝ in 𝓝 0, rootCost K f (p+t • z) = rootCost K f p) : z = 0 := by
    have ht : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
      have hcont : Continuous (fun t : ℝ => p+t • z) := by fun_prop
      simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto
    apply Convex.FiniteMinimumMotion.eq_zero_of_eventually_line_mem hnomotion
    filter_upwards [hz, ht.eventually (isOpen_interior.mem_nhds hp)] with t he hD
    exact ⟨interior_subset hD, he⟩
  have hpositive (hg : 0 < gapVolume K f p) : 2*m+1 ≤ C.card := by
    by_contra hn
    have hC : C.card ≤ 2*m := by omega
    obtain ⟨z, hzne, hz⟩ := exists_motion_at_positive_root_minimum
      hK hc hne hV f hW C hC p ho hreg hg hlocal
    exact hzne (no_line z hz)
  refine ⟨?_, hpositive⟩
  by_cases hzero : gapVolume K f p = 0
  · by_contra hn
    have hC : C.card < 2*m := Nat.lt_of_not_ge hn
    obtain ⟨z, hzne, hz⟩ := exists_zero_gap_motion
      hK hc hne hV f hW C hC p ho hreg hzero
    have ht : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
      have hcont : Continuous (fun t : ℝ => p+t • z) := by fun_prop
      simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto
    have hcost : ∀ᶠ t : ℝ in 𝓝 0, rootCost K f (p+t • z) =
        rootCost K f p + t * budget K f z := by
      filter_upwards [hz] with t ht
      rw [rootCost_eq_budget_of_gap_eq_zero ht, rootCost_eq_budget_of_gap_eq_zero hzero]
      simp only [← budgetLinear_apply, map_add, map_smul, smul_eq_mul]
    have hslope : budget K f z = 0 := by
      apply slope_eq_zero_of_eventually_nonneg
      filter_upwards [hcost, ht.eventually hlocal] with t he hl
      linarith only [he, hl]
    apply hzne
    apply no_line
    filter_upwards [hcost] with t he
    simpa only [hslope, mul_zero, add_zero] using he
  · have hg : 0 < gapVolume K f p :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (fun hz => hzero hz.symm)
    change 2*m ≤ C.card
    have h := hpositive hg
    omega


/-- Select the actual minimum and apply the analytic contact-count lemma. -/
theorem exists_minimum_contact_counts_of_boundary
    {K : Set (Point n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point n →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (D : Set (Endpoints (Fin m))) (hD : IsCompact D)
    (hregular : ∀ p ∈ interior D, ∀ i, p.1 i < p.2 i)
    (hboundary : ∀ p ∈ D, p ∉ interior D → 1 ≤ rootCost K f p)
    {p₀ : Endpoints (Fin m)} (hp₀ : p₀ ∈ D) (hbad : rootCost K f p₀ < 1) :
    ∃ p ∈ interior D, rootCost K f p < 1 ∧
      (∀ e ∈ D, rootCost K f p ≤ rootCost K f e) ∧
      2*m ≤ (nonemptyCells K f p).card ∧
      (0 < gapVolume K f p → 2*m+1 ≤ (nonemptyCells K f p).card) := by
  obtain ⟨p, hpI, hneg, hminimum, hrigid⟩ :=
    ResearchFormalized.CompactMinimum.exists_interior_minimum_no_motion hD
      (continuous_rootCost hK hne f hW) hboundary hp₀ hbad
  have hcounts := contact_counts_at_minimum hK hc hne hV f hW D p hpI
    (hregular p hpI) hminimum hrigid
  exact ⟨p, hpI, hneg, hminimum, hcounts⟩

open FiniteDimensionalParameterDomain FiniteDimensionalInductionBoundary

/-- The normalized-domain interface. The smaller-plank boundary hypothesis
remains explicit; contact counts use affine majorants and linear algebra. -/
theorem exists_minimum_contact_counts (hm : SharpBound n m)
    {K : Set (Point n)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point n →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p₀ : Endpoints (Fin (m+1))} (hp₀ : p₀ ∈ domain K f)
    (hbad : rootCost K f p₀ < 1) :
    ∃ p ∈ interior (domain K f), rootCost K f p < 1 ∧
      (∀ e ∈ domain K f, rootCost K f p ≤ rootCost K f e) ∧
      2*(m+1) ≤ (nonemptyCells K f p).card ∧
      (0 < gapVolume K f p → 2*(m+1)+1 ≤ (nonemptyCells K f p).card) := by
  exact exists_minimum_contact_counts_of_boundary hK hc hne hV f hW
    (domain K f) (isCompact_domain K f)
    (fun p hp => strict_windows_of_interior K f hp)
    (fun p hp hn => rootCost_on_boundary hm hK hc hne hV f hW hnorm ⟨subset_closure hp,hn⟩)
    hp₀ hbad


end Plank.AntipodalEndpointCells

/-- info: 'Plank.AntipodalEndpointCells.contact_counts_at_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.AntipodalEndpointCells.contact_counts_at_minimum

/-- info: 'Plank.AntipodalEndpointCells.exists_minimum_contact_counts_of_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.AntipodalEndpointCells.exists_minimum_contact_counts_of_boundary

/-- info: 'Plank.AntipodalEndpointCells.exists_minimum_contact_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.AntipodalEndpointCells.exists_minimum_contact_counts
