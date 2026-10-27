/- Compact minimum selection for actual plank gaps in every positive dimension.
Boundary bounds and regularity are explicit; zero gap remains an alternative. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalEndpointCells
public import Plank.Proofs.Quant.FiniteDimensionalFewCellScaling
public import Plank.Convex.FiniteMinimumMotion
public import ResearchFormalized.Convex.CompactMinimum
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalMinimumCellRank

open Set MeasureTheory Filter FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
open scoped Topology

variable {n m : ℕ}

/-- If the dimension-power margin is nonnegative on a compact endpoint domain
and has a zero, regular interior zeros include one with at least `2*m+1`
nonempty closed cells. No covering theorem or minimum-existence hypothesis
for arbitrary plank configurations is hidden in this conditional statement. -/
theorem exists_many_of_compact_zero_domain {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (B : ℝ) (D : Set (Endpoints (Fin m))) (hD : IsCompact D)
    (hzero : ∃ p ∈ D, margin K f B p = 0)
    (hminimum : ∀ p ∈ D, 0 ≤ margin K f B p)
    (hregular : ∀ p ∈ D, margin K f B p = 0 →
      p ∈ interior D ∧ (∀ i, p.1 i < p.2 i) ∧ 0 < B-budget K f p) :
    ∃ p ∈ interior D, margin K f B p = 0 ∧
      2*m+1 ≤ (nonemptyCells K f p).card := by
  classical
  let Z := D ∩ (margin K f B) ⁻¹' {0}
  have hZ : IsCompact Z := hD.inter_right
    (isClosed_singleton.preimage (continuous_margin hK hne f hW B))
  obtain ⟨a,ha,haz⟩ := hzero
  obtain ⟨p,hp,_,hnomotion⟩ := Plank.Convex.FiniteMinimumMotion.exists_minimizer_no_motion
    Z hZ ⟨a,ha,haz⟩ (0 : Endpoints (Fin m) →L[ℝ] ℝ)
  have hz : margin K f B p = 0 := hp.2
  obtain ⟨hpI,ho,hq⟩ := hregular p hp.1 hz
  have hmin : IsLocalMin (margin K f B) p := by
    apply Filter.Eventually.mono (isOpen_interior.mem_nhds hpI)
    intro e he
    rw [hz]
    exact hminimum e (interior_subset he)
  refine ⟨p,hpI,hz,?_⟩
  by_contra hn
  let C := nonemptyCells K f p
  have hC : C.card ≤ 2*m := by change ¬(2*m+1) ≤ C.card at hn; omega
  have hreg : p ∈ region K f C := by
    intro s hs
    apply not_nonempty_iff_eq_empty.mp
    intro he
    exact hs (by simpa only [C,nonemptyCells,Finset.mem_filter,Finset.mem_univ,true_and] using he)
  obtain ⟨z,hzne,c,_,hline⟩ := exists_common_upper_scaling_at_minimum
    hK hc hne hV f hW C hC B p ho hreg hq hz hmin
  have ht : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
    have hcont : Continuous (fun t : ℝ => p+t • z) := by fun_prop
    simpa only [zero_smul,add_zero] using
      (hcont.continuousAt (x := (0 : ℝ))).tendsto
  have hplus : ∀ᶠ t : ℝ in 𝓝 0, p+t • z ∈ Z := by
    filter_upwards [hline,ht.eventually (isOpen_interior.mem_nhds hpI)] with t he hD
    exact ⟨interior_subset hD,he.2.2⟩
  exact hzne (Plank.Convex.FiniteMinimumMotion.eq_zero_of_eventually_line_mem hnomotion hplus)

private theorem gapRoot_pow (K : Set (Point n))
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin m)) :
    gapRoot K f p ^ (n+1) = gapVolume K f p / (volume K).toReal :=
  Real.rpow_inv_natCast_pow
    (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (Nat.succ_ne_zero n)

private theorem gap_eq_root_pow {K : Set (Point n)} (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin m)) :
    gapVolume K f p = (volume K).toReal * gapRoot K f p ^ (n+1) := by
  rw [gapRoot_pow, mul_comm, div_mul_cancel₀ _ hV.ne']

/-- Few cells make root cost affine from above along a nonzero line.
At a local minimum the slope vanishes, so the same root cost is retained. -/
theorem exists_motion_at_positive_root_minimum {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (C : Finset (Finset (Fin m))) (hC : C.card ≤ 2*m)
    (p : Endpoints (Fin m)) (ho : ∀ i, p.1 i < p.2 i)
    (hreg : p ∈ region K f C) (hpositive : 0 < gapVolume K f p)
    (hmin : IsLocalMin (rootCost K f) p) :
    ∃ z : Endpoints (Fin m), z ≠ 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, rootCost K f (p+t • z) = rootCost K f p := by
  obtain ⟨z,hzne,c,_,hupper⟩ := exists_common_upper_cell_scaling
    hK hc hne hV f hW C hC p ho hreg hpositive
  have hline : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
    have hh : Continuous (fun t : ℝ => p+t • z) := by fun_prop
    simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto
  have hfactor : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1+t*c := by
    exact (show Continuous (fun t : ℝ => 1+t*c) by fun_prop).continuousAt.eventually
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1+0*c))
  have hq : 0 ≤ gapRoot K f p := Real.rpow_nonneg
    (div_nonneg ENNReal.toReal_nonneg hV.le) _
  have hcost : ∀ᶠ t : ℝ in 𝓝 0, rootCost K f (p+t • z) ≤
      rootCost K f p+t*(budget K f z+gapRoot K f p*c) := by
    filter_upwards [hupper,hfactor] with t hu ht
    have hroot : gapRoot K f (p+t • z) ≤ gapRoot K f p*(1+t*c) := by
      apply le_of_pow_le_pow_left₀ (Nat.succ_ne_zero n) (mul_nonneg hq ht.le)
      simp only [mul_pow,gapRoot_pow]
      exact (div_le_div_of_nonneg_right hu.2 hV.le).trans_eq (by
        simp only [Nat.succ_eq_add_one]; ring)
    have hb : budget K f (p+t • z) = budget K f p+t*budget K f z := by
      simp only [← budgetLinear_apply,map_add,map_smul,smul_eq_mul]
    unfold rootCost
    rw [hb]
    nlinarith only [hroot]
  have hslope : budget K f z+gapRoot K f p*c = 0 := by
    apply slope_eq_zero_of_eventually_nonneg
    filter_upwards [hcost,hline.eventually hmin] with t hu hl
    linarith only [hu,hl]
  refine ⟨z,hzne,?_⟩
  filter_upwards [hcost,hline.eventually hmin] with t hu hl
  rw [hslope,mul_zero,add_zero] at hu
  exact le_antisymm hu hl

/-- Select the root-cost minimum once and retain its no-motion witness in
both branches. No qualitative gap positivity is assumed. -/
theorem exists_rigid_minimum_zero_or_many_of_boundary {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (D : Set (Endpoints (Fin m))) (hD : IsCompact D)
    (hR : ∀ p ∈ D, 0 ≤ budget K f p)
    (hregular : ∀ p ∈ interior D, ∀ i, p.1 i < p.2 i)
    (hboundary : ∀ p ∈ D, p ∉ interior D → 1 ≤ rootCost K f p)
    {p₀ : Endpoints (Fin m)} (hp₀ : p₀ ∈ D) (hbad : rootCost K f p₀ < 1) :
    ∃ p ∈ interior D, rootCost K f p < 1 ∧
      (∀ e ∈ D, rootCost K f p ≤ rootCost K f e) ∧
      (∀ z, p-z ∈ D ∩ (rootCost K f) ⁻¹' {rootCost K f p} →
        p+z ∈ D ∩ (rootCost K f) ⁻¹' {rootCost K f p} → z = 0) ∧
      (gapVolume K f p = 0 ∨ ∃ B, 0 < B ∧ B < 1 ∧ budget K f p < B ∧
        margin K f B p = 0 ∧ 2*m+1 ≤ (nonemptyCells K f p).card) := by
  classical
  obtain ⟨p,hpI,hneg,hminimum,hnomotion⟩ :=
    ResearchFormalized.CompactMinimum.exists_interior_minimum_no_motion hD
      (continuous_rootCost hK hne f hW) hboundary hp₀ hbad
  refine ⟨p,hpI,hneg,hminimum,hnomotion,?_⟩
  by_cases hG : gapVolume K f p = 0
  · exact Or.inl hG
  have hGpos : 0 < gapVolume K f p :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (fun hz => hG hz.symm)
  have hq : 0 < gapRoot K f p := Real.rpow_pos_of_pos (div_pos hGpos hV) _
  let B := rootCost K f p
  have hB0 : 0 < B := add_pos_of_pos_of_nonneg hq (hR p (interior_subset hpI))
  have hRp : budget K f p < B := by dsimp [B,rootCost]; linarith only [hq]
  have hBp : B-budget K f p = gapRoot K f p := by dsimp [B,rootCost]; ring
  have hz : margin K f B p = 0 := by
    unfold margin
    rw [hBp,← gap_eq_root_pow hV f p,sub_self]
  have hmin : IsLocalMin (rootCost K f) p := by
    filter_upwards [isOpen_interior.mem_nhds hpI] with e he
    exact hminimum e (interior_subset he)
  refine Or.inr ⟨B,hB0,hneg,hRp,hz,?_⟩
  by_contra hn
  let C := nonemptyCells K f p
  have hC : C.card ≤ 2*m := by change ¬(2*m+1) ≤ C.card at hn; omega
  have hreg : p ∈ region K f C := by
    intro s hs
    apply not_nonempty_iff_eq_empty.mp
    intro he
    exact hs (by simpa only [C,nonemptyCells,Finset.mem_filter,Finset.mem_univ,true_and] using he)
  obtain ⟨z,hzne,hline⟩ := exists_motion_at_positive_root_minimum
    hK hc hne hV f hW C hC p (hregular p hpI) hreg hGpos hmin
  have ht : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
    have hcont : Continuous (fun t : ℝ => p+t • z) := by fun_prop
    simpa only [zero_smul,add_zero] using
      (hcont.continuousAt (x := (0 : ℝ))).tendsto
  have hplus : ∀ᶠ t : ℝ in 𝓝 0,
      p+t • z ∈ D ∩ (rootCost K f) ⁻¹' {rootCost K f p} := by
    filter_upwards [hline,ht.eventually (isOpen_interior.mem_nhds hpI)] with t he hD
    exact ⟨interior_subset hD,he⟩
  exact hzne (Plank.Convex.FiniteMinimumMotion.eq_zero_of_eventually_line_mem hnomotion hplus)

/-- The original interface, obtained by forgetting the retained no-motion witness. -/
theorem exists_minimum_zero_or_many_of_boundary {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (D : Set (Endpoints (Fin m))) (hD : IsCompact D)
    (hR : ∀ p ∈ D, 0 ≤ budget K f p)
    (hregular : ∀ p ∈ interior D, ∀ i, p.1 i < p.2 i)
    (hboundary : ∀ p ∈ D, p ∉ interior D → 1 ≤ rootCost K f p)
    {p₀ : Endpoints (Fin m)} (hp₀ : p₀ ∈ D) (hbad : rootCost K f p₀ < 1) :
    ∃ p ∈ interior D, rootCost K f p < 1 ∧
      (∀ e ∈ D, rootCost K f p ≤ rootCost K f e) ∧
      (gapVolume K f p = 0 ∨ ∃ B, 0 < B ∧ B < 1 ∧ budget K f p < B ∧
        margin K f B p = 0 ∧ 2*m+1 ≤ (nonemptyCells K f p).card) := by
  obtain ⟨p,hp,hbadp,hminimum,_,hcases⟩ := exists_rigid_minimum_zero_or_many_of_boundary
    hK hc hne hV f hW D hD hR hregular hboundary hp₀ hbad
  exact ⟨p,hp,hbadp,hminimum,hcases⟩

end Plank.FiniteDimensionalMinimumCellRank

#print axioms Plank.FiniteDimensionalMinimumCellRank.exists_many_of_compact_zero_domain
#print axioms Plank.FiniteDimensionalMinimumCellRank.exists_minimum_zero_or_many_of_boundary

#print axioms Plank.FiniteDimensionalMinimumCellRank.exists_rigid_minimum_zero_or_many_of_boundary

#print axioms Plank.FiniteDimensionalMinimumCellRank.exists_motion_at_positive_root_minimum
