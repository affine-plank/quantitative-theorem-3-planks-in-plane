/- The actual smaller width-budget domain and its strict boundary barrier. -/
module

public import Plank.Proofs.Quant.PlanarGapPositivity
public import Plank.Proofs.Quant.ShiftedBudget

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarShiftedDomain

open Set MeasureTheory PlanarQuantitative
open PlanarParameterDomain (Endpoints budget gapArea rootMargin)
open Plank.Convex.DeficientHeightTilt

/-- The original normalized endpoint box cut down to relative budget `B`. -/
def domain {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) (B : ℝ) :
    Set (Endpoints m) := PlanarParameterDomain.domain K f ∩ {p | budget K f p ≤ B}

theorem isCompact_domain {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (B : ℝ) : IsCompact (domain K f B) :=
  (PlanarParameterDomain.isCompact_domain K f).inter_right
    (isClosed_le (PlanarParameterDomain.continuous_budget K f) continuous_const)

theorem mem_interior_of_lt {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (B : ℝ) {p : Endpoints m} (hp : p ∈ interior (PlanarParameterDomain.domain K f))
    (hB : budget K f p < B) : p ∈ interior (domain K f B) := by
  rw [domain, interior_inter]
  refine ⟨hp, ?_⟩
  exact interior_maximal (fun _ h => le_of_lt h)
    (isOpen_lt (PlanarParameterDomain.continuous_budget K f) continuous_const) hB

/-- A boundary point either exhausts the new budget or was already on the
boundary of the old endpoint domain. -/
theorem boundary_cases {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (B : ℝ) {p : Endpoints m} (hp : p ∈ domain K f B)
    (hnot : p ∉ interior (domain K f B)) :
    budget K f p = B ∨ p ∈ frontier (PlanarParameterDomain.domain K f) := by
  by_cases heq : budget K f p = B
  · exact Or.inl heq
  · right
    refine ⟨subset_closure hp.1, ?_⟩
    intro hi
    exact hnot (mem_interior_of_lt K f B hi (lt_of_le_of_ne hp.2 heq))

/-- A nonconstant linear constraint is strict at every interior point. -/
theorem strict_linear_lower_of_interior {m : ℕ} (L : Endpoints m →ₗ[ℝ] ℝ)
    (hL : Function.Surjective L) {D : Set (Endpoints m)} {c : ℝ}
    (hD : D ⊆ L ⁻¹' Ici c) {p : Endpoints m} (hp : p ∈ interior D) : c < L p := by
  have hi := (L.isOpenMap_of_finiteDimensional hL).interior_preimage_subset_preimage_interior
    (interior_mono hD hp)
  simpa only [mem_preimage, interior_Ici, mem_Ioi] using hi

/-- The strict window guards required by the area regularity theorem follow
from the ordinary interior of the actual endpoint domain. -/
theorem strict_windows_of_interior {m : ℕ} (K : Set Point)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (B : ℝ) {p : Endpoints m}
    (hp : p ∈ interior (domain K f B)) : ∀ i, p.1 i < p.2 i := by
  intro i
  let L : Endpoints m →ₗ[ℝ] ℝ := (LinearMap.proj i).comp
    (LinearMap.snd ℝ (Fin m → ℝ) (Fin m → ℝ) - LinearMap.fst ℝ _ _)
  have hL : Function.Surjective L := fun r => ⟨(0, fun _ => r), by simp [L]⟩
  have hsub : domain K f B ⊆ L ⁻¹' Ici 0 := by
    intro q hq
    exact sub_nonneg.mpr (hq.1.1 i).2.1
  exact sub_pos.mp (strict_linear_lower_of_interior L hL hsub hp)

/-- The relative width budget is a genuine linear map on endpoint space. -/
def budgetLinear {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) :
    Endpoints m →ₗ[ℝ] ℝ :=
  ∑ i, (rangeWidth K (f i))⁻¹ • ((LinearMap.proj i).comp
    (LinearMap.snd ℝ (Fin m → ℝ) (Fin m → ℝ) - LinearMap.fst ℝ _ _))

@[simp] theorem budgetLinear_apply {m : ℕ} (K : Set Point)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) : budgetLinear K f p = budget K f p := by
  simp [budgetLinear, budget, div_eq_mul_inv, mul_comm]

/-- The affine deficit in the smaller domain. -/
def deficit {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) (B : ℝ) :
    Endpoints m →ᵃ[ℝ] ℝ := AffineMap.const ℝ (Endpoints m) B - (budgetLinear K f).toAffineMap

@[simp] theorem deficit_apply {m : ℕ} (K : Set Point)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (B : ℝ) (p : Endpoints m) :
    deficit K f B p = B-budget K f p := by
  simp [deficit]

def margin {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) (B : ℝ)
    (p : Endpoints m) : ℝ := gapArea K f p-(volume K).toReal*(B-budget K f p)^2

/-- The preceding quantitative bound and explicit subcritical gap positivity
pay the two kinds of boundary face. The plank count is unrestricted. -/
theorem margin_pos_on_boundary_of_gap {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hgap : ∀ p : Endpoints (m+1), (∀ i, p.1 i ≤ p.2 i) →
      budget K f p < 1 → 0 < gapArea K f p)
    (B : ℝ) (hB : B < 1) {p : Endpoints (m+1)} (hp : p ∈ domain K f B)
    (hnot : p ∉ interior (domain K f B)) : 0 < margin K f B p := by
  rcases boundary_cases K f B hp hnot with heq | hfront
  · have hG := hgap p (fun i => (hp.1.1 i).2.1) (hp.2.trans_lt hB)
    simpa [margin, heq] using hG
  · have hpaid := PlanarParameterDomain.bound_on_boundary hm hK hconv hne f hW hnorm hfront
    rw [max_eq_right (sub_nonneg.mpr hp.1.2)] at hpaid
    have hstrict := ShiftedBudget.boundary_target_strict (volume K).toReal B (budget K f p)
      hV hB hp.2
    dsimp [margin]
    nlinarith only [hpaid, hstrict]

/-- The original public boundary statement supplies positivity from the
qualitative covering theorem. -/
theorem margin_pos_on_boundary {m : ℕ} (hsmall : m+1 ≤ 3) (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (B : ℝ) (hB : B < 1) {p : Endpoints (m+1)} (hp : p ∈ domain K f B)
    (hnot : p ∉ interior (domain K f B)) : 0 < margin K f B p :=
  margin_pos_on_boundary_of_gap hm hK hconv hne hV f hW hnorm
    (fun q hq hR => PlanarGapPositivity.gapArea_pos_of_le_three hsmall
      hK hconv hne hV f q hq hW hR) B hB hp hnot

/-- An actual normalized counterexample constructs the smaller compact
domain, a zero of its nonnegative margin, and a strict boundary barrier.
The preceding quantitative bound and subcritical gap positivity are explicit;
no restriction on the plank count, polygon or chart assumption is needed. -/
theorem exists_shifted_barrier_of_gap {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hgap : ∀ p : Endpoints (m+1), (∀ i, p.1 i ≤ p.2 i) →
      budget K f p < 1 → 0 < gapArea K f p)
    {p₀ : Endpoints (m+1)} (hp₀ : p₀ ∈ PlanarParameterDomain.domain K f)
    (hbad : gapArea K f p₀ < (max 0 (1-budget K f p₀))^2 * (volume K).toReal) :
    ∃ B, 0 < B ∧ B < 1 ∧ ∃ p ∈ interior (domain K f B), margin K f B p = 0 ∧
      (∀ q ∈ domain K f B, 0 ≤ margin K f B q) ∧
      ∀ q ∈ domain K f B, q ∉ interior (domain K f B) → 0 < margin K f B q := by
  obtain ⟨p, hp, hneg, hmin⟩ := PlanarParameterDomain.exists_negative_interior_minimum hm
    hK hconv hne hV f hW hnorm hp₀ hbad
  have hmem : p ∈ PlanarParameterDomain.domain K f := interior_subset hp
  have hG := hgap p (fun i => (hmem.1 i).2.1)
    (PlanarGapPositivity.budget_lt_one_of_rootMargin_neg f p hneg)
  have hnegative : Real.sqrt (gapArea K f p/(volume K).toReal)+budget K f p < 1 := by
    dsimp [rootMargin] at hneg
    linarith only [hneg]
  have hminimum (q : PlanarParameterDomain.domain K f) :
      Real.sqrt (gapArea K f p/(volume K).toReal)+budget K f p ≤
      Real.sqrt (gapArea K f q/(volume K).toReal)+budget K f q := by
    have hh := hmin q q.property
    dsimp [rootMargin] at hh
    linarith only [hh]
  obtain ⟨B, hBpos, hB, hRp, hzero, hbound⟩ := ShiftedBudget.budget_of_root_minimum
    (volume K).toReal (fun q : PlanarParameterDomain.domain K f => budget K f q)
    (fun q => gapArea K f q) ⟨p, hmem⟩ hV (fun _ => ENNReal.toReal_nonneg) hG
    (PlanarParameterDomain.budget_nonneg f hW hmem) hnegative hminimum
  refine ⟨B, hBpos, hB, p, mem_interior_of_lt K f B hp hRp, ?_, ?_, ?_⟩
  · exact sub_eq_zero.mpr hzero
  · intro q hq
    exact sub_nonneg.mpr (hbound ⟨q, hq.1⟩ hq.2)
  · exact fun q hq hn => margin_pos_on_boundary_of_gap hm hK hconv hne hV f hW hnorm
      hgap B hB hq hn

/-- The original public construction is the explicit-positive-gap theorem
with the earlier qualitative covering input supplied. -/
theorem exists_shifted_barrier {m : ℕ} (hsmall : m+1 ≤ 3) (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p₀ : Endpoints (m+1)} (hp₀ : p₀ ∈ PlanarParameterDomain.domain K f)
    (hbad : gapArea K f p₀ < (max 0 (1-budget K f p₀))^2 * (volume K).toReal) :
    ∃ B, 0 < B ∧ B < 1 ∧ ∃ p ∈ interior (domain K f B), margin K f B p = 0 ∧
      (∀ q ∈ domain K f B, 0 ≤ margin K f B q) ∧
      ∀ q ∈ domain K f B, q ∉ interior (domain K f B) → 0 < margin K f B q :=
  exists_shifted_barrier_of_gap hm hK hconv hne hV f hW hnorm
    (fun q hq hR => PlanarGapPositivity.gapArea_pos_of_le_three hsmall
      hK hconv hne hV f q hq hW hR) hp₀ hbad

end Plank.PlanarShiftedDomain
