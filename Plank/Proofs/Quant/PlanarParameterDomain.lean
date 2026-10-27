/- The actual endpoint domain and its inductively paid boundary. -/
module

public import Plank.Proofs.Quant.PlanarWindowData

public import Plank.Proofs.Quant.PlanarInductionBoundary
public import Plank.Proofs.Quant.PlanarGapAnalysis
public import Plank.Proofs.Quant.FiniteDimensionalParameterDomain

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParameterDomain

open Set MeasureTheory PlanarQuantitative
open Plank.Convex.DeficientHeightTilt

/-- Ordered windows in the unit support box, with total actual relative width
at most one. The body and affine functionals stay fixed. -/
def domain {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) : Set (Endpoints m) :=
  {p | (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1) ∧ budget K f p ≤ 1}

theorem continuous_budget {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) :
    Continuous (budget K f) := by
  exact FiniteDimensionalParameterDomain.continuous_budget K f

theorem isClosed_domain {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) :
    IsClosed (domain K f) := by
  exact FiniteDimensionalParameterDomain.isClosed_domain K f

theorem isCompact_domain {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) :
    IsCompact (domain K f) := by
  exact FiniteDimensionalParameterDomain.isCompact_domain K f

theorem domain_nonempty {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) :
    (domain K f).Nonempty := ⟨0, by simp [domain, budget]⟩

theorem budget_nonneg {m : ℕ} {K : Set Point} (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) {p : Endpoints m} (hp : p ∈ domain K f) :
    0 ≤ budget K f p :=
  Finset.sum_nonneg fun i _ => div_nonneg (sub_nonneg.mpr (hp.1 i).2.1) (hW i).le

/-- Strict window and budget inequalities place the endpoint vector inside
the actual domain, in the ordinary topology of endpoint space. -/
theorem mem_interior_of_strict {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    {p : Endpoints m} (hp : ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1)
    (hbudget : budget K f p < 1) : p ∈ interior (domain K f) := by
  let U : Set (Endpoints m) :=
    {p | (∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1) ∧ budget K f p < 1}
  have hopen : IsOpen U := by
    simp only [U, Set.ofPred_and, Set.ofPred_forall]
    exact (isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (by fun_prop)).inter
        ((isOpen_lt (by fun_prop) (by fun_prop)).inter
          (isOpen_lt (by fun_prop) continuous_const))).inter
      (isOpen_lt (continuous_budget K f) continuous_const)
  have hsub : U ⊆ domain K f := by
    intro q hq
    exact ⟨fun i => ⟨(hq.1 i).1.le, (hq.1 i).2.1.le, (hq.1 i).2.2.le⟩, hq.2.le⟩
  exact (interior_maximal hsub hopen) ⟨hp, hbudget⟩

/-- Every point of the domain outside its interior has a tight budget or a
zero-width/support-endpoint equality. This is a topological boundary fact. -/
theorem boundary_cases {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    {p : Endpoints m} (hp : p ∈ domain K f) (hnot : p ∉ interior (domain K f)) :
    budget K f p = 1 ∨ ∃ i, p.1 i = 0 ∨ p.1 i = p.2 i ∨ p.2 i = 1 := by
  exact FiniteDimensionalParameterDomain.boundary_cases K f hp hnot

/-- The previous full quantitative theorem pays the entire boundary of the
normalized actual endpoint domain. No area-chart assumption is used. -/
theorem bound_on_boundary {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p : Endpoints (m+1)} (hp : p ∈ frontier (domain K f)) :
    (max 0 (1-budget K f p))^2 * (volume K).toReal ≤ gapArea K f p := by
  exact FiniteDimensionalParameterDomain.bound_on_boundary hm hK hconv hne f hW hnorm hp

/-- The actual normalized square-root margin used in the minimum argument. -/
def rootMargin {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints m) : ℝ :=
  Real.sqrt (gapArea K f p / (volume K).toReal) + budget K f p - 1

theorem continuous_gapArea {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (hne : K.Nonempty) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) : Continuous (gapArea K f) :=
  PlanarGapAnalysis.continuous_gap_area hK hne f hW

theorem continuous_rootMargin {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (hne : K.Nonempty) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) : Continuous (rootMargin K f) :=
  (((continuous_gapArea hK hne f hW).div_const _).sqrt.add
    (continuous_budget K f)).sub continuous_const

/-- The root margin is negative exactly when the actual quantitative bound
fails, on the domain with budget at most one. -/
theorem rootMargin_neg_iff {m : ℕ} {K : Set Point}
    (hV : 0 < (volume K).toReal) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints m) (hR : budget K f p ≤ 1) :
    rootMargin K f p < 0 ↔
      gapArea K f p < (max 0 (1-budget K f p))^2 * (volume K).toReal := by
  have hd : 0 ≤ 1-budget K f p := sub_nonneg.mpr hR
  have hG : 0 ≤ gapArea K f p := ENNReal.toReal_nonneg
  calc
    rootMargin K f p < 0 ↔
        Real.sqrt (gapArea K f p / (volume K).toReal) < 1-budget K f p := by
      unfold rootMargin
      constructor <;> intro h <;> linarith
    _ ↔ gapArea K f p / (volume K).toReal < (1-budget K f p)^2 :=
      Real.sqrt_lt (div_nonneg hG hV.le) hd
    _ ↔ gapArea K f p < (1-budget K f p)^2 * (volume K).toReal := div_lt_iff₀ hV
    _ ↔ gapArea K f p < (max 0 (1-budget K f p))^2 * (volume K).toReal := by
      rw [max_eq_right hd]

theorem rootMargin_nonneg_on_boundary {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p : Endpoints (m+1)} (hp : p ∈ frontier (domain K f)) :
    0 ≤ rootMargin K f p := by
  have hmem : p ∈ domain K f := (isClosed_domain K f).frontier_subset hp
  by_contra hn
  have hbad := (rootMargin_neg_iff hV f p hmem.2).mp (lt_of_not_ge hn)
  exact (not_lt_of_ge (bound_on_boundary hm hK hconv hne f hW hnorm hp)) hbad

/-- An actual counterexample on the normalized endpoint domain has an
interior negative root-margin minimum. Compactness, continuity, attainment
and the inductive boundary bound are proved rather than supplied as inputs. -/
theorem exists_negative_interior_minimum {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p₀ : Endpoints (m+1)} (hp₀ : p₀ ∈ domain K f)
    (hbad : gapArea K f p₀ < (max 0 (1-budget K f p₀))^2 * (volume K).toReal) :
    ∃ p ∈ interior (domain K f), rootMargin K f p < 0 ∧
      ∀ q ∈ domain K f, rootMargin K f p ≤ rootMargin K f q := by
  have hnegative := (rootMargin_neg_iff hV f p₀ hp₀.2).mpr hbad
  obtain ⟨p, hp, hmin⟩ := (isCompact_domain K f).exists_isMinOn (domain_nonempty K f)
    (continuous_rootMargin hK hne f hW).continuousOn
  have hneg : rootMargin K f p < 0 := (hmin hp₀).trans_lt hnegative
  have hint : p ∈ interior (domain K f) := by
    by_contra hn
    have hfrontier : p ∈ frontier (domain K f) := ⟨subset_closure hp, hn⟩
    exact (not_lt_of_ge (rootMargin_nonneg_on_boundary hm hK hconv hne hV f hW hnorm
      hfrontier)) hneg
  exact ⟨p, hint, hneg, fun q hq => hmin hq⟩

end Plank.PlanarParameterDomain
