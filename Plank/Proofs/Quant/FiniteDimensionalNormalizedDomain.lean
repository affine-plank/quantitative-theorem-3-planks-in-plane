/- The actual endpoint domain and its inductively paid boundary. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalInductionBoundary
public import Plank.Proofs.Quant.FiniteDimensionalEndpointCells

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalParameterDomain

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalMinimumCellRank FiniteDimensionalInductionBoundary
open scoped Topology

variable {d : ℕ}

/-- Ordered windows in the unit support box, with total actual relative width
at most one. The body and affine functionals stay fixed. -/
def domain {m : ℕ} (K : Set (Point d)) (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) : Set (Endpoints (Fin m)) :=
  {p | (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1) ∧ budget K f p ≤ 1}

theorem continuous_budget {m : ℕ} (K : Set (Point d)) (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) :
    Continuous (budget K f) := by
  unfold budget
  fun_prop

theorem isClosed_domain {m : ℕ} (K : Set (Point d)) (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) :
    IsClosed (domain K f) := by
  simp only [domain, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun i =>
    (isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_le (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) continuous_const))).inter
    (isClosed_le (continuous_budget K f) continuous_const)

theorem isCompact_domain {m : ℕ} (K : Set (Point d)) (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) :
    IsCompact (domain K f) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : Endpoints (Fin m)) 1)).of_isClosed_subset
    (isClosed_domain K f)
  intro p hp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i
    exact (hp.1 i).1
  · intro i
    exact (hp.1 i).1.trans (hp.1 i).2.1
  · intro i
    exact (hp.1 i).2.1.trans (hp.1 i).2.2
  · intro i
    exact (hp.1 i).2.2

theorem domain_nonempty {m : ℕ} (K : Set (Point d)) (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) :
    (domain K f).Nonempty := ⟨0, by simp [domain, budget]⟩

theorem budget_nonneg {m : ℕ} {K : Set (Point d)} (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < Body.width K (f i)) {p : Endpoints (Fin m)} (hp : p ∈ domain K f) :
    0 ≤ budget K f p :=
  Finset.sum_nonneg fun i _ => div_nonneg (sub_nonneg.mpr (hp.1 i).2.1) (hW i).le

/-- Strict window and budget inequalities place the endpoint vector inside
the actual domain, in the ordinary topology of endpoint space. -/
theorem mem_interior_of_strict {m : ℕ} (K : Set (Point d)) (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    {p : Endpoints (Fin m)} (hp : ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1)
    (hbudget : budget K f p < 1) : p ∈ interior (domain K f) := by
  let U : Set (Endpoints (Fin m)) :=
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
theorem boundary_cases {m : ℕ} (K : Set (Point d)) (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    {p : Endpoints (Fin m)} (hp : p ∈ domain K f) (hnot : p ∉ interior (domain K f)) :
    budget K f p = 1 ∨ ∃ i, p.1 i = 0 ∨ p.1 i = p.2 i ∨ p.2 i = 1 := by
  classical
  by_cases hbudget : budget K f p = 1
  · exact Or.inl hbudget
  · right
    by_contra hn
    apply hnot
    apply mem_interior_of_strict K f
    · intro i
      have hlo : p.1 i ≠ 0 := fun h => hn ⟨i, Or.inl h⟩
      have hmid : p.1 i ≠ p.2 i := fun h => hn ⟨i, Or.inr (Or.inl h)⟩
      have hhi : p.2 i ≠ 1 := fun h => hn ⟨i, Or.inr (Or.inr h)⟩
      exact ⟨lt_of_le_of_ne (hp.1 i).1 hlo.symm,
        lt_of_le_of_ne (hp.1 i).2.1 hmid, lt_of_le_of_ne (hp.1 i).2.2 hhi⟩
    · exact lt_of_le_of_ne hp.2 hbudget

/-- The previous full quantitative theorem pays the entire boundary of the
normalized actual endpoint domain. No area-chart assumption is used. -/
theorem bound_on_boundary {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p : Endpoints (Fin (m+1))} (hp : p ∈ frontier (domain K f)) :
    (max 0 (1-budget K f p))^(d+1) * (volume K).toReal ≤ gapVolume K f p := by
  have hmem : p ∈ domain K f := (isClosed_domain K f).frontier_subset hp
  rcases boundary_cases K f hmem hp.2 with hbudget | ⟨i, hlo | hzero | hhi⟩
  · rw [hbudget]
    simp only [sub_self, max_self, zero_pow (Nat.succ_ne_zero d), zero_mul]
    exact ENNReal.toReal_nonneg
  · apply FiniteDimensionalInductionBoundary.bound_at_index hm hK hconv hne f p.1 p.2
      (fun i => (hmem.1 i).2.1) hW i
    exact Or.inr (Or.inl (fun x hx => by rw [hlo]; exact (hnorm i x hx).1))
  · apply FiniteDimensionalInductionBoundary.bound_at_index hm hK hconv hne f p.1 p.2
      (fun i => (hmem.1 i).2.1) hW i
    exact Or.inl hzero
  · apply FiniteDimensionalInductionBoundary.bound_at_index hm hK hconv hne f p.1 p.2
      (fun i => (hmem.1 i).2.1) hW i
    exact Or.inr (Or.inr (fun x hx => by rw [hhi]; exact (hnorm i x hx).2))

/-- The ordinary interior forces every window to have positive width. -/
theorem strict_windows_of_interior {m : ℕ} (K : Set (Point d))
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) {p : Endpoints (Fin m)}
    (hp : p ∈ interior (domain K f)) : ∀ i, p.1 i < p.2 i := by
  intro i
  let L : Endpoints (Fin m) →ₗ[ℝ] ℝ := (LinearMap.proj i).comp
    (LinearMap.snd ℝ (Fin m → ℝ) (Fin m → ℝ) - LinearMap.fst ℝ _ _)
  have hL : Function.Surjective L := fun r => ⟨(0, fun _ => r), by simp [L]⟩
  have hsub : domain K f ⊆ L ⁻¹' Ici 0 := by
    intro q hq
    exact sub_nonneg.mpr (hq.1 i).2.1
  have hi := (L.isOpenMap_of_finiteDimensional hL).interior_preimage_subset_preimage_interior
    (interior_mono hsub hp)
  have hh : 0 < L p := by simpa only [mem_preimage, interior_Ici, mem_Ioi] using hi
  exact sub_pos.mp hh

/-- Subunit root cost is exactly failure of the dimension-power bound. -/
theorem rootCost_lt_one_iff {m : ℕ} {K : Set (Point d)} (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin m))
    (hR : budget K f p ≤ 1) :
    rootCost K f p < 1 ↔
      gapVolume K f p < (max 0 (1-budget K f p))^(d+1)*(volume K).toReal := by
  have hq : 0 ≤ gapRoot K f p :=
    Real.rpow_nonneg (div_nonneg ENNReal.toReal_nonneg hV.le) _
  have hpow : gapRoot K f p ^ (d+1) = gapVolume K f p/(volume K).toReal :=
    Real.rpow_inv_natCast_pow
      (div_nonneg ENNReal.toReal_nonneg hV.le) (Nat.succ_ne_zero d)
  rw [max_eq_right (sub_nonneg.mpr hR),rootCost,← lt_sub_iff_add_lt,
    ← pow_lt_pow_iff_left₀ hq (sub_nonneg.mpr hR) (Nat.succ_ne_zero d),hpow]
  exact div_lt_iff₀ hV

/-- The preceding full bound supplies the root-cost boundary inequality. -/
theorem rootCost_on_boundary {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p : Endpoints (Fin (m+1))} (hp : p ∈ frontier (domain K f)) :
    1 ≤ rootCost K f p := by
  have hmem := (isClosed_domain K f).frontier_subset hp
  by_contra hn
  have hbad := (rootCost_lt_one_iff hV f p hmem.2).mp (lt_of_not_ge hn)
  exact hbad.not_ge (bound_on_boundary hm hK hc hne f hW hnorm hp)

end Plank.FiniteDimensionalParameterDomain

#print axioms Plank.FiniteDimensionalParameterDomain.bound_on_boundary
