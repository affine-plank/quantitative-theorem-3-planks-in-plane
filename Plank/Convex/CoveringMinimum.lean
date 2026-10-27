/- Separation and rank for covering minima, independently of any plank inequality. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalEndpointCells
public import Plank.Convex.PlanarWindowBounds
public import Plank.Convex.FiniteMinimumMotion
public import ResearchFormalized.Convex.FiniteAffineSeparation

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace Plank.CoveringFirstContact

open FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling FiniteDimensionalMinimumCellRank
open Convex.PlanarCoverSpace Convex.PlanarCoverMinimum

variable {n m : ℕ}

abbrev Image (K : Set (FiniteDimensionalCapWindowScaling.Point n))
    (f : Fin m → FiniteDimensionalCapWindowScaling.Point n →ᵃ[ℝ] ℝ) :=
  (AffineMap.pi f) '' K

/-- One separating row preserves emptiness of one strict exterior cell. -/
theorem frozen_row [NeZero m]
    {K : Set (FiniteDimensionalCapWindowScaling.Point n)} (hc : Convex ℝ K)
    (f : Fin m → FiniteDimensionalCapWindowScaling.Point n →ᵃ[ℝ] ℝ)
    (p : Endpoints (Fin m)) (hcover : Covers (Image K f) p)
    (s : Finset (Fin m)) :
    ∃ row : Endpoints (Fin m) →L[ℝ] ℝ, ∀ e, row p ≤ row e →
      ¬ ∃ x ∈ K, ∀ i, if i ∈ s then e.2 i < f i x else f i x < e.1 i := by
  classical
  let g : Fin m → FiniteDimensionalCapWindowScaling.Point n →ᵃ[ℝ] ℝ := fun i =>
    if i ∈ s then f i - AffineMap.const ℝ _ (p.2 i)
    else AffineMap.const ℝ _ (p.1 i) - f i
  have he : ¬ ∃ x ∈ K, ∀ i, 0 < g i x := by
    rintro ⟨x, hx, hg⟩
    obtain ⟨i, hi, hj⟩ := hcover _ ⟨x, hx, rfl⟩
    have h := hg i
    by_cases hs : i ∈ s <;> simp only [g, hs, ite_true, ite_false,
      AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply] at h
    · exact (sub_pos.mp h).not_ge hj
    · exact (sub_pos.mp h).not_ge hi
  obtain ⟨a, ha, hsum, hbound⟩ :=
    ResearchFormalized.FiniteAffineSeparation.exists_weights K hc g he
  let row : Endpoints (Fin m) →L[ℝ] ℝ :=
    ∑ i, a i • wall (decide (i ∈ s)) i
  have hr (e : Endpoints (Fin m)) : row e =
      ∑ i, a i * (if i ∈ s then e.2 i else -e.1 i) := by
    simp only [row, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> simp [wall, hi]
  have hg (x) : (∑ i, a i * g i x) =
      (∑ i, a i * (if i ∈ s then f i x else -f i x)) - row p := by
    rw [hr, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : i ∈ s <;> simp [g, hs] <;> ring
  refine ⟨row, ?_⟩
  rintro e he ⟨x, hx, hcuts⟩
  have hstrict (i) : 0 < (if i ∈ s then f i x else -f i x) -
      (if i ∈ s then e.2 i else -e.1 i) := by
    have h := hcuts i
    by_cases hs : i ∈ s <;> simp only [hs, ite_true, ite_false] at h ⊢ <;> linarith
  have hapos : 0 < ∑ i, a i := by rw [hsum]; exact zero_lt_one
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => ha i)).mp hapos
  have hpos : 0 < ∑ i, a i * ((if i ∈ s then f i x else -f i x) -
      (if i ∈ s then e.2 i else -e.1 i)) :=
    Finset.sum_pos' (fun j _ => mul_nonneg (ha j) (hstrict j).le)
      ⟨i, Finset.mem_univ i, mul_pos hi (hstrict i)⟩
  simp only [mul_sub, Finset.sum_sub_distrib, ← hr] at hpos
  have hb := hbound x hx
  rw [hg] at hb
  linarith

/-- At an interior covering with no two-sided feasible motion, the number
of nonempty closed exterior cells is at least the number of wall parameters.
Only separation and linear algebra are used; no area or plank inequality. -/
theorem contact_count [NeZero m]
    {K : Set (FiniteDimensionalCapWindowScaling.Point n)}
    (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Fin m → FiniteDimensionalCapWindowScaling.Point n →ᵃ[ℝ] ℝ)
    (p : Endpoints (Fin m)) (hp : p ∈ strictWindows)
    (hcover : Covers (Image K f) p)
    (hnomotion : ∀ z, p-z ∈ unitCovers (Image K f) →
      p+z ∈ unitCovers (Image K f) → z = 0) :
    2*m ≤ (nonemptyCells K f p).card := by
  classical
  let C := nonemptyCells K f p
  choose row hrow using fun s : C => frozen_row hc f p hcover s.val
  let U : Set (Endpoints (Fin m)) := strictWindows ∩ region K f C
  have hU : IsOpen U := open_strictWindows.inter (isOpen_region hK f C)
  have hpU : p ∈ U := by
    refine ⟨hp, ?_⟩
    intro s hs
    apply not_nonempty_iff_eq_empty.mp
    intro h
    exact hs (by simpa only [C, nonemptyCells, Finset.mem_filter,
      Finset.mem_univ, true_and] using h)
  have hlocal (e : Endpoints (Fin m)) (he : e ∈ U)
      (hrows : ∀ s : C, row s p ≤ row s e) : e ∈ unitCovers (Image K f) := by
    apply unitCovers_of_strict_cover _ _ he.1
    rintro _ ⟨x, hx, rfl⟩
    by_contra hn
    let s := Finset.univ.filter (fun i => e.2 i < f i x)
    have hs (i) : (i ∈ s) ↔ e.2 i < f i x := by simp [s]
    have hcuts (i) : if i ∈ s then e.2 i < f i x else f i x < e.1 i := by
      by_cases hi : i ∈ s
      · exact ite_eq_left hi ▸ (hs i).mp hi
      · rw [ite_eq_right hi]
        have hhi : f i x ≤ e.2 i := le_of_not_gt (fun h => hi ((hs i).mpr h))
        exact lt_of_not_ge (fun h => hn ⟨i, h, hhi⟩)
    by_cases hmem : s ∈ C
    · exact hrow ⟨s, hmem⟩ e (hrows ⟨s, hmem⟩) ⟨x, hx, hcuts⟩
    · have hcell : x ∈ signCell K f e s := by
        refine ⟨hx, ?_⟩
        intro i
        have h := hcuts i
        by_cases hi : i ∈ s <;> simp only [hi, ite_true, ite_false] at h ⊢
        exacts [h.le, h.le]
      rw [he.2 s hmem] at hcell
      exact hcell
  have h := Convex.FiniteMinimumMotion.card_active_ge_finrank
    (unitCovers (Image K f)) U p hnomotion hU hpU row (fun s => row s p)
    (fun _ => le_rfl) hlocal
  simpa only [Module.finrank_prod, Module.finrank_pi, Module.finrank_self,
    Fintype.card_fin, Nat.mul_one, Nat.card_eq_fintype_card,
    Fintype.card_subtype_true, Fintype.card_coe, ← two_mul] using h

end Plank.CoveringFirstContact
