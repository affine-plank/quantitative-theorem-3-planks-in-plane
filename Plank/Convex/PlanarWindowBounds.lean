/- Clamping preserves covers and decreases width. The two-window theorem
and boundary homothety make every deficient cover strictly interior. -/
module
public import Plank.Convex.PlanarWindows
public import Plank.Convex.AffineSlabNormalization
public import Plank.Convex.ClosedCover
public import Plank.Convex.TwoAffineWindows
public import Plank.Convex.AffineBoundaryWindows
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.PlanarCoverMinimum
open PlanarCoverSpace AffineSlabNormalization

def width {n : ℕ} : Walls n →L[ℝ] ℝ :=
  ∑ i, ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _) -
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _))

theorem width_apply {n : ℕ} (B : Walls n) : width B = ∑ i, (B.2 i - B.1 i) := by
  simp [width]

def clipped {n : ℕ} (B : Walls n) : Walls n := (clamp ∘ B.1, clamp ∘ B.2)

theorem clipped_width_le {n : ℕ} (B : Walls n) (horder : ∀ i, B.1 i ≤ B.2 i) :
    width (clipped B) ≤ width B := by
  simp only [width_apply]
  exact Finset.sum_le_sum fun i _ => clamp_sub_le _ _ (horder i)

theorem clipped_unitCovers {n : ℕ} (K : Set (Point n))
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1) (B : Walls n)
    (horder : ∀ i, B.1 i ≤ B.2 i) (hcover : Covers K B) :
    clipped B ∈ unitCovers K := by
  refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, fun i => clamp_mono (horder i)⟩, ?_⟩
  · exact fun i => clamp_nonneg (B.1 i)
  · exact fun i => clamp_nonneg (B.2 i)
  · exact fun i => clamp_le_one (B.1 i)
  · exact fun i => clamp_le_one (B.2 i)
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact ⟨i, clamp_interval _ _ _ (hbox x hx i) hi⟩

private theorem two_coordinates_bound (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (c : Fin 2 → Fin 3) (lo hi : Fin 2 → ℝ) (horder : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ x (c j) ∧ x (c j) ≤ hi j) :
    1 ≤ ∑ j, (hi j - lo j) := by
  simpa only [Fin.sum_univ_two] using TwoAffineWindows.width_bound K hK
    (AffineMap.proj (c 0)) (AffineMap.proj (c 1))
    (fun x hx => ⟨hbox x hx _, hbox x hx _⟩)
    (lo 0) (hi 0) (lo 1) (hi 1) (horder 0) (horder 1) (hL _) (hU _) (hL _) (hU _)
    (fun x hx => by simpa only [Fin.exists_fin_two, AffineMap.proj_apply] using hcover x hx)

/-- A zero-width window can be removed, leaving the two-window theorem. -/
theorem widths_positive (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (B : Walls 3) (horder : ∀ i, B.1 i ≤ B.2 i)
    (hcover : Covers K B) (hdef : width B < 1) : ∀ i, B.1 i < B.2 i := by
  intro k
  by_contra hn
  have he : B.2 k = B.1 k := le_antisymm (le_of_not_gt hn) (horder k)
  let c := k.succAbove
  let C : Set (Point 3) := ⋃ j : Fin 2, {x | B.1 (c j) ≤ x (c j) ∧ x (c j) ≤ B.2 (c j)}
  have hclosed (i : Fin 3) : IsClosed {x : Point 3 | B.1 i ≤ x i ∧ x i ≤ B.2 i} :=
    (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  obtain ⟨p, hp, hpk⟩ : ∃ p ∈ K, p k ≠ B.1 k := by
    by_cases hl : B.1 k = 0
    · obtain ⟨p, hp, hpk⟩ := hU k
      exact ⟨p, hp, by rw [hpk, hl]; norm_num⟩
    · obtain ⟨p, hp, hpk⟩ := hL k
      exact ⟨p, hp, by rw [hpk]; exact Ne.symm hl⟩
  have hcov : K ⊆ C := by
    apply ClosedCover.closed_cover_remove_affine K C hK
      (isClosed_iUnion_of_finite fun j => hclosed (c j))
      (AffineMap.proj k) (B.1 k) p hp hpk
    intro x hx
    rcases (Fin.exists_iff_succAbove k).mp (hcover x hx) with ⟨hli, hhi⟩ | h
    · exact Or.inr (by change x k = B.1 k; rw [he] at hhi; exact le_antisymm hhi hli)
    · exact Or.inl (Set.mem_iUnion.mpr h)
  have htwo := two_coordinates_bound K hK hbox hL hU c (B.1 ∘ c) (B.2 ∘ c)
    (fun j => horder (c j)) (fun x hx => Set.mem_iUnion.mp (hcov hx))
  rw [width_apply, Fin.sum_univ_succAbove _ k, he, sub_self, zero_add] at hdef
  exact hdef.not_ge htwo

/-- A boundary window would leave a deficient two-window cover on a
homothetic copy of the body. No minimality or plane relation is needed. -/
theorem endpoints_strict (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (B : Walls 3) (horder : ∀ i, B.1 i ≤ B.2 i)
    (hends : ∀ i, 0 ≤ B.1 i ∧ B.2 i ≤ 1)
    (hcover : Covers K B) (hdef : width B < 1) :
    ∀ i, 0 < B.1 i ∧ B.2 i < 1 := by
  intro k
  have hno : ¬ (B.1 k = 0 ∨ B.2 k = 1) := by
    intro hb
    let c := k.succAbove
    have h := AffineBoundaryWindows.width_bound K hK (AffineMap.proj k)
      (fun j => AffineMap.proj (c j)) (fun x hx => hbox x hx k) (hL k) (hU k)
      (two_coordinates_bound K hK hbox hL hU c) (B.1 k) (B.2 k) (horder k)
      (B.1 ∘ c) (B.2 ∘ c) (fun j => horder (c j))
      (fun x hx => (Fin.exists_iff_succAbove k).mp (hcover x hx)) hb
    rw [width_apply, Fin.sum_univ_succAbove _ k] at hdef
    exact hdef.not_ge h
  exact ⟨lt_of_le_of_ne (hends k).1 (Ne.symm (not_or.mp hno).1),
    lt_of_le_of_ne (hends k).2 (not_or.mp hno).2⟩

end Plank.Convex.PlanarCoverMinimum
