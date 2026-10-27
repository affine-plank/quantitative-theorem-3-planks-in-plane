/-
# Three slabs with one parallel unit chord

A convex set with unit contacts in its first two coordinates and a unit
chord constant in those coordinates satisfies the three-slab width bound.
The coordinates are arbitrary continuous linear maps on a real normed
space. Only a finite contact hull is compact; the original set need not be.
-/
module

public import Plank.Convex.TwoCoreChordPlanks
public import Plank.Convex.TwoCapChordPlanks

@[expose] public section
noncomputable section

namespace Plank.Convex.ThreePlankParallelChord
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two unit coordinate gaps force the two-slab bound, even if the convex
set is unbounded. Apply the compact theorem to the four contact witnesses. -/
theorem two_coordinate_width_bound (K : Set E) (hK : Convex ℝ K)
    (f : Fin 2 → E →L[ℝ] ℝ)
    (hcontacts : ∀ (j : Fin 2) (side : Bool),
      ∃ x ∈ K, f j x = if side then 1 else 0)
    (lo hi : Fin 2 → ℝ) (hle : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) :
    1 ≤ ∑ j, (hi j - lo j) := by
  classical
  choose p hp hvalue using hcontacts
  let v : (Fin 2 × Bool) → E := fun q => p q.1 q.2
  let C : Set E := convexHull ℝ (Set.range v)
  have hC : Convex ℝ C := convex_convexHull ℝ _
  have hcompact : IsCompact C := (Set.finite_range v).isCompact_convexHull ℝ
  have hCK : C ⊆ K := by
    apply convexHull_min ?_ hK
    rintro _ ⟨q, rfl⟩
    exact hp q.1 q.2
  have hmem (j : Fin 2) (side : Bool) : p j side ∈ C :=
    subset_convexHull ℝ _ ⟨(j, side), rfl⟩
  have htwo := TwoCapChordPlanks.two_plank_chord_bound hC hcompact
    (f 0) (f 1) (lo 0) (lo 1) (hi 0 - lo 0) (hi 1 - lo 1) 1 1
    (sub_nonneg.mpr (hle 0)) (sub_nonneg.mpr (hle 1)) zero_lt_one zero_lt_one
    (hmem 0 false) (hmem 0 true) (hmem 1 false) (hmem 1 true)
    (by rw [hvalue 0 true, hvalue 0 false]; norm_num)
    (by rw [hvalue 1 true, hvalue 1 false]; norm_num)
    (by
      intro x hx
      obtain ⟨j, hjlo, hjhi⟩ := hcover x (hCK hx)
      fin_cases j
      · change (f 0) x ≤ hi 0 at hjhi
        exact Or.inl ⟨hjlo, by linarith only [hjhi]⟩
      · change (f 1) x ≤ hi 1 at hjhi
        exact Or.inr ⟨hjlo, by linarith only [hjhi]⟩)
  simpa only [div_one, Fin.sum_univ_two] using htwo

/-- Three ordered slabs covering a convex set have total coordinate width
at least one if the last unit chord is constant in the first two coordinates.
No transverse bounds, closedness, compactness, or finite dimension is assumed. -/
theorem width_bound (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →L[ℝ] ℝ)
    (hcontacts : ∀ (j : Fin 2) (side : Bool),
      ∃ x ∈ K, f j.castSucc x = if side then 1 else 0)
    (U V : E) (hU : U ∈ K) (hV : V ∈ K)
    (hU0 : f 2 U = 0) (hV1 : f 2 V = 1)
    (hparallel : ∀ j : Fin 3, j ≠ 2 → f j U = f j V)
    (lo hi : Fin 3 → ℝ) (hle : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) :
    1 ≤ ∑ j, (hi j - lo j) := by
  apply sum_ge_one_of_last_parallel_chord (n := 2) K hK
    (fun j => (f j).toLinearMap.toAffineMap) U V hU hV hU0 hV1 ?_ ?_ lo hi hle hcover
  · intro j
    exact hparallel j.castSucc (ne_of_lt (Fin.castSucc_lt_last j))
  · intro low high hlecore hcovercore
    exact two_coordinate_width_bound K hK (fun j => f j.castSucc) hcontacts
      low high hlecore hcovercore

end Plank.Convex.ThreePlankParallelChord
