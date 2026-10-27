/- Helly's argument on a hyperplane of finitely many cut values. The original
space needs no topology or dimension bound; Radon's theorem is applied only
in the finite-dimensional space of cut values. -/
module
public import Mathlib.Analysis.Convex.Radon
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace ResearchFormalized.FiniteCutHelly

/-- Omission witnesses that are affinely dependent give a common point. -/
theorem common_point_of_dependent_witnesses {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] (F : ι → Set E) (hF : ∀ i, Convex ℝ (F i))
    (p : ι → E) (hp : ∀ i j, j ≠ i → p i ∈ F j)
    (hdep : ¬ AffineIndependent ℝ p) : ∃ x, ∀ i, x ∈ F i := by
  classical
  obtain ⟨I, x, hx, hxc⟩ := _root_.Convex.radon_partition hdep
  refine ⟨x, fun i => ?_⟩
  have hsub (J : Set ι) (hi : i ∉ J) : convexHull ℝ (p '' J) ⊆ F i := by
    apply convexHull_min _ (hF i)
    rintro _ ⟨j, hj, rfl⟩
    exact hp j i (by rintro rfl; exact hi hj)
  by_cases hi : i ∈ I
  · exact hsub Iᶜ (by simpa) hxc
  · exact hsub I hi hx

/-- A nonconstant affine level set cannot contain an affine basis. -/
theorem dependent_of_level {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] (p : ι → E)
    (hcard : Fintype.card ι = Module.finrank ℝ E + 1)
    (L : E →ᵃ[ℝ] ℝ) (hL : ∃ x y, L x ≠ L y) (d : ℝ)
    (hp : ∀ i, L (p i) = d) : ¬ AffineIndependent ℝ p := by
  intro hi
  have hspan := hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr hcard
  have heq : L = AffineMap.const ℝ E d := AffineMap.ext_on hspan (by
    rintro _ ⟨i, rfl⟩
    exact hp i)
  obtain ⟨x, y, hxy⟩ := hL
  exact hxy (by rw [heq]; rfl)

variable {ι : Type*} [Fintype ι]

/-- If the strict cuts meet on the body's hyperplane in cut space, an empty
cell on the body already becomes empty after one cut is omitted. -/
theorem exists_redundant_cut (K : Set (ι → ℝ)) (hK : Convex ℝ K)
    (L : (ι → ℝ) →ᵃ[ℝ] ℝ) (hL : ∃ x y, L x ≠ L y) (d : ℝ)
    (hplane : ∀ x ∈ K, L x = d)
    (f : ι → (ι → ℝ) →ᵃ[ℝ] ℝ)
    (q : ι → ℝ) (hqL : L q = d) (hq : ∀ i, 0 < f i q)
    (he : ¬ ∃ x ∈ K, ∀ i, 0 < f i x) :
    ∃ i, ¬ ∃ x ∈ K, ∀ j, j ≠ i → 0 < f j x := by
  classical
  by_contra! hn
  choose p hpK hp using hn
  let F : Option ι → Set (ι → ℝ) := fun o => o.elim K (fun i => {x | 0 < f i x})
  let P : Option ι → (ι → ℝ) := fun o => o.elim q p
  have hF (o : Option ι) : Convex ℝ (F o) := by
    cases o with
    | none => exact hK
    | some i => exact (convex_Ioi (𝕜 := ℝ) (0 : ℝ)).affine_preimage (f i)
  have hP : ∀ i j : Option ι, j ≠ i → P i ∈ F j := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hq _
    · exact hpK _
    · exact hp _ _ (fun h => hij (congrArg some h))
  have hdep := dependent_of_level P (by simp) L hL d (fun o => by
    cases o with
    | none => exact hqL
    | some i => exact hplane _ (hpK i))
  obtain ⟨x, hx⟩ := common_point_of_dependent_witnesses F hF P hP hdep
  exact he ⟨x, hx none, fun i => hx (some i)⟩

/-- Pass to the cut values and apply Helly on their relation hyperplane. -/
theorem exists_redundant_cut_of_relation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (hK : Convex ℝ K) (f : ι → E →ᵃ[ℝ] ℝ)
    (r : ι → ℝ) (d : ℝ) (hr : ∃ i, r i ≠ 0)
    (hrel : ∀ x ∈ K, ∑ i, r i * f i x = d)
    (hq : ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∑ i, r i * q i = d)
    (he : ¬ ∃ x ∈ K, ∀ i, 0 < f i x) :
    ∃ i, ¬ ∃ x ∈ K, ∀ j, j ≠ i → 0 < f j x := by
  classical
  let G := AffineMap.pi f
  let L : (ι → ℝ) →ᵃ[ℝ] ℝ :=
    (∑ i, r i • (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).toAffineMap
  have hL (x : ι → ℝ) : L x = ∑ i, r i * x i := by
    simp [L, LinearMap.sum_apply, smul_eq_mul]
  have hnc : ∃ x y, L x ≠ L y := by
    obtain ⟨i, hi⟩ := hr
    refine ⟨Pi.single i 1, 0, ?_⟩
    simpa [hL, Pi.single_apply, mul_ite] using hi
  obtain ⟨q, hq, hqL⟩ := hq
  obtain ⟨i, hi⟩ := exists_redundant_cut (G '' K) (hK.affine_image G) L hnc d
    (by rintro _ ⟨x, hx, rfl⟩; simpa [hL, G] using hrel x hx)
    (fun i => AffineMap.proj i) q (by simpa [hL] using hqL) hq
    (by rintro ⟨_, ⟨x, hx, rfl⟩, hf⟩; exact he ⟨x, hx, hf⟩)
  refine ⟨i, ?_⟩
  rintro ⟨x, hx, hf⟩
  exact hi ⟨G x, ⟨x, hx, rfl⟩, hf⟩

private theorem positive_point_by_adjustment (r : ι → ℝ) (d : ℝ) (i : ι)
    (hri : r i ≠ 0) (ht : 0 ≤ (d - ∑ j, r j) / r i) :
    ∃ q : ι → ℝ, (∀ j, 0 < q j) ∧ ∑ j, r j * q j = d := by
  classical
  let t := (d - ∑ j, r j) / r i
  refine ⟨fun j => 1 + if j = i then t else 0, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs <;> linarith only [ht]
  · simp only [mul_add, mul_one, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    dsimp [t]
    rw [mul_div_cancel₀ _ hri]
    ring

/-- A plane with a mixed normal meets the positive orthant at every height. -/
theorem positive_point_of_mixed (r : ι → ℝ) (d : ℝ)
    (hp : ∃ i, 0 < r i) (hn : ∃ i, r i < 0) :
    ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∑ i, r i * q i = d := by
  by_cases h : (∑ i, r i) ≤ d
  · obtain ⟨i, hi⟩ := hp
    exact positive_point_by_adjustment r d i hi.ne'
      (div_nonneg (sub_nonneg.mpr h) hi.le)
  · obtain ⟨i, hi⟩ := hn
    exact positive_point_by_adjustment r d i hi.ne
      (div_nonneg_of_nonpos (sub_nonpos.mpr (le_of_not_ge h)) hi.le)

/-- A positive normal and positive height give a positive point by scaling. -/
theorem positive_point_of_positive [Nonempty ι] (r : ι → ℝ) (d : ℝ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) :
    ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∑ i, r i * q i = d := by
  have hs : 0 < ∑ i, r i := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  refine ⟨fun _ => d / ∑ i, r i, fun _ => div_pos hd hs, ?_⟩
  rw [← Finset.sum_mul, mul_div_cancel₀ _ hs.ne']

end ResearchFormalized.FiniteCutHelly
