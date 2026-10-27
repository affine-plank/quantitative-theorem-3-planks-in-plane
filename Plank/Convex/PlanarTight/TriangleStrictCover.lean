/- A strict normalized window covers at most one triangle vertex.
Three strict windows therefore need an interior vertex in every direction. -/
module
public import Plank.Convex.PlanarTight.AnchoredCapBody
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TriangleStrictCover

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem max_vertex (K : Set E) (hK : Convex ℝ K) (v : Fin 3 → E)
    (hbody : K = convexHull ℝ (Set.range v)) (f : E →ᵃ[ℝ] ℝ)
    (hbound : ∀ z ∈ K, f z ≤ 1) (M : E) (hM : M ∈ K) (hmax : f M = 1) :
    ∃ i, f (v i) = 1 := by
  have hf : ConvexOn ℝ K f := by
    refine ⟨hK, ?_⟩
    intro x _ y _ s t _ _ hst
    have ht : t = 1 - s := by linarith only [hst]
    rw [ht, AnchoredCorner.map_contract]
    exact le_rfl
  have hsub : Set.range v ⊆ K := by rw [hbody]; exact subset_convexHull ℝ _
  obtain ⟨_, ⟨i, rfl⟩, hle⟩ := hf.exists_ge_of_mem_convexHull hsub (by rwa [← hbody])
  exact ⟨i, le_antisymm (hbound (v i) (hsub ⟨i, rfl⟩)) (by rwa [hmax] at hle)⟩

theorem extrema_on_vertices (K : Set E) (hK : Convex ℝ K) (v : Fin 3 → E)
    (hbody : K = convexHull ℝ (Set.range v)) (f : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ z ∈ K, 0 ≤ f z ∧ f z ≤ 1)
    (hL : ∃ z ∈ K, f z = 0) (hU : ∃ z ∈ K, f z = 1) :
    (∃ i, f (v i) = 0) ∧ ∃ i, f (v i) = 1 := by
  obtain ⟨L, hL, hL₀⟩ := hL
  obtain ⟨U, hU, hU₁⟩ := hU
  refine ⟨?_, max_vertex K hK v hbody f (fun z hz => (hbox z hz).2) U hU hU₁⟩
  obtain ⟨i, hi⟩ := max_vertex K hK v hbody (TwoPlankClassification.reflect f)
    (by
      intro z hz
      change 1 - f z ≤ 1
      linarith only [(hbox z hz).1]) L hL (by simp [hL₀])
  refine ⟨i, ?_⟩
  change 1 - f (v i) = 1 at hi
  linarith only [hi]

private theorem interior_unique (v : Fin 3 → ℝ) (p q : Fin 3)
    (hp : v p = 0) (hq : v q = 1) (i j : Fin 3)
    (hi₀ : 0 < v i) (hi₁ : v i < 1) (hj₀ : 0 < v j) (hj₁ : v j < 1) : i = j := by
  have hpq : p ≠ q := by intro h; rw [h] at hp; linarith only [hp, hq]
  have hip : i ≠ p := by intro h; rw [h, hp] at hi₀; linarith only [hi₀]
  have hiq : i ≠ q := by intro h; rw [h, hq] at hi₁; linarith only [hi₁]
  have hjp : j ≠ p := by intro h; rw [h, hp] at hj₀; linarith only [hj₀]
  have hjq : j ≠ q := by intro h; rw [h, hq] at hj₁; linarith only [hj₁]
  omega

/-- If one coordinate is extremal at every triangle vertex, three
strict windows cannot cover the triangle. No width-sum hypothesis is needed. -/
theorem not_cover (K : Set E) (hK : Convex ℝ K) (v : Fin 3 → E)
    (hbody : K = convexHull ℝ (Set.range v)) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ f i z ∧ f i z ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, f i z = 0) (hU : ∀ i, ∃ z ∈ K, f i z = 1)
    (hfirst : ∀ j, f 0 (v j) = 0 ∨ f 0 (v j) = 1)
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1) :
    ¬ ∀ z ∈ K, ∃ i, lo i ≤ f i z ∧ f i z ≤ hi i := by
  classical
  intro hcover
  have hv : ∀ j, v j ∈ K := by
    intro j
    rw [hbody]
    exact subset_convexHull ℝ _ ⟨j, rfl⟩
  choose k hkl hku using (fun j : Fin 3 => hcover (v j) (hv j))
  have h₀ (j : Fin 3) : 0 < f (k j) (v j) := (hlo (k j)).trans_le (hkl j)
  have h₁ (j : Fin 3) : f (k j) (v j) < 1 := (hku j).trans_lt (hhi (k j))
  have hinj : Function.Injective k := by
    intro i j he
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := extrema_on_vertices K hK v hbody (f (k i))
      (fun z hz => hbox z hz (k i)) (hL (k i)) (hU (k i))
    exact interior_unique (fun t => f (k i) (v t)) p q hp hq i j (h₀ i) (h₁ i)
      (by rw [he]; exact h₀ j) (by rw [he]; exact h₁ j)
  obtain ⟨j, hj⟩ := (Finite.surjective_of_injective hinj) 0
  have hpos := h₀ j
  have hlt := h₁ j
  rw [hj] at hpos hlt
  rcases hfirst j with h | h <;> linarith only [h, hpos, hlt]

theorem cap_not_cover (K : Set (Fin 3 → ℝ)) (hK : Convex ℝ K)
    (T : Fin 3 → ℝ) (hcap : AnchoredCapBody.Has K (AffineMap.proj 0) T)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1) :
    ¬ ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i := by
  obtain ⟨hT₀, A, B, hA₀, hB₀, hbody⟩ := hcap
  apply not_cover K hK ![T, A, B] _ (fun i => AffineMap.proj i) hbox hL hU _ lo hi hlo hhi
  · simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union] using hbody
  · intro j
    fin_cases j
    · exact Or.inr hT₀
    · exact Or.inl hA₀
    · exact Or.inl hB₀

end Plank.Convex.PlanarTight.TriangleStrictCover

/-- info: 'Plank.Convex.PlanarTight.TriangleStrictCover.not_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TriangleStrictCover.not_cover

/-- info: 'Plank.Convex.PlanarTight.TriangleStrictCover.cap_not_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TriangleStrictCover.cap_not_cover
