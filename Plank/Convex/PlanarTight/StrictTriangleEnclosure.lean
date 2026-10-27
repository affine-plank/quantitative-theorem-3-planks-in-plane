/- A strictly covered triangle cannot properly enclose a convex body
with all of the same directional ranges. -/
module
public import Plank.Convex.PlanarTight.TriangleStrictCover
public import Plank.Convex.PlanarTight.CyclicTriangle
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.StrictTriangleEnclosure

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem unique_maximum {ι : Type*} (v : ι → E) (f : E →ᵃ[ℝ] ℝ) (i : ι)
    (hmax : f (v i) = 1) (hother : ∀ j, j ≠ i → f (v j) < 1)
    (M : E) (hM : M ∈ convexHull ℝ (Set.range v)) (hM₁ : f M = 1) : M = v i := by
  have hconv : Convex ℝ {x | x = v i ∨ f x < 1} := by
    intro x hx y hy a b ha hb hab
    by_cases ha₀ : a = 0
    · have hb₁ : b = 1 := by linarith only [hab, ha₀]
      simpa only [ha₀, hb₁, zero_smul, one_smul, zero_add] using hy
    by_cases hb₀ : b = 0
    · have ha₁ : a = 1 := by linarith only [hab, hb₀]
      simpa only [ha₁, hb₀, zero_smul, one_smul, add_zero] using hx
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha₀)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb₀)
    have he : f (a • x + b • y) = a * f x + b * f y := by
      have hb₁ : b = 1 - a := by linarith only [hab]
      rw [hb₁, AnchoredCorner.map_contract]
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · left
      rw [hx, hy, ← add_smul, hab, one_smul]
    · right
      rw [he, hx, hmax]
      have h := mul_lt_mul_of_pos_left hy hb'
      nlinarith only [h, hab]
    · right
      rw [he, hy, hmax]
      have h := mul_lt_mul_of_pos_left hx ha'
      nlinarith only [h, hab]
    · right
      rw [he]
      have h₁ := mul_lt_mul_of_pos_left hx ha'
      have h₂ := mul_lt_mul_of_pos_left hy hb'
      nlinarith only [h₁, h₂, hab]
  have hsub : convexHull ℝ (Set.range v) ⊆ {x | x = v i ∨ f x < 1} := by
    apply convexHull_min _ hconv
    rintro _ ⟨j, rfl⟩
    by_cases he : j = i
    · exact Or.inl (congrArg v he)
    · exact Or.inr (hother j he)
  exact (hsub hM).resolve_right (by rw [hM₁]; exact lt_irrefl 1)

theorem eq_triangle (K : Set E) (hK : Convex ℝ K) (v : Fin 3 → E)
    (hsub : K ⊆ convexHull ℝ (Set.range v)) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hbox : ∀ z ∈ convexHull ℝ (Set.range v), ∀ i, 0 ≤ f i z ∧ f i z ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, f i z = 0) (hU : ∀ i, ∃ z ∈ K, f i z = 1)
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hcover : ∀ z ∈ convexHull ℝ (Set.range v), ∃ i, lo i ≤ f i z ∧ f i z ≤ hi i) :
    K = convexHull ℝ (Set.range v) := by
  apply Set.Subset.antisymm hsub
  apply convexHull_min _ hK
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hji⟩ := exists_ne i
  have hjmem : v j ∈ convexHull ℝ (Set.range v) := subset_convexHull ℝ _ ⟨j, rfl⟩
  obtain ⟨a, hja₀, hja₁⟩ := hcover (v j) hjmem
  have hj₀ : 0 < f a (v j) := (hlo a).trans_le hja₀
  have hj₁ : f a (v j) < 1 := hja₁.trans_lt (hhi a)
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := TriangleStrictCover.extrema_on_vertices
    (convexHull ℝ (Set.range v)) (convex_convexHull ℝ _) v rfl (f a)
    (fun z hz => hbox z hz a)
    (by obtain ⟨z, hz, he⟩ := hL a; exact ⟨z, hsub hz, he⟩)
    (by obtain ⟨z, hz, he⟩ := hU a; exact ⟨z, hsub hz, he⟩)
  have hpq : p ≠ q := by intro he; rw [he] at hp; linarith only [hp, hq]
  have hjp : j ≠ p := by intro he; rw [he, hp] at hj₀; linarith only [hj₀]
  have hjq : j ≠ q := by intro he; rw [he, hq] at hj₁; linarith only [hj₁]
  have hipq : i = p ∨ i = q := by omega
  rcases hipq with he | he
  · have hfi : f a (v i) = 0 := by rw [he]; exact hp
    have hother : ∀ k, k ≠ i → 0 < f a (v k) := by
      intro k hki
      have hk : k = q ∨ k = j := by omega
      rcases hk with rfl | rfl
      · rw [hq]
        exact zero_lt_one
      · exact hj₀
    obtain ⟨L, hLK, hL₀⟩ := hL a
    have hLeq := unique_maximum v (TwoPlankClassification.reflect (f a)) i
      (by simp [hfi]) (by
        intro k hki
        change 1 - f a (v k) < 1
        linarith only [hother k hki]) L (hsub hLK) (by simp [hL₀])
    exact hLeq ▸ hLK
  · have hfi : f a (v i) = 1 := by rw [he]; exact hq
    have hother : ∀ k, k ≠ i → f a (v k) < 1 := by
      intro k hki
      have hk : k = p ∨ k = j := by omega
      rcases hk with rfl | rfl
      · rw [hp]
        exact zero_lt_one
      · exact hj₁
    obtain ⟨U, hUK, hU₁⟩ := hU a
    have hUeq := unique_maximum v (f a) i hfi hother U (hsub hUK) hU₁
    exact hUeq ▸ hUK

/-- The cyclic mixed-cap equality case has an exact triangle body;
the enclosing triangle from the cap construction cannot be larger than K. -/
theorem cyclic_eq_triangle [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a : Fin 3 → ℝ) (d : ℝ)
    (ha : ∀ i, 0 < a i) (hplane : ∀ x, ∑ i, a i * f i x = d)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (lo hi : Fin 3 → ℝ) (hwidth : ∀ i, lo i < hi i)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (hcaps : ∀ i, ¬ ∃ x ∈ K, hi i < f i x ∧
      f (CyclicCapTriangle.next i) x < lo (CyclicCapTriangle.next i)) :
    ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v) := by
  obtain ⟨v, hv, hsub, hbox', hcover'⟩ := CyclicTriangle.enclosing_triangle_of_tight
    hdim K hK f a d ha hplane hinj hbox hL hU lo hi hwidth hlo hhi hcover hsum hcaps
  exact ⟨v, hv, eq_triangle K hK v hsub f hbox' hL hU lo hi hlo hhi hcover'⟩

end Plank.Convex.PlanarTight.StrictTriangleEnclosure

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleEnclosure.unique_maximum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleEnclosure.unique_maximum

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleEnclosure.eq_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleEnclosure.eq_triangle

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleEnclosure.cyclic_eq_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleEnclosure.cyclic_eq_triangle
