/- Every zero objective coefficient reduces to a positive anchored equality cover. -/
module
public import Plank.Convex.SameSignFlatAnchor
public import Plank.Convex.SameSignWallSymmetry
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace Plank.Convex.SameSignFlatAnchorSymmetry
open SameSignCapMinimum SameSignWallSymmetry

theorem upper_zero_anchor (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls) (hsum : width B = 1)
    (r : Index → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B)
    (i : Fin 3) (hn : SameSignLocalMinimum.numerator r (true, i) = 0) :
    ∃ C ∈ wallSet K, C.1 = B.1 ∧ width C = 1 ∧
      (∀ j, C.1 j < C.2 j) ∧ ∃ j, C.2 j = 1 := by
  let σ := rotation i
  have hσ (j : Fin 3) : σ (next j) = next (σ j) := rotation_next i j
  have hσ₀ : σ 0 = i := rotation_zero i
  have hbox' : ∀ x ∈ permute σ '' K, ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
    rintro x ⟨y, hy, rfl⟩ j
    exact hbox y hy (σ j)
  have hL' : ∀ j, ∃ x ∈ permute σ '' K, x j = 0 := by
    intro j
    obtain ⟨x, hx, he⟩ := hL (σ j)
    exact ⟨permute σ x, ⟨x, hx, rfl⟩, he⟩
  have hU' : ∀ j, ∃ x ∈ permute σ '' K, x j = 1 := by
    intro j
    obtain ⟨x, hx, he⟩ := hU (σ j)
    exact ⟨permute σ x, ⟨x, hx, rfl⟩, he⟩
  have hp' : ∀ x ∈ permute σ '' K, ∑ j, A (σ j) * x j = D := by
    rintro x ⟨y, hy, rfl⟩
    simpa only [permute_apply, Equiv.sum_comp σ (fun j => A j * y j)] using hplane y hy
  have hn' : SameSignLocalMinimum.numerator (slopes σ r) (true, 0) = 0 := by
    rw [numerator_permute σ hσ, hσ₀]
    exact hn
  obtain ⟨C', hC', hlo', hsum', hw', j, hj⟩ := SameSignFlatAnchor.upper_zero_anchor
    (permute σ '' K) (Convex.affine_image (permute σ) hK) hbox' hL' hU'
    (fun j => A (σ j)) D (fun j => hA (σ j)) hp'
    (walls σ B) (wallSet_permute σ hσ K B hB) (strict_permute σ B hstrict)
    (by rw [width_walls]; exact hsum) (slopes σ r)
    (fun j => hr (j.1, σ j.2)) (supports_permute σ hσ K B r hs) hn'
  let C := walls σ.symm C'
  have hC : C ∈ wallSet K := by
    have h := wallSet_permute σ.symm (symm_next σ hσ) (permute σ '' K) C' hC'
    simpa only [image_symm] using h
  refine ⟨C, hC, ?_, ?_, ?_, σ j, ?_⟩
  · change permute σ.symm C'.1 = B.1
    rw [hlo']
    exact permute_symm σ _
  · change width (walls σ.symm C') = 1
    rw [width_walls]
    exact hsum'
  · intro k
    exact hw' (σ.symm k)
  · change C'.2 (σ.symm (σ j)) = 1
    simpa only [σ.symm_apply_apply] using hj

theorem lower_zero_anchor (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls) (hsum : width B = 1)
    (r : Index → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B)
    (i : Fin 3) (hn : SameSignLocalMinimum.numerator r (false, i) = 0) :
    ∃ C ∈ wallSet K, C.2 = B.2 ∧ width C = 1 ∧
      (∀ j, C.1 j < C.2 j) ∧ ∃ j, C.1 j = 0 := by
  have hbox' : ∀ x ∈ reflect '' K, ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
    rintro x ⟨y, hy, rfl⟩ j
    change 0 ≤ 1 - y j ∧ 1 - y j ≤ 1
    exact ⟨sub_nonneg.mpr (hbox y hy j).2, by linarith only [(hbox y hy j).1]⟩
  have hL' : ∀ j, ∃ x ∈ reflect '' K, x j = 0 := by
    intro j
    obtain ⟨x, hx, he⟩ := hU j
    exact ⟨reflect x, ⟨x, hx, rfl⟩, by rw [reflect_apply, he, sub_self]⟩
  have hU' : ∀ j, ∃ x ∈ reflect '' K, x j = 1 := by
    intro j
    obtain ⟨x, hx, he⟩ := hL j
    exact ⟨reflect x, ⟨x, hx, rfl⟩, by rw [reflect_apply, he, sub_zero]⟩
  have hp' : ∀ x ∈ reflect '' K, ∑ j, A j * x j = (∑ j, A j) - D := by
    rintro x ⟨y, hy, rfl⟩
    simp only [reflect_apply, mul_sub, mul_one, Finset.sum_sub_distrib, hplane y hy]
  have hn' : SameSignLocalMinimum.numerator (reflectedSlopes r) (true, i) = 0 := by
    simpa only [numerator_reflect, Bool.not_true] using hn
  obtain ⟨C', hC', hlo', hsum', hw', j, hj⟩ := upper_zero_anchor
    (reflect '' K) (Convex.affine_image reflect hK) hbox' hL' hU'
    A ((∑ j, A j) - D) hA hp' (reflectedWalls B) (wallSet_reflect K B hB)
    (strict_reflect B hstrict) (by rw [width_reflected]; exact hsum)
    (reflectedSlopes r) (fun j => hr (!j.1, j.2)) (supports_reflect K B r hs) i hn'
  let C := reflectedWalls C'
  have hC : C ∈ wallSet K := by
    have h := wallSet_reflect (reflect '' K) C' hC'
    simpa only [image_reflect] using h
  refine ⟨C, hC, ?_, ?_, ?_, j, ?_⟩
  · change reflect C'.1 = B.2
    rw [hlo']
    exact reflect_reflect _
  · change width (reflectedWalls C') = 1
    rw [width_reflected]
    exact hsum'
  · intro k
    exact sub_lt_sub_left (hw' k) 1
  · change 1 - C'.2 j = 0
    rw [hj, sub_self]

/-- Any zero objective coefficient supplies a positive equality cover anchored at a coordinate extreme. -/
theorem zero_anchor (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls) (hsum : width B = 1)
    (r : Index → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B)
    (j : Index) (hn : SameSignLocalMinimum.numerator r j = 0) :
    ∃ C ∈ wallSet K, width C = 1 ∧ (∀ i, C.1 i < C.2 i) ∧
      ∃ i, C.1 i = 0 ∨ C.2 i = 1 := by
  rcases j with ⟨s, j⟩
  cases s
  · obtain ⟨C, hC, _, hw, hp, i, hi⟩ := lower_zero_anchor K hK hbox hL hU A D hA hplane
      B hB hstrict hsum r hr hs j hn
    exact ⟨C, hC, hw, hp, i, Or.inl hi⟩
  · obtain ⟨C, hC, _, hw, hp, i, hi⟩ := upper_zero_anchor K hK hbox hL hU A D hA hplane
      B hB hstrict hsum r hr hs j hn
    exact ⟨C, hC, hw, hp, i, Or.inr hi⟩

/-- The original interior equality minimum either has all six contacts, or the same body
has a positive anchored equality cover. Zero-width minimizing boxes are never used. -/
theorem contacts_or_positive_anchor (K : Set Point) (hcK : IsCompact K) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls)
    (hmin : IsMinOn width (wallSet K) B) (hsum : width B = 1)
    (r : Index → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B) :
    (∀ j, ∃ x ∈ K, cut j x = wall B j ∧ cut (succ j) x = wall B (succ j)) ∨
    ∃ C ∈ wallSet K, width C = 1 ∧ (∀ i, C.1 i < C.2 i) ∧
      ∃ i, C.1 i = 0 ∨ C.2 i = 1 := by
  by_cases hp : ∀ j, 0 < SameSignLocalMinimum.numerator r j
  · exact Or.inl fun j => SameSignLocalMinimum.contact_of_numerator_pos
      K hcK hK B hmin hstrict hL hU r hr hs j (hp j)
  · push Not at hp
    obtain ⟨j, hj⟩ := hp
    have hn := SameSignLocalMinimum.numerator_nonneg_of_minimum K B hmin hstrict r hr hs j
    exact Or.inr (zero_anchor K hK hbox hL hU A D hA hplane B hB hstrict hsum r hr hs j
      (le_antisymm hj hn))

end Plank.Convex.SameSignFlatAnchorSymmetry

/-- info: 'Plank.Convex.SameSignFlatAnchorSymmetry.zero_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignFlatAnchorSymmetry.zero_anchor

/-- info: 'Plank.Convex.SameSignFlatAnchorSymmetry.contacts_or_positive_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignFlatAnchorSymmetry.contacts_or_positive_anchor
