/- Active corners of the contracted two-plank triangle force the first
coordinate to vanish on the edge opposite its unique maximum. -/
module
public import Mathlib.Analysis.Convex.Jensen
public import Plank.Convex.PlanarTight.AnchoredCorner
public import Plank.Convex.PlanarTight.CornerPropagation
public import Plank.Convex.PlanarTight.TwoPlankClassification
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.AnchoredTriangleRigidity

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem zero_on_edge (K : Set E) (hK : Convex ℝ K) (X Y Z : E →ᵃ[ℝ] ℝ)
    (T A B : E) (hT : T ∈ K) (hA : A ∈ K) (hB : B ∈ K) (hXT : X T = 1)
    (p q t r : ℝ) (hp : 0 < p) (ht : 0 < t) (ht₁ : t < 1)
    (hr : 0 < r) (hr₁ : r < 1)
    (hYA : Y A = 0) (hZA : Z A = p) (hYB : Y B = q) (hZB : Z B = 0)
    (hXA : 0 ≤ X A) (hXB : 0 ≤ X B)
    (hoff : p * Y T + q * Z T ≠ p * q)
    (hempty : ¬ ∃ z ∈ K, r < X z ∧
      Y z < r * Y T + (1 - r) * ((1 - t) * q) ∧
      Z z < r * Z T + (1 - r) * (t * p)) : X A = 0 ∧ X B = 0 := by
  have hsum : t * X A + (1 - t) * X B ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    apply hoff
    exact AnchoredCorner.on_edge K hK X Y Z T A B hT hA hB hXT p q t r hp ht ht₁ hr hr₁
      hYA hZA hYB hZB (by rw [AnchoredCorner.map_contract]; exact hpos) hempty
  have h₁ := mul_nonneg ht.le hXA
  have h₂ := mul_nonneg (sub_pos.mpr ht₁).le hXB
  refine ⟨le_antisymm ?_ hXA, le_antisymm ?_ hXB⟩
  · exact nonpos_of_mul_nonpos_right (by linarith only [hsum, h₂]) ht
  · exact nonpos_of_mul_nonpos_right (by linarith only [hsum, h₁]) (sub_pos.mpr ht₁)

/-- A contracted point on just one window face cannot lie strictly
beyond the first cut while the other window misses it. -/
theorem zero_at_window_face (K : Set E) (hK : Convex ℝ K) (X Y G : E →ᵃ[ℝ] ℝ)
    (T B : E) (hT : T ∈ K) (hB : B ∈ K) (hXT : X T = 1)
    (hXB : 0 ≤ X B) (hYT : 0 < Y T) (hYB : Y B = 0)
    (r : ℝ) (hr : 0 < r) (hr₁ : r < 1)
    (hgap : 0 < G (r • T + (1 - r) • B))
    (hempty : ¬ ∃ z ∈ K, r < X z ∧ Y z < r * Y T ∧ 0 < G z) : X B = 0 := by
  apply le_antisymm _ hXB
  apply le_of_not_gt
  intro hpos
  let cuts : Fin 3 → E →ᵃ[ℝ] ℝ := ![
    X - AffineMap.const ℝ E r,
    AffineMap.const ℝ E (r * Y T) - Y,
    G]
  have hs := CornerPropagation.support K hK cuts (r • T + (1 - r) • B)
    (hK hT hB hr.le (sub_pos.mpr hr₁).le (by ring))
    (by
      change 0 < X (r • T + (1 - r) • B) - r
      rw [AnchoredCorner.map_contract, hXT]
      nlinarith only [mul_pos (sub_pos.mpr hr₁) hpos])
    (by
      change r * Y T - Y (r • T + (1 - r) • B) = 0
      rw [AnchoredCorner.map_contract, hYB]
      ring) hgap (by
        rintro ⟨z, hz, hc⟩
        exact hempty ⟨z, hz, sub_pos.mp (hc 0), sub_pos.mp (hc 1), hc 2⟩) B hB
  change r * Y T - Y B ≤ 0 at hs
  rw [hYB] at hs
  have hpositive := mul_pos hr hYT
  linarith only [hs, hpositive]

/-- The unique maximum of an affine coordinate on a triangle is one
of its three vertices. -/
theorem maximizer_is_vertex (K : Set E) (hK : Convex ℝ K) (X : E →ᵃ[ℝ] ℝ)
    (A B C : E) (hbody : K = convexHull ℝ {A, B, C})
    (hbox : ∀ z ∈ K, X z ≤ 1) (hface : {z | z ∈ K ∧ X z = 1}.Subsingleton)
    (T : E) (hT : T ∈ K) (hXT : X T = 1) : T = A ∨ T = B ∨ T = C := by
  have hf : ConvexOn ℝ K X := by
    refine ⟨hK, ?_⟩
    intro x _ y _ s t _ _ hst
    have ht : t = 1 - s := by linarith only [hst]
    rw [ht, AnchoredCorner.map_contract]
    exact le_rfl
  have hsub : {A, B, C} ⊆ K := by
    rw [hbody]
    exact subset_convexHull ℝ _
  obtain ⟨W, hW, hle⟩ := hf.exists_ge_of_mem_convexHull hsub (by rwa [← hbody])
  have hW₁ : X W = 1 := le_antisymm (hbox W (hsub hW)) (by rwa [hXT] at hle)
  have he : T = W := hface ⟨hT, hXT⟩ ⟨hsub hW, hW₁⟩
  rw [← he] at hW
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hW

/-- At any of the three vertices of an interior two-plank triangular
enclosure, the original equality cover forces the other two vertices
onto the zero face of its anchored coordinate. -/
theorem other_vertices_zero (K : Set E) (hK : Convex ℝ K) (X Y Z : E →ᵃ[ℝ] ℝ)
    (T A B C : E) (hT : T ∈ K) (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K)
    (hXT : X T = 1) (hX : ∀ z ∈ K, 0 ≤ X z)
    (c g r : ℝ) (hc : 0 < c) (hc₁ : c < 1) (hg : 0 < g) (hg₁ : g < 1)
    (hr : 0 < r) (hr₁ : r < 1)
    (hYA : Y A = 0) (hZA : Z A = 0) (hYB : Y B = 0) (hZB : Z B = 1)
    (hYC : Y C = 1) (hZC : Z C = c)
    (hwhere : T = A ∨ T = B ∨ T = C)
    (hcover : ∀ z ∈ K, X z ≤ r ∨
      (r * Y T ≤ Y z ∧ Y z ≤ r * Y T + (1 - r) * g) ∨
      (r * Z T + (1 - r) * (g * c) ≤ Z z ∧
        Z z ≤ r * Z T + (1 - r) * (1 - g + g * c))) :
    (T = A ∧ X B = 0 ∧ X C = 0) ∨ (T = B ∧ X A = 0 ∧ X C = 0) ∨
      (T = C ∧ X A = 0 ∧ X B = 0) := by
  rcases hwhere with hwhere | hwhere | hwhere
  · subst T
    refine Or.inl ⟨rfl, ?_⟩
    have hz := zero_on_edge K hK X (TwoPlankClassification.reflect Y)
      (TwoPlankClassification.reflect Z) A C B hT hC hB hXT
      (1 - c) 1 g r (sub_pos.mpr hc₁) hg hg₁ hr hr₁
      (by simp [hYC]) (by simp [hZC]) (by simp [hYB]) (by simp [hZB])
      (hX C hC) (hX B hB) (by
        change (1 - c) * (1 - Y A) + 1 * (1 - Z A) ≠ (1 - c) * 1
        rw [hYA, hZA]
        intro he
        linarith only [he]) (by
        rintro ⟨z, hz, hx, hy, hzz⟩
        change 1 - Y z < r * (1 - Y A) + (1 - r) * ((1 - g) * 1) at hy
        change 1 - Z z < r * (1 - Z A) + (1 - r) * (g * (1 - c)) at hzz
        rcases hcover z hz with h | h | h
        · exact not_le_of_gt hx h
        · nlinarith only [hy, h.2]
        · nlinarith only [hzz, h.2])
    exact hz.symm
  · subst T
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    have hz := zero_on_edge K hK X (TwoPlankClassification.reflect Y) Z
      B C A hT hC hA hXT c 1 g r hc hg hg₁ hr hr₁
      (by simp [hYC]) hZC (by simp [hYA]) hZA
      (hX C hC) (hX A hA) (by
        change c * (1 - Y B) + 1 * Z B ≠ c * 1
        rw [hYB, hZB]
        intro he
        linarith only [he]) (by
        rintro ⟨z, hz, hx, hy, hzz⟩
        change 1 - Y z < r * (1 - Y B) + (1 - r) * ((1 - g) * 1) at hy
        rcases hcover z hz with h | h | h
        · exact not_le_of_gt hx h
        · nlinarith only [hy, h.2]
        · exact not_lt_of_ge h.1 hzz)
    exact hz.symm
  · subst T
    refine Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)
    · apply zero_at_window_face K hK X Y
        (AffineMap.const ℝ E (r * Z C + (1 - r) * (g * c)) - Z)
        C A hT hA hXT (hX A hA) (by rw [hYC]; exact zero_lt_one) hYA r hr hr₁
      · change 0 < r * Z C + (1 - r) * (g * c) - Z (r • C + (1 - r) • A)
        rw [AnchoredCorner.map_contract, hZA]
        nlinarith only [mul_pos (sub_pos.mpr hr₁) (mul_pos hg hc)]
      · rintro ⟨z, hz, hx, hy, hgap⟩
        change 0 < r * Z C + (1 - r) * (g * c) - Z z at hgap
        rcases hcover z hz with h | h | h
        · exact not_le_of_gt hx h
        · exact not_lt_of_ge h.1 hy
        · linarith only [hgap, h.1]
    · apply zero_at_window_face K hK X Y
        (Z - AffineMap.const ℝ E (r * Z C + (1 - r) * (1 - g + g * c)))
        C B hT hB hXT (hX B hB) (by rw [hYC]; exact zero_lt_one) hYB r hr hr₁
      · change 0 < Z (r • C + (1 - r) • B) -
          (r * Z C + (1 - r) * (1 - g + g * c))
        rw [AnchoredCorner.map_contract, hZB]
        nlinarith only [mul_pos (sub_pos.mpr hr₁) (mul_pos hg (sub_pos.mpr hc₁))]
      · rintro ⟨z, hz, hx, hy, hgap⟩
        change 0 < Z z - (r * Z C + (1 - r) * (1 - g + g * c)) at hgap
        rcases hcover z hz with h | h | h
        · exact not_le_of_gt hx h
        · exact not_lt_of_ge h.1 hy
        · linarith only [hgap, h.2]

end Plank.Convex.PlanarTight.AnchoredTriangleRigidity

/-- info: 'Plank.Convex.PlanarTight.AnchoredTriangleRigidity.zero_on_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredTriangleRigidity.zero_on_edge

/-- info: 'Plank.Convex.PlanarTight.AnchoredTriangleRigidity.zero_at_window_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredTriangleRigidity.zero_at_window_face

/-- info: 'Plank.Convex.PlanarTight.AnchoredTriangleRigidity.maximizer_is_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredTriangleRigidity.maximizer_is_vertex

/-- info: 'Plank.Convex.PlanarTight.AnchoredTriangleRigidity.other_vertices_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredTriangleRigidity.other_vertices_zero
