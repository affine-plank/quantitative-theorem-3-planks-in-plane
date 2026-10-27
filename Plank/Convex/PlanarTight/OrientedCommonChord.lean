/- The common-extremal-segment family with arbitrary original
orientations of the three plank coordinates. -/
module
public import Plank.Convex.AffineWindowOrientation
public import Plank.Convex.PlanarTight.CommonChordClassification
public import Plank.Convex.PlanarTight.OppositeVertices
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.OrientedCommonChord

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- After independent coordinate reflections and a permutation, the
windows are `[0,r]`, `[r,s]`, `[s,1]`, with the corresponding affine
coordinates ordered throughout the body. -/
def Normal (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ) : Prop :=
  ∃ flip : Fin 3 → Bool, CommonChordClassification.Normal K (coordinates flip f)
    (lower flip lo hi) (upper flip lo hi)

private theorem tight_of_normal (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ f i z ∧ f i z ≤ 1)
    (lo hi : Fin 3 → ℝ) (h : CommonChordClassification.Normal K f lo hi) :
    (∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ f i z ∧ f i z ≤ hi i := by
  obtain ⟨σ, r, s, _, _, _, hl0, hu0, hl1, hu1, hl2, hu2, hord⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← Equiv.sum_comp σ (fun i => hi i - lo i), Fin.sum_univ_three]
    rw [hl0, hu0, hl1, hu1, hl2, hu2]
    ring
  · intro z hz
    by_cases h₀ : f (σ 0) z ≤ r
    · exact ⟨σ 0, by rw [hl0, hu0]; exact ⟨(hbox z hz _).1, h₀⟩⟩
    by_cases h₁ : f (σ 1) z ≤ s
    · refine ⟨σ 1, ?_⟩
      rw [hl1, hu1]
      exact ⟨(le_of_not_ge h₀).trans (hord z hz).1, h₁⟩
    · refine ⟨σ 2, ?_⟩
      rw [hl2, hu2]
      exact ⟨(le_of_not_ge h₁).trans (hord z hz).2, (hbox z hz _).2⟩

/-- The displayed family always gives a tight cover of its stated body
enclosure; a common extremal segment is only needed for necessity. -/
theorem Normal.tight (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ f i z ∧ f i z ≤ 1)
    (lo hi : Fin 3 → ℝ) (h : Normal K f lo hi) :
    (∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ f i z ∧ f i z ≤ hi i := by
  obtain ⟨flip, hn⟩ := h
  obtain ⟨hsum, hcover⟩ := tight_of_normal K (coordinates flip f)
    (fun z hz i => box flip f z i (hbox z hz i)) (lower flip lo hi) (upper flip lo hi) hn
  refine ⟨?_, ?_⟩
  · simpa only [width_eq] using hsum
  · intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    exact ⟨i, (window_iff flip f lo _ z i).mp hi⟩

/-- Full equality classification for any three normalized coordinates
whose extrema occur at a common pair of points, in either orientation. -/
theorem tight_iff (K : Set E) (hK : Convex ℝ K) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (A B : E) (hA : A ∈ K) (hB : B ∈ K)
    (hvertex : ∀ i, f i A = 0 ∨ f i A = 1) (hopposite : ∀ i, f i B = 1 - f i A)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ f i z ∧ f i z ≤ 1)
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hwidth : ∀ i, lo i < hi i) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ f i z ∧ f i z ≤ hi i) ↔
      Normal K f lo hi := by
  classical
  constructor
  · rintro ⟨hsum, hcover⟩
    let flip : Fin 3 → Bool := fun i => decide (f i A = 1)
    have hmin (i : Fin 3) : coordinates flip f i A = 0 := by
      rcases hvertex i with h | h <;> simp [coordinates, flip, h]
    have hmax (i : Fin 3) : coordinates flip f i B = 1 := by
      rcases hvertex i with h | h <;> simp [coordinates, flip, h, hopposite]
    have hlo' (i : Fin 3) : 0 ≤ lower flip lo hi i := by
      cases he : flip i <;> simp only [lower, he, ↓reduceIte]
      · exact hlo i
      · exact sub_nonneg.mpr (hhi i)
    have hhi' (i : Fin 3) : upper flip lo hi i ≤ 1 := by
      cases he : flip i <;> simp only [upper, he, ↓reduceIte]
      · exact hhi i
      · linarith only [hlo i]
    have hwidth' (i : Fin 3) : lower flip lo hi i < upper flip lo hi i := by
      apply sub_pos.mp
      rw [width_eq]
      exact sub_pos.mpr (hwidth i)
    refine ⟨flip, (CommonChordClassification.tight_iff K hK (coordinates flip f) A B hA hB
      hmin hmax (fun z hz i => box flip f z i (hbox z hz i))
      (lower flip lo hi) (upper flip lo hi) hlo' hhi' hwidth').mp ⟨?_, ?_⟩⟩
    · simpa only [width_eq] using hsum
    · intro z hz
      obtain ⟨i, hi⟩ := hcover z hz
      exact ⟨i, (window_iff flip f lo _ z i).mpr hi⟩
  · exact Normal.tight K f hbox lo hi

theorem tight_iff_of_opposite_vertices (K : Set (Fin 3 → ℝ)) (hK : Convex ℝ K)
    (hvertices : OppositeVertices.Has K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hwidth : ∀ i, lo i < hi i) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i) ↔
      Normal K (fun i => AffineMap.proj i) lo hi := by
  obtain ⟨A, hA, B, hB, hv, ho⟩ := hvertices
  exact tight_iff K hK (fun i => AffineMap.proj i) A B hA hB hv ho hbox lo hi hlo hhi hwidth

end Plank.Convex.PlanarTight.OrientedCommonChord

/-- info: 'Plank.Convex.PlanarTight.OrientedCommonChord.Normal.tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.OrientedCommonChord.Normal.tight

/-- info: 'Plank.Convex.PlanarTight.OrientedCommonChord.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.OrientedCommonChord.tight_iff

/-- info: 'Plank.Convex.PlanarTight.OrientedCommonChord.tight_iff_of_opposite_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.OrientedCommonChord.tight_iff_of_opposite_vertices
