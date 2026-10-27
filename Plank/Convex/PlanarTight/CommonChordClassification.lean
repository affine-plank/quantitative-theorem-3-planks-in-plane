/- An explicit equality family when all oriented plank coordinates
share a minimum point and a maximum point. The planks partition that
segment and their coordinates are ordered throughout the body. -/
module
public import Plank.Convex.PlanarTight.ParallelClassification
public import Plank.Convex.PlanarTight.AnchoredCorner
public import Plank.Convex.PlanarTight.TwoPlankClassification
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.CommonChordClassification

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- At a point inside the common extremal segment, a missing three-cut
cell forces the two adjacent coordinates to be ordered on all of K. -/
theorem order_of_missing_corner (K : Set E) (hK : Convex ℝ K)
    (X Y Z : E →ᵃ[ℝ] ℝ) (A B : E) (hA : A ∈ K) (hB : B ∈ K)
    (hXA : X A = 0) (hYA : Y A = 0) (hZA : Z A = 0)
    (hXB : X B = 1) (hYB : Y B = 1) (hZB : Z B = 1)
    (t s : ℝ) (ht : 0 < t) (ht₁ : t < 1) (hts : t < s)
    (hempty : ¬ ∃ z ∈ K, t < X z ∧ Y z < t ∧ Z z < s) :
    ∀ z ∈ K, X z ≤ Y z := by
  let cuts : Fin 3 → E →ᵃ[ℝ] ℝ := ![
    X - AffineMap.const ℝ E t,
    AffineMap.const ℝ E t - Y,
    AffineMap.const ℝ E s - Z]
  obtain ⟨m, hm, hsum, hrows⟩ := ConvexCellSeparation.exists_weights K hK cuts (by
    rintro ⟨z, hz, hc⟩
    exact hempty ⟨z, hz, sub_pos.mp (hc 0), sub_pos.mp (hc 1), sub_pos.mp (hc 2)⟩)
  have hrow (z : E) (hz : z ∈ K) :
      m 0 * (X z - t) + m 1 * (t - Y z) + m 2 * (s - Z z) ≤ 0 := by
    simpa [Fin.sum_univ_three, cuts, AffineMap.coe_sub] using hrows z hz
  let Q := t • B + (1 - t) • A
  have hQ : Q ∈ K := hK hB hA ht.le (sub_pos.mpr ht₁).le (by ring)
  have hXQ : X Q = t := by rw [AnchoredCorner.map_contract, hXB, hXA]; ring
  have hYQ : Y Q = t := by rw [AnchoredCorner.map_contract, hYB, hYA]; ring
  have hZQ : Z Q = t := by rw [AnchoredCorner.map_contract, hZB, hZA]; ring
  have hq := hrow Q hQ
  rw [hXQ, hYQ, hZQ] at hq
  have hprod : m 2 * (s - t) ≤ 0 := by simpa only [sub_self, mul_zero, zero_add] using hq
  have hm₂ : m 2 = 0 := le_antisymm
    (nonpos_of_mul_nonpos_left hprod (sub_pos.mpr hts)) (hm 2)
  have hrow' (z : E) (hz : z ∈ K) :
      m 0 * (X z - t) + m 1 * (t - Y z) ≤ 0 := by
    simpa only [hm₂, zero_mul, add_zero] using hrow z hz
  have h₀ := hrow' A hA
  have h₁ := hrow' B hB
  rw [hXA, hYA] at h₀
  rw [hXB, hYB] at h₁
  have hm01 : m 0 = m 1 := by
    have hle : t * (m 1 - m 0) ≤ 0 := by nlinarith only [h₀]
    have hge : (1 - t) * (m 0 - m 1) ≤ 0 := by nlinarith only [h₁]
    have hle' := nonpos_of_mul_nonpos_right hle ht
    have hge' := nonpos_of_mul_nonpos_right hge (sub_pos.mpr ht₁)
    linarith only [hle', hge']
  have hm₀ : 0 < m 0 := by
    rw [Fin.sum_univ_three, hm₂, ← hm01] at hsum
    linarith only [hsum]
  intro z hz
  have hzrow := hrow' z hz
  rw [← hm01] at hzrow
  have hp : m 0 * (X z - Y z) ≤ 0 := by nlinarith only [hzrow]
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hp hm₀)

/-- For consecutive positive windows, the entire body is covered exactly
when the three affine coordinates occur in that order throughout K. -/
theorem cover_iff_ordered (K : Set E) (hK : Convex ℝ K)
    (X Y Z : E →ᵃ[ℝ] ℝ) (A B : E) (hA : A ∈ K) (hB : B ∈ K)
    (hXA : X A = 0) (hYA : Y A = 0) (hZA : Z A = 0)
    (hXB : X B = 1) (hYB : Y B = 1) (hZB : Z B = 1)
    (hbox : ∀ z ∈ K, 0 ≤ X z ∧ Z z ≤ 1)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs : s < 1) :
    (∀ z ∈ K, (0 ≤ X z ∧ X z ≤ r) ∨ (r ≤ Y z ∧ Y z ≤ s) ∨
      (s ≤ Z z ∧ Z z ≤ 1)) ↔
    (∀ z ∈ K, X z ≤ Y z ∧ Y z ≤ Z z) := by
  constructor
  · intro hcover
    have hXY := order_of_missing_corner K hK X Y Z A B hA hB hXA hYA hZA hXB hYB hZB
      r s hr (hrs.trans hs) hrs (by
        rintro ⟨z, hz, hX, hY, hZ⟩
        rcases hcover z hz with h | h | h
        · exact not_le_of_gt hX h.2
        · exact not_lt_of_ge h.1 hY
        · exact not_lt_of_ge h.1 hZ)
    have hZY := order_of_missing_corner K hK
      (TwoPlankClassification.reflect Z) (TwoPlankClassification.reflect Y)
      (TwoPlankClassification.reflect X) B A hB hA
      (by simp [hZB]) (by simp [hYB]) (by simp [hXB])
      (by simp [hZA]) (by simp [hYA]) (by simp [hXA])
      (1 - s) (1 - r) (sub_pos.mpr hs) (by linarith only [hr, hrs])
      (by linarith only [hrs]) (by
        rintro ⟨z, hz, hZ, hY, hX⟩
        change 1 - s < 1 - Z z at hZ
        change 1 - Y z < 1 - s at hY
        change 1 - X z < 1 - r at hX
        rcases hcover z hz with h | h | h <;> linarith only [h.1, h.2, hZ, hY, hX])
    intro z hz
    refine ⟨hXY z hz, ?_⟩
    have h := hZY z hz
    change 1 - Z z ≤ 1 - Y z at h
    linarith only [h]
  · intro hord z hz
    by_cases hX : X z ≤ r
    · exact Or.inl ⟨(hbox z hz).1, hX⟩
    by_cases hY : Y z ≤ s
    · exact Or.inr (Or.inl ⟨(le_of_not_ge hX).trans (hord z hz).1, hY⟩)
    · exact Or.inr (Or.inr ⟨(le_of_not_ge hY).trans (hord z hz).2, (hbox z hz).2⟩)

/-- The explicit common-chord family. The window endpoints partition
`[0,1]`, and two affine inequalities specify the permitted body enclosure. -/
def Normal (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (r s : ℝ), 0 < r ∧ r < s ∧ s < 1 ∧
    lo (σ 0) = 0 ∧ hi (σ 0) = r ∧ lo (σ 1) = r ∧ hi (σ 1) = s ∧
    lo (σ 2) = s ∧ hi (σ 2) = 1 ∧
    ∀ z ∈ K, f (σ 0) z ≤ f (σ 1) z ∧ f (σ 1) z ≤ f (σ 2) z

/-- Complete positive equality classification when the oriented
coordinates share a minimum and a maximum. Directions need not be parallel,
and the body can have any shape satisfying the two stated affine inequalities. -/
theorem tight_iff (K : Set E) (hK : Convex ℝ K) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (A B : E) (hA : A ∈ K) (hB : B ∈ K)
    (hmin : ∀ i, f i A = 0) (hmax : ∀ i, f i B = 1)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ f i z ∧ f i z ≤ 1)
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hwidth : ∀ i, lo i < hi i) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ f i z ∧ f i z ≤ hi i) ↔
      Normal K f lo hi := by
  constructor
  · rintro ⟨hsum, hcover⟩
    have ht : ParallelClassification.TightIntervals lo hi := by
      refine ⟨hsum, ?_⟩
      intro t ht
      have hQ := hK.lineMap_mem hA hB ht
      have he (i : Fin 3) : f i (AffineMap.lineMap A B t) = t := by
        rw [(f i).apply_lineMap, AffineMap.lineMap_apply_ring, hmin, hmax]
        ring
      simpa only [he] using hcover (AffineMap.lineMap A B t) hQ
    obtain ⟨σ, r, s, hr, hrs, hs, hl0, hu0, hl1, hu1, hl2, hu2⟩ :=
      (ParallelClassification.tight_intervals_iff lo hi hlo hhi hwidth).mp ht
    refine ⟨σ, r, s, hr, hrs, hs, hl0, hu0, hl1, hu1, hl2, hu2, ?_⟩
    apply (cover_iff_ordered K hK (f (σ 0)) (f (σ 1)) (f (σ 2)) A B hA hB
      (hmin _) (hmin _) (hmin _) (hmax _) (hmax _) (hmax _)
      (fun z hz => ⟨(hbox z hz _).1, (hbox z hz _).2⟩) r s hr hrs hs).mp
    intro z hz
    obtain ⟨i, hil, hiu⟩ := hcover z hz
    obtain ⟨j, rfl⟩ := σ.surjective i
    fin_cases j <;> dsimp at hil hiu
    · rw [hl0] at hil
      rw [hu0] at hiu
      exact Or.inl ⟨hil, hiu⟩
    · rw [hl1] at hil
      rw [hu1] at hiu
      exact Or.inr (Or.inl ⟨hil, hiu⟩)
    · rw [hl2] at hil
      rw [hu2] at hiu
      exact Or.inr (Or.inr ⟨hil, hiu⟩)
  · rintro ⟨σ, r, s, hr, hrs, hs, hl0, hu0, hl1, hu1, hl2, hu2, hord⟩
    refine ⟨?_, ?_⟩
    · rw [← Equiv.sum_comp σ (fun i => hi i - lo i), Fin.sum_univ_three]
      rw [hl0, hu0, hl1, hu1, hl2, hu2]
      ring
    · have hc := (cover_iff_ordered K hK (f (σ 0)) (f (σ 1)) (f (σ 2)) A B hA hB
        (hmin _) (hmin _) (hmin _) (hmax _) (hmax _) (hmax _)
        (fun z hz => ⟨(hbox z hz _).1, (hbox z hz _).2⟩) r s hr hrs hs).mpr hord
      intro z hz
      rcases hc z hz with h | h | h
      · exact ⟨σ 0, by rw [hl0, hu0]; exact h⟩
      · exact ⟨σ 1, by rw [hl1, hu1]; exact h⟩
      · exact ⟨σ 2, by rw [hl2, hu2]; exact h⟩

end Plank.Convex.PlanarTight.CommonChordClassification

/-- info: 'Plank.Convex.PlanarTight.CommonChordClassification.order_of_missing_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CommonChordClassification.order_of_missing_corner

/-- info: 'Plank.Convex.PlanarTight.CommonChordClassification.cover_iff_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CommonChordClassification.cover_iff_ordered

/-- info: 'Plank.Convex.PlanarTight.CommonChordClassification.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CommonChordClassification.tight_iff
