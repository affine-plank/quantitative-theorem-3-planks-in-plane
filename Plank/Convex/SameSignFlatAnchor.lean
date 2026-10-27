/- Zero objective coefficients move an interior equality cover to a positive anchored cover. -/
module
public import Plank.Convex.SameSignLocalMinimum
public import Plank.Convex.SameSignCapMinimumStrict
public import Plank.Convex.TwoWindowUpperCorner
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace Plank.Convex.SameSignFlatAnchor
open SameSignCapMinimum

/-- Positive supporting rows also suffice at nonstrict endpoint boundaries. -/
theorem wallSet_of_rows (K : Set Point) (B : Walls) (hbox : B ∈ Icc 0 1)
    (horder : ∀ i, B.1 i ≤ B.2 i) (r : SameSignLocalMinimum.Index → ℝ)
    (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B) :
    B ∈ wallSet K := by
  refine ⟨hbox, mem_iInter.mpr horder, ?_⟩
  refine mem_iInter.mpr fun x => mem_iInter.mpr fun hx => mem_iInter.mpr fun i => ⟨?_, ?_⟩
  · by_contra hn
    have hi : B.2 i < x i := lt_of_not_ge fun h => hn (Or.inl h)
    have hj : B.2 (next i) < x (next i) := lt_of_not_ge fun h => hn (Or.inr h)
    have h := hs x hx (true, i)
    simp only [SameSignLocalMinimum.rows, row_upper] at h
    linarith only [h, hi, mul_lt_mul_of_pos_left hj (hr (true, i))]
  · by_contra hn
    have hi : x i < B.1 i := lt_of_not_ge fun h => hn (Or.inl h)
    have hj : x (next i) < B.1 (next i) := lt_of_not_ge fun h => hn (Or.inr h)
    have h := hs x hx (false, i)
    simp only [SameSignLocalMinimum.rows, row_lower] at h
    linarith only [h, hi, mul_lt_mul_of_pos_left hj (hr (false, i))]

/-- A positive plane over the diagonal region has a coordinate-extreme cube vertex,
which an interior same-sign cover excludes. -/
theorem no_diagonal (K : Set Point)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls) :
    ¬ TwoWindowUpperCorner.Diagonal K (AffineMap.proj 0) (AffineMap.proj 1) := by
  rintro ⟨hd, ⟨L, hL, hL0, hL1⟩, ⟨R, hR, hR0, hR1⟩⟩
  change L 0 = 0 at hL0
  change L 1 = 1 at hL1
  change R 0 = 1 at hR0
  change R 1 = 0 at hR1
  obtain ⟨M, hM, hM2⟩ := hU 2
  have hMplane := hplane M hM
  have hLplane := hplane L hL
  have hRplane := hplane R hR
  simp only [Fin.sum_univ_three, hM2, hL0, hL1, hR0, hR1, mul_zero, mul_one, zero_add,
    add_zero] at hMplane hLplane hRplane
  have hMd : 1 ≤ M 0 + M 1 := hd M hM
  have hh (i : Fin 3) : B.2 i < 1 := (mem_iInter.mp hstrict i).2
  by_cases h01 : A 0 ≤ A 1
  · have hlow : A 0 ≤ A 0 * M 0 + A 1 * M 1 := by
      have h := mul_le_mul_of_nonneg_left hMd (hA 0).le
      have he := mul_nonneg (sub_nonneg.mpr h01) (hbox M hM 1).1
      nlinarith only [h, he]
    have hR2 : R 2 = 1 := by
      have hb := (hbox R hR 2).2
      have ha := hA 2
      nlinarith only [hMplane, hRplane, hlow, hb, ha]
    apply cap_empty K B hB (true, 2)
    refine ⟨R, hR, ?_, ?_⟩
    · change B.2 2 < R 2
      rw [hR2]
      exact hh 2
    · change B.2 0 < R 0
      rw [hR0]
      exact hh 0
  · have hlow : A 1 ≤ A 0 * M 0 + A 1 * M 1 := by
      have h := mul_le_mul_of_nonneg_left hMd (hA 1).le
      have he := mul_nonneg (sub_nonneg.mpr (le_of_not_ge h01)) (hbox M hM 0).1
      nlinarith only [h, he]
    have hL2 : L 2 = 1 := by
      have hb := (hbox L hL 2).2
      have ha := hA 2
      nlinarith only [hMplane, hLplane, hlow, hb, ha]
    apply cap_empty K B hB (true, 1)
    refine ⟨L, hL, ?_, ?_⟩
    · change B.2 1 < L 1
      rw [hL1]
      exact hh 1
    · change B.2 2 < L 2
      rw [hL2]
      exact hh 2

/-- Increasing both upper endpoints of the first pair cannot produce a zero third
width at equality while preserving the original positive-plane body. -/
theorem third_width_pos (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls)
    (C : Walls) (hC : C ∈ wallSet K) (hsum : width C = 1)
    (hlo : C.1 = B.1) (hinc₀ : B.2 0 < C.2 0) (hinc₁ : B.2 1 < C.2 1) :
    C.1 2 < C.2 2 := by
  by_contra hn
  have hz : C.2 2 = C.1 2 :=
    le_antisymm (le_of_not_gt hn) (mem_iInter.mp hC.2.1 2)
  have hends (i : Fin 3) : (0 < B.1 i ∧ B.1 i < B.2 i) ∧ B.2 i < 1 := mem_iInter.mp hstrict i
  have hwidth₀ : C.1 0 < C.2 0 := by rw [hlo]; exact (hends 0).1.2.trans hinc₀
  have hwidth₁ : C.1 1 < C.2 1 := by rw [hlo]; exact (hends 1).1.2.trans hinc₁
  have hlow₀ : 0 < C.1 0 := by rw [hlo]; exact (hends 0).1.1
  have hlow₁ : 0 < C.1 1 := by rw [hlo]; exact (hends 1).1.1
  have hcover : ∀ x ∈ K, ∃ i, C.1 i ≤ x i ∧ x i ≤ C.2 i := by
    intro x hx
    apply SameSignCapMinimumStrict.cover_of_pair_caps
    intro i
    have h := mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hC.2.2 x) hx) i
    change (x i ≤ C.2 i ∨ x (next i) ≤ C.2 (next i)) ∧
      (C.1 i ≤ x i ∨ C.1 (next i) ≤ x (next i)) at h
    have he (j : Fin 3) : next j = SameSignCapAlgebra.next j := by fin_cases j <;> rfl
    simpa only [he] using h
  let W : Set Point := {x | C.1 0 ≤ x 0 ∧ x 0 ≤ C.2 0} ∪
    {x | C.1 1 ≤ x 1 ∧ x 1 ≤ C.2 1}
  have hclosed (i : Fin 3) : IsClosed {x : Point | C.1 i ≤ x i ∧ x i ≤ C.2 i} :=
    (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  obtain ⟨p, hp, hp₂⟩ := hL 2
  have hpne : p 2 ≠ C.1 2 := by rw [hp₂, hlo]; exact (hends 2).1.1.ne
  have htwo : K ⊆ W := by
    apply ClosedCover.closed_cover_remove_affine K W hK ((hclosed 0).union (hclosed 1))
      (AffineMap.proj 2) (C.1 2) p hp hpne
    intro x hx
    obtain ⟨i, hli, hhi⟩ := hcover x hx
    fin_cases i
    · exact Or.inl (Or.inl ⟨hli, hhi⟩)
    · exact Or.inl (Or.inr ⟨hli, hhi⟩)
    · apply Or.inr
      change x 2 = C.1 2
      change x 2 ≤ C.2 2 at hhi
      change C.1 2 ≤ x 2 at hli
      rw [hz] at hhi
      exact le_antisymm hhi hli
  have hsum' : (C.2 0 - C.1 0) + (C.2 1 - C.1 1) = 1 := by
    simpa only [width_apply, Fin.sum_univ_three, hz, sub_self, add_zero] using hsum
  let H : PlanarTight.TwoPlankClassification.Ranges K (AffineMap.proj 0) (AffineMap.proj 1) :=
    ⟨fun x hx => ⟨hbox x hx 0, hbox x hx 1⟩, hL 0, hU 0, hL 1, hU 1⟩
  rcases TwoWindowUpperCorner.upper_corner_or_diagonal K hK _ _ H
    (C.1 0) (C.2 0) (C.1 1) (C.2 1) hlow₀ (hC.1.2.2 0) hlow₁ (hC.1.2.2 1)
    hwidth₀ hwidth₁ hsum' htwo with hcorner | hdiag
  · obtain ⟨x, hx, hx₀, hx₁⟩ := hcorner
    apply cap_empty K B hB (true, 0)
    refine ⟨x, hx, ?_, ?_⟩
    · change B.2 0 < x 0
      rw [show x 0 = C.2 0 from hx₀]
      exact hinc₀
    · change B.2 1 < x 1
      rw [show x 1 = C.2 1 from hx₁]
      exact hinc₁
  · exact no_diagonal K hbox hU A D hA hplane B hB hstrict hdiag.2.2

/-- A zero upper coefficient moves the original equality cover to an upper anchor,
keeping all widths positive and the original body and lower endpoints fixed. -/
theorem upper_zero_anchor (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls) (hsum : width B = 1)
    (r : SameSignLocalMinimum.Index → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B)
    (hn : SameSignLocalMinimum.numerator r (true, 0) = 0) :
    ∃ C ∈ wallSet K, C.1 = B.1 ∧ width C = 1 ∧
      (∀ i, C.1 i < C.2 i) ∧ ∃ i, C.2 i = 1 := by
  let q := r (true, 1) * r (true, 2)
  let a := r (true, 2)
  have hq : 0 < q := mul_pos (hr _) (hr _)
  have ha : 0 < a := hr _
  have hends (i : Fin 3) : (0 < B.1 i ∧ B.1 i < B.2 i) ∧ B.2 i < 1 := mem_iInter.mp hstrict i
  let t := min (1 - B.2 0) (min ((1 - B.2 1) / q) ((B.2 2 - B.1 2) / a))
  have ht : 0 < t := lt_min (sub_pos.mpr (hends 0).2)
    (lt_min (div_pos (sub_pos.mpr (hends 1).2) hq) (div_pos (sub_pos.mpr (hends 2).1.2) ha))
  have ht₀ : t ≤ 1 - B.2 0 := min_le_left _ _
  have htq : t * q ≤ 1 - B.2 1 := (le_div_iff₀ hq).mp
    ((min_le_right _ _).trans (min_le_left _ _))
  have hta : t * a ≤ B.2 2 - B.1 2 := (le_div_iff₀ ha).mp
    ((min_le_right _ _).trans (min_le_right _ _))
  let d := SameSignLocalMinimum.motion r (true, 0)
  let C := B + t • d
  have hdlo : d.1 = 0 := rfl
  have hd₀ : d.2 0 = 1 := rfl
  have hd₁ : d.2 1 = q := rfl
  have hd₂ : d.2 2 = -a := rfl
  have hlo : C.1 = B.1 := by
    change B.1 + t • d.1 = B.1
    rw [hdlo, smul_zero, add_zero]
  have hc₀ : C.2 0 = B.2 0 + t := by
    change B.2 0 + t * d.2 0 = _
    rw [hd₀, mul_one]
  have hc₁ : C.2 1 = B.2 1 + t * q := by
    change B.2 1 + t * d.2 1 = _
    rw [hd₁]
  have hc₂ : C.2 2 = B.2 2 - t * a := by
    change B.2 2 + t * d.2 2 = _
    rw [hd₂]
    ring
  have hi₀ : B.2 0 < C.2 0 := by rw [hc₀]; linarith only [ht]
  have hi₁ : B.2 1 < C.2 1 := by rw [hc₁]; exact lt_add_of_pos_right _ (mul_pos ht hq)
  have horder (i : Fin 3) : C.1 i ≤ C.2 i := by
    rw [hlo]
    fin_cases i
    · exact ((hends 0).1.2.trans hi₀).le
    · exact ((hends 1).1.2.trans hi₁).le
    · change B.1 2 ≤ C.2 2
      rw [hc₂]
      linarith only [hta]
  have hupper (i : Fin 3) : C.2 i ≤ 1 := by
    fin_cases i
    · change C.2 0 ≤ 1
      rw [hc₀]
      linarith only [ht₀]
    · change C.2 1 ≤ 1
      rw [hc₁]
      linarith only [htq]
    · change C.2 2 ≤ 1
      rw [hc₂]
      have hp := mul_pos ht ha
      linarith only [hp, (hends 2).2]
  have hCbox : C ∈ Icc 0 1 := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, hupper⟩⟩
    · intro i
      rw [hlo]
      exact (hends i).1.1.le
    · intro i
      exact (show 0 < C.1 i by rw [hlo]; exact (hends i).1.1).le.trans (horder i)
    · intro i
      rw [hlo]
      exact ((hends i).1.2.trans (hends i).2).le
  have hdrows (j : SameSignLocalMinimum.Index) : 0 ≤ SameSignLocalMinimum.rows r j d := by
    by_cases hj : j = (true, 0)
    · subst j
      rw [SameSignLocalMinimum.row_motion_self]
      exact (add_pos zero_lt_one (Finset.prod_pos fun i _ => hr (true, i))).le
    · rw [SameSignLocalMinimum.row_motion_other r (true, 0) j hj]
  have hC : C ∈ wallSet K := by
    apply wallSet_of_rows K C hCbox horder r hr
    intro x hx j
    apply (hs x hx j).trans
    change SameSignLocalMinimum.rows r j B ≤ SameSignLocalMinimum.rows r j (B + t • d)
    rw [map_add, map_smul, smul_eq_mul]
    exact le_add_of_nonneg_right (mul_nonneg ht.le (hdrows j))
  have hsC : width C = 1 := by
    change width (B + t • d) = 1
    have hd : width d = 0 := by simpa only [d, SameSignLocalMinimum.motion_width] using hn
    rw [map_add, map_smul, hd, smul_zero, add_zero]
    exact hsum
  have hw₂ := third_width_pos K hK hbox hL hU A D hA hplane B hB hstrict C hC hsC hlo hi₀ hi₁
  have htcases : t = 1 - B.2 0 ∨ t = (1 - B.2 1) / q ∨ t = (B.2 2 - B.1 2) / a := by
    by_cases h₀ : 1 - B.2 0 ≤ min ((1 - B.2 1) / q) ((B.2 2 - B.1 2) / a)
    · exact Or.inl (min_eq_left h₀)
    · have he : t = min ((1 - B.2 1) / q) ((B.2 2 - B.1 2) / a) := min_eq_right (le_of_not_ge h₀)
      by_cases h₁ : (1 - B.2 1) / q ≤ (B.2 2 - B.1 2) / a
      · exact Or.inr (Or.inl (he.trans (min_eq_left h₁)))
      · exact Or.inr (Or.inr (he.trans (min_eq_right (le_of_not_ge h₁))))
  refine ⟨C, hC, hlo, hsC, ?_, ?_⟩
  · intro i
    fin_cases i
    · rw [hlo]
      exact (hends 0).1.2.trans hi₀
    · rw [hlo]
      exact (hends 1).1.2.trans hi₁
    · exact hw₂
  · rcases htcases with ht0 | ht1 | ht2
    · exact ⟨0, by rw [hc₀, ht0]; ring⟩
    · have he := (eq_div_iff hq.ne').mp ht1
      exact ⟨1, by rw [hc₁, he]; ring⟩
    · have he := (eq_div_iff ha.ne').mp ht2
      have hz : C.2 2 = C.1 2 := by rw [hc₂, he, hlo]; ring
      exact False.elim (hw₂.ne' hz)

end Plank.Convex.SameSignFlatAnchor

/-- info: 'Plank.Convex.SameSignFlatAnchor.third_width_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignFlatAnchor.third_width_pos

/-- info: 'Plank.Convex.SameSignFlatAnchor.upper_zero_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignFlatAnchor.upper_zero_anchor
