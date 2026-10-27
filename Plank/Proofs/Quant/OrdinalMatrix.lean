module
/- # Ordering the three ABC interactions -/
public import Plank.Proofs.Quant.OrdinalTranslations

@[expose] public section

noncomputable section

namespace Quant.OrdinalMatrix

open OrdinalTranslations

def bit (s : Bool) (a : ℝ) : ℝ := if s then a else 0

theorem bit_not (s : Bool) (a : ℝ) : bit (!s) a = a - bit s a := by
  cases s <;> simp [bit]

theorem bit_order {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 0 < A) (hB : 0 < B)
    (ho : (A < B ∧ a ≤ b) ∨ (B < A ∧ b ≤ a)) (s₀ s₁ t₀ t₁ : Bool)
    (h : bit s₀ A + bit s₁ B ≤ bit t₀ A + bit t₁ B) :
    bit s₀ a + bit s₁ b ≤ bit t₀ a + bit t₁ b := by
  rcases ho with ho | ho
  · exact two_bit_monotone ha ho.2 hA ho.1 s₀ s₁ t₀ t₁ h
  · have h' : bit s₁ B + bit s₀ A ≤ bit t₁ B + bit t₀ A := by linarith
    have hm := two_bit_monotone hb ho.2 hB ho.1 s₁ s₀ t₁ t₀ h'
    change bit s₁ b + bit s₀ a ≤ bit t₁ b + bit t₀ a at hm
    linarith

theorem bit_sub_order {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 0 < A) (hB : 0 < B)
    (ho : (A < B ∧ a ≤ b) ∨ (B < A ∧ b ≤ a)) (s₀ s₁ t₀ t₁ : Bool)
    (h : bit s₀ A - bit s₁ B ≤ bit t₀ A - bit t₁ B) :
    bit s₀ a - bit s₁ b ≤ bit t₀ a - bit t₁ b := by
  have h' : bit s₀ A + bit (!s₁) B ≤ bit t₀ A + bit (!t₁) B := by
    rw [bit_not, bit_not]
    linarith
  have hm := bit_order ha hb hA hB ho s₀ (!s₁) t₀ (!t₁) h'
  rw [bit_not, bit_not] at hm
  linarith

def matrix (p q r s t u : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![0, p, q], ![r, 0, -s], ![t, -u, 0]]

def model (x y z : ℝ) : Fin 3 → Fin 3 → ℝ := matrix x y x z y z

def pick (S : Finset (Fin 3)) (i : Fin 3) : Bool := by
  classical
  exact decide (i ∈ S)

theorem sum_membership (f : Fin 3 → ℝ) (S : Finset (Fin 3)) :
    S.sum f = ∑ i : Fin 3, if i ∈ S then f i else 0 := by
  classical
  simp [Finset.sum_ite_mem]

theorem row_zero (p q r s t u : ℝ) (S : Finset (Fin 3)) :
    S.sum (matrix p q r s t u 0) = bit (pick S 1) p + bit (pick S 2) q := by
  classical
  rw [sum_membership, Fin.sum_univ_three]
  simp [matrix, bit, pick]

theorem row_one (p q r s t u : ℝ) (S : Finset (Fin 3)) :
    S.sum (matrix p q r s t u 1) = bit (pick S 0) r - bit (pick S 2) s := by
  classical
  rw [sum_membership, Fin.sum_univ_three]
  simp only [matrix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, bit, pick, decide_eq_true_eq]
  split_ifs <;> ring

theorem row_two (p q r s t u : ℝ) (S : Finset (Fin 3)) :
    S.sum (matrix p q r s t u 2) = bit (pick S 0) t - bit (pick S 1) u := by
  classical
  rw [sum_membership, Fin.sum_univ_three]
  simp only [matrix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, bit, pick, decide_eq_true_eq]
  split_ifs <;> ring

/-- An auxiliary symmetric matrix with the same three local weight orders
preserves every row's subset-sum order. -/
theorem matrix_order (p q r s t u x y z : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h₀ : (x < y ∧ p ≤ q) ∨ (y < x ∧ q ≤ p))
    (h₁ : (x < z ∧ r ≤ s) ∨ (z < x ∧ s ≤ r))
    (h₂ : (y < z ∧ t ≤ u) ∨ (z < y ∧ u ≤ t)) :
    ∀ (i : Fin 3) (S T : Finset (Fin 3)), S.sum (model x y z i) ≤ T.sum (model x y z i) →
      S.sum (matrix p q r s t u i) ≤ T.sum (matrix p q r s t u i) := by
  intro i S T h
  fin_cases i
  · change S.sum (model x y z 0) ≤ T.sum (model x y z 0) at h
    change S.sum (matrix p q r s t u 0) ≤ T.sum (matrix p q r s t u 0)
    simp only [model, row_zero] at h ⊢
    exact bit_order hp hq hx hy h₀ _ _ _ _ h
  · change S.sum (model x y z 1) ≤ T.sum (model x y z 1) at h
    change S.sum (matrix p q r s t u 1) ≤ T.sum (matrix p q r s t u 1)
    simp only [model, row_one] at h ⊢
    exact bit_sub_order hr hs hx hz h₁ _ _ _ _ h
  · change S.sum (model x y z 2) ≤ T.sum (model x y z 2) at h
    change S.sum (matrix p q r s t u 2) ≤ T.sum (matrix p q r s t u 2)
    simp only [model, row_two] at h ⊢
    exact bit_sub_order ht hu hy hz h₂ _ _ _ _ h

/-- The six consistent weak orders of the three undirected interactions.
The two strictly cyclic comparison patterns are excluded. -/
def Compatible (p q r s t u : ℝ) : Prop :=
  (p ≤ q ∧ r ≤ s ∧ t ≤ u) ∨
  (p ≤ q ∧ r ≤ s ∧ u ≤ t) ∨
  (q ≤ p ∧ r ≤ s ∧ t ≤ u) ∨
  (q ≤ p ∧ s ≤ r ∧ t ≤ u) ∨
  (p ≤ q ∧ s ≤ r ∧ u ≤ t) ∨
  (q ≤ p ∧ s ≤ r ∧ u ≤ t)

theorem compatible_iff_not_cycles (p q r s t u : ℝ) :
    Compatible p q r s t u ↔
      ¬ ((q < p ∧ r < s ∧ u < t) ∨ (p < q ∧ s < r ∧ t < u)) := by
  constructor
  · intro h hn
    rcases h with h | h | h | h | h | h <;>
      rcases hn with hn | hn <;> linarith
  · intro hn
    unfold Compatible
    by_cases hp : p ≤ q <;> by_cases hr : r ≤ s <;> by_cases ht : t ≤ u
    · exact Or.inl ⟨hp, hr, ht⟩
    · have htu := (lt_of_not_ge ht).le
      exact Or.inr (Or.inl ⟨hp, hr, htu⟩)
    · have hrs := (lt_of_not_ge hr).le
      by_cases hq : q ≤ p
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hrs, ht⟩)))
      · have hu : u ≤ t := by
          by_contra hu
          exact hn (Or.inr ⟨lt_of_not_ge hq, lt_of_not_ge hr, lt_of_not_ge hu⟩)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hrs, hu⟩))))
    · have hrs := (lt_of_not_ge hr).le
      have htu := (lt_of_not_ge ht).le
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hrs, htu⟩))))
    · have hqp := (lt_of_not_ge hp).le
      exact Or.inr (Or.inr (Or.inl ⟨hqp, hr, ht⟩))
    · have hqp := (lt_of_not_ge hp).le
      have htu := (lt_of_not_ge ht).le
      have hs : s ≤ r := by
        by_contra hs
        exact hn (Or.inl ⟨lt_of_not_ge hp, lt_of_not_ge hs, lt_of_not_ge ht⟩)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hqp, hs, htu⟩))))
    · have hqp := (lt_of_not_ge hp).le
      have hrs := (lt_of_not_ge hr).le
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hqp, hrs, ht⟩)))
    · have hqp := (lt_of_not_ge hp).le
      have hrs := (lt_of_not_ge hr).le
      have htu := (lt_of_not_ge ht).le
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hqp, hrs, htu⟩))))

theorem compatible_of_product_eq (p q r s t u : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (he : p * s * t = q * r * u) : Compatible p q r s t u := by
  apply (compatible_iff_not_cycles p q r s t u).mpr
  rintro (⟨hqp, hrs, hut⟩ | ⟨hpq, hsr, htu⟩)
  · have hp' : 0 < p := hq.trans_lt hqp
    have hs' : 0 < s := hr.trans_lt hrs
    have hlt : q * r * u < p * s * t := by
      calc
        q * r * u ≤ p * r * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqp.le hr) hu
        _ ≤ p * s * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrs.le hp) hu
        _ < p * s * t := mul_lt_mul_of_pos_left hut (mul_pos hp' hs')
    exact (ne_of_lt hlt) he.symm
  · have hq' : 0 < q := hp.trans_lt hpq
    have hr' : 0 < r := hs.trans_lt hsr
    have hlt : p * s * t < q * r * u := by
      calc
        p * s * t ≤ q * s * t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpq.le hs) ht
        _ ≤ q * r * t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsr.le hq) ht
        _ < q * r * u := mul_lt_mul_of_pos_left htu (mul_pos hq' hr')
    exact (ne_of_lt hlt) he

theorem exists_model (p q r s t u : ℝ) (h : Compatible p q r s t u) :
    ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      ((x < y ∧ p ≤ q) ∨ (y < x ∧ q ≤ p)) ∧
      ((x < z ∧ r ≤ s) ∨ (z < x ∧ s ≤ r)) ∧
      ((y < z ∧ t ≤ u) ∨ (z < y ∧ u ≤ t)) := by
  rcases h with h | h | h | h | h | h
  · refine ⟨1, 2, 3, by norm_num, by norm_num, by norm_num,
      Or.inl ⟨by norm_num, h.1⟩, Or.inl ⟨by norm_num, h.2.1⟩,
      Or.inl ⟨by norm_num, h.2.2⟩⟩
  · refine ⟨1, 3, 2, by norm_num, by norm_num, by norm_num,
      Or.inl ⟨by norm_num, h.1⟩, Or.inl ⟨by norm_num, h.2.1⟩,
      Or.inr ⟨by norm_num, h.2.2⟩⟩
  · refine ⟨2, 1, 3, by norm_num, by norm_num, by norm_num,
      Or.inr ⟨by norm_num, h.1⟩, Or.inl ⟨by norm_num, h.2.1⟩,
      Or.inl ⟨by norm_num, h.2.2⟩⟩
  · refine ⟨3, 1, 2, by norm_num, by norm_num, by norm_num,
      Or.inr ⟨by norm_num, h.1⟩, Or.inr ⟨by norm_num, h.2.1⟩,
      Or.inl ⟨by norm_num, h.2.2⟩⟩
  · refine ⟨2, 3, 1, by norm_num, by norm_num, by norm_num,
      Or.inl ⟨by norm_num, h.1⟩, Or.inr ⟨by norm_num, h.2.1⟩,
      Or.inr ⟨by norm_num, h.2.2⟩⟩
  · refine ⟨3, 2, 1, by norm_num, by norm_num, by norm_num,
      Or.inr ⟨by norm_num, h.1⟩, Or.inr ⟨by norm_num, h.2.1⟩,
      Or.inr ⟨by norm_num, h.2.2⟩⟩

theorem model_symmetric (x y z : ℝ) : ∀ i j, model x y z i j = model x y z j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem model_diagonal (x y z : ℝ) : ∀ i, model x y z i i = 0 := by
  intro i
  fin_cases i <;> rfl

end Quant.OrdinalMatrix
