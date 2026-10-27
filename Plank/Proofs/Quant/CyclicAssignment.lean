module
/-
# The exact obstruction to three binary side assignments

For the ABC interaction matrix, a side assignment fails precisely in one
of two open boxes in threshold space. This is a statement about the
designated side assignments, not about coverage of all candidate points.
-/
public import Plank.Proofs.Quant.OrdinalMatrix

@[expose] public section

noncomputable section

namespace Quant.CyclicAssignment

/-- The eight possible side assignments, with the diagonal removed. -/
inductive Pattern (p q r s t u x y z : ℝ) : Prop
  | s000 (h0 : 0 ≤ x) (h1 : 0 ≤ y) (h2 : 0 ≤ z)
  | s100 (h0 : x ≤ 0) (h1 : r ≤ y) (h2 : t ≤ z)
  | s010 (h0 : p ≤ x) (h1 : y ≤ 0) (h2 : -u ≤ z)
  | s001 (h0 : q ≤ x) (h1 : -s ≤ y) (h2 : z ≤ 0)
  | s110 (h0 : x ≤ p) (h1 : y ≤ r) (h2 : t - u ≤ z)
  | s101 (h0 : x ≤ q) (h1 : r - s ≤ y) (h2 : z ≤ t)
  | s011 (h0 : p + q ≤ x) (h1 : y ≤ -s) (h2 : z ≤ -u)
  | s111 (h0 : x ≤ p + q) (h1 : y ≤ r - s) (h2 : z ≤ t - u)

/-- Both boxes are open; their equality boundaries admit an assignment. -/
def Bad (p q r s t u x y z : ℝ) : Prop :=
  ((q < x ∧ x < p) ∧ (r - s < y ∧ y < 0) ∧ (0 < z ∧ z < t - u)) ∨
  ((p < x ∧ x < q) ∧ (0 < y ∧ y < r - s) ∧ (t - u < z ∧ z < 0))

private theorem negative_pair (A B H K y z : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K) :
    (A ≤ y ∧ B ≤ z) ∨ (y ≤ A ∧ B - K ≤ z) ∨
      (A - H ≤ y ∧ z ≤ B) ∨ (y ≤ A - H ∧ z ≤ B - K) := by
  by_cases hy : y ≤ A - H
  · by_cases hz : z ≤ B - K
    · exact Or.inr (Or.inr (Or.inr ⟨hy, hz⟩))
    · exact Or.inr (Or.inl ⟨by linarith, le_of_not_ge hz⟩)
  · by_cases hz : z ≤ B
    · exact Or.inr (Or.inr (Or.inl ⟨le_of_not_ge hy, hz⟩))
    · by_cases hyA : A ≤ y
      · exact Or.inl ⟨hyA, le_of_not_ge hz⟩
      · exact Or.inr (Or.inl ⟨le_of_not_ge hyA, by linarith⟩)

theorem bad_of_not_pattern {p q r s t u x y z : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hn : ¬ Pattern p q r s t u x y z) :
    Bad p q r s t u x y z := by
  have hx0 : 0 < x := by
    by_contra hx
    have hx' : x ≤ 0 := le_of_not_gt hx
    rcases negative_pair r t s u y z hs hu with h | h | h | h
    · exact hn (.s100 hx' h.1 h.2)
    · exact hn (.s110 (by linarith) h.1 h.2)
    · exact hn (.s101 (by linarith) h.1 h.2)
    · exact hn (.s111 (by linarith) h.1 h.2)
  have hxpq : x < p + q := by
    by_contra hx
    have hx' : p + q ≤ x := le_of_not_gt hx
    rcases negative_pair 0 0 s u y z hs hu with h | h | h | h
    · exact hn (.s000 hx0.le h.1 h.2)
    · exact hn (.s010 (by linarith) h.1 (by linarith [h.2]))
    · exact hn (.s001 (by linarith) (by linarith [h.1]) h.2)
    · exact hn (.s011 hx' (by linarith [h.1]) (by linarith [h.2]))
  have hys : -s < y := by
    by_contra hy
    have hy' : y ≤ -s := le_of_not_gt hy
    by_cases hz : z ≤ t - u
    · exact hn (.s111 hxpq.le (by linarith) hz)
    · by_cases hx : x ≤ p
      · exact hn (.s110 hx (by linarith) (le_of_not_ge hz))
      · exact hn (.s010 (le_of_not_ge hx) (by linarith) (by linarith))
  have hyr : y < r := by
    by_contra hy
    have hy' : r ≤ y := le_of_not_gt hy
    by_cases hz : 0 ≤ z
    · exact hn (.s000 hx0.le (by linarith) hz)
    · by_cases hx : q ≤ x
      · exact hn (.s001 hx (by linarith) (le_of_not_ge hz))
      · exact hn (.s101 (le_of_not_ge hx) (by linarith) (by linarith))
  have hzu : -u < z := by
    by_contra hz
    have hz' : z ≤ -u := le_of_not_gt hz
    by_cases hy : y ≤ r - s
    · exact hn (.s111 hxpq.le hy (by linarith))
    · by_cases hx : x ≤ q
      · exact hn (.s101 hx (le_of_not_ge hy) (by linarith))
      · exact hn (.s001 (le_of_not_ge hx) (by linarith) (by linarith))
  have hzt : z < t := by
    by_contra hz
    have hz' : t ≤ z := le_of_not_gt hz
    by_cases hy : 0 ≤ y
    · exact hn (.s000 hx0.le hy (by linarith))
    · by_cases hx : p ≤ x
      · exact hn (.s010 hx (le_of_not_ge hy) (by linarith))
      · exact hn (.s110 (le_of_not_ge hx) (by linarith) (by linarith))
  by_cases hy0 : 0 ≤ y
  · have hz0 : z < 0 := by
      by_contra hz
      exact hn (.s000 hx0.le hy0 (le_of_not_gt hz))
    have hxq : x < q := by
      by_contra hx
      exact hn (.s001 (le_of_not_gt hx) hys.le hz0.le)
    have hyr' : y < r - s := by
      by_contra hy
      exact hn (.s101 hxq.le (le_of_not_gt hy) hzt.le)
    have hztu : t - u < z := by
      by_contra hz
      exact hn (.s111 hxpq.le hyr'.le (le_of_not_gt hz))
    have hpx : p < x := by
      by_contra hx
      exact hn (.s110 (le_of_not_gt hx) hyr.le hztu.le)
    have hypos : 0 < y := by
      by_contra hy
      exact hn (.s010 hpx.le (le_of_not_gt hy) hzu.le)
    exact Or.inr ⟨⟨hpx, hxq⟩, ⟨hypos, hyr'⟩, ⟨hztu, hz0⟩⟩
  · have hyneg : y < 0 := lt_of_not_ge hy0
    by_cases hz0 : 0 ≤ z
    · have hxp : x < p := by
        by_contra hx
        exact hn (.s010 (le_of_not_gt hx) hyneg.le (by linarith))
      have hztu : z < t - u := by
        by_contra hz
        exact hn (.s110 hxp.le hyr.le (le_of_not_gt hz))
      have hrsy : r - s < y := by
        by_contra hy
        exact hn (.s111 hxpq.le (le_of_not_gt hy) hztu.le)
      have hqx : q < x := by
        by_contra hx
        exact hn (.s101 (le_of_not_gt hx) hrsy.le hzt.le)
      have hzpos : 0 < z := by
        by_contra hz
        exact hn (.s001 hqx.le hys.le (le_of_not_gt hz))
      exact Or.inl ⟨⟨hqx, hxp⟩, ⟨hrsy, hyneg⟩, ⟨hzpos, hztu⟩⟩
    · exfalso
      have hzneg : z < 0 := lt_of_not_ge hz0
      by_cases hy : r - s ≤ y
      · by_cases hx : x ≤ q
        · exact hn (.s101 hx hy hzt.le)
        · exact hn (.s001 (le_of_not_ge hx) hys.le hzneg.le)
      · by_cases hz : z ≤ t - u
        · exact hn (.s111 hxpq.le (le_of_not_ge hy) hz)
        · by_cases hx : p ≤ x
          · exact hn (.s010 hx hyneg.le hzu.le)
          · exact hn (.s110 (le_of_not_ge hx) hyr.le (le_of_not_ge hz))

theorem pattern_iff_not_bad {p q r s t u x y z : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    Pattern p q r s t u x y z ↔ ¬ Bad p q r s t u x y z := by
  constructor
  · intro h hb
    cases h <;>
      rcases hb with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ | ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ <;>
      linarith
  · intro hb
    by_contra hn
    exact hb (bad_of_not_pattern hp hq hr hs ht hu hn)

theorem Bad.bounds {p q r s t u x y z : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (h : Bad p q r s t u x y z) :
    0 < x ∧ x < p + q ∧ -s < y ∧ y < r ∧ -u < z ∧ z < t := by
  rcases h with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ | ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem Pattern.exists_set {p q r s t u x y z : ℝ}
    (h : Pattern p q r s t u x y z) :
    ∃ S : Finset (Fin 3), ∀ i,
      if i ∈ S then ![x, y, z] i ≤ S.sum (OrdinalMatrix.matrix p q r s t u i)
      else S.sum (OrdinalMatrix.matrix p q r s t u i) ≤ ![x, y, z] i := by
  classical
  cases h with
  | s000 h0 h1 h2 =>
    refine ⟨∅, ?_⟩
    intro i
    fin_cases i <;> simp_all [OrdinalMatrix.matrix]
  | s100 h0 h1 h2 =>
    refine ⟨{0}, ?_⟩
    intro i
    fin_cases i <;> simp_all [OrdinalMatrix.matrix]
  | s010 h0 h1 h2 =>
    refine ⟨{1}, ?_⟩
    intro i
    fin_cases i <;> simp_all [OrdinalMatrix.matrix]
  | s001 h0 h1 h2 =>
    refine ⟨{2}, ?_⟩
    intro i
    fin_cases i <;> simp_all [OrdinalMatrix.matrix]
  | s110 h0 h1 h2 =>
    refine ⟨{0, 1}, ?_⟩
    intro i
    fin_cases i <;> simp_all [OrdinalMatrix.matrix, sub_eq_add_neg]
  | s101 h0 h1 h2 =>
    refine ⟨{0, 2}, ?_⟩
    intro i
    fin_cases i <;> simp_all [OrdinalMatrix.matrix, sub_eq_add_neg]
  | s011 h0 h1 h2 =>
    refine ⟨{1, 2}, ?_⟩
    intro i
    fin_cases i <;> simp_all [OrdinalMatrix.matrix]
  | s111 h0 h1 h2 =>
    refine ⟨{0, 1, 2}, ?_⟩
    intro i
    fin_cases i <;> simp_all [OrdinalMatrix.matrix, sub_eq_add_neg]

theorem pattern_of_set {p q r s t u x y z : ℝ} (S : Finset (Fin 3))
    (hS : ∀ i, if i ∈ S then ![x, y, z] i ≤ S.sum (OrdinalMatrix.matrix p q r s t u i)
      else S.sum (OrdinalMatrix.matrix p q r s t u i) ≤ ![x, y, z] i) :
    Pattern p q r s t u x y z := by
  classical
  have he : ∀ i, S.sum (OrdinalMatrix.matrix p q r s t u i) =
      ∑ j : Fin 3, if j ∈ S then OrdinalMatrix.matrix p q r s t u i j else 0 := by
    intro i
    simp [Finset.sum_ite_mem]
  have h0 := hS 0
  have h1 := hS 1
  have h2 := hS 2
  simp only [he, Fin.sum_univ_three] at h0 h1 h2
  by_cases h₀ : (0 : Fin 3) ∈ S <;> by_cases h₁ : (1 : Fin 3) ∈ S <;>
    by_cases h₂ : (2 : Fin 3) ∈ S <;>
    simp [OrdinalMatrix.matrix, h₀, h₁, h₂] at h0 h1 h2
  · exact .s111 h0 (by linarith) (by linarith)
  · exact .s110 h0 h1 (by linarith)
  · exact .s101 h0 (by linarith) h2
  · exact .s100 h0 h1 h2
  · exact .s011 h0 h1 h2
  · exact .s010 h0 h1 h2
  · exact .s001 h0 h1 h2
  · exact .s000 h0 h1 h2

theorem exists_set_iff_not_bad {p q r s t u x y z : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    (∃ S : Finset (Fin 3), ∀ i,
      if i ∈ S then ![x, y, z] i ≤ S.sum (OrdinalMatrix.matrix p q r s t u i)
      else S.sum (OrdinalMatrix.matrix p q r s t u i) ≤ ![x, y, z] i) ↔
        ¬ Bad p q r s t u x y z := by
  constructor
  · rintro ⟨S, hS⟩
    exact (pattern_iff_not_bad hp hq hr hs ht hu).mp (pattern_of_set S hS)
  · intro h
    exact ((pattern_iff_not_bad hp hq hr hs ht hu).mpr h).exists_set

open CommonVertex OrdinalTranslations SymmetricTranslations

/-- Separating the self increment from the off-diagonal interactions. -/
theorem dot_shift_interaction {ι : Type*} [DecidableEq ι] (P : ι → Plank) (v : ι → ℝ × ℝ)
    (hself : ∀ i, dot (P i).u (v i) = (P i).hi - (P i).lo)
    (S : Finset ι) (i : ι) :
    dot (P i).u (shift v S) = S.sum (interaction P v i) +
      (if i ∈ S then (P i).hi - (P i).lo else 0) := by
  classical
  rw [dot_shift]
  have he : ∀ j, dot (P i).u (v j) = interaction P v i j +
      (if j = i then (P i).hi - (P i).lo else 0) := by
    intro j
    by_cases hij : i = j
    · subst j
      simp [interaction, hself]
    · simp [interaction, hij, Ne.symm hij]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  congr 1
  simp

/-- A pattern for the actual thresholds gives the designated exterior sides. -/
theorem exists_side_assignment (P : Fin 3 → Plank) (v : Fin 3 → ℝ × ℝ)
    (hself : ∀ i, dot (P i).u (v i) = (P i).hi - (P i).lo)
    (p q r s t u : ℝ)
    (hmatrix : ∀ i j, interaction P v i j = OrdinalMatrix.matrix p q r s t u i j)
    (a : ℝ × ℝ)
    (hpattern : Pattern p q r s t u
      ((P 0).lo - dot (P 0).u a) ((P 1).lo - dot (P 1).u a)
      ((P 2).lo - dot (P 2).u a)) :
    ∃ S : Finset (Fin 3),
      (∀ i ∈ S, (P i).hi ≤ dot (P i).u (a + shift v S)) ∧
      (∀ i ∉ S, dot (P i).u (a + shift v S) ≤ (P i).lo) := by
  classical
  obtain ⟨S, hS⟩ := hpattern.exists_set
  have hthreshold : ∀ i : Fin 3,
      ![(P 0).lo - dot (P 0).u a, (P 1).lo - dot (P 1).u a,
        (P 2).lo - dot (P 2).u a] i = (P i).lo - dot (P i).u a := by
    intro i
    fin_cases i <;> rfl
  have hdot : ∀ i, dot (P i).u (a + shift v S) =
      dot (P i).u a + S.sum (OrdinalMatrix.matrix p q r s t u i) +
        (if i ∈ S then (P i).hi - (P i).lo else 0) := by
    intro i
    have he : dot (P i).u (a + shift v S) =
        dot (P i).u a + dot (P i).u (shift v S) := by
      simp only [dot, Prod.fst_add, Prod.snd_add]
      ring
    rw [he, dot_shift_interaction P v hself]
    simp only [hmatrix, add_assoc]
  refine ⟨S, ?_, ?_⟩
  · intro i hi
    have h := hS i
    rw [if_pos hi, hthreshold] at h
    rw [hdot, if_pos hi]
    linarith
  · intro i hi
    have h := hS i
    rw [if_neg hi, hthreshold] at h
    rw [hdot, if_neg hi]
    linarith

end Quant.CyclicAssignment
