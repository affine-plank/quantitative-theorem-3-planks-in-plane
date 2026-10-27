module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace SixBoundaries

abbrev Coordinates := Fin 3 → ℝ

def triangle (x : Coordinates) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

def level (d x : Coordinates) (i : Fin 3) : ℝ := d i * x i + x (i + 2)

def covers (d L G : Coordinates) : Prop :=
  ∀ x, triangle x → ∃ i, L i ≤ level d x i ∧ level d x i ≤ 1 - G i

def coversBoundary (d L G : Coordinates) : Prop :=
  ∀ x, triangle x → (∃ i, x i = 0) →
    ∃ i, L i ≤ level d x i ∧ level d x i ≤ 1 - G i

theorem indices (i j : Fin 3) : j = i ∨ j = i + 1 ∨ j = i + 2 := by
  revert i j; decide

theorem sum_cyclic (x : Coordinates) (i : Fin 3) :
    ∑ j, x j = x i + x (i + 1) + x (i + 2) := by
  have h := Equiv.sum_comp (Equiv.addLeft i) x
  simpa only [Fin.sum_univ_three, Equiv.coe_addLeft, add_zero] using h.symm

theorem add12 (i : Fin 3) : i + 1 + 2 = i := by omega
theorem add21 (i : Fin 3) : i + 2 + 1 = i := by omega
theorem add22 (i : Fin 3) : i + 2 + 2 = i + 1 := by omega

def bridges (d L G : Coordinates) (i : Fin 3) : Prop :=
  L (i + 1) + d (i + 1) * L i ≤ d (i + 1) ∧
    G (i + 2) + (1 - d (i + 2)) * G i ≤ 1 - d (i + 2)

def meets (d L G : Coordinates) (i : Fin 3) : Prop :=
  L (i + 1) / d (i + 1) + G (i + 2) / (1 - d (i + 2)) ≤ 1

private theorem intervals_iff {A B C D : ℝ} (hA : 0 ≤ A) (hB : B ≤ 1) :
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 → s ≤ A ∨ B ≤ s ∨ (C ≤ s ∧ s ≤ D)) ↔
      B ≤ A ∨ (C ≤ A ∧ B ≤ D) := by
  constructor
  · intro hc
    rcases le_or_gt B A with h | h
    · exact Or.inl h
    have hgap : Set.Ioo A B ⊆ Set.Icc C D := fun s ⟨hsA, hsB⟩ =>
      ((hc s (hA.trans hsA.le) (hsB.le.trans hB)).resolve_left hsA.not_ge).resolve_left hsB.not_ge
    have hclosed := closure_minimal hgap isClosed_Icc
    rw [closure_Ioo h.ne, Set.Icc_subset_Icc_iff h.le] at hclosed
    exact Or.inr hclosed
  · intro h s _ _
    by_cases hsA : s ≤ A
    · exact Or.inl hsA
    by_cases hsB : B ≤ s
    · exact Or.inr (Or.inl hsB)
    rcases h with h | ⟨hC, hD⟩
    · exact (hsA ((le_of_not_ge hsB).trans h)).elim
    · exact Or.inr (Or.inr ⟨hC.trans (le_of_not_ge hsA), (le_of_not_ge hsB).trans hD⟩)

def sidePoint (i : Fin 3) (s : ℝ) : Coordinates :=
  fun k => ![0, 1 - s, s] (k - i)

private theorem sidePoint_triangle (i : Fin 3) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    triangle (sidePoint i s) := by
  constructor
  · intro k
    rcases indices i k with hk | hk | hk <;> subst k <;> simp [sidePoint, hs0, hs1]
  · rw [sum_cyclic _ i]
    simp [sidePoint]

private theorem sidePoint_eq {x : Coordinates} (hx : triangle x) {i : Fin 3}
    (hi : x i = 0) : sidePoint i (x (i + 2)) = x := by
  have hs := (sum_cyclic x i).symm.trans hx.2
  ext k
  rcases indices i k with hk | hk | hk
  · subst k; simp [sidePoint, hi]
  · subst k; simp [sidePoint]; linarith
  · subst k; simp [sidePoint]

private theorem sidePoint_covered_iff {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hL : ∀ i, L i ≤ d i) (hG : ∀ i, G i ≤ 1 - d i)
    (i : Fin 3) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∃ k, L k ≤ level d (sidePoint i s) k ∧ level d (sidePoint i s) k ≤ 1 - G k) ↔
      s ≤ 1 - L (i + 1) / d (i + 1) ∨ G (i + 2) / (1 - d (i + 2)) ≤ s ∨
        (L i ≤ s ∧ s ≤ 1 - G i) := by
  have h0 : level d (sidePoint i s) i = s := by simp [level, sidePoint]
  have h1 : level d (sidePoint i s) (i + 1) = d (i + 1) * (1 - s) := by
    simp [level, sidePoint, add12]
  have h2 : level d (sidePoint i s) (i + 2) = 1 - (1 - d (i + 2)) * s := by
    simp [level, sidePoint, add22]
    ring
  have he : 0 < 1 - d (i + 2) := sub_pos.mpr (hd1 _)
  have hlo : L (i + 1) ≤ d (i + 1) * (1 - s) ↔ s ≤ 1 - L (i + 1) / d (i + 1) := by
    rw [mul_comm (d (i + 1)), ← div_le_iff₀ (hd0 _)]
    constructor <;> intro h <;> linarith
  have hhi : 1 - (1 - d (i + 2)) * s ≤ 1 - G (i + 2) ↔ G (i + 2) / (1 - d (i + 2)) ≤ s := by
    rw [div_le_iff₀ he]
    constructor <;> intro h <;> nlinarith only [h]
  constructor
  · rintro ⟨k, hk0, hk1⟩
    rcases indices i k with hk | hk | hk <;> subst k
    · exact Or.inr (Or.inr (by simpa only [h0] using And.intro hk0 hk1))
    · exact Or.inl (hlo.mp (by simpa only [h1] using hk0))
    · exact Or.inr (Or.inl (hhi.mp (by simpa only [h2] using hk1)))
  · rintro (h | h | h)
    · refine ⟨i + 1, by rw [h1]; exact hlo.mpr h, ?_⟩
      rw [h1]
      have := mul_nonneg (hd0 (i + 1)).le hs0
      linarith only [this, hG (i + 1)]
    · refine ⟨i + 2, ?_, by rw [h2]; exact hhi.mpr h⟩
      rw [h2]
      have := mul_le_mul_of_nonneg_left hs1 he.le
      linarith only [this, hL (i + 2)]
    · exact ⟨i, by simpa only [h0] using h⟩

/-- On each side the endpoint intervals meet, or the third interval bridges
their gap. These are respectively one and two linear conditions in `L, G`. -/
theorem boundary_iff_side_alternatives {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hL : ∀ i, L i ≤ d i) (hG : ∀ i, G i ≤ 1 - d i) :
    coversBoundary d L G ↔ ∀ i, meets d L G i ∨ bridges d L G i := by
  have hside (i : Fin 3) :
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        ∃ k, L k ≤ level d (sidePoint i s) k ∧ level d (sidePoint i s) k ≤ 1 - G k) ↔
      meets d L G i ∨ bridges d L G i := by
    have he : 0 < 1 - d (i + 2) := sub_pos.mpr (hd1 _)
    have hLdiv : L (i + 1) / d (i + 1) ≤ 1 :=
      (div_le_one (hd0 _)).mpr (hL _)
    have hGdiv : G (i + 2) / (1 - d (i + 2)) ≤ 1 :=
      (div_le_one he).mpr (hG _)
    have htrace :
        (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          ∃ k, L k ≤ level d (sidePoint i s) k ∧ level d (sidePoint i s) k ≤ 1 - G k) ↔
        (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          s ≤ 1 - L (i + 1) / d (i + 1) ∨ G (i + 2) / (1 - d (i + 2)) ≤ s ∨
            (L i ≤ s ∧ s ≤ 1 - G i)) := by
      constructor <;> intro h s hs0 hs1
      · exact (sidePoint_covered_iff hd0 hd1 hL hG i hs0 hs1).mp (h s hs0 hs1)
      · exact (sidePoint_covered_iff hd0 hd1 hL hG i hs0 hs1).mpr (h s hs0 hs1)
    rw [htrace]
    rw [intervals_iff (by linarith : 0 ≤ 1 - L (i + 1) / d (i + 1)) hGdiv]
    have hlo : L i ≤ 1 - L (i + 1) / d (i + 1) ↔
        L (i + 1) + d (i + 1) * L i ≤ d (i + 1) := by
      have hdiv : L (i + 1) / d (i + 1) ≤ 1 - L i ↔
          L (i + 1) ≤ (1 - L i) * d (i + 1) := div_le_iff₀ (hd0 _)
      constructor <;> intro h
      · have := hdiv.mp (by linarith)
        nlinarith only [this]
      · have := hdiv.mpr (by nlinarith only [h])
        linarith only [this]
    have hhi : G (i + 2) / (1 - d (i + 2)) ≤ 1 - G i ↔
        G (i + 2) + (1 - d (i + 2)) * G i ≤ 1 - d (i + 2) := by
      rw [div_le_iff₀ he]
      constructor <;> intro h <;> nlinarith only [h]
    rw [hlo, hhi]
    dsimp [meets, bridges]
    constructor <;> rintro (h | h)
    · exact Or.inl (by linarith only [h])
    · exact Or.inr h
    · exact Or.inl (by linarith only [h])
    · exact Or.inr h
  constructor
  · intro hc i
    apply (hside i).mp
    intro s hs0 hs1
    exact hc _ (sidePoint_triangle i hs0 hs1) ⟨i, by simp [sidePoint]⟩
  · intro hc x hx hboundary
    obtain ⟨i, hi⟩ := hboundary
    have hs : x (i + 2) ≤ 1 := by
      have hsum := (sum_cyclic x i).symm.trans hx.2
      linarith only [hsum, hx.1 i, hx.1 (i + 1)]
    simpa only [sidePoint_eq hx hi] using (hside i).mpr (hc i) _ (hx.1 _) hs

end SixBoundaries
