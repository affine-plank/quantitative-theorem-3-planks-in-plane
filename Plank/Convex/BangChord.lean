/- Bang's chord bound for explicit realized chords and unit normals.
Weighted sums of chord segments lie in the convex body; Bang's symmetric
sign lemma chooses a vertex of this translated zonotope outside all planks.
No common midpoint, orthogonality, or symmetry of the body is required. -/
module

public import ResearchFormalized.Ball1991
public import Mathlib.Analysis.Convex.Combination

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace

namespace Plank.Convex

/-- A covering by planks with unit normals has sum of halfwidth/chord-radius
at least one, for any chosen parallel chords contained in the convex body. -/
theorem sum_ge_one_of_realized_chord_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (hn : 0 < n) (K : Set E) (hK : Convex ℝ K)
    (c u : Fin n → E) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (hu : ∀ i, ‖u i‖ = 1)
    (hends : ∀ i, c i - r i • u i ∈ K ∧ c i + r i • u i ∈ K)
    (a w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ x ∈ K, ∃ i, |⟪x, u i⟫ - a i| ≤ w i) :
    1 ≤ ∑ i, w i / r i := by
  classical
  by_contra h
  have hS : ∑ i, w i / r i < 1 := lt_of_not_ge h
  let δ := 1 - ∑ i, w i / r i
  have hd : 0 < δ := sub_pos.mpr hS
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let lam : Fin n → ℝ := fun i => w i / r i + δ / n
  have hl (i : Fin n) : 0 ≤ lam i :=
    add_nonneg (div_nonneg (hw i) (hr i).le) (div_nonneg hd.le hnr.le)
  have hl1 : ∑ i, lam i = 1 := by
    dsimp [lam]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hf : (n : ℝ) * (δ / n) = δ := by field_simp
    rw [hf]
    dsimp [δ]
    ring
  let b : E := ∑ i, lam i • c i
  let H : Matrix (Fin n) (Fin n) ℝ := fun i j => ⟪u j, u i⟫
  have hsym : H.IsSymm := by
    ext i j
    exact real_inner_comm _ _
  have hdiag (i : Fin n) : H i i = 1 := by
    dsimp [H]
    rw [real_inner_self_eq_norm_sq, hu i]
    norm_num
  obtain ⟨ε, he, hbang⟩ := Ball1991.lemma3_bang H hsym hdiag
    (fun i => a i - ⟪b, u i⟫) (fun i => lam i * r i)
    (fun i => mul_nonneg (hl i) (hr i).le)
  let z : Fin n → E := fun i => c i + (ε i * r i) • u i
  let x : E := ∑ i, lam i • z i
  have hz (i : Fin n) : z i ∈ K := by
    rcases he i with hi | hi
    · simpa [z, hi] using (hends i).2
    · simpa [z, hi, sub_eq_add_neg] using (hends i).1
  have hx : x ∈ K := hK.sum_mem (fun i _ => hl i) hl1 (fun i _ => hz i)
  have hxeq : x = b + ∑ j, (ε j * (lam j * r j)) • u j := by
    dsimp [x, z, b]
    simp only [smul_add, Finset.sum_add_distrib, smul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  obtain ⟨i, hi⟩ := hcover x hx
  have hinner : ⟪x, u i⟫ - a i =
      (∑ j, H i j * ε j * (lam j * r j)) - (a i - ⟪b, u i⟫) := by
    rw [hxeq]
    simp only [inner_add_left, sum_inner, real_inner_smul_left]
    dsimp [H]
    have heq : (∑ j, (ε j * (lam j * r j)) * ⟪u j, u i⟫) =
        ∑ j, ⟪u j, u i⟫ * ε j * (lam j * r j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    ring
  have hstrict : w i < lam i * r i := by
    have hpos : 0 < (δ / n) * r i := mul_pos (div_pos hd hnr) (hr i)
    dsimp [lam]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt (hr i))]
    linarith
  rw [hinner] at hi
  linarith [hbang i]

end Plank.Convex

/-- info: 'Plank.Convex.sum_ge_one_of_realized_chord_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.sum_ge_one_of_realized_chord_cover

namespace Plank.Convex

/-- The chord parameter used by the research scaffold scales inversely
with the normal: for [-1,1] and u=1/2 its value is four. -/
theorem half_normal_chord_parameter :
    sSup {t : ℝ | 0 ≤ t ∧ ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      ∃ y ∈ Set.Icc (-1 : ℝ) 1, x - y = t * (1/2)} = 4 := by
  let T := {t : ℝ | 0 ≤ t ∧ ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      ∃ y ∈ Set.Icc (-1 : ℝ) 1, x - y = t * (1/2)}
  have h4 : (4 : ℝ) ∈ T := ⟨by norm_num, 1, by norm_num, -1, by norm_num, by norm_num⟩
  have hb : ∀ t ∈ T, t ≤ 4 := by
    rintro t ⟨_, x, hx, y, hy, hxy⟩
    linarith [hx.2, hy.1]
  exact le_antisymm (csSup_le ⟨4, h4⟩ hb) (le_csSup ⟨4, hb⟩ h4)

/-- Explicit scaling obstruction to dividing raw functional width by the
chord parameter without a squared normal-norm factor. -/
theorem scaled_normal_counterexample :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, -(1/2) ≤ x * (1/2) ∧ x * (1/2) ≤ 1/2) ∧
    ((1/2 : ℝ) - (-(1/2))) /
      sSup {t : ℝ | 0 ≤ t ∧ ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        ∃ y ∈ Set.Icc (-1 : ℝ) 1, x - y = t * (1/2)} < 1 := by
  constructor
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · rw [half_normal_chord_parameter]
    norm_num

end Plank.Convex

/-- info: 'Plank.Convex.scaled_normal_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.scaled_normal_counterexample
