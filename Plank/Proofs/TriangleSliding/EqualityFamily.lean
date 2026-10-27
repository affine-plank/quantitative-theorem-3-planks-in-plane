/- The width-one covers remaining after shrinking form a two-parameter family.
This geometric description is separate from the proof of the inequality. -/
module
public import Plank.Proofs.TriangleSliding.WidthBound

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace SixBoundaries.Rigidity

theorem width_one_equalities {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hB : ∀ i, bridges d L G i) (hs : ∑ i, (1 - L i - G i) = 1) :
    (∀ i, L i + d i * L (i + 2) = d i) ∧
    (∀ i, G i + (1 - d i) * G (i + 1) = 1 - d i) ∧
    d 0 * d 1 * d 2 = (1 - d 0) * (1 - d 1) * (1 - d 2) := by
  let P := 1 + d 0 * d 1 * d 2
  let Q := 1 + (1 - d 0) * (1 - d 1) * (1 - d 2)
  have hP : 0 < P := add_pos zero_lt_one (mul_pos (mul_pos (hd0 0) (hd0 1)) (hd0 2))
  have hQ : 0 < Q := add_pos zero_lt_one
    (mul_pos (mul_pos (sub_pos.mpr (hd1 0)) (sub_pos.mpr (hd1 1)))
      (sub_pos.mpr (hd1 2)))
  have hA (i : Fin 3) : 0 < lowerWeight d i :=
    add_pos (sub_pos.mpr (hd1 _)) (mul_pos (hd0 _) (hd0 _))
  have hB' (i : Fin 3) : 0 < upperWeight d i := add_pos (hd0 _)
    (mul_pos (sub_pos.mpr (hd1 _)) (sub_pos.mpr (hd1 _)))
  have hL (i : Fin 3) : 0 ≤ d i - L i - d i * L (i + 2) := by
    have h := (hB (i + 2)).1
    rw [add21] at h
    linarith only [h]
  have hG (i : Fin 3) : 0 ≤ 1 - d i - G i - (1 - d i) * G (i + 1) := by
    have h := (hB (i + 1)).2
    rw [add12] at h
    linarith only [h]
  have hLs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hA i).le (hL i))
  have hGs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hB' i).le (hG i))
  have h := bridge_identity d L G
  change P * Q * (∑ i, (1 - L i - G i) - 1) = _ at h
  rw [hs, sub_self, mul_zero] at h
  have hqp := mul_nonneg hQ.le hLs
  have hpq := mul_nonneg hP.le hGs
  have hzpair := (add_eq_zero_iff_of_nonneg
    (add_nonneg (sq_nonneg (P - Q)) hqp) hpq).mp h.symm
  have hzparts := (add_eq_zero_iff_of_nonneg (sq_nonneg (P - Q)) hqp).mp hzpair.1
  have hz : (P - Q) ^ 2 = 0 := hzparts.1
  have hzL : ∑ i, lowerWeight d i * (d i - L i - d i * L (i + 2)) = 0 :=
    (mul_eq_zero.mp hzparts.2).resolve_left hQ.ne'
  have hzG : ∑ i, upperWeight d i * (1 - d i - G i - (1 - d i) * G (i + 1)) = 0 :=
    (mul_eq_zero.mp hzpair.2).resolve_left hP.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hA j).le (hL j))).mp hzL i (Finset.mem_univ i)
    have ht' := (mul_eq_zero.mp ht).resolve_left (hA i).ne'
    linarith only [ht']
  · intro i
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hB' j).le (hG j))).mp hzG i (Finset.mem_univ i)
    have ht' := (mul_eq_zero.mp ht).resolve_left (hB' i).ne'
    linarith only [ht']
  · have he : P = Q := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    dsimp [P, Q] at he
    linarith only [he]

/-- One contact on a side is on two plank boundaries and beyond the third. -/
theorem equalities_not_open_cover {d L G : Coordinates}
    (hd1 : ∀ i, d i < 1) (hL0 : 0 ≤ L 0) (hL1 : L 0 ≤ 1)
    (hr0 : 0 ≤ 1 - L 0 - G 0)
    (hL : ∀ i, L i + d i * L (i + 2) = d i)
    (hG : ∀ i, G i + (1 - d i) * G (i + 1) = 1 - d i) :
    ¬ (∀ x, triangle x → ∃ i, L i < level d x i ∧ level d x i < 1 - G i) := by
  let x : Coordinates := ![0, 1 - L 0, L 0]
  have hx : triangle x := by
    constructor
    · intro i
      fin_cases i
      · exact le_rfl
      · exact sub_nonneg.mpr hL1
      · exact hL0
    · simp [x, Fin.sum_univ_three]
  intro hc
  obtain ⟨i, hlo, hhi⟩ := hc x hx
  fin_cases i
  · simp [level, x] at hlo
  · have h := hL 1
    dsimp [level, x] at hlo h
    nlinarith only [h, hlo]
  · have h := hG 2
    have hp := mul_nonneg (sub_pos.mpr (hd1 2)).le hr0
    dsimp [level, x] at hhi h
    nlinarith only [h, hhi, hp]

theorem width_one_bridges {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hL0 : ∀ i, 0 < L i) (hL : ∀ i, L i ≤ d i)
    (hG0 : ∀ i, 0 < G i) (hG : ∀ i, G i ≤ 1 - d i)
    (hr0 : ∀ i, 0 < 1 - L i - G i)
    (hs : ∑ i, (1 - L i - G i) = 1) (hc : covers d L G) :
    ∀ i, bridges d L G i := by
  have ha := (boundary_iff_side_alternatives hd0 hd1 hL hG).mp
    (show coversBoundary d L G from fun x hx _ => hc x hx)
  rcases boundary_cases hd0 hd1 hL0 hG0 hs.le ha with hM | hB
  · have hpair (i : Fin 3) : (1 - L i - G i) + (1 - L (i + 1) - G (i + 1)) < 1 := by
      have ht := hs
      rw [sum_cyclic _ i] at ht
      linarith only [ht, hr0 (i + 2)]
    exact (all_meet_not_cover hd0 hd1 (fun i => (hr0 i).le) hM hs.le hpair hc).elim
  · exact hB


/-- Three bridge conditions already cover the whole triangle. Two uncovered
planks would have to be missed on the same side, which a bridge forbids. -/
theorem bridges_cover {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hB : ∀ i, bridges d L G i) : covers d L G := by
  intro x hx
  by_contra! hn
  have hm (i : Fin 3) : level d x i < L i ∨ 1 - G i < level d x i := by
    by_cases hi : L i ≤ level d x i
    · exact Or.inr (hn i hi)
    · exact Or.inl (lt_of_not_ge hi)
  have lower (i : Fin 3) (hi : level d x i < L i)
      (hj : level d x (i + 1) < L (i + 1)) : False := by
    have ht := (sum_cyclic x i).symm.trans hx.2
    have he : level d x (i + 1) + d (i + 1) * level d x i =
        d (i + 1) + (1 - d (i + 1) + d (i + 1) * d i) * x i := by
      simp only [level, add12]
      linear_combination d (i + 1) * ht
    have hp := mul_lt_mul_of_pos_left hi (hd0 (i + 1))
    have hc := mul_nonneg (add_nonneg (sub_pos.mpr (hd1 (i + 1))).le
      (mul_pos (hd0 (i + 1)) (hd0 i)).le) (hx.1 i)
    linarith only [he, hp, hj, hc, (hB i).1]
  have upper (i : Fin 3) (hi : 1 - G i < level d x i)
      (hj : 1 - G (i + 2) < level d x (i + 2)) : False := by
    have ht := (sum_cyclic x i).symm.trans hx.2
    have he : (1 - level d x (i + 2)) + (1 - d (i + 2)) * (1 - level d x i) =
        1 - d (i + 2) + (d (i + 2) + (1 - d (i + 2)) * (1 - d i)) * x i := by
      simp only [level, add22]
      linear_combination -ht
    have hp := mul_lt_mul_of_pos_left hi (sub_pos.mpr (hd1 (i + 2)))
    have hc := mul_nonneg (add_nonneg (hd0 (i + 2)).le
      (mul_pos (sub_pos.mpr (hd1 (i + 2))) (sub_pos.mpr (hd1 i))).le) (hx.1 i)
    nlinarith only [he, hp, hj, hc, (hB i).2]
  rcases hm 0 with h0 | h0 <;> rcases hm 1 with h1 | h1 <;> rcases hm 2 with h2 | h2
  · exact lower 0 h0 h1
  · exact lower 0 h0 h1
  · exact lower 2 h2 h0
  · exact upper 2 h2 h1
  · exact lower 1 h1 h2
  · exact upper 0 h0 h2
  · exact upper 1 h1 h0
  · exact upper 0 h0 h2

/-- In the hexagonal equality case, the three widths determine every boundary
and every direction in these normalized coordinates. -/
theorem equalities_width_parameters {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i)
    (hL : ∀ i, L i + d i * L (i + 2) = d i)
    (hG : ∀ i, G i + (1 - d i) * G (i + 1) = 1 - d i)
    (hprod : d 0 * d 1 * d 2 = (1 - d 0) * (1 - d 1) * (1 - d 2))
    (hs : ∑ i, (1 - L i - G i) = 1) :
    ∀ i, L i = 1 - L (i + 1) - G (i + 1) ∧
      G i = 1 - L (i + 2) - G (i + 2) ∧
      d i * (L i + G i) = L i := by
  let P := 1 + d 0 * d 1 * d 2
  have hP : P ≠ 0 := (add_pos zero_lt_one
    (mul_pos (mul_pos (hd0 0) (hd0 1)) (hd0 2))).ne'
  have hp (i : Fin 3) : d 0 * d 1 * d 2 = d i * d (i + 1) * d (i + 2) := by
    fin_cases i <;> dsimp <;> ring
  have hq (i : Fin 3) : d 0 * d 1 * d 2 =
      (1 - d i) * (1 - d (i + 1)) * (1 - d (i + 2)) := by
    rw [hprod]
    fin_cases i <;> dsimp <;> ring
  have match_sides (i : Fin 3) : L i = G (i + 2) := by
    have h0 := hL i
    have h1 := hL (i + 1)
    have h2 := hL (i + 2)
    simp only [add12, add22] at h1 h2
    have lower : P * (1 - L i) = 1 - d i + d i * d (i + 2) := by
      dsimp [P]
      rw [hp i]
      linear_combination -h0 + d i * h2 - d i * d (i + 2) * h1
    have g0 := hG i
    have g1 := hG (i + 1)
    have g2 := hG (i + 2)
    have hadd : i + 1 + 1 = i + 2 := by omega
    simp only [hadd, add21] at g1 g2
    have upper : P * (1 - G (i + 2)) = 1 - d i + d i * d (i + 2) := by
      dsimp [P]
      rw [hq i]
      linear_combination -g2 + (1 - d (i + 2)) * g0 -
        (1 - d (i + 2)) * (1 - d i) * g1
    have hh := mul_left_cancel₀ hP (lower.trans upper.symm)
    linarith only [hh]
  intro i
  have m0 := match_sides i
  have m1 := match_sides (i + 1)
  have m2 := match_sides (i + 2)
  simp only [add12, add22] at m1 m2
  have ht := hs
  rw [sum_cyclic _ i] at ht
  have hl := hL i
  refine ⟨by linarith only [ht, m0, m1, m2],
    by linarith only [ht, m0, m1, m2], ?_⟩
  have hsum : L i + G i + L (i + 2) = 1 := by linarith only [ht, m0, m1, m2]
  linear_combination -hl + d i * hsum

theorem width_one_iff {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hL0 : ∀ i, 0 < L i) (hL : ∀ i, L i ≤ d i)
    (hG0 : ∀ i, 0 < G i) (hG : ∀ i, G i ≤ 1 - d i)
    (hr0 : ∀ i, 0 < 1 - L i - G i) :
    (covers d L G ∧ ∑ i, (1 - L i - G i) = 1) ↔
    ((∀ i, L i + d i * L (i + 2) = d i) ∧
      (∀ i, G i + (1 - d i) * G (i + 1) = 1 - d i) ∧
      d 0 * d 1 * d 2 = (1 - d 0) * (1 - d 1) * (1 - d 2)) := by
  constructor
  · rintro ⟨hc, hs⟩
    exact width_one_equalities hd0 hd1
      (width_one_bridges hd0 hd1 hL0 hL hG0 hG hr0 hs hc) hs
  · rintro ⟨hLe, hGe, hp⟩
    constructor
    · apply bridges_cover hd0 hd1
      intro i
      have hl := hLe (i + 1)
      have hg := hGe (i + 2)
      simp only [add12, add21] at hl hg
      exact ⟨hl.le, hg.le⟩
    · have h := bridge_identity d L G
      have hl (i : Fin 3) : d i - L i - d i * L (i + 2) = 0 := by
        linarith only [hLe i]
      have hg (i : Fin 3) : 1 - d i - G i - (1 - d i) * G (i + 1) = 0 := by
        linarith only [hGe i]
      dsimp only at h
      simp only [hl, hg, mul_zero, Finset.sum_const_zero, add_zero, hp, sub_self, zero_pow
        (by decide : 2 ≠ 0)] at h
      have hpos : 0 < 1 + (1 - d 0) * (1 - d 1) * (1 - d 2) := add_pos zero_lt_one
        (mul_pos (mul_pos (sub_pos.mpr (hd1 0)) (sub_pos.mpr (hd1 1)))
          (sub_pos.mpr (hd1 2)))
      have hz := (mul_eq_zero.mp h).resolve_left (mul_pos hpos hpos).ne'
      linarith only [hz]

/-- The equality family has only two free parameters: three positive widths
whose sum is one. -/
theorem width_one_parameters {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hL0 : ∀ i, 0 < L i) (hL : ∀ i, L i ≤ d i)
    (hG0 : ∀ i, 0 < G i) (hG : ∀ i, G i ≤ 1 - d i)
    (hr0 : ∀ i, 0 < 1 - L i - G i)
    (hc : covers d L G) (hs : ∑ i, (1 - L i - G i) = 1) :
    let r (i : Fin 3) := 1 - L i - G i
    ∀ i, L i = r (i + 1) ∧ G i = r (i + 2) ∧ d i * (1 - r i) = r (i + 1) := by
  obtain ⟨hl, hg, hp⟩ := (width_one_iff hd0 hd1 hL0 hL hG0 hG hr0).mp ⟨hc, hs⟩
  have ht := equalities_width_parameters hd0 hl hg hp hs
  intro r i
  obtain ⟨hi, hj, hk⟩ := ht i
  refine ⟨hi, hj, ?_⟩
  dsimp [r]
  linear_combination hk + hi

/-- Every triple of positive widths summing to one gives an equality cover. -/
theorem width_parameters_tight (r : Coordinates)
    (hr : ∀ i, 0 < r i) (hs : ∑ i, r i = 1) :
    let d (i : Fin 3) := r (i + 1) / (1 - r i)
    covers d (fun i => r (i + 1)) (fun i => r (i + 2)) ∧
      ∑ i, (1 - r (i + 1) - r (i + 2)) = 1 := by
  intro d
  have hsum (i : Fin 3) : r i + r (i + 1) + r (i + 2) = 1 := by
    rw [← sum_cyclic r i]
    exact hs
  have hden (i : Fin 3) : 0 < 1 - r i := by
    linarith only [hsum i, hr (i + 1), hr (i + 2)]
  have hd0 (i : Fin 3) : 0 < d i := div_pos (hr _) (hden i)
  have hd1 (i : Fin 3) : d i < 1 := (div_lt_one (hden i)).mpr (by
    linarith only [hsum i, hr (i + 2)])
  have hrow (i : Fin 3) : d i * (1 - r i) = r (i + 1) := div_mul_cancel₀ _ (hden i).ne'
  have hlo (i : Fin 3) : r (i + 1) + d i * r i = d i := by
    linear_combination -hrow i
  have hgap (i : Fin 3) : r (i + 2) + (1 - d i) * r i = 1 - d i := by
    linear_combination hsum i + hrow i
  constructor
  · apply bridges_cover hd0 hd1
    intro i
    have hl := hlo (i + 1)
    have hg := hgap (i + 2)
    have hadd : i + 1 + 1 = i + 2 := by omega
    simpa only [bridges, hadd, add12, add21, add22] using And.intro hl.le hg.le
  · simp only [Fin.sum_univ_three] at hs ⊢
    dsimp
    linarith only [hs]

end SixBoundaries.Rigidity
