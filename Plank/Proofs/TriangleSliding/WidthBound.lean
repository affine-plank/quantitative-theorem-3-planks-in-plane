/- Covering the sides leaves two cases: three bridges give a nonnegative
identity; three meetings leave a hole if the total width is too small. -/
module
public import Plank.Proofs.TriangleSliding.BridgeIdentity

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace SixBoundaries

theorem lower_margin_lt_next_width {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1) (i : Fin 3)
    (hLi : 0 < L i) (hb : bridges d L G i) (hc : meets d L G (i + 2)) :
    L i < 1 - L (i + 1) - G (i + 1) := by
  simp only [meets, add21, add22] at hc
  have hratio : L i < L i / d i :=
    (lt_div_iff₀ (hd0 i)).mpr (mul_lt_of_lt_one_right hLi (hd1 i))
  have hh : G (i + 1) / (1 - d (i + 1)) < 1 - L i := by linarith only [hc, hratio]
  have hh' := (div_lt_iff₀ (sub_pos.mpr (hd1 (i + 1)))).mp hh
  nlinarith only [hh', hb.1]

theorem upper_margin_lt_prev_width {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1) (i : Fin 3)
    (hGi : 0 < G i) (hb : bridges d L G i) (hc : meets d L G (i + 1)) :
    G i < 1 - L (i + 2) - G (i + 2) := by
  have hadd : i + 1 + 1 = i + 2 := by omega
  simp only [meets, hadd, add12] at hc
  have hratio : G i < G i / (1 - d i) :=
    (lt_div_iff₀ (sub_pos.mpr (hd1 i))).mpr
      (mul_lt_of_lt_one_right hGi (by linarith only [hd0 i]))
  have hh : L (i + 2) / d (i + 2) < 1 - G i := by linarith only [hc, hratio]
  have hh' := (div_lt_iff₀ (hd0 (i + 2))).mp hh
  nlinarith only [hh', hb.2]

theorem one_bridge_strict {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hL0 : ∀ i, 0 < L i) (hG0 : ∀ i, 0 < G i) (i : Fin 3)
    (hb : bridges d L G i) (hc1 : meets d L G (i + 1)) (hc2 : meets d L G (i + 2)) :
    1 < ∑ j, (1 - L j - G j) := by
  have h1 := lower_margin_lt_next_width hd0 hd1 i (hL0 i) hb hc2
  have h2 := upper_margin_lt_prev_width hd0 hd1 i (hG0 i) hb hc1
  rw [sum_cyclic _ i]
  linarith only [h1, h2]

theorem two_bridges_strict {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hL0 : ∀ i, 0 < L i) (hG0 : ∀ i, 0 < G i) (i : Fin 3)
    (hb0 : bridges d L G i) (hb1 : bridges d L G (i + 1)) (hc : meets d L G (i + 2)) :
    1 < ∑ j, (1 - L j - G j) := by
  have h1 := lower_margin_lt_next_width hd0 hd1 i (hL0 i) hb0 hc
  have hadd : i + 1 + 1 = i + 2 := by omega
  have h0 := upper_margin_lt_prev_width hd0 hd1 (i + 1) (hG0 (i + 1)) hb1
    (by simpa only [hadd] using hc)
  rw [add12] at h0
  have h := hb1.1
  simp only [hadd] at h
  have h2 : d (i + 2) * L (i + 1) + (1 - d (i + 2)) * G i ≤
      1 - L (i + 2) - G (i + 2) := by linarith only [h, hb0.2]
  rw [sum_cyclic _ i]
  have hp := mul_lt_mul_of_pos_left h1 (sub_pos.mpr (hd1 (i + 2)))
  have hq := mul_lt_mul_of_pos_left h0 (hd0 (i + 2))
  nlinarith only [hp, hq, h2]

/-- If every pair of widths sums to less than one, meeting on all sides
leaves a hole whenever the total is at most one. -/
theorem all_meet_legs_not_cover {d u v : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hr0 : ∀ i, 0 ≤ d i * u i + (1 - d i) * v i)
    (hM : ∀ i, 1 ≤ u (i + 1) + v (i + 2))
    (hs : ∑ i, (d i * u i + (1 - d i) * v i) ≤ 1)
    (hpair : ∀ i, (d i * u i + (1 - d i) * v i) +
      (d (i + 1) * u (i + 1) + (1 - d (i + 1)) * v (i + 1)) < 1) :
    ¬ covers d (fun i => d i * (1 - u i))
      (fun i => (1 - d i) * (1 - v i)) := by
  let r (i : Fin 3) := d i * u i + (1 - d i) * v i
  have hU (i : Fin 3) (h : u i ≤ v i) : u i ≤ r i := by
    have := mul_nonneg (sub_pos.mpr (hd1 i)).le (sub_nonneg.mpr h)
    dsimp [r]
    nlinarith only [this]
  have hV (i : Fin 3) (h : v i ≤ u i) : v i ≤ r i := by
    have := mul_nonneg (hd0 i).le (sub_nonneg.mpr h)
    dsimp [r]
    nlinarith only [this]
  let ε := (1 - ∑ i, r i) / 3
  have hε : 0 ≤ ε := div_nonneg (sub_nonneg.mpr hs) (by norm_num)
  have hsum (i : Fin 3) : r i + r (i + 1) + r (i + 2) + 3 * ε = 1 := by
    rw [← sum_cyclic r i]
    dsimp [ε]
    ring
  have hx (k : Fin 3) : triangle (fun i => r (i + k) + ε) := by
    refine ⟨fun i => add_nonneg (hr0 _) hε, ?_⟩
    have he := Equiv.sum_comp (Equiv.addRight k) r
    simp only [Equiv.coe_addRight] at he
    rw [Finset.sum_add_distrib, he]
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [ε]
    ring
  have hswitch (i : Fin 3) (h : u i ≤ v i) (h' : v (i + 1) ≤ u (i + 1)) : False := by
    have hm := hM (i + 2)
    rw [add21, add22] at hm
    linarith only [hm, hU i h, hV (i + 1) h', hpair i]
  have hchoice : (∀ i, u i < v i) ∨ (∀ i, v i < u i) := by
    by_cases h : ∃ i, u i ≤ v i
    · obtain ⟨i, hi⟩ := h
      have hnext (j : Fin 3) (hj : u j ≤ v j) : u (j + 1) < v (j + 1) :=
        lt_of_not_ge (fun hn => hswitch j hj hn)
      have h1 := hnext i hi
      have h2 : u (i + 2) < v (i + 2) := by
        simpa only [add_assoc, show (1 : Fin 3) + 1 = 2 by decide] using hnext (i + 1) h1.le
      have h0 : u i < v i := by simpa only [add21] using hnext (i + 2) h2.le
      exact Or.inl (fun j => by rcases indices i j with rfl | rfl | rfl <;> assumption)
    · exact Or.inr (fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩))
  intro hc
  rcases hchoice with hchoice | hchoice
  · have hUr (i : Fin 3) : u i < r i := by
      have := mul_pos (sub_pos.mpr (hd1 i)) (sub_pos.mpr (hchoice i))
      dsimp [r]
      nlinarith only [this]
    let x (i : Fin 3) := r (i + 2) + ε
    obtain ⟨i, hi, _⟩ := hc x (hx 2)
    have hm := hM (i + 1)
    have hadd : i + 1 + 1 = i + 2 := by omega
    rw [hadd, add12] at hm
    have hside : 1 < r (i + 2) + v i := by linarith only [hm, hUr (i + 2)]
    have hp := mul_pos (sub_pos.mpr (hd1 i)) (sub_pos.mpr hside)
    simp only [level, x, add22] at hi
    have ht := hsum i
    dsimp [r] at hi hp ht
    have hε' := mul_nonneg (show 0 ≤ 2 - d i by linarith only [hd1 i]) hε
    nlinarith only [hi, hp, ht, hε']
  · have hVr (i : Fin 3) : v i < r i := by
      have := mul_pos (hd0 i) (sub_pos.mpr (hchoice i))
      dsimp [r]
      nlinarith only [this]
    let x (i : Fin 3) := r (i + 1) + ε
    obtain ⟨i, _, hi⟩ := hc x (hx 1)
    have hm := hM (i + 2)
    rw [add21, add22] at hm
    have hside : 1 < u i + r (i + 1) := by linarith only [hm, hVr (i + 1)]
    have hp := mul_pos (hd0 i) (sub_pos.mpr hside)
    simp only [level, x, add21] at hi
    have ht := hsum i
    dsimp [r] at hi hp ht
    have hε' := mul_nonneg (add_pos (hd0 i) zero_lt_one).le hε
    nlinarith only [hi, hp, ht, hε']

theorem all_meet_not_cover {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hr0 : ∀ i, 0 ≤ 1 - L i - G i)
    (hM : ∀ i, meets d L G i) (hs : ∑ i, (1 - L i - G i) ≤ 1)
    (hpair : ∀ i, (1 - L i - G i) + (1 - L (i + 1) - G (i + 1)) < 1) :
    ¬ covers d L G := by
  let u (i : Fin 3) := 1 - L i / d i
  let v (i : Fin 3) := 1 - G i / (1 - d i)
  have hlo (i : Fin 3) : d i * (1 - u i) = L i := by
    dsimp [u]
    rw [sub_sub_cancel, mul_div_cancel₀ _ (hd0 i).ne']
  have hgap (i : Fin 3) : (1 - d i) * (1 - v i) = G i := by
    dsimp [v]
    rw [sub_sub_cancel, mul_div_cancel₀ _ (sub_pos.mpr (hd1 i)).ne']
  have hwidth (i : Fin 3) : d i * u i + (1 - d i) * v i = 1 - L i - G i := by
    linear_combination -hlo i - hgap i
  have hm (i : Fin 3) : 1 ≤ u (i + 1) + v (i + 2) := by
    have h := hM i
    dsimp [meets] at h
    dsimp [u, v]
    linarith only [h]
  have hn := all_meet_legs_not_cover hd0 hd1
    (by simpa only [hwidth] using hr0) hm (by simpa only [hwidth] using hs)
    (by simpa only [hwidth] using hpair)
  simpa only [hlo, hgap] using hn


/-- With total at most one, the boundary alternatives cannot be mixed. -/
theorem boundary_cases {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hL0 : ∀ i, 0 < L i) (hG0 : ∀ i, 0 < G i)
    (hs : ∑ i, (1 - L i - G i) ≤ 1)
    (ha : ∀ i, meets d L G i ∨ bridges d L G i) :
    (∀ i, meets d L G i) ∨ (∀ i, bridges d L G i) := by
  rcases ha 0 with h0 | h0 <;> rcases ha 1 with h1 | h1 <;> rcases ha 2 with h2 | h2
  · exact Or.inl (by intro i; fin_cases i <;> assumption)
  · have := one_bridge_strict hd0 hd1 hL0 hG0 2 h2 h0 h1; linarith only [this, hs]
  · have := one_bridge_strict hd0 hd1 hL0 hG0 1 h1 h2 h0; linarith only [this, hs]
  · have := two_bridges_strict hd0 hd1 hL0 hG0 1 h1 h2 h0; linarith only [this, hs]
  · have := one_bridge_strict hd0 hd1 hL0 hG0 0 h0 h1 h2; linarith only [this, hs]
  · have := two_bridges_strict hd0 hd1 hL0 hG0 2 h2 h0 h1; linarith only [this, hs]
  · have := two_bridges_strict hd0 hd1 hL0 hG0 0 h0 h1 h2; linarith only [this, hs]
  · exact Or.inr (by intro i; fin_cases i <;> assumption)

theorem width_bound_strict {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hL0 : ∀ i, 0 < L i) (hL : ∀ i, L i ≤ d i)
    (hG0 : ∀ i, 0 < G i) (hG : ∀ i, G i ≤ 1 - d i)
    (hc : covers d L G) : 1 ≤ ∑ i, (1 - L i - G i) := by
  by_contra! hsmall
  have hr0 (i : Fin 3) : 0 ≤ 1 - L i - G i := by linarith only [hL i, hG i]
  have hpair (i : Fin 3) : (1 - L i - G i) + (1 - L (i + 1) - G (i + 1)) < 1 := by
    have hs := hsmall
    rw [sum_cyclic _ i] at hs
    linarith only [hs, hr0 (i + 2)]
  have ha := (boundary_iff_side_alternatives hd0 hd1 hL hG).mp
    (show coversBoundary d L G from fun x hx _ => hc x hx)
  rcases boundary_cases hd0 hd1 hL0 hG0 hsmall.le ha with hM | hB
  · exact all_meet_not_cover hd0 hd1 hr0 hM hsmall.le hpair hc
  · exact hsmall.not_ge (bridge_width_bound hd0 hd1 hB)

end SixBoundaries
