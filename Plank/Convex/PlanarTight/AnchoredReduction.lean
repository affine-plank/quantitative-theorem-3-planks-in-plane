/- Pull an anchored three-plank equality cover back along a homothety.
The other two windows become a tight cover of the entire original body. -/
module
public import Plank.Convex.PlanarTight.TwoPlankComplete
public import Plank.Convex.ZeroWidthSlabRemoval
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AnchoredReduction

abbrev Point := Fin 3 → ℝ

/-- If the first positive window is `[0,r]`, contracting the body towards
any point of its opposite support face turns that first window into a
removable zero-width face. Pulling the other two windows back gives their
explicit two-plank normal form on the original body. -/
theorem two_plank_normal (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hL : ∀ i, ∃ p ∈ K, p i = 0) (hU : ∀ i, ∃ p ∈ K, p i = 1)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0)
    (hcover : ∀ p ∈ K, ∃ i, lo i ≤ p i ∧ p i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (T : Point) (hT : T ∈ K) (hT0 : T 0 = 1) :
    TwoPlankClassification.Normal K (AffineMap.proj 1) (AffineMap.proj 2)
      ((lo 1 - hi 0 * T 1) / (1 - hi 0)) ((hi 1 - hi 0 * T 1) / (1 - hi 0))
      ((lo 2 - hi 0 * T 2) / (1 - hi 0)) ((hi 2 - hi 0 * T 2) / (1 - hi 0)) := by
  have hs := hsum
  rw [Fin.sum_univ_three, hanchor, sub_zero] at hs
  have h0 : 0 < hi 0 := by simpa only [hanchor] using hwidth 0
  have h1 := hwidth 1
  have h2 := hwidth 2
  have hr : hi 0 < 1 := by linarith only [hs, h1, h2]
  have hd : 0 < 1 - hi 0 := sub_pos.mpr hr
  let L := (lo 1 - hi 0 * T 1) / (1 - hi 0)
  let U := (hi 1 - hi 0 * T 1) / (1 - hi 0)
  let M := (lo 2 - hi 0 * T 2) / (1 - hi 0)
  let V := (hi 2 - hi 0 * T 2) / (1 - hi 0)
  let lo' : Point := ![0, L, M]
  let hi' : Point := ![0, U, V]
  have hcov : ∀ p ∈ K, ∃ i, lo' i ≤ p i ∧ p i ≤ hi' i := by
    intro p hp
    let q : Point := hi 0 • T + (1 - hi 0) • p
    have hq : q ∈ K := hK hT hp h0.le hd.le (by ring)
    have hqcoord (i : Fin 3) : q i = hi 0 * T i + (1 - hi 0) * p i := rfl
    obtain ⟨i, hil, hiu⟩ := hcover q hq
    refine ⟨i, ?_⟩
    fin_cases i
    · change q 0 ≤ hi 0 at hiu
      have hq0 := hqcoord 0
      rw [hT0, mul_one] at hq0
      have hp0 : p 0 = 0 := by
        have hx := (hbox p hp 0).1
        nlinarith only [hiu, hq0, hx, hd]
      change 0 ≤ p 0 ∧ p 0 ≤ 0
      rw [hp0]
      exact ⟨le_rfl, le_rfl⟩
    · change lo 1 ≤ q 1 at hil
      change q 1 ≤ hi 1 at hiu
      change L ≤ p 1 ∧ p 1 ≤ U
      constructor
      · apply (div_le_iff₀ hd).mpr
        have hq1 := hqcoord 1
        nlinarith only [hil, hq1]
      · apply (le_div_iff₀ hd).mpr
        have hq1 := hqcoord 1
        nlinarith only [hiu, hq1]
    · change lo 2 ≤ q 2 at hil
      change q 2 ≤ hi 2 at hiu
      change M ≤ p 2 ∧ p 2 ≤ V
      constructor
      · apply (div_le_iff₀ hd).mpr
        have hq2 := hqcoord 2
        nlinarith only [hil, hq2]
      · apply (le_div_iff₀ hd).mpr
        have hq2 := hqcoord 2
        nlinarith only [hiu, hq2]
  have hrem := ZeroWidthSlabRemoval.cover_without_zero K hK
    (fun i => ContinuousLinearMap.proj i) lo' hi' 0 rfl T hT
    (by change T 0 ≠ 0; rw [hT0]; exact one_ne_zero) hcov
  have hc : ∀ p ∈ K, (L ≤ p 1 ∧ p 1 ≤ U) ∨ (M ≤ p 2 ∧ p 2 ≤ V) := by
    intro p hp
    obtain ⟨i, hi0, hi⟩ := hrem p hp
    fin_cases i
    · exact False.elim (hi0 rfl)
    · exact Or.inl hi
    · exact Or.inr hi
  have hLU : L < U := (div_lt_div_iff_of_pos_right hd).mpr (sub_lt_sub_right h1 _)
  have hMV : M < V := (div_lt_div_iff_of_pos_right hd).mpr (sub_lt_sub_right h2 _)
  have hsum' : (U - L) + (V - M) = 1 := by
    calc
      (U - L) + (V - M) = ((hi 1 - lo 1) + (hi 2 - lo 2)) / (1 - hi 0) := by
        dsimp [L, U, M, V]
        ring
      _ = 1 := (div_eq_one_iff_eq hd.ne').mpr (by linarith only [hs])
  have H : TwoPlankClassification.Ranges K (AffineMap.proj 1) (AffineMap.proj 2) :=
    ⟨fun p hp => ⟨hbox p hp 1, hbox p hp 2⟩, hL 1, hU 1, hL 2, hU 2⟩
  have hn := (TwoPlankComplete.tight_iff K hK _ _ H L U M V hLU.le hMV.le).mp ⟨hsum', hc⟩
  rcases hn with ⟨_, _, hn⟩ | ⟨hz, _⟩ | ⟨hz, _⟩
  · exact hn
  · exact False.elim (hLU.ne hz)
  · exact False.elim (hMV.ne hz)

end Plank.Convex.PlanarTight.AnchoredReduction

/-- info: 'Plank.Convex.PlanarTight.AnchoredReduction.two_plank_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredReduction.two_plank_normal
