/- Scalar handover and row inequalities for two planks, followed by the
normalized coordinate theorem and window clamping. No topology or ambient
affine structure is used here. Historical declaration names are preserved. -/
module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.SplitIfs
@[expose] public section
noncomputable section

namespace Plank.TwoPlankBodyCS

/-! ## §1  ★ The segment argument, as one real inequality ★ -/

/-- ★★ **The handover core** ★★ — if every `t ∈ [0,1]` satisfies
`B ≤ tμ` or `tν ≤ Γ`, then `Bν ≤ Γμ`.  Contrapositively: if `Γμ < Bν`
the thresholds `Γ/ν < B/μ` are in the wrong order and their midpoint
`(Γμ + Bν)/(2μν) ∈ [0,1]` satisfies neither.  KERNEL. -/
theorem corner_ineq {mu nu B Ga : ℝ} (hmu : 0 < mu) (hnu : 0 < nu)
    (hB : 0 ≤ B) (hGa : 0 ≤ Ga) (hBmu : B ≤ mu)
    (hcov : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → B ≤ t * mu ∨ t * nu ≤ Ga) :
    B * nu ≤ Ga * mu := by
  by_contra hcon
  rw [not_le] at hcon
  have hden : (0:ℝ) < 2 * mu * nu := by positivity
  set t : ℝ := (Ga * mu + B * nu) / (2 * mu * nu) with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) hden.le
  have htmu : t * mu < B := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ hden]; nlinarith
  have ht1 : t ≤ 1 := by nlinarith
  have htnu : Ga < t * nu := by
    rw [ht, div_mul_eq_mul_div, lt_div_iff₀ hden]; nlinarith
  rcases hcov t ht0 ht1 with h | h
  · linarith
  · linarith

/-! ## §2  ★ One corner ★ -/

/-- ★★ **The handover inequality at one corner** ★★  `X` and `Y` are two
coordinates on a set `T` that is segment-closed in the sense of `hseg`;
the planks are the windows `[l₁,h₁]` in `X` and `[l₂,h₂]` in `Y`, and
they cover `T`.  If `X p = 0` with `l₁ > 0` then `p` is in the second
plank; if `Y q = 1` with `h₂ < 1` then `q` is in the first; the segment
from `p` to `q` hands over from one plank to the other, and §1 gives
`l₁(1 − h₂) ≤ (X q − l₁)(h₂ − Y p)`.  KERNEL. -/
theorem handover_corner {α : Type*} {T : Set α} {X Y : α → ℝ}
    (hseg : ∀ P ∈ T, ∀ Q ∈ T, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ R ∈ T, X R = X P + t * (X Q - X P) ∧ Y R = Y P + t * (Y Q - Y P))
    {l1 h1 l2 h2 : ℝ}
    (hcov : ∀ P ∈ T, (l1 ≤ X P ∧ X P ≤ h1) ∨ (l2 ≤ Y P ∧ Y P ≤ h2))
    {p q : α} (hp : p ∈ T) (hq : q ∈ T) (hXp : X p = 0) (hYq : Y q = 1)
    (ha : 0 < l1) (hd : h2 < 1) :
    l1 * (1 - h2) ≤ (X q - l1) * (h2 - Y p) := by
  have hpH : l2 ≤ Y p ∧ Y p ≤ h2 := by
    rcases hcov p hp with hk | hk
    · rw [hXp] at hk; exact absurd hk.1 (by linarith)
    · exact hk
  have hqV : l1 ≤ X q ∧ X q ≤ h1 := by
    rcases hcov q hq with hk | hk
    · exact hk
    · rw [hYq] at hk; exact absurd hk.2 (by linarith)
  have hcore : l1 * (1 - Y p) ≤ (h2 - Y p) * X q := by
    refine corner_ineq (by linarith [hqV.1] : (0:ℝ) < X q)
      (by linarith [hpH.2] : (0:ℝ) < 1 - Y p) ha.le (by linarith [hpH.2])
      hqV.1 ?_
    intro t ht0 ht1
    obtain ⟨R, hR, hXR, hYR⟩ := hseg p hp q hq t ht0 ht1
    rw [hXp] at hXR
    rw [hYq] at hYR
    rcases hcov R hR with hk | hk
    · exact Or.inl (by rw [hXR] at hk; nlinarith [hk.1])
    · exact Or.inr (by rw [hYR] at hk; nlinarith [hk.2])
  nlinarith [hcore]

/-! ## §3  ★ The escape-side pairing ★ -/

/-- ★★ **The row bound** ★★ — from `a·c ≤ α·x` and `b·c ≤ β·y`,
`c(a+b)² ≤ (α+β)(ax + by)`: Cauchy–Schwarz at weights `(a,b)`, written
without division (the cross term is AM–GM on the product of the two
hypotheses).  KERNEL. -/
theorem row_bound {a b c x y al be : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hal : 0 ≤ al) (hbe : 0 ≤ be)
    (h1 : a * c ≤ al * x) (h2 : b * c ≤ be * y) :
    c * (a + b) ^ 2 ≤ (al + be) * (a * x + b * y) := by
  have h3 : a * (a * c) ≤ a * (al * x) := mul_le_mul_of_nonneg_left h1 ha
  have h4 : b * (b * c) ≤ b * (be * y) := mul_le_mul_of_nonneg_left h2 hb
  have hu : 0 ≤ al * b * y := mul_nonneg (mul_nonneg hal hb) hy
  have hv : 0 ≤ be * a * x := mul_nonneg (mul_nonneg hbe ha) hx
  have habc : 0 ≤ a * b * c := mul_nonneg (mul_nonneg ha hb) hc
  have hprod : (a * b * c) ^ 2 ≤ (al * b * y) * (be * a * x) := by
    have e1 : 0 ≤ a * c := mul_nonneg ha hc
    have e2 : 0 ≤ b * c := mul_nonneg hb hc
    nlinarith [mul_le_mul h1 h2 e2 (le_trans e1 h1), mul_nonneg ha hb]
  have hcross : 2 * (a * b * c) ≤ al * b * y + be * a * x := by
    nlinarith [sq_nonneg (al * b * y - be * a * x), hprod, hu, hv, habc]
  nlinarith [h3, h4, hcross]

/-- ★★ **The two-plank core** ★★  The four handover inequalities, paired
by escape side, give `g₁ + g₂ ≥ 1`.  `a, b` are the `x`-escape margins
(`a + b = 1 − g₁`), `c, d` the `y`-escape margins (`c + d = 1 − g₂`),
`s_L, s_R ∈ [0, g₂]` the heights of the two `x`-escape realisers and
`α_•, β_•` the split of `g₁` at the two `y`-escape realisers.  ★ The
offset sum `S = a s_L + b s_R` cancels on adding the two rows — that is
the whole proof, and why the pairing is by escape side. ★  KERNEL. -/
theorem twoplank_core {a b c d g1 g2 sL sR alU beU alD beD : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hg2 : 0 ≤ g2)
    (hsL : 0 ≤ sL) (hsL' : sL ≤ g2) (hsR : 0 ≤ sR) (hsR' : sR ≤ g2)
    (halU : 0 ≤ alU) (hbeU : 0 ≤ beU) (hUsum : alU + beU = g1)
    (halD : 0 ≤ alD) (hbeD : 0 ≤ beD) (hDsum : alD + beD = g1)
    (hLU : a * d ≤ alU * (g2 - sL)) (hRU : b * d ≤ beU * (g2 - sR))
    (hLD : a * c ≤ alD * sL) (hRD : b * c ≤ beD * sR)
    (hab : a + b = 1 - g1) (hcd : c + d = 1 - g2) :
    1 ≤ g1 + g2 := by
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ a + b) with hA | hA
  · linarith
  · have hup : d * (a + b) ^ 2 ≤ g1 * (a * (g2 - sL) + b * (g2 - sR)) := by
      have h := row_bound ha hb hd (by linarith) (by linarith) halU hbeU hLU hRU
      rw [hUsum] at h; exact h
    have hdown : c * (a + b) ^ 2 ≤ g1 * (a * sL + b * sR) := by
      have h := row_bound ha hb hc hsL hsR halD hbeD hLD hRD
      rw [hDsum] at h; exact h
    have hsum : (c + d) * (a + b) ^ 2 ≤ g1 * ((a + b) * g2) := by nlinarith [hup, hdown]
    have hfin : (c + d) * (a + b) ≤ g1 * g2 := by nlinarith [hA, hsum]
    rw [hab, hcd] at hfin
    nlinarith [hfin]

/-! ## §4  ★ The normalised statement ★ -/

/-- ★★ **Two planks on a normalised body** ★★ — `T` is segment-closed in
the coordinates `X, Y`, which range over `[0,1]` with the extremes
attained (`pL, pR, qD, qU`); two windows `[l₁,h₁] ⊆ [0,1]` and
`[l₂,h₂] ⊆ [0,1]` cover it.  Then their widths sum to at least `1`.

The four handover inequalities are four calls to `handover_corner` in
the mirrored coordinates; each is trivially true when its escape margin
vanishes (the left side is `0`), which is why the guarded offsets need
no separate geometry.  `twoplank_core` then closes it.  KERNEL. -/
theorem twoplank_normalised {α : Type*} {T : Set α} {X Y : α → ℝ}
    (hseg : ∀ P ∈ T, ∀ Q ∈ T, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ R ∈ T, X R = X P + t * (X Q - X P) ∧ Y R = Y P + t * (Y Q - Y P))
    {l1 h1 l2 h2 : ℝ}
    (hl1 : 0 ≤ l1) (hlh1 : l1 ≤ h1) (hh1 : h1 ≤ 1)
    (hl2 : 0 ≤ l2) (hlh2 : l2 ≤ h2) (hh2 : h2 ≤ 1)
    (hcov : ∀ P ∈ T, (l1 ≤ X P ∧ X P ≤ h1) ∨ (l2 ≤ Y P ∧ Y P ≤ h2))
    {pL pR qD qU : α} (hpL : pL ∈ T) (hpR : pR ∈ T) (hqD : qD ∈ T)
    (hqU : qU ∈ T) (hXpL : X pL = 0) (hXpR : X pR = 1) (hYqD : Y qD = 0)
    (hYqU : Y qU = 1) :
    1 ≤ (h1 - l1) + (h2 - l2) := by
  -- the three mirrored segment hypotheses
  have hsegX : ∀ P ∈ T, ∀ Q ∈ T, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ R ∈ T, (1 - X R) = (1 - X P) + t * ((1 - X Q) - (1 - X P)) ∧
        Y R = Y P + t * (Y Q - Y P) := by
    intro P hP Q hQ t ht0 ht1
    obtain ⟨R, hR, e1, e2⟩ := hseg P hP Q hQ t ht0 ht1
    exact ⟨R, hR, by rw [e1]; ring, e2⟩
  have hsegY : ∀ P ∈ T, ∀ Q ∈ T, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ R ∈ T, X R = X P + t * (X Q - X P) ∧
        (1 - Y R) = (1 - Y P) + t * ((1 - Y Q) - (1 - Y P)) := by
    intro P hP Q hQ t ht0 ht1
    obtain ⟨R, hR, e1, e2⟩ := hseg P hP Q hQ t ht0 ht1
    exact ⟨R, hR, e1, by rw [e2]; ring⟩
  have hsegXY : ∀ P ∈ T, ∀ Q ∈ T, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ R ∈ T, (1 - X R) = (1 - X P) + t * ((1 - X Q) - (1 - X P)) ∧
        (1 - Y R) = (1 - Y P) + t * ((1 - Y Q) - (1 - Y P)) := by
    intro P hP Q hQ t ht0 ht1
    obtain ⟨R, hR, e1, e2⟩ := hseg P hP Q hQ t ht0 ht1
    exact ⟨R, hR, by rw [e1]; ring, by rw [e2]; ring⟩
  -- the three mirrored covering hypotheses
  have hcovX : ∀ P ∈ T,
      ((1 - h1) ≤ 1 - X P ∧ 1 - X P ≤ (1 - l1)) ∨ (l2 ≤ Y P ∧ Y P ≤ h2) := by
    intro P hP
    rcases hcov P hP with hk | hk
    · exact Or.inl ⟨by linarith [hk.2], by linarith [hk.1]⟩
    · exact Or.inr hk
  have hcovY : ∀ P ∈ T,
      (l1 ≤ X P ∧ X P ≤ h1) ∨ ((1 - h2) ≤ 1 - Y P ∧ 1 - Y P ≤ (1 - l2)) := by
    intro P hP
    rcases hcov P hP with hk | hk
    · exact Or.inl hk
    · exact Or.inr ⟨by linarith [hk.2], by linarith [hk.1]⟩
  have hcovXY : ∀ P ∈ T,
      ((1 - h1) ≤ 1 - X P ∧ 1 - X P ≤ (1 - l1)) ∨
        ((1 - h2) ≤ 1 - Y P ∧ 1 - Y P ≤ (1 - l2)) := by
    intro P hP
    rcases hcov P hP with hk | hk
    · exact Or.inl ⟨by linarith [hk.2], by linarith [hk.1]⟩
    · exact Or.inr ⟨by linarith [hk.2], by linarith [hk.1]⟩
  -- the escape facts, each available exactly when its margin is positive
  have hpLH : 0 < l1 → l2 ≤ Y pL ∧ Y pL ≤ h2 := by
    intro h
    rcases hcov pL hpL with hk | hk
    · rw [hXpL] at hk; exact absurd hk.1 (by linarith)
    · exact hk
  have hpRH : h1 < 1 → l2 ≤ Y pR ∧ Y pR ≤ h2 := by
    intro h
    rcases hcov pR hpR with hk | hk
    · rw [hXpR] at hk; exact absurd hk.2 (by linarith)
    · exact hk
  have hqUV : h2 < 1 → l1 ≤ X qU ∧ X qU ≤ h1 := by
    intro h
    rcases hcov qU hqU with hk | hk
    · exact hk
    · rw [hYqU] at hk; exact absurd hk.2 (by linarith)
  have hqDV : 0 < l2 → l1 ≤ X qD ∧ X qD ≤ h1 := by
    intro h
    rcases hcov qD hqD with hk | hk
    · exact hk
    · rw [hYqD] at hk; exact absurd hk.1 (by linarith)
  -- the offsets, guarded so that they stay in range when an escape is absent
  set sL : ℝ := if 0 < l1 then Y pL - l2 else 0 with hsL
  set sR : ℝ := if h1 < 1 then Y pR - l2 else 0 with hsR
  set alU : ℝ := if h2 < 1 then X qU - l1 else h1 - l1 with halU
  set alD : ℝ := if 0 < l2 then X qD - l1 else h1 - l1 with halD
  have hsLmem : 0 ≤ sL ∧ sL ≤ h2 - l2 := by
    rw [hsL]; split_ifs with h
    · obtain ⟨u, v⟩ := hpLH h; constructor <;> linarith
    · exact ⟨le_refl 0, by linarith⟩
  have hsRmem : 0 ≤ sR ∧ sR ≤ h2 - l2 := by
    rw [hsR]; split_ifs with h
    · obtain ⟨u, v⟩ := hpRH h; constructor <;> linarith
    · exact ⟨le_refl 0, by linarith⟩
  have halUmem : 0 ≤ alU ∧ alU ≤ h1 - l1 := by
    rw [halU]; split_ifs with h
    · obtain ⟨u, v⟩ := hqUV h; constructor <;> linarith
    · exact ⟨by linarith, le_refl _⟩
  have halDmem : 0 ≤ alD ∧ alD ≤ h1 - l1 := by
    rw [halD]; split_ifs with h
    · obtain ⟨u, v⟩ := hqDV h; constructor <;> linarith
    · exact ⟨by linarith, le_refl _⟩
  -- ★ the four handover inequalities ★
  have hLU : l1 * (1 - h2) ≤ alU * ((h2 - l2) - sL) := by
    rcases eq_or_lt_of_le hl1 with h | h
    · have : alU * ((h2 - l2) - sL) ≥ 0 :=
        mul_nonneg halUmem.1 (by linarith [hsLmem.2])
      simpa only [← h, zero_mul] using this
    rcases eq_or_lt_of_le hh2 with h' | h'
    · have : alU * ((h2 - l2) - sL) ≥ 0 :=
        mul_nonneg halUmem.1 (by linarith [hsLmem.2])
      simpa only [h', sub_self, mul_zero] using this
    have hs : sL = Y pL - l2 := by rw [hsL, if_pos h]
    have hal : alU = X qU - l1 := by rw [halU, if_pos h']
    have := handover_corner hseg hcov hpL hqU hXpL hYqU h h'
    rw [hs, hal]
    simpa only [sub_sub_sub_cancel_right] using this
  have hRU : (1 - h1) * (1 - h2) ≤ ((h1 - l1) - alU) * ((h2 - l2) - sR) := by
    rcases eq_or_lt_of_le hh1 with h | h
    · have : ((h1 - l1) - alU) * ((h2 - l2) - sR) ≥ 0 :=
        mul_nonneg (by linarith [halUmem.2]) (by linarith [hsRmem.2])
      simpa only [h, sub_self, zero_mul] using this
    rcases eq_or_lt_of_le hh2 with h' | h'
    · have : ((h1 - l1) - alU) * ((h2 - l2) - sR) ≥ 0 :=
        mul_nonneg (sub_nonneg.mpr halUmem.2) (sub_nonneg.mpr hsRmem.2)
      simpa only [h', sub_self, mul_zero] using this
    have hs : sR = Y pR - l2 := by rw [hsR, if_pos (by linarith)]
    have hal : alU = X qU - l1 := by rw [halU, if_pos h']
    have := handover_corner hsegX hcovX hpR hqU (by rw [hXpR]; ring) hYqU
      (by linarith) h'
    rw [hs, hal]
    simpa only [sub_sub_sub_cancel_right, sub_sub_sub_cancel_left] using this
  have hLD : l1 * l2 ≤ alD * sL := by
    rcases eq_or_lt_of_le hl1 with h | h
    · have : alD * sL ≥ 0 := mul_nonneg halDmem.1 hsLmem.1
      simpa only [← h, zero_mul] using this
    rcases eq_or_lt_of_le hl2 with h' | h'
    · have : alD * sL ≥ 0 := mul_nonneg halDmem.1 hsLmem.1
      simpa only [← h', mul_zero] using this
    have hs : sL = Y pL - l2 := by rw [hsL, if_pos h]
    have hal : alD = X qD - l1 := by rw [halD, if_pos h']
    have := handover_corner hsegY hcovY hpL hqD hXpL (by rw [hYqD]; ring) h
      (by linarith)
    rw [hs, hal]
    simpa only [sub_sub_cancel, sub_sub_sub_cancel_left] using this
  have hRD : (1 - h1) * l2 ≤ ((h1 - l1) - alD) * sR := by
    rcases eq_or_lt_of_le hh1 with h | h
    · have : ((h1 - l1) - alD) * sR ≥ 0 :=
        mul_nonneg (by linarith [halDmem.2]) hsRmem.1
      simpa only [h, sub_self, zero_mul] using this
    rcases eq_or_lt_of_le hl2 with h' | h'
    · have : ((h1 - l1) - alD) * sR ≥ 0 :=
        mul_nonneg (sub_nonneg.mpr halDmem.2) hsRmem.1
      simpa only [← h', mul_zero] using this
    have hs : sR = Y pR - l2 := by rw [hsR, if_pos (by linarith)]
    have hal : alD = X qD - l1 := by rw [halD, if_pos h']
    have := handover_corner hsegXY hcovXY hpR hqD (by rw [hXpR]; ring)
      (by rw [hYqD]; ring) (by linarith) (by linarith)
    rw [hs, hal]
    simpa only [sub_sub_cancel, sub_sub_sub_cancel_right, sub_sub_sub_cancel_left] using this
  -- ★ the escape-side pairing closes it ★
  exact twoplank_core (a := l1) (b := 1 - h1) (c := l2) (d := 1 - h2)
    (g1 := h1 - l1) (g2 := h2 - l2) (sL := sL) (sR := sR)
    (alU := alU) (beU := (h1 - l1) - alU) (alD := alD) (beD := (h1 - l1) - alD)
    hl1 (by linarith) hl2 (by linarith) (by linarith)
    hsLmem.1 hsLmem.2 hsRmem.1 hsRmem.2
    halUmem.1 (by linarith [halUmem.2]) (by ring)
    halDmem.1 (by linarith [halDmem.2]) (by ring)
    hLU hRU hLD hRD (by ring) (by ring)

/-! ## §5  ★ Two planks on a compact convex body ★ -/

/-- Clamping a level to `[0,1]`: trimming a window to the body's own
range preserves the covering and only shrinks the window. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem clamp01_mono {s t : ℝ} (h : s ≤ t) : clamp01 s ≤ clamp01 t :=
  max_le_max le_rfl (min_le_min le_rfl h)

/-- Clamping is `1`-Lipschitz, so trimming never grows a window. -/
theorem clamp01_sub_le {s t : ℝ} (h : s ≤ t) : clamp01 t - clamp01 s ≤ t - s := by
  simp only [clamp01, max_def, min_def]; split_ifs <;> linarith

/-- A point of the body inside the untrimmed window is inside the trimmed one. -/
theorem clamp01_le_of {s x : ℝ} (hx0 : 0 ≤ x) (h : s ≤ x) : clamp01 s ≤ x :=
  max_le hx0 ((min_le_right _ _).trans h)

theorem le_clamp01_of {t x : ℝ} (hx1 : x ≤ 1) (h : x ≤ t) : x ≤ clamp01 t :=
  (le_min hx1 h).trans (le_max_right _ _)

end Plank.TwoPlankBodyCS

end
