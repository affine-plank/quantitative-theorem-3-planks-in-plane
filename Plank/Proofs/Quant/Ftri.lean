/-
# The triple-overlap slice function `Ftri`, and its unimodality

Port of `Dim2N3/KPlankBoxCap.lean` (§1, the clamp) and
`Dim2N3/KPlankFtri.lean` (§2–§5) — both substrate-free analysis, so the
port is a re-homing of namespace and prose only.

App AM §AM.1 gives the closed form

    (F-CF)  F(S) = (2/L₃) ∫_{−S−A₃}^{−S+A₃} g(w) dw ,
            g(w) = max(0, min(A₁+A₂−|w|, 2A₁, 2A₂)) / L₁₂ ,

for the triple overlap of three slabs read through the chart of
`Plank/Proofs/Quant/Chart.lean`: `Aᵢ` are the cofactor-scaled
half-widths, `S` the concurrency defect, and the prefactor `2/L₃` is
the Jacobian `1/|det|` times the ledger's `1/|T| = 2` — `F` measures
the triple overlap in units of `|T|`, matching the relative areas used
by the ledger.  Two conventions are load-bearing and were pinned down
exactly before the ancestor was formalised: the `λᵢ` must be the
**Cramer cofactors** of the three normals (the formula is *not*
invariant under `λ ↦ tλ`), and the constant against the bare area is
`1/L₃`, not `2/L₃`.

This file proves what the box clamp consumes: the window integral
`Wtri` of the trapezoid density `gTrap` is **even** and **nonincreasing
in the distance of the window from the origin** — sliding the window
away from the peak can only shed mass (`Wtri_antitone`; the difference
of the two windows is an integral of `g(x) − g(x + 2A₃)` over a range
where the trapezoid's decay makes the integrand nonnegative).  Hence
`Ftri` is even and unimodal, `(F-PEAK)` evaluates it at the peak, and
the clamp closes the chain `(U1-BOXCAP) ⟹ (U1)` on any box.

§1 is the clamp itself, abstracted from all geometry: for *any* even
function nonincreasing on `[0,∞)`, the sup over a box `|s − S₀| ≤ smax`
is the clamped value `Fbox` — the peak value if the box reaches the
peak, the nearer endpoint's value otherwise.
-/
module

public import Plank.Proofs.Quant.TwoPlank

@[expose] public section


noncomputable section

open intervalIntegral

namespace Quant

/-! ## §1  The unimodal clamp

(Ancestor: `KPlankBoxCap`, inlined — the clamp is three lemmas of
order theory and reads better as the opening section of the file whose
function it clamps.) -/

/-- An even function that is nonincreasing on `[0,∞)` peaks at `0`. -/
theorem le_peak (F : ℝ → ℝ) (hsym : ∀ s, F (-s) = F s)
    (hmono : ∀ s t, 0 ≤ s → s ≤ t → F t ≤ F s) (s : ℝ) : F s ≤ F 0 := by
  by_cases h : (0:ℝ) ≤ s
  · exact hmono 0 s le_rfl h
  · push_neg at h
    rw [← hsym s]
    exact hmono 0 (-s) le_rfl (by linarith)

/-- The clamped box value: the peak if the box `|s − S₀| ≤ smax`
reaches it, the nearer endpoint otherwise. -/
def Fbox (F : ℝ → ℝ) (S₀ smax : ℝ) : ℝ :=
  if |S₀| ≤ smax then F 0 else if 0 < S₀ then F (S₀ - smax) else F (S₀ + smax)

/-- **The box clamp.**  For an even, `[0,∞)`-nonincreasing `F`, every
point of the box `|s − S₀| ≤ smax` is dominated by the clamped value. -/
theorem le_Fbox (F : ℝ → ℝ) (hsym : ∀ s, F (-s) = F s)
    (hmono : ∀ s t, 0 ≤ s → s ≤ t → F t ≤ F s) (S₀ smax s : ℝ)
    (hbox : |s - S₀| ≤ smax) : F s ≤ Fbox F S₀ smax := by
  rw [abs_le] at hbox
  unfold Fbox
  by_cases hnear : |S₀| ≤ smax
  · rw [if_pos hnear]
    exact le_peak F hsym hmono s
  · rw [if_neg hnear]
    have habs : smax < |S₀| := not_le.mp hnear
    by_cases hpos : 0 < S₀
    · -- the whole box sits to the right of the peak
      rw [if_pos hpos]
      have hfar : smax < S₀ := by rwa [abs_of_pos hpos] at habs
      exact hmono (S₀ - smax) s (by linarith) (by linarith [hbox.1])
    · -- the whole box sits to the left of the peak
      rw [if_neg hpos]
      push_neg at hpos
      have hfar : S₀ < -smax := by
        rw [abs_of_nonpos hpos] at habs
        linarith
      rw [← hsym s, ← hsym (S₀ + smax)]
      exact hmono (-(S₀ + smax)) (-s) (by linarith) (by linarith [hbox.2])

/-! ## §2  The trapezoid density -/

/-- The density of `w = λ₀u + λ₁v` on the rectangle `|u| ≤ c₀`,
`|v| ≤ c₁`, in the `A`-variables: a trapezoid of support half-width
`A₁ + A₂`, plateau half-width `|A₁ − A₂|`, and total mass `4A₁A₂/L₁₂`. -/
def gTrap (A₁ A₂ L₁₂ : ℝ) (w : ℝ) : ℝ :=
  max 0 (min (A₁ + A₂ - |w|) (min (2 * A₁) (2 * A₂))) / L₁₂

theorem gTrap_even (A₁ A₂ L₁₂ : ℝ) (w : ℝ) :
    gTrap A₁ A₂ L₁₂ (-w) = gTrap A₁ A₂ L₁₂ w := by
  unfold gTrap
  rw [abs_neg]

theorem gTrap_nonneg (A₁ A₂ L₁₂ : ℝ) (hL : 0 ≤ L₁₂) (w : ℝ) :
    0 ≤ gTrap A₁ A₂ L₁₂ w := by
  unfold gTrap
  exact div_nonneg (le_max_left _ _) hL

/-- The trapezoid is nonincreasing in `|w|`. -/
theorem gTrap_le_of_abs_le (A₁ A₂ L₁₂ : ℝ) (hL : 0 ≤ L₁₂) {w₁ w₂ : ℝ}
    (h : |w₁| ≤ |w₂|) : gTrap A₁ A₂ L₁₂ w₂ ≤ gTrap A₁ A₂ L₁₂ w₁ := by
  unfold gTrap
  apply div_le_div_of_nonneg_right _ hL
  apply max_le_max_left
  apply min_le_min_right
  linarith

theorem gTrap_continuous (A₁ A₂ L₁₂ : ℝ) :
    Continuous (gTrap A₁ A₂ L₁₂) := by
  unfold gTrap
  fun_prop

theorem gTrap_intervalIntegrable (A₁ A₂ L₁₂ a b : ℝ) :
    IntervalIntegrable (gTrap A₁ A₂ L₁₂) MeasureTheory.volume a b :=
  (gTrap_continuous A₁ A₂ L₁₂).intervalIntegrable a b

/-! ## §3  The window integral -/

/-- The integral of the trapezoid over the window of half-length `A₃`
centred at `c`. -/
def Wtri (A₁ A₂ A₃ L₁₂ : ℝ) (c : ℝ) : ℝ :=
  ∫ w in (c - A₃)..(c + A₃), gTrap A₁ A₂ L₁₂ w

theorem Wtri_even (A₁ A₂ A₃ L₁₂ : ℝ) (c : ℝ) :
    Wtri A₁ A₂ A₃ L₁₂ (-c) = Wtri A₁ A₂ A₃ L₁₂ c := by
  unfold Wtri
  have h := integral_comp_neg (a := c - A₃) (b := c + A₃)
    (f := gTrap A₁ A₂ L₁₂)
  have hfun : (fun x => gTrap A₁ A₂ L₁₂ (-x)) = gTrap A₁ A₂ L₁₂ := by
    funext x
    exact gTrap_even A₁ A₂ L₁₂ x
  rw [hfun] at h
  rw [show -c - A₃ = -(c + A₃) by ring, show -c + A₃ = -(c - A₃) by ring]
  exact h.symm

/-- **The unimodality step.**  Sliding the window away from the origin
can only decrease the integral: the difference is an integral of
`g(x) − g(x + 2A₃)` over a window that stays to the right of `−A₃`,
where the trapezoid's decay in `|w|` makes the integrand nonnegative. -/
theorem Wtri_antitone (A₁ A₂ A₃ L₁₂ : ℝ) (hA₃ : 0 ≤ A₃) (hL : 0 ≤ L₁₂)
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc : c₁ ≤ c₂) :
    Wtri A₁ A₂ A₃ L₁₂ c₂ ≤ Wtri A₁ A₂ A₃ L₁₂ c₁ := by
  have hsplit₁ : Wtri A₁ A₂ A₃ L₁₂ c₁
      = (∫ w in (c₁ - A₃)..(c₂ - A₃), gTrap A₁ A₂ L₁₂ w)
        + ∫ w in (c₂ - A₃)..(c₁ + A₃), gTrap A₁ A₂ L₁₂ w :=
    (integral_add_adjacent_intervals (gTrap_intervalIntegrable _ _ _ _ _)
      (gTrap_intervalIntegrable _ _ _ _ _)).symm
  have hsplit₂ : Wtri A₁ A₂ A₃ L₁₂ c₂
      = (∫ w in (c₂ - A₃)..(c₁ + A₃), gTrap A₁ A₂ L₁₂ w)
        + ∫ w in (c₁ + A₃)..(c₂ + A₃), gTrap A₁ A₂ L₁₂ w :=
    (integral_add_adjacent_intervals (gTrap_intervalIntegrable _ _ _ _ _)
      (gTrap_intervalIntegrable _ _ _ _ _)).symm
  have hshift : (∫ w in (c₁ + A₃)..(c₂ + A₃), gTrap A₁ A₂ L₁₂ w)
      = ∫ x in (c₁ - A₃)..(c₂ - A₃), gTrap A₁ A₂ L₁₂ (x + 2 * A₃) := by
    rw [integral_comp_add_right (f := gTrap A₁ A₂ L₁₂) (d := 2 * A₃)]
    rw [show c₁ - A₃ + 2 * A₃ = c₁ + A₃ by ring,
      show c₂ - A₃ + 2 * A₃ = c₂ + A₃ by ring]
  have hdiff : 0 ≤ (∫ x in (c₁ - A₃)..(c₂ - A₃),
      (gTrap A₁ A₂ L₁₂ x - gTrap A₁ A₂ L₁₂ (x + 2 * A₃))) := by
    apply integral_nonneg (by linarith)
    intro x hx
    have hxlow : -A₃ ≤ x := by
      have := hx.1
      linarith
    have habs : |x| ≤ |x + 2 * A₃| := by
      rw [abs_le]
      constructor
      · have : 0 ≤ x + 2 * A₃ := by linarith
        rw [abs_of_nonneg this]
        linarith
      · have : 0 ≤ x + 2 * A₃ := by linarith
        rw [abs_of_nonneg this]
        linarith
    have := gTrap_le_of_abs_le A₁ A₂ L₁₂ hL habs
    linarith
  have hcont₂ : Continuous fun x : ℝ => gTrap A₁ A₂ L₁₂ (x + 2 * A₃) :=
    (gTrap_continuous A₁ A₂ L₁₂).comp (continuous_id.add continuous_const)
  have hsub : (∫ x in (c₁ - A₃)..(c₂ - A₃),
        (gTrap A₁ A₂ L₁₂ x - gTrap A₁ A₂ L₁₂ (x + 2 * A₃)))
      = (∫ x in (c₁ - A₃)..(c₂ - A₃), gTrap A₁ A₂ L₁₂ x)
        - ∫ x in (c₁ - A₃)..(c₂ - A₃), gTrap A₁ A₂ L₁₂ (x + 2 * A₃) :=
    integral_sub (gTrap_intervalIntegrable _ _ _ _ _)
      (hcont₂.intervalIntegrable _ _)
  rw [hsub] at hdiff
  rw [hsplit₁, hsplit₂, hshift]
  linarith

/-! ## §4  `Ftri` -/

/-- **(F-CF)**: the triple-overlap slice function, in units of `|T|`. -/
def Ftri (A₁ A₂ A₃ L₁₂ L₃ : ℝ) (S : ℝ) : ℝ :=
  (2 / L₃) * Wtri A₁ A₂ A₃ L₁₂ (-S)

theorem Ftri_even (A₁ A₂ A₃ L₁₂ L₃ : ℝ) (S : ℝ) :
    Ftri A₁ A₂ A₃ L₁₂ L₃ (-S) = Ftri A₁ A₂ A₃ L₁₂ L₃ S := by
  unfold Ftri
  rw [neg_neg, ← Wtri_even A₁ A₂ A₃ L₁₂ S]

/-- **`Ftri` is unimodal** — nonincreasing in `|S|`, hence peaked at
`S = 0`.  This is App AM §AM.1's convolution fact, and it is the
hypothesis `le_Fbox` needs. -/
theorem Ftri_antitone (A₁ A₂ A₃ L₁₂ L₃ : ℝ) (hA₃ : 0 ≤ A₃) (hL : 0 ≤ L₁₂)
    (hL₃ : 0 ≤ L₃) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Ftri A₁ A₂ A₃ L₁₂ L₃ t ≤ Ftri A₁ A₂ A₃ L₁₂ L₃ s := by
  unfold Ftri
  rw [Wtri_even A₁ A₂ A₃ L₁₂ s, Wtri_even A₁ A₂ A₃ L₁₂ t]
  exact mul_le_mul_of_nonneg_left (Wtri_antitone A₁ A₂ A₃ L₁₂ hA₃ hL hs hst)
    (by positivity)

/-! ## §5  (F-PEAK): the closed form at the peak -/

/-- The trapezoid's plateau half-width is `|A₁ − A₂|`. -/
theorem plateau_width (A₁ A₂ : ℝ) :
    A₁ + A₂ - min (2 * A₁) (2 * A₂) = |A₁ - A₂| := by
  rcases le_total A₁ A₂ with h | h
  · rw [min_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring

/-- **(F-PEAK)**  At the peak `S = 0`, under the strict triangle
inequalities on `(A₁, A₂, A₃)`: `F(0) = 2(XY + YZ + ZX)/Λ` with
`X, Y, Z` the three triangle slacks and `Λ = L₁₂·L₃`. -/
theorem Ftri_peak (A₁ A₂ A₃ L₁₂ L₃ : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hsum : A₃ < A₁ + A₂) (hdiff : |A₁ - A₂| < A₃)
    (hL₁₂ : 0 < L₁₂) (hL₃ : 0 < L₃) :
    Ftri A₁ A₂ A₃ L₁₂ L₃ 0
      = 2 * ((A₁ + A₂ - A₃) * (A₂ + A₃ - A₁)
          + (A₂ + A₃ - A₁) * (A₃ + A₁ - A₂)
          + (A₃ + A₁ - A₂) * (A₁ + A₂ - A₃)) / (L₁₂ * L₃) := by
  have hq := plateau_width A₁ A₂
  have hq0 : (0:ℝ) ≤ |A₁ - A₂| := abs_nonneg _
  have hK0 : (0:ℝ) ≤ min (2 * A₁) (2 * A₂) := le_min (by linarith) (by linarith)
  have hA₃0 : 0 < A₃ := lt_of_le_of_lt hq0 hdiff
  -- the trapezoid on the three pieces
  have hleft : ∀ w ∈ Set.uIcc (-A₃) (-|A₁ - A₂|),
      gTrap A₁ A₂ L₁₂ w = (A₁ + A₂ + w) / L₁₂ := by
    intro w hw
    rw [Set.uIcc_of_le (by linarith)] at hw
    have hwneg : w ≤ 0 := by linarith [hw.2]
    have hwabs : |w| = -w := abs_of_nonpos hwneg
    unfold gTrap
    rw [hwabs, min_eq_left (by linarith [hw.2]), max_eq_right (by linarith [hw.1])]
    ring
  have hmid : ∀ w ∈ Set.uIcc (-|A₁ - A₂|) |A₁ - A₂|,
      gTrap A₁ A₂ L₁₂ w = min (2 * A₁) (2 * A₂) / L₁₂ := by
    intro w hw
    rw [Set.uIcc_of_le (by linarith)] at hw
    have hwabs : |w| ≤ |A₁ - A₂| := abs_le.mpr ⟨hw.1, hw.2⟩
    unfold gTrap
    rw [min_eq_right (by linarith), max_eq_right hK0]
  have hright : ∀ w ∈ Set.uIcc |A₁ - A₂| A₃,
      gTrap A₁ A₂ L₁₂ w = (A₁ + A₂ - w) / L₁₂ := by
    intro w hw
    rw [Set.uIcc_of_le (by linarith)] at hw
    have hwpos : 0 ≤ w := le_trans hq0 hw.1
    have hwabs : |w| = w := abs_of_nonneg hwpos
    unfold gTrap
    rw [hwabs, min_eq_left (by linarith [hw.1]), max_eq_right (by linarith [hw.2])]
  -- split the window at the plateau ends and evaluate
  have hsplit : (∫ w in (-A₃)..A₃, gTrap A₁ A₂ L₁₂ w)
      = ((∫ w in (-A₃)..(-|A₁ - A₂|), gTrap A₁ A₂ L₁₂ w)
          + ∫ w in (-|A₁ - A₂|)..|A₁ - A₂|, gTrap A₁ A₂ L₁₂ w)
        + ∫ w in |A₁ - A₂|..A₃, gTrap A₁ A₂ L₁₂ w := by
    rw [integral_add_adjacent_intervals (gTrap_intervalIntegrable _ _ _ _ _)
      (gTrap_intervalIntegrable _ _ _ _ _),
      integral_add_adjacent_intervals (gTrap_intervalIntegrable _ _ _ _ _)
      (gTrap_intervalIntegrable _ _ _ _ _)]
  unfold Ftri Wtri
  rw [neg_zero, zero_sub, zero_add, hsplit, integral_congr hleft,
    integral_congr hmid, integral_congr hright]
  have hI₁ : (∫ x in (-A₃)..(-|A₁ - A₂|), (A₁ + A₂ + x))
      = ((A₁ + A₂ + -|A₁ - A₂|) ^ 2 - (A₁ + A₂ + -A₃) ^ 2) / 2 := by
    rw [integral_comp_add_left (f := fun x : ℝ => x) (d := A₁ + A₂), integral_id]
  have hI₂ : (∫ x in |A₁ - A₂|..A₃, (A₁ + A₂ - x))
      = ((A₁ + A₂ - |A₁ - A₂|) ^ 2 - (A₁ + A₂ - A₃) ^ 2) / 2 := by
    rw [integral_comp_sub_left (f := fun x : ℝ => x) (d := A₁ + A₂), integral_id]
  simp only [integral_div]
  rw [hI₁, hI₂, integral_const, smul_eq_mul]
  have hsq : |A₁ - A₂| ^ 2 = (A₁ - A₂) ^ 2 := sq_abs _
  field_simp
  nlinarith [hsq, hq]

/-! ## §6  (U1-BOXCAP) -/

/-- `Ftri` is dominated on any box by its clamped value `Fbox`. -/
theorem Ftri_le_Fbox (A₁ A₂ A₃ L₁₂ L₃ : ℝ) (hA₃ : 0 ≤ A₃) (hL : 0 ≤ L₁₂)
    (hL₃ : 0 ≤ L₃) (S₀ smax s : ℝ) (hbox : |s - S₀| ≤ smax) :
    Ftri A₁ A₂ A₃ L₁₂ L₃ s ≤ Fbox (Ftri A₁ A₂ A₃ L₁₂ L₃) S₀ smax :=
  le_Fbox _ (Ftri_even A₁ A₂ A₃ L₁₂ L₃)
    (fun _ _ h h' => Ftri_antitone A₁ A₂ A₃ L₁₂ L₃ hA₃ hL hL₃ h h') S₀ smax s
    hbox

/-- **(U1-BOXCAP) ⟹ (U1) on the box**: the box bound `Φ₀ ≥ Fbox − F(S₀)`
implies the pointwise bound `Φ₀ ≥ F(s) − F(S₀)` at every `s` of the box.
`Φ₀` is a parameter: no property of it is used. -/
theorem U1_of_boxcap (A₁ A₂ A₃ L₁₂ L₃ : ℝ) (hA₃ : 0 ≤ A₃) (hL : 0 ≤ L₁₂)
    (hL₃ : 0 ≤ L₃) (Φ₀ S₀ smax : ℝ)
    (hcap : Fbox (Ftri A₁ A₂ A₃ L₁₂ L₃) S₀ smax
      - Ftri A₁ A₂ A₃ L₁₂ L₃ S₀ ≤ Φ₀) :
    ∀ s : ℝ, |s - S₀| ≤ smax →
      Ftri A₁ A₂ A₃ L₁₂ L₃ s - Ftri A₁ A₂ A₃ L₁₂ L₃ S₀ ≤ Φ₀ := by
  intro s hs
  have := Ftri_le_Fbox A₁ A₂ A₃ L₁₂ L₃ hA₃ hL hL₃ S₀ smax s hs
  linarith

end Quant
