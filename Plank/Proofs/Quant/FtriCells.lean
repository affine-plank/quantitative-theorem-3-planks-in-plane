/-
# `Ftri` in closed form, its breakpoints, and the cell quadratics

Port of `Dim2N3/KPlankFtriCells.lean` (App AX) — substrate-free, so the
port re-homes namespace and prose only.

The mechanism.  `gTrap` is the trapezoid of support half-width
`P = A₁ + A₂` and plateau half-width `p = |A₁ − A₂|`.  The identity that
makes everything elementary is the **four-term positive-part form**

    L₁₂ · gTrap w = (w+P)₊ − (w+p)₊ − (w−p)₊ + (w−P)₊        (`gTrap_eq`)

— a sum of ramps with kinks exactly at `w = ±P, ±p` and *no* kink at
`0`: the two `|w|`-kinks of the naive split cancel.  Its antiderivative
is the same sum with `t₊ ↦ (t₊)²/2 =: Qpos t` (`gTrapAnti`,
`hasDerivAt_gTrapAnti`), and the fundamental theorem gives the closed
forms

    Wtri c = gTrapAnti (c+A₃) − gTrapAnti (c−A₃)             (`Wtri_eq`)
    Ftri S = (2/L₃)·(gTrapAnti (A₃−S) − gTrapAnti (−A₃−S))   (`Ftri_eq`)

Expanding, `Ftri S` is a signed sum of eight terms `Qpos (b − S)`, one
per breakpoint

    (BP)   b ∈ {±A₃ ± (A₁+A₂)} ∪ {±A₃ ± |A₁−A₂|}

— here **derived** rather than posited.  `Qpos (b − ·)` is `(b−S)²/2`
for `S ≤ b` and `0` for `S ≥ b`, so on any interval containing no
breakpoint in its interior every term is a quadratic
(`Ftri_quadratic_on_cell`), and the certification functional inherits
this (`Q_quadratic_on_cell`) — which is what makes a per-cell minimum
(endpoints plus interior vertex) the *exact* box minimum
(`boxmin_eq_cellwise_min`).  §5 shows the breakpoint decision chain is
a partition with twelve reachable leaves.
-/
module

public import Plank.Proofs.Quant.Ftri

@[expose] public section


noncomputable section

open Set intervalIntegral

namespace Quant

/-! ## §1  `Qpos`: the antiderivative of the positive part -/

/-- `Qpos t = (t₊)²/2`, the antiderivative of `t ↦ t₊` vanishing on
`t ≤ 0`. -/
def Qpos (t : ℝ) : ℝ := (max 0 t) ^ 2 / 2

theorem Qpos_of_nonneg {t : ℝ} (h : 0 ≤ t) : Qpos t = t ^ 2 / 2 := by
  rw [Qpos, max_eq_right h]

theorem Qpos_of_nonpos {t : ℝ} (h : t ≤ 0) : Qpos t = 0 := by
  rw [Qpos, max_eq_left h]; ring

theorem Qpos_nonneg (t : ℝ) : 0 ≤ Qpos t := by
  rw [Qpos]; positivity

/-- `Qpos` is differentiable everywhere, with derivative the positive
part.  The only delicate point is `t = 0`, where the positive part
vanishes to second order, so the two one-sided derivatives agree. -/
theorem hasDerivAt_Qpos (t : ℝ) : HasDerivAt Qpos (max 0 t) t := by
  rcases lt_trichotomy t 0 with h | h | h
  · have hev : Qpos =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds h] with x hx
      exact Qpos_of_nonpos hx.le
    rw [max_eq_left h.le]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst h
    rw [max_self, hasDerivAt_iff_isLittleO]
    have hzero : Qpos 0 = 0 := Qpos_of_nonpos le_rfl
    simp only [hzero, sub_zero, smul_zero]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < 2 * c)]
      with y hy
    have hy' : |y| < 2 * c := by simpa [Real.dist_eq] using hy
    have h2 : Qpos y ≤ |y| * |y| / 2 := by
      have hm : (max 0 y) ^ 2 ≤ y ^ 2 := by
        rcases le_total 0 y with hy0 | hy0
        · rw [max_eq_right hy0]
        · rw [max_eq_left hy0]; simpa using sq_nonneg y
      have hy2 : |y| * |y| = y ^ 2 := by rw [abs_mul_abs_self]; ring
      rw [Qpos, hy2]
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Qpos_nonneg y)]
    nlinarith [abs_nonneg y, hy'.le]
  · have hev : Qpos =ᶠ[nhds t] fun x => x ^ 2 / 2 := by
      filter_upwards [eventually_gt_nhds h] with x hx
      exact Qpos_of_nonneg hx.le
    rw [max_eq_right h.le]
    have hd : HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t := by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    exact hd.congr_of_eventuallyEq hev

/-! ## §2  The four-term form of the trapezoid -/

theorem abs_sub_le_add {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) :
    |A₁ - A₂| ≤ A₁ + A₂ := by
  rcases le_total A₁ A₂ with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- **The four-term positive-part form of the trapezoid.**  With
support half-width `P = A₁ + A₂` and plateau half-width `p = |A₁ − A₂|`,
the trapezoid is a signed sum of four ramps whose kinks are exactly
`±P, ±p`.  In particular the `|w|`-kink at the origin present in the
naive split cancels — which is why `F`'s breakpoint set is (BP) and
contains no term from `w = 0`. -/
theorem gTrap_eq {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (L₁₂ w : ℝ) :
    gTrap A₁ A₂ L₁₂ w
      = (max 0 (w + (A₁ + A₂)) - max 0 (w + |A₁ - A₂|)
          - max 0 (w - |A₁ - A₂|) + max 0 (w - (A₁ + A₂))) / L₁₂ := by
  have hplat : min (2 * A₁) (2 * A₂) = (A₁ + A₂) - |A₁ - A₂| := by
    have := plateau_width A₁ A₂; linarith
  have hp0 : 0 ≤ |A₁ - A₂| := abs_nonneg _
  have hpP : |A₁ - A₂| ≤ A₁ + A₂ := abs_sub_le_add hA₁ hA₂
  unfold gTrap
  congr 1
  rw [hplat]
  set P := A₁ + A₂ with hPdef
  set p := |A₁ - A₂| with hpdef
  rcases le_total w (-P) with h1 | h1
  · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith : w + P ≤ 0),
      max_eq_left (by linarith : w + p ≤ 0), max_eq_left (by linarith : w - p ≤ 0),
      max_eq_left (by linarith : w - P ≤ 0),
      max_eq_left (le_trans (min_le_left _ _) (by linarith : P - -w ≤ 0))]
    ring
  rcases le_total w (-p) with h2 | h2
  · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith : (0:ℝ) ≤ w + P),
      max_eq_left (by linarith : w + p ≤ 0), max_eq_left (by linarith : w - p ≤ 0),
      max_eq_left (by linarith : w - P ≤ 0),
      min_eq_left (by linarith : P - -w ≤ P - p),
      max_eq_right (by linarith : (0:ℝ) ≤ P - -w)]
    ring
  rcases le_total w p with h3 | h3
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ w + P),
      max_eq_right (by linarith : (0:ℝ) ≤ w + p),
      max_eq_left (by linarith : w - p ≤ 0),
      max_eq_left (by linarith : w - P ≤ 0),
      min_eq_right (by have : |w| ≤ p := abs_le.mpr ⟨h2, h3⟩; linarith :
        P - p ≤ P - |w|),
      max_eq_right (by linarith : (0:ℝ) ≤ P - p)]
    ring
  rcases le_total w P with h4 | h4
  · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith : (0:ℝ) ≤ w + P),
      max_eq_right (by linarith : (0:ℝ) ≤ w + p),
      max_eq_right (by linarith : (0:ℝ) ≤ w - p),
      max_eq_left (by linarith : w - P ≤ 0),
      min_eq_left (by linarith : P - w ≤ P - p),
      max_eq_right (by linarith : (0:ℝ) ≤ P - w)]
    ring
  · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith : (0:ℝ) ≤ w + P),
      max_eq_right (by linarith : (0:ℝ) ≤ w + p),
      max_eq_right (by linarith : (0:ℝ) ≤ w - p),
      max_eq_right (by linarith : (0:ℝ) ≤ w - P),
      max_eq_left (le_trans (min_le_left _ _) (by linarith : P - w ≤ 0))]
    ring

/-! ## §3  The antiderivative and the closed forms -/

/-- The antiderivative of `gTrap`: the four-term form with `t₊`
replaced by `(t₊)²/2`. -/
def gTrapAnti (A₁ A₂ L₁₂ : ℝ) (x : ℝ) : ℝ :=
  (Qpos (x + (A₁ + A₂)) - Qpos (x + |A₁ - A₂|)
    - Qpos (x - |A₁ - A₂|) + Qpos (x - (A₁ + A₂))) / L₁₂

theorem hasDerivAt_gTrapAnti {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (L₁₂ x : ℝ) :
    HasDerivAt (gTrapAnti A₁ A₂ L₁₂) (gTrap A₁ A₂ L₁₂ x) x := by
  have hshift : ∀ m : ℝ, HasDerivAt (fun y : ℝ => Qpos (y + m)) (max 0 (x + m)) x := by
    intro m
    simpa [Function.comp_def] using (hasDerivAt_Qpos (x + m)).comp x ((hasDerivAt_id x).add_const m)
  have h1 := hshift (A₁ + A₂)
  have h2 := hshift |A₁ - A₂|
  have h3 := hshift (-|A₁ - A₂|)
  have h4 := hshift (-(A₁ + A₂))
  simp only [← sub_eq_add_neg] at h3 h4
  rw [gTrap_eq hA₁ hA₂]
  exact (((h1.sub h2).sub h3).add h4).div_const L₁₂

/-- **`Wtri` in closed form.** -/
theorem Wtri_eq {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (A₃ L₁₂ c : ℝ) :
    Wtri A₁ A₂ A₃ L₁₂ c
      = gTrapAnti A₁ A₂ L₁₂ (c + A₃) - gTrapAnti A₁ A₂ L₁₂ (c - A₃) := by
  unfold Wtri
  exact integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_gTrapAnti hA₁ hA₂ L₁₂ y)
    (gTrap_intervalIntegrable _ _ _ _ _)

/-- **`Ftri` in closed form** — App AM's closed form for `F`, as an
elementary expression in eight `Qpos` terms. -/
theorem Ftri_eq {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (A₃ L₁₂ L₃ S : ℝ) :
    Ftri A₁ A₂ A₃ L₁₂ L₃ S
      = (2 / L₃) * (gTrapAnti A₁ A₂ L₁₂ (A₃ - S)
          - gTrapAnti A₁ A₂ L₁₂ (-A₃ - S)) := by
  unfold Ftri
  rw [Wtri_eq hA₁ hA₂, show -S + A₃ = A₃ - S by ring, show -S - A₃ = -A₃ - S by ring]

/-- `Ftri` written out over its eight breakpoints: each term is
`Qpos (b − S)` with `b` running over (BP). -/
theorem Ftri_eq_bp {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (A₃ L₁₂ L₃ S : ℝ) :
    Ftri A₁ A₂ A₃ L₁₂ L₃ S
      = (2 / L₃) *
        (((Qpos ((A₃ + (A₁ + A₂)) - S) - Qpos ((A₃ + |A₁ - A₂|) - S)
            - Qpos ((A₃ - |A₁ - A₂|) - S) + Qpos ((A₃ - (A₁ + A₂)) - S)) / L₁₂)
          - ((Qpos ((-A₃ + (A₁ + A₂)) - S) - Qpos ((-A₃ + |A₁ - A₂|) - S)
            - Qpos ((-A₃ - |A₁ - A₂|) - S) + Qpos ((-A₃ - (A₁ + A₂)) - S)) / L₁₂)) := by
  rw [Ftri_eq hA₁ hA₂]
  unfold gTrapAnti
  congr 3 <;> ring_nf

/-- `{x, −x} = {|x|, −|x|}`: all that separates the shift form of (BP)
from its magnitude form `±m₁, …, ±m₄`. -/
theorem bp_pair_abs (x : ℝ) : ({x, -x} : Set ℝ) = {|x|, -|x|} := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, Set.pair_comm]; simp

/-! ## §4  Agreeing with a quadratic on an interval -/

/-- `f` agrees with a quadratic polynomial on `[u, v]`. -/
def QuadOn (f : ℝ → ℝ) (u v : ℝ) : Prop :=
  ∃ a b c : ℝ, ∀ x ∈ Icc u v, f x = a * x ^ 2 + b * x + c

theorem QuadOn.sub {f g : ℝ → ℝ} {u v : ℝ} (hf : QuadOn f u v) (hg : QuadOn g u v) :
    QuadOn (fun x => f x - g x) u v := by
  obtain ⟨a, b, c, hf⟩ := hf
  obtain ⟨a', b', c', hg⟩ := hg
  refine ⟨a - a', b - b', c - c', fun x hx => ?_⟩
  show f x - g x = _
  rw [hf x hx, hg x hx]; ring

theorem QuadOn.add {f g : ℝ → ℝ} {u v : ℝ} (hf : QuadOn f u v) (hg : QuadOn g u v) :
    QuadOn (fun x => f x + g x) u v := by
  obtain ⟨a, b, c, hf⟩ := hf
  obtain ⟨a', b', c', hg⟩ := hg
  refine ⟨a + a', b + b', c + c', fun x hx => ?_⟩
  show f x + g x = _
  rw [hf x hx, hg x hx]; ring

theorem QuadOn.div_const {f : ℝ → ℝ} {u v : ℝ} (hf : QuadOn f u v) (k : ℝ) :
    QuadOn (fun x => f x / k) u v := by
  obtain ⟨a, b, c, hf⟩ := hf
  refine ⟨a / k, b / k, c / k, fun x hx => ?_⟩
  show f x / k = _
  rw [hf x hx]; ring

theorem QuadOn.const_mul {f : ℝ → ℝ} {u v : ℝ} (hf : QuadOn f u v) (k : ℝ) :
    QuadOn (fun x => k * f x) u v := by
  obtain ⟨a, b, c, hf⟩ := hf
  refine ⟨k * a, k * b, k * c, fun x hx => ?_⟩
  show k * f x = _
  rw [hf x hx]; ring

/-- `QuadOn` transported along a translation of the variable. -/
theorem QuadOn.comp_add {f : ℝ → ℝ} {k u v : ℝ} (hf : QuadOn f (k + u) (k + v)) :
    QuadOn (fun s => f (k + s)) u v := by
  obtain ⟨a, b, c, hf⟩ := hf
  refine ⟨a, 2 * a * k + b, a * k ^ 2 + b * k + c, fun s hs => ?_⟩
  show f (k + s) = _
  rw [hf (k + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩]
  ring

/-- **The cell lemma for one breakpoint.**  `Qpos (b − ·)` agrees with
a quadratic on `[u, v]` as soon as the breakpoint `b` does not lie in
the interior. -/
theorem Qpos_sub_quadOn {b u v : ℝ} (h : v ≤ b ∨ b ≤ u) :
    QuadOn (fun x => Qpos (b - x)) u v := by
  rcases h with h | h
  · refine ⟨1 / 2, -b, b ^ 2 / 2, fun x hx => ?_⟩
    show Qpos (b - x) = _
    rw [Qpos_of_nonneg (by linarith [hx.2] : (0:ℝ) ≤ b - x)]
    ring
  · refine ⟨0, 0, 0, fun x hx => ?_⟩
    show Qpos (b - x) = _
    rw [Qpos_of_nonpos (by linarith [hx.1] : b - x ≤ 0)]
    ring

/-- **`Ftri` is exactly quadratic on every cell.**  If none of the
eight breakpoints `±A₃ ± (A₁+A₂)`, `±A₃ ± |A₁−A₂|` lies in the interior
of `[u, v]`, then `Ftri` agrees on `[u, v]` with a quadratic — which is
what makes the per-cell minimum (endpoints plus interior vertex) the
*exact* box minimum. -/
theorem Ftri_quadratic_on_cell {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (A₃ L₁₂ L₃ u v : ℝ)
    (b₁ : v ≤ A₃ + (A₁ + A₂) ∨ A₃ + (A₁ + A₂) ≤ u)
    (b₂ : v ≤ A₃ + |A₁ - A₂| ∨ A₃ + |A₁ - A₂| ≤ u)
    (b₃ : v ≤ A₃ - |A₁ - A₂| ∨ A₃ - |A₁ - A₂| ≤ u)
    (b₄ : v ≤ A₃ - (A₁ + A₂) ∨ A₃ - (A₁ + A₂) ≤ u)
    (b₅ : v ≤ -A₃ + (A₁ + A₂) ∨ -A₃ + (A₁ + A₂) ≤ u)
    (b₆ : v ≤ -A₃ + |A₁ - A₂| ∨ -A₃ + |A₁ - A₂| ≤ u)
    (b₇ : v ≤ -A₃ - |A₁ - A₂| ∨ -A₃ - |A₁ - A₂| ≤ u)
    (b₈ : v ≤ -A₃ - (A₁ + A₂) ∨ -A₃ - (A₁ + A₂) ≤ u) :
    QuadOn (Ftri A₁ A₂ A₃ L₁₂ L₃) u v := by
  have hq : QuadOn (fun S =>
      (2 / L₃) *
        (((Qpos ((A₃ + (A₁ + A₂)) - S) - Qpos ((A₃ + |A₁ - A₂|) - S)
            - Qpos ((A₃ - |A₁ - A₂|) - S) + Qpos ((A₃ - (A₁ + A₂)) - S)) / L₁₂)
          - ((Qpos ((-A₃ + (A₁ + A₂)) - S) - Qpos ((-A₃ + |A₁ - A₂|) - S)
            - Qpos ((-A₃ - |A₁ - A₂|) - S) + Qpos ((-A₃ - (A₁ + A₂)) - S)) / L₁₂)))
      u v :=
    QuadOn.const_mul
      (QuadOn.sub
        (QuadOn.div_const
          (QuadOn.add
            (QuadOn.sub (QuadOn.sub (Qpos_sub_quadOn b₁) (Qpos_sub_quadOn b₂))
              (Qpos_sub_quadOn b₃))
            (Qpos_sub_quadOn b₄)) L₁₂)
        (QuadOn.div_const
          (QuadOn.add
            (QuadOn.sub (QuadOn.sub (Qpos_sub_quadOn b₅) (Qpos_sub_quadOn b₆))
              (Qpos_sub_quadOn b₇))
            (Qpos_sub_quadOn b₈)) L₁₂)) (2 / L₃)
  obtain ⟨a, b, c, hq⟩ := hq
  exact ⟨a, b, c, fun S hS => by rw [Ftri_eq_bp hA₁ hA₂]; exact hq S hS⟩

/-- The (U1-BOX) certification functional, after the `F(S₀)`
cancellation: `Q s = Φ(0) + s²/A − [F(S₀+s) − F(S₀)]`. -/
def Qcert (Φ₀ Alg S₀ : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  Φ₀ + s ^ 2 / Alg - (F (S₀ + s) - F S₀)

/-- **The certification replay lemma**: on a cell of the `s`-partition
(equivalently: an `S`-cell translated by `S₀`) the certification
functional is exactly quadratic, so its minimum over the cell is
attained at an endpoint or at the vertex `−B/2A`. -/
theorem Q_quadratic_on_cell {F : ℝ → ℝ} {Φ₀ Alg S₀ u v : ℝ}
    (hF : QuadOn F (S₀ + u) (S₀ + v)) :
    QuadOn (Qcert Φ₀ Alg S₀ F) u v := by
  have h1 : QuadOn (fun s : ℝ => Φ₀ + s ^ 2 / Alg) u v :=
    ⟨1 / Alg, 0, Φ₀, fun s _ => by ring⟩
  have h2 : QuadOn (fun s => F (S₀ + s) - F S₀) u v :=
    QuadOn.sub (QuadOn.comp_add hF) ⟨0, 0, F S₀, fun _ _ => by ring⟩
  exact h1.sub h2

/-! ## §5  The breakpoint decision chain is a partition -/

/-- The tier of the breakpoint decision tree: `A₃` against the plateau
half-width `|A₁−A₂|` and the support half-width `A₁+A₂`. -/
inductive Tier | C1 | C2 | C3
  deriving DecidableEq, Repr

/-- The sub-index of the decision tree: `A₃` against `min` and `max` of
`A₁, A₂`. -/
inductive Sub | a | b | c
  deriving DecidableEq, Repr

/-- A leaf of the tree: tier, sub-index, and the `A₁ ≤ A₂` relabelling
flag. -/
structure Leaf where
  tier : Tier
  sub : Sub
  swapped : Bool
  deriving DecidableEq, Repr

def tierCond : Tier → ℝ → ℝ → ℝ → Prop
  | Tier.C1, A₁, A₂, A₃ => A₃ ≤ |A₁ - A₂|
  | Tier.C2, A₁, A₂, A₃ => |A₁ - A₂| < A₃ ∧ A₃ ≤ A₁ + A₂
  | Tier.C3, A₁, A₂, A₃ => A₁ + A₂ < A₃

def subCond : Sub → ℝ → ℝ → ℝ → Prop
  | Sub.a, A₁, A₂, A₃ => A₃ ≤ min A₁ A₂
  | Sub.b, A₁, A₂, A₃ => min A₁ A₂ < A₃ ∧ A₃ ≤ max A₁ A₂
  | Sub.c, A₁, A₂, A₃ => max A₁ A₂ < A₃

/-- The leaf condition: the three tests of the decision chain. -/
def leafCond (l : Leaf) (A₁ A₂ A₃ : ℝ) : Prop :=
  (l.swapped = true ↔ A₂ < A₁) ∧ tierCond l.tier A₁ A₂ A₃ ∧ subCond l.sub A₁ A₂ A₃

theorem tier_exists (A₁ A₂ A₃ : ℝ) : ∃ t, tierCond t A₁ A₂ A₃ := by
  rcases le_or_gt A₃ |A₁ - A₂| with h | h
  · exact ⟨Tier.C1, h⟩
  rcases le_or_gt A₃ (A₁ + A₂) with h2 | h2
  · exact ⟨Tier.C2, h, h2⟩
  · exact ⟨Tier.C3, h2⟩

/-- The three tiers are mutually exclusive.  Nonnegativity of `A₁, A₂`
is needed and is automatic for the box data: without it
`|A₁ − A₂| > A₁ + A₂` and tiers `C1`, `C3` can overlap. -/
theorem tier_unique {t t' : Tier} {A₁ A₂ A₃ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (h : tierCond t A₁ A₂ A₃) (h' : tierCond t' A₁ A₂ A₃) : t = t' := by
  have habs : |A₁ - A₂| ≤ A₁ + A₂ := abs_sub_le_add hA₁ hA₂
  cases t <;> cases t' <;> simp only [tierCond] at h h' <;>
    first
      | rfl
      | (exfalso; linarith)

theorem sub_exists (A₁ A₂ A₃ : ℝ) : ∃ s, subCond s A₁ A₂ A₃ := by
  rcases le_or_gt A₃ (min A₁ A₂) with h | h
  · exact ⟨Sub.a, h⟩
  rcases le_or_gt A₃ (max A₁ A₂) with h2 | h2
  · exact ⟨Sub.b, h, h2⟩
  · exact ⟨Sub.c, h2⟩

theorem sub_unique {s s' : Sub} {A₁ A₂ A₃ : ℝ} (h : subCond s A₁ A₂ A₃)
    (h' : subCond s' A₁ A₂ A₃) : s = s' := by
  have hle : min A₁ A₂ ≤ max A₁ A₂ := min_le_max
  cases s <;> cases s' <;> simp only [subCond] at h h' <;>
    first
      | rfl
      | (exfalso; linarith)

/-- **The decision chain is a partition**: every triple `(A₁, A₂, A₃)`
satisfies the leaf condition of exactly one leaf.  Ties fall into the
closed side of each test by construction, so degenerate configurations
need no separate case. -/
theorem leaf_exhaustive {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (A₃ : ℝ) :
    ∃! l : Leaf, leafCond l A₁ A₂ A₃ := by
  obtain ⟨t, ht⟩ := tier_exists A₁ A₂ A₃
  obtain ⟨s, hs⟩ := sub_exists A₁ A₂ A₃
  refine ⟨⟨t, s, decide (A₂ < A₁)⟩, ⟨by simp, ht, hs⟩, ?_⟩
  rintro ⟨t', s', b'⟩ ⟨hb', ht', hs'⟩
  have h1 : t' = t := tier_unique hA₁ hA₂ ht' ht
  have h2 : s' = s := sub_unique hs' hs
  subst h1; subst h2
  simp only [Leaf.mk.injEq, true_and]
  rcases lt_or_ge A₂ A₁ with hlt | hle
  · rw [decide_eq_true hlt]
    exact hb'.mpr hlt
  · have hb : b' = false := by
      by_contra hcon
      exact absurd (hb'.mp (by simpa using hcon)) (not_lt.mpr hle)
    rw [hb, decide_eq_false (not_lt.mpr hle)]

/-- The leaf table has **12** reachable leaves rather than 18: `C1c`,
`C3a` and `C3b` are unreachable for nonnegative `A₁, A₂`. -/
theorem leaf_twelve {l : Leaf} {A₁ A₂ A₃ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (h : leafCond l A₁ A₂ A₃) :
    ¬(l.tier = Tier.C1 ∧ l.sub = Sub.c) ∧ ¬(l.tier = Tier.C3 ∧ l.sub ≠ Sub.c) := by
  obtain ⟨lt, ls, lb⟩ := l
  obtain ⟨-, ht, hs⟩ := h
  dsimp only at ht hs ⊢
  have hminmax : min A₁ A₂ ≤ max A₁ A₂ := min_le_max
  have hmax : max A₁ A₂ ≤ A₁ + A₂ := by
    rcases le_total A₁ A₂ with hle | hle
    · rw [max_eq_right hle]; linarith
    · rw [max_eq_left hle]; linarith
  have habs : |A₁ - A₂| ≤ max A₁ A₂ := by
    rcases le_total A₁ A₂ with hle | hle
    · rw [abs_of_nonpos (by linarith), max_eq_right hle]; linarith
    · rw [abs_of_nonneg (by linarith), max_eq_left hle]; linarith
  refine ⟨?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    simp only [tierCond] at ht
    simp only [subCond] at hs
    linarith
  · rintro ⟨rfl, hne⟩
    simp only [tierCond] at ht
    cases ls with
    | a => simp only [subCond] at hs; linarith
    | b => simp only [subCond] at hs; linarith [hs.2]
    | c => exact hne rfl

/-! ## §6  The box minimum is the least of the cell minima -/

/-- **`Finset.inf'` bookkeeping**: if the box is covered by finitely
many cells and `f` attains the value `m i` on cell `i` and is bounded
below by it there, then the box minimum is `⨅ i, m i`.  Combined with
`Ftri_quadratic_on_cell` (each cell quadratic, so its minimum is at an
endpoint or the vertex) this is "min over box = min over cells". -/
theorem boxmin_eq_cellwise_min {ι : Type*} {c : Finset ι} (hc : c.Nonempty)
    {cell : ι → Set ℝ} {S : Set ℝ} (hcover : S = ⋃ i ∈ c, cell i)
    {f : ℝ → ℝ} {m : ι → ℝ}
    (hmem : ∀ i ∈ c, ∃ x ∈ cell i, f x = m i)
    (hlb : ∀ i ∈ c, ∀ x ∈ cell i, m i ≤ f x) :
    IsLeast (f '' S) (c.inf' hc m) := by
  obtain ⟨i₀, hi₀, hval⟩ := Finset.exists_mem_eq_inf' hc m
  obtain ⟨x₀, hx₀, hfx₀⟩ := hmem i₀ hi₀
  constructor
  · refine ⟨x₀, ?_, ?_⟩
    · rw [hcover]
      exact Set.mem_biUnion hi₀ hx₀
    · rw [hfx₀, hval]
  · rintro y ⟨x, hxS, rfl⟩
    rw [hcover] at hxS
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxS
    exact le_trans (Finset.inf'_le m hi) (hlb i hi x hxi)

end Quant
