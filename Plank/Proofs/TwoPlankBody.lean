/-
# Two planks on a convex body — Hunter's proof

Paper §4 (`sec:warmup`), after Hunter (1993, Figure 1).

> **Theorem (two planks).**  If two planks cover a compact convex body,
> their relative widths sum to at least `1`.

Normalise so that the body's two shadows are `[0,1]`; the planks are
then the windows `[l₁,h₁]` in `X` and `[l₂,h₂]` in `Y`, their union is a
cross, and its complement is four open quadrants, one at each corner
of `[l₁,h₁] × [l₂,h₂]`.  The paper's steps, in order:

* **§1 Coordinates.**  `Coords` — a set with two coordinates along
  which it is segment-closed and ranges over `[0,1]`, two windows that
  cover it, and the four width-realising points.  ★ The reflections
  `flipX`, `swap`, `flipY` are the substitutions `X ↦ 1 − X`, `X ↔ Y`,
  `Y ↦ 1 − Y`: every statement at one corner is the same statement at
  the others. ★
* **§2 The four corners.**  `in_H`, `in_V` — if `h₁ < 1` the realiser
  `P_R` is outside the first plank, so inside the second.
* **§3 The segment through a corner.**  `segment_below` is the segment
  argument as one real inequality (the midpoint of the two thresholds,
  the only division of the argument); `corner_line` is the paper's
  crossing claim `(1 − y_R)(1 − h₁) ≤ (1 − x_U)(h₂ − y_R)`.
* **§4 Zero margins.**  `corner_drop`, `zero_margin` — if `l₁ ≤ 0` the
  crossing inequalities at the two right-hand corners, with the factor
  `1 − x ≤ 1` dropped, give `g₂ ≥ 1 − h₁`.  No enlargement is needed.
* **§5 Euclid I.43 and the sign**, on a box `[x_L,x_R] × [y_B,y_T]`
  (the paper's `[0,1]²`; the general box saves the rescaling).
  `euclid`: the four incidences (E) add up to
  `g₁H + g₂W − WH = (x_T − x_B)(y_L − y_R)`.  `sign`: the paper's two
  eliminations, multiplied out, are the single identity
  `abcd·H·(x_T − x_B)(y_L − y_R) = (x_T − x_B)²·[…]` with `[…] ≥ 0`.
  `hunter_core`: `g₁ + g₂ ≥ 1` once `W, H ≥ 1`.
* **§6 The enlarged body.**  `vertex` (two slanted lines meet, at the
  extreme point of their wedge), `collinear` (three points on a line);
  `enlarged_body` — the four lines through the corners, the four
  vertices, the box containing the four realisers, the corners on the
  sides (that is (E)), and `hunter_core`.
* **§7** `positive_margins`, `twoplank_normalised`, `twoplank_affine` —
  the assembly, and the theorem on a compact convex body in any real
  topological vector space for two continuous affine functionals.

The Cauchy–Schwarz proof of the same theorem is retained in
`Proofs/TwoPlankBodyCS.lean`.

Grading: KERNEL.  No `sorry`, nothing assumed.
-/
module

public import Plank.Proofs.Body

@[expose] public section


noncomputable section

open Set Finset Plank.Body

namespace Plank.TwoPlankBody

/-! ## §1  Coordinates -/

/-- ★ **The normalised picture** ★ — a set `T` with two coordinates
`X, Y` along which it is segment-closed and takes values in `[0,1]`,
two windows `[l₁,h₁]`, `[l₂,h₂]` whose cross covers it, and the four
width-realising points `P_L, P_R` (`X = 0, 1`) and `Q_D, Q_U`
(`Y = 0, 1`). -/
structure Coords (α : Type*) where
  T : Set α
  X : α → ℝ
  Y : α → ℝ
  seg : ∀ P ∈ T, ∀ Q ∈ T, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ∃ R ∈ T, X R = X P + t * (X Q - X P) ∧ Y R = Y P + t * (Y Q - Y P)
  range : ∀ P ∈ T, (0 ≤ X P ∧ X P ≤ 1) ∧ (0 ≤ Y P ∧ Y P ≤ 1)
  l1 : ℝ
  h1 : ℝ
  l2 : ℝ
  h2 : ℝ
  le1 : l1 ≤ h1
  le2 : l2 ≤ h2
  cov : ∀ P ∈ T, (l1 ≤ X P ∧ X P ≤ h1) ∨ (l2 ≤ Y P ∧ Y P ≤ h2)
  pL : ∃ P ∈ T, X P = 0
  pR : ∃ P ∈ T, X P = 1
  qD : ∃ P ∈ T, Y P = 0
  qU : ∃ P ∈ T, Y P = 1

namespace Coords

variable {α : Type*} (c : Coords α)

/-- ★ The reflection `X ↦ 1 − X` ★: the right-hand corners become the
left-hand ones. -/
def flipX : Coords α where
  T := c.T
  X := fun P => 1 - c.X P
  Y := c.Y
  seg P hP Q hQ t ht0 ht1 :=
    let ⟨R, hR, e1, e2⟩ := c.seg P hP Q hQ t ht0 ht1
    ⟨R, hR, by rw [e1]; ring, e2⟩
  range P hP := ⟨⟨by linarith [(c.range P hP).1.2], by linarith [(c.range P hP).1.1]⟩,
    (c.range P hP).2⟩
  l1 := 1 - c.h1
  h1 := 1 - c.l1
  l2 := c.l2
  h2 := c.h2
  le1 := by linarith [c.le1]
  le2 := c.le2
  cov P hP := (c.cov P hP).imp (fun h => ⟨by linarith [h.2], by linarith [h.1]⟩) id
  pL := let ⟨P, hP, e⟩ := c.pR; ⟨P, hP, by simp [e]⟩
  pR := let ⟨P, hP, e⟩ := c.pL; ⟨P, hP, by simp [e]⟩
  qD := c.qD
  qU := c.qU

/-- ★ The exchange `X ↔ Y` ★: the sides become the top and bottom. -/
def swap : Coords α where
  T := c.T
  X := c.Y
  Y := c.X
  seg P hP Q hQ t ht0 ht1 :=
    let ⟨R, hR, e1, e2⟩ := c.seg P hP Q hQ t ht0 ht1
    ⟨R, hR, e2, e1⟩
  range P hP := (c.range P hP).symm
  l1 := c.l2
  h1 := c.h2
  l2 := c.l1
  h2 := c.h1
  le1 := c.le2
  le2 := c.le1
  cov P hP := (c.cov P hP).symm
  pL := c.qD
  pR := c.qU
  qD := c.pL
  qU := c.pR

/-- The reflection `Y ↦ 1 − Y`, as `swap ∘ flipX ∘ swap`. -/
def flipY : Coords α := c.swap.flipX.swap

/-! ## §2  The four corners -/

/-- If `h₁ < 1`, a point with `X = 1` is outside the first plank, so
inside the second. -/
theorem in_H (hb : c.h1 < 1) {P : α} (hP : P ∈ c.T) (hX : c.X P = 1) :
    c.l2 ≤ c.Y P ∧ c.Y P ≤ c.h2 :=
  (c.cov P hP).resolve_left fun h => by linarith [h.2]

/-- If `h₂ < 1`, a point with `Y = 1` is inside the first plank. -/
theorem in_V (hd : c.h2 < 1) {P : α} (hP : P ∈ c.T) (hY : c.Y P = 1) :
    c.l1 ≤ c.X P ∧ c.X P ≤ c.h1 :=
  (c.cov P hP).resolve_right fun h => by linarith [h.2]

end Coords

/-! ## §3  The segment through a corner -/

/-- ★ **The segment argument as one real inequality** ★ — if every
`t ∈ [0,1]` satisfies `B ≤ tμ` or `tν ≤ Γ`, then `Bν ≤ Γμ`.
Contrapositively: if `Γμ < Bν` the thresholds `Γ/ν < B/μ` are in the
wrong order and their midpoint `(Γμ + Bν)/(2μν) ∈ [0,1]` satisfies
neither.  This is the only division in the segment argument. -/
theorem segment_below {mu nu B Ga : ℝ} (hmu : 0 < mu) (hnu : 0 < nu)
    (hB : 0 ≤ B) (hGa : 0 ≤ Ga) (hBmu : B ≤ mu)
    (hcov : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → B ≤ t * mu ∨ t * nu ≤ Ga) :
    B * nu ≤ Ga * mu := by
  by_contra hcon
  rw [not_le] at hcon
  have hden : (0:ℝ) < 2 * mu * nu := by positivity
  have ht0 : 0 ≤ (Ga * mu + B * nu) / (2 * mu * nu) := div_nonneg (by positivity) hden.le
  have ht1 : (Ga * mu + B * nu) / (2 * mu * nu) ≤ 1 := by
    rw [div_le_one hden]; linarith [mul_le_mul_of_nonneg_right hBmu hnu.le]
  rcases hcov _ ht0 ht1 with h | h
  · rw [div_mul_eq_mul_div, le_div_iff₀ hden] at h
    linarith [mul_lt_mul_of_pos_left hcon hmu]
  · rw [div_mul_eq_mul_div, div_le_iff₀ hden] at h
    linarith [mul_lt_mul_of_pos_left hcon hnu]

namespace Coords

variable {α : Type*} (c : Coords α)

/-- ★★ **The segment `P_R Q_U` passes below the corner** ★★ — with
`h₁ < 1` and `h₂ < 1`, the segment from `P_R` (to the right of the
corner `(h₁,h₂)`, not above it) to `Q_U` (above it, not to its right)
crosses the vertical through the corner at or below it, since the
points beyond a higher crossing would lie in the uncovered quadrant:
`(1 − y_R)(1 − h₁) ≤ (1 − x_U)(h₂ − y_R)`. -/
theorem corner_line (hb : c.h1 < 1) (hd : c.h2 < 1) {R U : α} (hR : R ∈ c.T) (hU : U ∈ c.T)
    (eR : c.X R = 1) (eU : c.Y U = 1) :
    (1 - c.Y R) * (1 - c.h1) ≤ (1 - c.X U) * (c.h2 - c.Y R) := by
  obtain ⟨hr1, hr2⟩ := c.in_H hb hR eR
  obtain ⟨hu1, hu2⟩ := c.in_V hd hU eU
  have key : (1 - c.h1) * (1 - c.Y R) ≤ (c.h2 - c.Y R) * (1 - c.X U) := by
    refine segment_below (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ?_
    intro t ht0 ht1
    obtain ⟨S, hS, eX, eY⟩ := c.seg R hR U hU t ht0 ht1
    rw [eR] at eX; rw [eU] at eY
    exact (c.cov S hS).imp (fun h => by rw [eX] at h; linarith [h.2])
      (fun h => by rw [eY] at h; linarith [h.2])
  linarith

/-! ## §4  Zero margins -/

/-- The crossing inequality with the factor `1 − x_U ≤ 1` dropped:
`(1 − y_R)(1 − h₁) ≤ h₂ − y_R`.  When `h₂ ≥ 1` it says `P_R ∈ H`. -/
theorem corner_drop (hb : c.h1 < 1) (hh1 : 0 ≤ c.h1) {R U : α} (hR : R ∈ c.T) (hU : U ∈ c.T)
    (eR : c.X R = 1) (eU : c.Y U = 1) : (1 - c.Y R) * (1 - c.h1) ≤ c.h2 - c.Y R := by
  obtain ⟨-, hr2⟩ := c.in_H hb hR eR
  rcases le_or_gt 1 c.h2 with hd | hd
  · linarith [mul_nonneg (by linarith [(c.range R hR).2.2] : 0 ≤ 1 - c.Y R) hh1]
  · have := mul_le_mul_of_nonneg_right (by linarith [(c.range U hU).1.1] : 1 - c.X U ≤ 1)
      (by linarith : 0 ≤ c.h2 - c.Y R)
    linarith [c.corner_line hb hd hR hU eR eU]

/-- ★★ **Zero margin** ★★ — if `l₁ ≤ 0` the theorem follows from the
two right-hand corners alone: with `y_R` the height of `P_R`,
`h₂ − y_R ≥ (1 − y_R)(1 − h₁)` and `y_R − l₂ ≥ y_R (1 − h₁)` (the
paper's similar triangles, at `P_R` itself), and adding,
`g₂ ≥ 1 − h₁ ≥ 1 − g₁`. -/
theorem zero_margin (h0 : c.l1 ≤ 0) : 1 ≤ (c.h1 - c.l1) + (c.h2 - c.l2) := by
  obtain ⟨R, hR, eR⟩ := c.pR
  obtain ⟨U, hU, eU⟩ := c.qU
  obtain ⟨D, hD, eD⟩ := c.qD
  rcases lt_or_ge c.h1 0 with hneg | hh1
  · -- the first plank misses `T`, so the second contains `Q_D` and `Q_U`
    have hU' := (c.cov U hU).resolve_left fun h => by linarith [(c.range U hU).1.1, h.2]
    have hD' := (c.cov D hD).resolve_left fun h => by linarith [(c.range D hD).1.1, h.2]
    linarith [c.le1, eU ▸ hU'.2, eD ▸ hD'.1]
  rcases le_or_gt 1 c.h1 with hb | hb
  · linarith [c.le2]
  have hup := c.corner_drop hb hh1 hR hU eR eU
  have hdown := c.flipY.corner_drop hb hh1 hR hD (by simpa [flipY, flipX, swap] using eR)
    (by simpa [flipY, flipX, swap] using eD)
  dsimp only [flipY, flipX, swap] at hdown
  linarith

end Coords

/-! ## §5  Euclid I.43 and the sign -/

/-- ★★ **Euclid I.43, summed over the four corners** ★★ — a body with
box `[x_L,x_R] × [y_B,y_T]`, the cross with windows `[l₁,h₁]`,
`[l₂,h₂]`, and the four vertices `W_L = (x_L, y_L)`, `W_T = (x_T, y_T)`,
`W_R = (x_R, y_R)`, `W_B = (x_B, y_B)`, one on each side of the box.
If each corner of the cross is collinear with its two adjacent vertices
(the four relations (E)), then with `W = x_R − x_L`, `H = y_T − y_B`,
`g₁ = h₁ − l₁`, `g₂ = h₂ − l₂`,

  `g₁ H + g₂ W − W H = (x_T − x_B)(y_L − y_R)` ;

on the unit box this is the paper's `g₁ + g₂ − 1 = (x_T − x_B)(y_L − y_R)`. -/
theorem euclid {l1 h1 l2 h2 xL xR yB yT xT xB yL yR : ℝ}
    (F1 : (l1 - xL) * (yT - h2) = (xT - l1) * (h2 - yL))
    (F2 : (xR - h1) * (yT - h2) = (h1 - xT) * (h2 - yR))
    (F3 : (l1 - xL) * (l2 - yB) = (xB - l1) * (yL - l2))
    (F4 : (xR - h1) * (l2 - yB) = (h1 - xB) * (yR - l2)) :
    (h1 - l1) * (yT - yB) + (h2 - l2) * (xR - xL) - (xR - xL) * (yT - yB)
      = (xT - xB) * (yL - yR) := by
  linear_combination -F1 - F2 - F3 - F4

/-- ★★ **The sign** ★★ — `(x_T − x_B)(y_L − y_R) ≥ 0`.  The paper
eliminates `a` between the two left relations and `b` between the two
right ones (`SL`, `SR`); multiplying the two results by the positive
brackets of the other and adding gives one identity,

  `a b c d H · (x_T − x_B)(y_L − y_R)
     = (x_T − x_B)² · [ b · c(y_T − y_R) · K_L + a · c(y_T − y_L) · K_R ]`,

`K_L = (h₂ − y_L)(y_L − l₂)`, `K_R = (h₂ − y_R)(y_R − l₂)`, whose right
side is visibly nonnegative when `W_L, W_R` lie between the corner rows. -/
theorem sign {l1 h1 l2 h2 xL xR yB yT xT xB yL yR : ℝ}
    (ha : xL < l1) (hb : h1 < xR) (hc : yB < l2) (hd : h2 < yT)
    (hL : l2 ≤ yL ∧ yL ≤ h2) (hR : l2 ≤ yR ∧ yR ≤ h2)
    (F1 : (l1 - xL) * (yT - h2) = (xT - l1) * (h2 - yL))
    (F2 : (xR - h1) * (yT - h2) = (h1 - xT) * (h2 - yR))
    (F3 : (l1 - xL) * (l2 - yB) = (xB - l1) * (yL - l2))
    (F4 : (xR - h1) * (l2 - yB) = (h1 - xB) * (yR - l2)) :
    0 ≤ (xT - xB) * (yL - yR) := by
  have SL : (xT - xB) * ((h2 - yL) * (yL - l2))
      = (l1 - xL) * ((yL - yB) * (yT - h2) - (l2 - yB) * (yT - yL)) := by
    linear_combination (-(yL - l2)) * F1 + (h2 - yL) * F3
  have SR : (xT - xB) * ((h2 - yR) * (yR - l2))
      = (xR - h1) * ((l2 - yB) * (yT - yR) - (yR - yB) * (yT - h2)) := by
    linear_combination (yR - l2) * F2 - (h2 - yR) * F4
  have key : (l1 - xL) * (xR - h1) * (l2 - yB) * (yT - h2) * (yT - yB)
        * ((xT - xB) * (yL - yR))
      = (xT - xB) ^ 2 * ((xR - h1) * ((l2 - yB) * (yT - yR)) * ((h2 - yL) * (yL - l2))
          + (l1 - xL) * ((l2 - yB) * (yT - yL)) * ((h2 - yR) * (yR - l2))) := by
    linear_combination (-((xR - h1) * ((l2 - yB) * (yT - yR)) * (xT - xB))) * SL
      - (l1 - xL) * ((l2 - yB) * (yT - yL)) * (xT - xB) * SR
  have hpos : 0 < (l1 - xL) * (xR - h1) * (l2 - yB) * (yT - h2) * (yT - yB) :=
    mul_pos (mul_pos (mul_pos (mul_pos (sub_pos.2 ha) (sub_pos.2 hb)) (sub_pos.2 hc))
      (sub_pos.2 hd)) (by linarith)
  refine (mul_nonneg_iff_of_pos_left hpos).mp ?_
  rw [key]
  refine mul_nonneg (sq_nonneg _) (add_nonneg ?_ ?_)
  · exact mul_nonneg (mul_nonneg (sub_pos.2 hb).le (mul_nonneg (sub_pos.2 hc).le (by linarith)))
      (mul_nonneg (sub_nonneg.2 hL.2) (sub_nonneg.2 hL.1))
  · exact mul_nonneg (mul_nonneg (sub_pos.2 ha).le (mul_nonneg (sub_pos.2 hc).le (by linarith)))
      (mul_nonneg (sub_nonneg.2 hR.2) (sub_nonneg.2 hR.1))

/-- ★★ **The theorem for the enlarged body** ★★ — `g₁ + g₂ ≥ 1` when
the box has width and height at least `1`: by `euclid` and `sign`,
`g₁ H + g₂ W ≥ W H`, and `g_i ≥ 0`, `W, H ≥ 1`. -/
theorem hunter_core {l1 h1 l2 h2 xL xR yB yT xT xB yL yR : ℝ}
    (ha : xL < l1) (hb : h1 < xR) (hc : yB < l2) (hd : h2 < yT)
    (hL : l2 ≤ yL ∧ yL ≤ h2) (hR : l2 ≤ yR ∧ yR ≤ h2)
    (F1 : (l1 - xL) * (yT - h2) = (xT - l1) * (h2 - yL))
    (F2 : (xR - h1) * (yT - h2) = (h1 - xT) * (h2 - yR))
    (F3 : (l1 - xL) * (l2 - yB) = (xB - l1) * (yL - l2))
    (F4 : (xR - h1) * (l2 - yB) = (h1 - xB) * (yR - l2))
    (hg1 : l1 ≤ h1) (hg2 : l2 ≤ h2) (hW : 1 ≤ xR - xL) (hH : 1 ≤ yT - yB) :
    1 ≤ (h1 - l1) + (h2 - l2) := by
  have E := euclid F1 F2 F3 F4
  have S := sign ha hb hc hd hL hR F1 F2 F3 F4
  have P1 := mul_nonneg (mul_nonneg (sub_nonneg.2 hg1) (by linarith : 0 ≤ yT - yB))
    (sub_nonneg.2 hW)
  have P2 := mul_nonneg (mul_nonneg (sub_nonneg.2 hg2) (by linarith : 0 ≤ xR - xL))
    (sub_nonneg.2 hH)
  -- `W H (g₁ + g₂ − 1) = (g₁H + g₂W − WH) + g₁H(W − 1) + g₂W(H − 1) ≥ 0`
  have := (mul_nonneg_iff_of_pos_left (mul_pos (by linarith) (by linarith) :
    0 < (xR - xL) * (yT - yB))).mp
    (by linarith : 0 ≤ (xR - xL) * (yT - yB) * (((h1 - l1) + (h2 - l2)) - 1))
  linarith

/-! ## §6  The enlarged body -/

/-- ★ **A vertex of the enlarged body** ★ — two lines with normals
`(−α₁, β₁)` and `(α₂, β₂)`, all entries positive, meet, and their
meeting point is the highest point of the wedge below both. -/
theorem vertex {α₁ β₁ γ₁ α₂ β₂ γ₂ x y : ℝ} (hα₁ : 0 < α₁) (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂)
    (hβ₂ : 0 < β₂) (h₁ : -α₁ * x + β₁ * y ≤ γ₁) (h₂ : α₂ * x + β₂ * y ≤ γ₂) :
    ∃ x₀ y₀ : ℝ, -α₁ * x₀ + β₁ * y₀ = γ₁ ∧ α₂ * x₀ + β₂ * y₀ = γ₂ ∧ y ≤ y₀ := by
  have hD : 0 < α₂ * β₁ + α₁ * β₂ := by positivity
  refine ⟨(γ₂ * β₁ - γ₁ * β₂) / (α₂ * β₁ + α₁ * β₂),
    (α₂ * γ₁ + α₁ * γ₂) / (α₂ * β₁ + α₁ * β₂), ?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · rw [le_div_iff₀ hD]
    linarith [mul_le_mul_of_nonneg_left h₁ hα₂.le, mul_le_mul_of_nonneg_left h₂ hα₁.le]

/-- `vertex` upside down: the lowest point of the wedge above both lines. -/
theorem vertex' {α₁ β₁ γ₁ α₂ β₂ γ₂ x y : ℝ} (hα₁ : 0 < α₁) (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂)
    (hβ₂ : 0 < β₂) (h₁ : -α₁ * x - β₁ * y ≤ γ₁) (h₂ : α₂ * x - β₂ * y ≤ γ₂) :
    ∃ x₀ y₀ : ℝ, -α₁ * x₀ - β₁ * y₀ = γ₁ ∧ α₂ * x₀ - β₂ * y₀ = γ₂ ∧ y₀ ≤ y := by
  obtain ⟨x₀, y₀, e₁, e₂, h⟩ := vertex hα₁ hβ₁ hα₂ hβ₂ (γ₁ := γ₁) (γ₂ := γ₂) (x := x) (y := -y)
    (by linarith) (by linarith)
  exact ⟨x₀, -y₀, by linarith, by linarith, by linarith⟩

/-- ★ **Three points on a line** ★ — if `(x₀,y₀), (x₁,y₁), (x₂,y₂)` lie
on the line `ax + by = c` with `a ≠ 0`, then
`(x₁ − x₀)(y₂ − y₀) = (x₂ − x₀)(y₁ − y₀)`: this is Euclid I.43 at the
corner `(x₀,y₀)` of the rectangle spanned by the other two. -/
theorem collinear {a b c x₀ y₀ x₁ y₁ x₂ y₂ : ℝ} (ha : a ≠ 0)
    (e₀ : a * x₀ + b * y₀ = c) (e₁ : a * x₁ + b * y₁ = c) (e₂ : a * x₂ + b * y₂ = c) :
    (x₁ - x₀) * (y₂ - y₀) = (x₂ - x₀) * (y₁ - y₀) := by
  apply mul_left_cancel₀ ha
  linear_combination (y₂ - y₀) * e₁ - (y₁ - y₀) * e₂ + (y₁ - y₂) * e₀

/-- ★★ **The enlarged body** ★★ — all four margins positive (windows
`[l₁,h₁]`, `[l₂,h₂]` with `0 < l₁`, `h₁ < 1`, `0 < l₂`, `h₂ < 1`).  The
realisers are `P_L = (0, p_L)`, `P_R = (1, p_R)`, `Q_D = (q_D, 0)`,
`Q_U = (q_U, 1)`, each inside the other plank, and the four crossing
inequalities hold.  The line through each corner parallel to the
segment joining its two neighbouring realisers has normal
`(1 − p_R, 1 − q_U)`, `(−(1 − p_L), q_U)`, `(p_R, −(1 − q_D))`,
`(−p_L, −q_D)` — all four slanted.  Adjacent lines meet in the vertices
`W_T, W_L, W_B, W_R`, each the extreme point of its wedge, so the box of
the quadrilateral contains `[0,1]²` (its wedges contain the realisers);
the corners lie on the sides (`collinear`), which is (E); and
`hunter_core` closes. -/
theorem enlarged_body {l1 h1 l2 h2 pL pR qD qU : ℝ}
    (ha : 0 < l1) (hb : h1 < 1) (hc : 0 < l2) (hd : h2 < 1)
    (hpL : l2 ≤ pL ∧ pL ≤ h2) (hpR : l2 ≤ pR ∧ pR ≤ h2)
    (hqD : l1 ≤ qD ∧ qD ≤ h1) (hqU : l1 ≤ qU ∧ qU ≤ h1)
    (kTR : (1 - pR) * (1 - h1) ≤ (1 - qU) * (h2 - pR))
    (kTL : (1 - pL) * l1 ≤ qU * (h2 - pL))
    (kBR : pR * (1 - h1) ≤ (1 - qD) * (pR - l2))
    (kBL : pL * l1 ≤ qD * (pL - l2)) :
    1 ≤ (h1 - l1) + (h2 - l2) := by
  -- the four normals, all slanted
  have hA1 : 0 < 1 - pR := by linarith [hpR.2]
  have hB1 : 0 < 1 - qU := by linarith [hqU.2]
  have hA2 : 0 < 1 - pL := by linarith [hpL.2]
  have hB2 : 0 < qU := by linarith [hqU.1]
  have hA3 : 0 < pR := by linarith [hpR.1]
  have hB3 : 0 < 1 - qD := by linarith [hqD.2]
  have hA4 : 0 < pL := by linarith [hpL.1]
  have hB4 : 0 < qD := by linarith [hqD.1]
  -- ★ the four vertices, each extreme for its wedge, which contains a realiser ★
  obtain ⟨xT, yT, eT1, eT2, hyT⟩ := vertex hA2 hB2 hA1 hB1 (x := qU) (y := 1)
    (by linarith only [kTL] : -(1 - pL) * qU + qU * 1 ≤ -(1 - pL) * l1 + qU * h2)
    (by linarith only [kTR] : (1 - pR) * qU + (1 - qU) * 1 ≤ (1 - pR) * h1 + (1 - qU) * h2)
  obtain ⟨yL, xL, eL1, eL2, hxL⟩ := vertex' hB4 hA4 hB2 hA2 (x := pL) (y := 0)
    (by linarith only [kBL] : -qD * pL - pL * 0 ≤ -pL * l1 + -qD * l2)
    (by linarith only [kTL] : qU * pL - (1 - pL) * 0 ≤ -(1 - pL) * l1 + qU * h2)
  obtain ⟨xB, yB, eB1, eB2, hyB⟩ := vertex' hA4 hB4 hA3 hB3 (x := qD) (y := 0)
    (by linarith only [kBL] : -pL * qD - qD * 0 ≤ -pL * l1 + -qD * l2)
    (by linarith only [kBR] : pR * qD - (1 - qD) * 0 ≤ pR * h1 + -(1 - qD) * l2)
  obtain ⟨yR, xR, eR1, eR2, hxR⟩ := vertex hB3 hA3 hB1 hA1 (x := pR) (y := 1)
    (by linarith only [kBR] : -(1 - qD) * pR + pR * 1 ≤ pR * h1 + -(1 - qD) * l2)
    (by linarith only [kTR] : (1 - qU) * pR + (1 - pR) * 1 ≤ (1 - pR) * h1 + (1 - qU) * h2)
  -- the side vertices lie between the corner rows: the lines through the
  -- left corners have slopes of opposite signs and `W_L` is left of both
  have hyL2 : yL ≤ h2 := le_of_mul_le_mul_left
    (by linarith [eL2, mul_nonneg hA2.le (by linarith : 0 ≤ l1 - xL)]) hB2
  have hyL1 : l2 ≤ yL := le_of_mul_le_mul_left
    (by linarith [eL1, mul_nonneg hA4.le (by linarith : 0 ≤ l1 - xL)]) hB4
  have hyR1 : l2 ≤ yR := le_of_mul_le_mul_left
    (by linarith [eR1, mul_nonneg hA3.le (by linarith : 0 ≤ xR - h1)]) hB3
  have hyR2 : yR ≤ h2 := le_of_mul_le_mul_left
    (by linarith [eR2, mul_nonneg hA1.le (by linarith : 0 ≤ xR - h1)]) hB1
  -- ★ Euclid I.43: each corner is collinear with its two adjacent vertices ★
  have F1 := collinear (a := -(1 - pL)) (b := qU) (c := -(1 - pL) * l1 + qU * h2)
    (x₀ := l1) (y₀ := h2) (x₁ := xL) (y₁ := yL) (x₂ := xT) (y₂ := yT)
    (neg_ne_zero.2 hA2.ne') (by ring) (by linarith only [eL2]) eT1
  have F2 := collinear (a := 1 - pR) (b := 1 - qU) (c := (1 - pR) * h1 + (1 - qU) * h2)
    (x₀ := h1) (y₀ := h2) (x₁ := xT) (y₁ := yT) (x₂ := xR) (y₂ := yR)
    hA1.ne' (by ring) eT2 (by linarith only [eR2])
  have F3 := collinear (a := -pL) (b := -qD) (c := -pL * l1 + -qD * l2)
    (x₀ := l1) (y₀ := l2) (x₁ := xL) (y₁ := yL) (x₂ := xB) (y₂ := yB)
    (neg_ne_zero.2 hA4.ne') (by ring) (by linarith only [eL1]) (by linarith only [eB1])
  have F4 := collinear (a := pR) (b := -(1 - qD)) (c := pR * h1 + -(1 - qD) * l2)
    (x₀ := h1) (y₀ := l2) (x₁ := xB) (y₁ := yB) (x₂ := xR) (y₂ := yR)
    hA3.ne' (by ring) (by linarith only [eB2]) (by linarith only [eR1])
  exact hunter_core (xL := xL) (xR := xR) (yB := yB) (yT := yT) (xT := xT) (xB := xB)
    (yL := yL) (yR := yR) (by linarith) (by linarith) (by linarith) (by linarith)
    ⟨hyL1, hyL2⟩ ⟨hyR1, hyR2⟩ (by linear_combination -F1) (by linear_combination -F2)
    (by linear_combination F3) (by linear_combination F4) (by linarith [hqU.1, hqU.2])
    (by linarith [hpR.1, hpR.2]) (by linarith) (by linarith)

/-! ## §7  The assembly -/

namespace Coords

variable {α : Type*} (c : Coords α)

/-- ★★ **Positive margins** ★★ — the four crossing inequalities are
`corner_line` at `c`, `c.flipX`, `c.flipY`, `c.flipX.flipY`, and
`enlarged_body` closes it. -/
theorem positive_margins (ha : 0 < c.l1) (hb : c.h1 < 1) (hc : 0 < c.l2) (hd : c.h2 < 1) :
    1 ≤ (c.h1 - c.l1) + (c.h2 - c.l2) := by
  obtain ⟨L, hL, eL⟩ := c.pL
  obtain ⟨R, hR, eR⟩ := c.pR
  obtain ⟨D, hD, eD⟩ := c.qD
  obtain ⟨U, hU, eU⟩ := c.qU
  have eL' : 1 - c.X L = 1 := by rw [eL]; ring
  have eD' : 1 - c.Y D = 1 := by rw [eD]; ring
  have hb' : 1 - c.l1 < 1 := by linarith
  have hd' : 1 - c.l2 < 1 := by linarith
  have kTR := c.corner_line hb hd hR hU eR eU
  have kTL := c.flipX.corner_line hb' hd hL hU eL' eU
  have kBR := c.flipY.corner_line hb hd' hR hD eR eD'
  have kBL := c.flipX.flipY.corner_line hb' hd' hL hD eL' eD'
  have hyR := c.in_H hb hR eR
  have hyL := c.flipX.in_H hb' hL eL'
  have hxU := c.in_V hd hU eU
  have hxD := c.flipY.in_V hd' hD eD'
  dsimp only [flipX, flipY, swap] at kTL kBR kBL hyL hxD
  exact enlarged_body ha hb hc hd hyL hyR hxD hxU (by linarith) (by linarith) (by linarith)
    (by linarith)

end Coords

/-- ★★ **Two planks on a normalised body** ★★ — a window reaching an
end of the range is `zero_margin` at `c`, `c.flipX`, `c.swap`,
`c.swap.flipX`; otherwise `positive_margins`. -/
theorem twoplank_normalised {α : Type*} (c : Coords α) :
    1 ≤ (c.h1 - c.l1) + (c.h2 - c.l2) := by
  rcases le_or_gt c.l1 0 with ha | ha
  · exact c.zero_margin ha
  rcases le_or_gt 1 c.h1 with hb | hb
  · have := c.flipX.zero_margin (by dsimp only [Coords.flipX]; linarith)
    dsimp only [Coords.flipX] at this; linarith
  rcases le_or_gt c.l2 0 with hc | hc
  · have := c.swap.zero_margin hc
    dsimp only [Coords.swap] at this; linarith
  rcases le_or_gt 1 c.h2 with hd | hd
  · have := c.swap.flipX.zero_margin (by dsimp only [Coords.flipX, Coords.swap]; linarith)
    dsimp only [Coords.flipX, Coords.swap] at this; linarith
  exact c.positive_margins ha hb hc hd

/-! ## §8  Two planks on a compact convex body -/

/-- ★★ **Two planks on a convex body** ★★ — a compact convex body `K` in
a real topological vector space, two continuous affine functionals
`f 0, f 1` with windows `[lo i, hi i]` covering `K`: the relative widths
sum to at least `1`.  The realisers come from compactness, and the
coordinates are the functionals normalised by their own realisers.
KERNEL. -/
theorem twoplank_affine {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {K : Set E} (hconv : Convex ℝ K) (hcomp : IsCompact K) (hne : K.Nonempty)
    (f : Fin 2 → (E →ᵃ[ℝ] ℝ)) (hf : ∀ i, Continuous (f i)) (lo hi : Fin 2 → ℝ)
    (hle : ∀ i, lo i ≤ hi i) (hpos : ∀ i, 0 < width K (f i))
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    1 ≤ ∑ i : Fin 2, (hi i - lo i) / width K (f i) := by
  obtain ⟨pR, hpR, pL, hpL, hmax0, hmin0⟩ := exists_realisers hcomp hne (hf 0)
  obtain ⟨qU, hqU, qD, hqD, hmax1, hmin1⟩ := exists_realisers hcomp hne (hf 1)
  have hW0 : width K (f 0) = f 0 pR - f 0 pL := width_eq_of_realisers hpR hpL hmax0 hmin0
  have hW1 : width K (f 1) = f 1 qU - f 1 qD := width_eq_of_realisers hqU hqD hmax1 hmin1
  have hW0pos : 0 < f 0 pR - f 0 pL := hW0 ▸ hpos 0
  have hW1pos : 0 < f 1 qU - f 1 qD := hW1 ▸ hpos 1
  have main := twoplank_normalised
    { T := K
      X := fun P => (f 0 P - f 0 pL) / (f 0 pR - f 0 pL)
      Y := fun P => (f 1 P - f 1 qD) / (f 1 qU - f 1 qD)
      seg := fun P hP Q hQ t ht0 ht1 =>
        ⟨P + t • (Q - P), hconv.add_smul_sub_mem hP hQ ⟨ht0, ht1⟩,
          by simp only [map_add_smul_sub]; ring, by simp only [map_add_smul_sub]; ring⟩
      range := fun P hP =>
        ⟨⟨div_nonneg (by linarith [hmin0 P hP]) hW0pos.le,
            (div_le_one hW0pos).2 (by linarith [hmax0 P hP])⟩,
          div_nonneg (by linarith [hmin1 P hP]) hW1pos.le,
            (div_le_one hW1pos).2 (by linarith [hmax1 P hP])⟩
      l1 := (lo 0 - f 0 pL) / (f 0 pR - f 0 pL), h1 := (hi 0 - f 0 pL) / (f 0 pR - f 0 pL)
      l2 := (lo 1 - f 1 qD) / (f 1 qU - f 1 qD), h2 := (hi 1 - f 1 qD) / (f 1 qU - f 1 qD)
      le1 := (div_le_div_iff_of_pos_right hW0pos).2 (by linarith [hle 0])
      le2 := (div_le_div_iff_of_pos_right hW1pos).2 (by linarith [hle 1])
      cov := fun P hP => by
        obtain ⟨i, h1, h2⟩ := hcover P hP
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at h1 h2
        · exact Or.inl ⟨(div_le_div_iff_of_pos_right hW0pos).2 (by linarith),
            (div_le_div_iff_of_pos_right hW0pos).2 (by linarith)⟩
        · exact Or.inr ⟨(div_le_div_iff_of_pos_right hW1pos).2 (by linarith),
            (div_le_div_iff_of_pos_right hW1pos).2 (by linarith)⟩
      pL := ⟨pL, hpL, by simp⟩
      pR := ⟨pR, hpR, div_self hW0pos.ne'⟩
      qD := ⟨qD, hqD, by simp⟩
      qU := ⟨qU, hqU, div_self hW1pos.ne'⟩ }
  simp only [Fin.sum_univ_two, hW0, hW1]
  rw [div_sub_div_same, div_sub_div_same] at main
  simpa using main

end Plank.TwoPlankBody

end

/-- info: 'Plank.TwoPlankBody.twoplank_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.TwoPlankBody.twoplank_affine
