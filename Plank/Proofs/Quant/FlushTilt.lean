/-
# The flush band under a tilted normal: (S1) and (S3)

Port of `Dim2N3/KPlankFlushTilt.lean` onto the `Plank` vocabulary.
Appendix BD derived the two closed forms for the flush band's coverage
`c₃` under the tilt `n₃ = (1, 1+η)`, and (S3), the vanishing of the
triple term.  Both are here at kernel grade.

**BD.1 in one formula** (§1–§2).  For `0 < b` the set
`{p ∈ D : p₁ + b·p₂ ≤ L}` is the triangle with legs `L` and `L/b`, so —
as long as that triangle fits inside `D`, i.e. `L ≤ 1` and `L ≤ b` — its
area is `L²/(2b)` (`volume_cornerTilt`, a linear change of variables of
determinant `b/L²`).  A plank flush at the top of the level range of
`(1, b)` covers everything above its lower face `L`, so

>     ★  c₃ = 1 − L²/b  ★                          (`plankCap_flush`)

and BD.1's two branches are that one formula read at the two anchors:
for `η > 0` the width is `1+η` and `L = (1+η)(1−r₃)`, giving
`c₃ = 1 − (1+η)(1−r₃)²`; for `η < 0` the width is `1` and `L = 1−r₃`,
giving `c₃ = 1 − (1−r₃)²/(1+η)`.  BD.1's "reciprocal, not symmetric"
mechanism is visible directly: the anchor switch changes which leg
carries the `(1+η)`, so `b` multiplies the area on one side and divides
it on the other.  (S1) is then pure algebra (`S1_coverage`), and tends
to `2(1−r₃)²` as the tilt vanishes.

★ **A side condition BD.1 does not state.**  Both closed forms need the
complement triangle to fit inside `D`.  For `η > 0` that is
`(1+η)(1−r₃) ≤ 1`, i.e. `η ≤ r₃/(1−r₃)`; for `η < 0` it is
`1−r₃ ≤ 1+η`, i.e. `η ≥ −r₃`.  Outside those the triangle is clipped by
the hypotenuse and the formulas overstate the uncovered area.  The
hypotheses are carried explicitly below rather than left implicit. ★

**(S3) from the support of `F`** (§3).  BD.2 observed `p₁₂₃ = 0` at
every tested point and attributed it to App AR's ring criterion.  With
`Ftri`'s closed form this is a theorem: the antiderivative `gTrapAnti`
is `0` below `−(A₁+A₂)` and *constant* above `A₁+A₂`, so `Ftri S = 0` as
soon as `A₁+A₂+A₃ ≤ |S|` (`Ftri_eq_zero_of_far`) — which is exactly the
ring criterion, with `A_i = |λ_i|·halfWidth_i`.  Composing with (F-CF)
gives `S3_triple_zero`.  Because the criterion is an open condition it
holds on a neighbourhood, which is what makes the one-sided derivatives
vanish — BD.2's point.
-/
module

public import Plank.Proofs.Quant.Fubini

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant

namespace Quant

/-! ## §1  The corner triangle under a tilted normal -/

/-- The diagonal chart `(x,y) ↦ (x/L, b·y/L)`, which pulls `D` back to
the corner triangle `{x ≥ 0, y ≥ 0, x + b·y ≤ L}`. -/
def cornerLin (b L : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (z.1 / L, b * z.2 / L)
  map_add' z z' := by
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] <;> ring
  map_smul' r z := by
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
        Prod.smul_mk] <;> ring

private theorem det_cornerLin (b L : ℝ) :
    LinearMap.det (cornerLin b L) = b / L ^ 2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, cornerLin, Module.Basis.finTwoProd]
  ring

private theorem cornerLin_preimage {b L : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hL1 : L ≤ 1) (hLb : L ≤ b) :
    (cornerLin b L) ⁻¹' stdTriangle.set
      = {p : ℝ × ℝ | p ∈ stdTriangle.set ∧ p.1 + b * p.2 ≤ L} := by
  ext p
  simp only [Set.mem_preimage, stdTriangle_set_eq, cornerLin, LinearMap.coe_mk,
    AddHom.coe_mk, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : 0 ≤ p.1 := by
      by_contra hc
      exact absurd h1 (not_le.mpr (div_neg_of_neg_of_pos (not_le.mp hc) hL))
    have hy : 0 ≤ p.2 := by
      by_contra hc
      have : b * p.2 < 0 := mul_neg_of_pos_of_neg hb (not_le.mp hc)
      exact absurd h2 (not_le.mpr (div_neg_of_neg_of_pos this hL))
    have hsum : p.1 + b * p.2 ≤ L := by
      rw [← add_div, div_le_one hL] at h3
      linarith
    refine ⟨⟨hx, hy, ?_⟩, hsum⟩
    rcases le_total 1 b with hb1 | hb1
    · nlinarith
    · nlinarith
  · rintro ⟨⟨hx, hy, -⟩, hsum⟩
    refine ⟨div_nonneg hx hL.le, div_nonneg (by positivity) hL.le, ?_⟩
    rw [← add_div, div_le_one hL]
    exact hsum

/-- ★ **The corner area under a tilted normal** ★
`|{p ∈ D : p₁ + b·p₂ ≤ L}| = L²/(2b)` whenever the corner triangle fits
inside `D` (`L ≤ 1`, `L ≤ b`). -/
theorem volume_cornerTilt {b L : ℝ} (hb : 0 < b) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hLb : L ≤ b) :
    volume {p : ℝ × ℝ | p ∈ stdTriangle.set ∧ p.1 + b * p.2 ≤ L}
      = ENNReal.ofReal (L ^ 2 / (2 * b)) := by
  rcases eq_or_lt_of_le hL0 with hL | hL
  · -- `L = 0`: the corner degenerates to the vertex `(0,0)`
    subst hL
    have hnull : {p : ℝ × ℝ | p ∈ stdTriangle.set ∧ p.1 + b * p.2 ≤ 0}
        ⊆ {((0 : ℝ), (0 : ℝ))} := by
      rintro p ⟨hp, hs⟩
      rw [stdTriangle_set_eq] at hp
      obtain ⟨hx, hy, -⟩ := hp
      have hby : 0 ≤ b * p.2 := by positivity
      exact Set.mem_singleton_iff.mpr
        (Prod.ext_iff.mpr ⟨by simp; linarith, by simp; nlinarith⟩)
    rw [measure_mono_null hnull (measure_singleton _)]
    norm_num
  · have hdet : LinearMap.det (cornerLin b L) ≠ 0 := by
      rw [det_cornerLin]; positivity
    rw [← cornerLin_preimage hb hL hL1 hLb,
      Measure.addHaar_preimage_linearMap volume hdet, det_cornerLin,
      Proofs.Quant.volume_stdTriangle, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [abs_of_pos (by positivity : (0:ℝ) < (b / L ^ 2)⁻¹)]
    field_simp

/-! ## §2  The flush band's coverage -/

/-- ★ **BD.1 in one formula** ★  A plank flush at the top of the level
range of `(1, b)` covers `c₃ = 1 − L²/b` of `D`, `L = p.lo` its lower
face.  The upper-face hypotheses say the upper constraint is inactive on
`D` (the level of `(1, b)` on `D` never exceeds `max 1 b`). -/
theorem plankCap_flush (p : Plank) (b : ℝ) (hu : p.u = (1, b)) (hb : 0 < b)
    (hlo0 : 0 ≤ p.lo) (hlo1 : p.lo ≤ 1) (hlob : p.lo ≤ b)
    (hhi1 : 1 ≤ p.hi) (hhib : b ≤ p.hi) :
    2 * plankCap p = 1 - p.lo ^ 2 / b := by
  set C := {q : ℝ × ℝ | q ∈ stdTriangle.set ∧ q.1 + b * q.2 ≤ p.lo} with hC
  have hCmeas : MeasurableSet C := by
    have : C = stdTriangle.set ∩ {q : ℝ × ℝ | q.1 + b * q.2 ≤ p.lo} := by
      ext q; simp only [hC, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [this]
    exact measurableSet_stdTriangle.inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hunion : p.set ∩ stdTriangle.set ∪ C = stdTriangle.set := by
    ext q
    simp only [hC, plank_set_eq, hu, dot, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · rintro (⟨-, hq⟩ | ⟨hq, -⟩) <;> exact hq
    · intro hq
      have hq' := hq
      rw [stdTriangle_set_eq] at hq'
      obtain ⟨hx, hy, hs⟩ := hq'
      rcases le_total p.lo (1 * q.1 + b * q.2) with h | h
      · refine Or.inl ⟨⟨h, ?_⟩, hq⟩
        rcases le_total 1 b with hb1 | hb1
        · nlinarith
        · nlinarith
      · exact Or.inr ⟨hq, by linarith⟩
  have hinter : volume ((p.set ∩ stdTriangle.set) ∩ C) = 0 := by
    refine measure_mono_null ?_
      (volume_line_eq_zero (n := ((1 : ℝ), b)) (by simp [Prod.ext_iff]) p.lo)
    rintro q ⟨⟨hq, -⟩, ⟨-, h2⟩⟩
    rw [plank_set_eq, hu] at hq
    simp only [Set.mem_setOf_eq, dot] at hq ⊢
    exact le_antisymm (by linarith [hq.1]) (by linarith [hq.1])
  have hkey := measure_union_add_inter (μ := volume)
    (p.set ∩ stdTriangle.set) hCmeas
  have hCvol : volume C = ENNReal.ofReal (p.lo ^ 2 / (2 * b)) :=
    volume_cornerTilt hb hlo0 hlo1 hlob
  rw [hunion, hinter, add_zero, Proofs.Quant.volume_stdTriangle, hCvol] at hkey
  have hfin : volume (p.set ∩ stdTriangle.set) ≠ ⊤ :=
    volume_ne_top_of_subset_std Set.inter_subset_right
  have h2 := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 / 2 by norm_num),
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ p.lo ^ 2 / (2 * b))] at h2
  unfold plankCap area
  have hb0 : b ≠ 0 := hb.ne'
  field_simp at h2 ⊢
  linarith

/-- ★ **BD.1, `η > 0`** ★  The upper anchor is `(0,1)`, the width is
`1+η`, and the `(1+η)` multiplies the complement's area. -/
theorem plankCap_flush_pos (p : Plank) {η r₃ : ℝ} (hη : 0 < η)
    (hu : p.u = (1, 1 + η)) (hlo : p.lo = (1 + η) * (1 - r₃))
    (hhi : p.hi = 1 + η) (hr0 : 0 ≤ r₃) (hr1 : r₃ ≤ 1)
    (hfit : (1 + η) * (1 - r₃) ≤ 1) :
    2 * plankCap p = 1 - (1 + η) * (1 - r₃) ^ 2 := by
  have hb : (0 : ℝ) < 1 + η := by linarith
  rw [plankCap_flush p (1 + η) hu hb (by rw [hlo]; nlinarith)
    (by rw [hlo]; exact hfit) (by rw [hlo]; nlinarith)
    (by rw [hhi]; linarith) (by rw [hhi]), hlo]
  field_simp

/-- ★ **BD.1, `η < 0`** ★  The upper anchor switches to `(1,0)`, the
width is `1`, and now the `(1+η)` *divides* the complement's area —
BD.1's reciprocal mechanism, which is why the two one-sided slopes are
equal rather than opposite. -/
theorem plankCap_flush_neg (p : Plank) {η r₃ : ℝ} (hη1 : -1 < η) (hη : η < 0)
    (hu : p.u = (1, 1 + η)) (hlo : p.lo = 1 - r₃) (hhi : p.hi = 1)
    (hr0 : 0 ≤ r₃) (hr1 : r₃ ≤ 1) (hfit : 1 - r₃ ≤ 1 + η) :
    2 * plankCap p = 1 - (1 - r₃) ^ 2 / (1 + η) := by
  have hb : (0 : ℝ) < 1 + η := by linarith
  rw [plankCap_flush p (1 + η) hu hb (by rw [hlo]; linarith)
    (by rw [hlo]; linarith) (by rw [hlo]; exact hfit)
    (by rw [hhi]) (by rw [hhi]; linarith), hlo]

/-- ★ **(S1), derived** ★  The two one-sided coverage slopes at tilt
magnitude `h` sum to `(1−r₃)²(1 + 1/(1−h))`, which tends to `2(1−r₃)²` —
and to `2` as `r₃ → 0`.  This is BD.1's (S1), and it is pure algebra
once the two branches are in hand. -/
theorem S1_coverage {r₃ h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    -(((1 - (1 + h) * (1 - r₃) ^ 2) - (1 - (1 - r₃) ^ 2)) / h
        + ((1 - (1 - r₃) ^ 2 / (1 - h)) - (1 - (1 - r₃) ^ 2)) / h)
      = (1 - r₃) ^ 2 * (1 + 1 / (1 - h)) := by
  have h1 : (1 : ℝ) - h ≠ 0 := by linarith
  field_simp
  ring

/-! ## §3  (S3): the triple term vanishes off the ring -/

theorem gTrapAnti_of_le {A₁ A₂ L₁₂ x : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hx : x ≤ -(A₁ + A₂)) : gTrapAnti A₁ A₂ L₁₂ x = 0 := by
  have hp : |A₁ - A₂| ≤ A₁ + A₂ := abs_sub_le_add hA₁ hA₂
  have h0 : (0 : ℝ) ≤ |A₁ - A₂| := abs_nonneg _
  unfold gTrapAnti
  rw [Qpos_of_nonpos (by linarith), Qpos_of_nonpos (by linarith),
    Qpos_of_nonpos (by linarith), Qpos_of_nonpos (by linarith)]
  ring

theorem gTrapAnti_of_ge {A₁ A₂ L₁₂ x : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hx : A₁ + A₂ ≤ x) :
    gTrapAnti A₁ A₂ L₁₂ x = ((A₁ + A₂) ^ 2 - |A₁ - A₂| ^ 2) / L₁₂ := by
  have hp : |A₁ - A₂| ≤ A₁ + A₂ := abs_sub_le_add hA₁ hA₂
  have h0 : (0 : ℝ) ≤ |A₁ - A₂| := abs_nonneg _
  unfold gTrapAnti
  rw [Qpos_of_nonneg (by linarith), Qpos_of_nonneg (by linarith),
    Qpos_of_nonneg (by linarith), Qpos_of_nonneg (by linarith)]
  ring

/-- ★ **`F` vanishes off the ring** ★  `Ftri S = 0` as soon as
`A₁ + A₂ + A₃ ≤ |S|` — the antiderivative is `0` below the support and
*constant* above it, so the window integral is empty either way.  This
is AX.1's "`F ≡ 0` for `|S| ≥ m₁`", and App AR's ring criterion. -/
theorem Ftri_eq_zero_of_far {A₁ A₂ A₃ L₁₂ L₃ S : ℝ} (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃) (h : A₁ + A₂ + A₃ ≤ |S|) :
    Ftri A₁ A₂ A₃ L₁₂ L₃ S = 0 := by
  rw [Ftri_eq hA₁ hA₂]
  rcases abs_cases S with ⟨habs, -⟩ | ⟨habs, -⟩
  · rw [habs] at h
    rw [gTrapAnti_of_le hA₁ hA₂ (by linarith), gTrapAnti_of_le hA₁ hA₂ (by linarith)]
    ring
  · rw [habs] at h
    rw [gTrapAnti_of_ge hA₁ hA₂ (by linarith), gTrapAnti_of_ge hA₁ hA₂ (by linarith)]
    ring

/-- ★ **(S3): the triple term is zero off the ring** ★  On an unclipped
configuration whose concurrency defect satisfies App AR's ring criterion
`Σ_i |λ_i|·halfWidth_i ≤ |Σ_i λ_i·center_i|`, the ledger's triple term
vanishes.  The criterion is an *open* condition, so it holds on a
neighbourhood — which is BD.2's point, and what makes both one-sided
derivatives vanish. -/
theorem S3_triple_zero (C : Config) (lam₀ lam₁ lam₂ : ℝ)
    (hlam₀ : lam₀ ≠ 0) (hlam₁ : lam₁ ≠ 0) (hlam₂ : lam₂ ≠ 0)
    (hdet : (C.plank 0).u.1 * (C.plank 1).u.2
      - (C.plank 0).u.2 * (C.plank 1).u.1 = lam₂)
    (hdep : ∀ q : ℝ × ℝ,
      lam₀ * dot (C.plank 0).u q + lam₁ * dot (C.plank 1).u q
        + lam₂ * dot (C.plank 2).u q = 0)
    (hunclip : (C.plank 0).set ∩ (C.plank 1).set ∩ (C.plank 2).set
      ⊆ stdTriangle.set)
    (hring : |lam₀| * (C.plank 0).halfWidth + |lam₁| * (C.plank 1).halfWidth
        + |lam₂| * (C.plank 2).halfWidth
      ≤ |lam₀ * (C.plank 0).center + lam₁ * (C.plank 1).center
          + lam₂ * (C.plank 2).center|) :
    tripleD C = 0 := by
  rw [tripleD_eq_Ftri C lam₀ lam₁ lam₂ hlam₀ hlam₁ hlam₂ hdet hdep hunclip]
  have h0 := halfWidth_nonneg (C.plank 0)
  have h1 := halfWidth_nonneg (C.plank 1)
  have h2 := halfWidth_nonneg (C.plank 2)
  exact Ftri_eq_zero_of_far (by positivity) (by positivity) (by positivity) hring

end Quant
