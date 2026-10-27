/-
# The ledger ladder — `k ≤ 3`, the `K`-form, and the `P`-form

Port of `Dim2N3/KPlankLedger.lean` onto the `Plank`/`Config` vocabulary
(the topic file `Plank/Quant.lean` already carries the `k = 3` identity
as `Quant.ledger`; this file supplies everything the ancestor proved
*around* it).

The ladder: the same inclusion–exclusion bookkeeping at one and two
planks (`ledger1`, `ledger2`), and the reassembly of the three-plank
slack out of its three pairwise slacks (`sub_ledger`).  The `K`-form
splits each pair term into two separately signed budgets — the
curvature budget `wᵢwⱼ(Kᵢⱼ − 1)` and the clipping loss `wᵢwⱼKᵢⱼ − |Aᵢ∩Aⱼ|`
— whose `Kᵢⱼ` cancel, so both forms are unconditional.  The `P`-form
rewrites the slack over the pair surpluses and isolates the triple
overlap; `budget_rearrangement` prices it: the singles, the two largest
pairwise overlaps and `G` pay the pair budget `Σwᵢwⱼ`.

The `K`-free ledger and the `K`-form are deliberately kept as separate
theorems (`Quant.ledger` / `ledger_K`): the first is hypothesis-free
bookkeeping, the second names the two signed budgets the programme
bounds separately.

A width-zero plank is a null line, so deleting it changes no area:
the ladder collapses downward (`sqBound_iff_pairSlack_of_degenerate`,
`pairSlack_nonneg_iff_of_degenerate`), and a genuinely three-plank
phenomenon needs all three planks live.
-/
module

public import Plank.Quant

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant

namespace Quant

/-! ## §1  Areas, and the null line -/

/-- Area as a real number. -/
def area (s : Set (ℝ × ℝ)) : ℝ := (volume s).toReal

theorem area_nonneg (s : Set (ℝ × ℝ)) : 0 ≤ area s := ENNReal.toReal_nonneg

/-- Every subset of the triangle has finite area. -/
theorem volume_ne_top_of_subset_std {s : Set (ℝ × ℝ)} (h : s ⊆ stdTriangle.set) :
    volume s ≠ ⊤ :=
  Proofs.Quant.volume_ne_top_of_subset
    (by rw [Proofs.Quant.volume_stdTriangle]; exact ENNReal.ofReal_ne_top) h

theorem area_stdTriangle : area stdTriangle.set = 1 / 2 := by
  rw [area, Proofs.Quant.volume_stdTriangle, ENNReal.toReal_ofReal (by norm_num)]

/-- Monotonicity of area, inside the triangle. -/
theorem area_mono {s t : Set (ℝ × ℝ)} (hst : s ⊆ t) (ht : t ⊆ stdTriangle.set) :
    area s ≤ area t :=
  ENNReal.toReal_mono (volume_ne_top_of_subset_std ht) (measure_mono hst)

/-- The chart `p ↦ (⟪p, n^⊥⟫, ⟪p, n⟫)` straightening the lines
`dot n · = c` to horizontals.  Invertible whenever `n ≠ 0`. -/
def lineChart (n : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (-n.2 * p.1 + n.1 * p.2, n.1 * p.1 + n.2 * p.2)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    constructor <;> ring

private theorem det_lineChart (n : ℝ × ℝ) :
    LinearMap.det (lineChart n) = -(n.1 ^ 2 + n.2 ^ 2) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, lineChart, Module.Basis.finTwoProd]
  ring

/-- **A line is null.**  The locus `⟪·, n⟫ = c` has measure zero for
every nonzero normal. -/
theorem volume_line_eq_zero {n : ℝ × ℝ} (hn : n ≠ 0) (c : ℝ) :
    volume {p : ℝ × ℝ | dot n p = c} = 0 := by
  have hdet : LinearMap.det (lineChart n) ≠ 0 := by
    rw [det_lineChart]
    have h : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
    rcases h with h | h <;> intro hc <;>
      nlinarith [sq_nonneg n.1, sq_nonneg n.2, sq_pos_of_ne_zero h]
  have hpre : {p : ℝ × ℝ | dot n p = c}
      = lineChart n ⁻¹' (Set.univ ×ˢ ({c} : Set ℝ)) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_univ,
      Set.mem_singleton_iff, true_and, lineChart, LinearMap.coe_mk, AddHom.coe_mk, dot]
  rw [hpre, Measure.addHaar_preimage_linearMap volume hdet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_singleton, mul_zero, mul_zero]

/-! ## §2  The plank-level quantities

The topic file's `capArea`, `dDef`, `pairArea` are `Config`-indexed;
their plank-level forms below quantify over bare planks, which is what
the two-plank theory and the affine transport consume.  The bridges are
definitional. -/

/-- The area of the part of a plank inside the triangle. -/
def plankCap (p : Plank) : ℝ := area (p.set ∩ stdTriangle.set)

/-- The **one-plank deficit** `d(p) = |D|(2w − w²) − |p ∩ D|`: how far
the plank falls short of the most a relative-width-`w` plank can cover.
Nonnegative for `w ≤ 1` (`Calibration.plankDeficit_nonneg`). -/
def plankDeficit (p : Plank) : ℝ :=
  (1 / 2) * (2 * p.relWidth stdTriangle - p.relWidth stdTriangle ^ 2) - plankCap p

/-- The **one-plank gap** `|D \ p|`. -/
def plankGap (p : Plank) : ℝ := area (stdTriangle.set \ p.set)

/-- The **two-plank gap** `|D \ (p ∪ q)|`. -/
def pairGap (p q : Plank) : ℝ := area (stdTriangle.set \ (p.set ∪ q.set))

/-- The area of the overlap of two planks inside the triangle. -/
def pairOverlap (p q : Plank) : ℝ := area (p.set ∩ q.set ∩ stdTriangle.set)

/-- The **pair surplus** `|p ∩ q ∩ D| − w_p w_q`: what the overlap holds
beyond the generic-position value.  Either sign occurs. -/
def pairSurplus (p q : Plank) : ℝ :=
  pairOverlap p q - p.relWidth stdTriangle * q.relWidth stdTriangle

/-- The **pair slack** `P(p,q) = d(p) + d(q) + sur(p,q)` — exactly the
two-plank ledger slack (`pairSlack_eq`), so its nonnegativity *is* the
two-plank square bound for the pair. -/
def pairSlack (p q : Plank) : ℝ := plankDeficit p + plankDeficit q + pairSurplus p q

/-- The definitional bridges to the `Config`-indexed vocabulary. -/
theorem capArea_eq (C : Config) (i : Fin 3) : capArea C i = plankCap (C.plank i) := rfl

theorem dDef_eq (C : Config) (i : Fin 3) : dDef C i = plankDeficit (C.plank i) := rfl

theorem pairArea_eq (C : Config) (i j : Fin 3) :
    pairArea C i j = pairOverlap (C.plank i) (C.plank j) := rfl

theorem relW_eq (C : Config) (i : Fin 3) :
    C.relW i = (C.plank i).relWidth stdTriangle := rfl

/-! ## §3  Inclusion–exclusion at `k = 1` and `k = 2` -/

/-- Splitting the triangle along one plank. -/
theorem ie1 (p : Plank) : plankGap p + plankCap p = 1 / 2 := by
  have h : volume (stdTriangle.set ∩ p.set) + volume (stdTriangle.set \ p.set)
      = volume stdTriangle.set :=
    measure_inter_add_diff _ (measurableSet_plank p)
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (volume_ne_top_of_subset_std Set.inter_subset_left)
    (volume_ne_top_of_subset_std Set.diff_subset)] at h2
  have hc : stdTriangle.set ∩ p.set = p.set ∩ stdTriangle.set := Set.inter_comm _ _
  rw [hc] at h2
  have hD : (volume stdTriangle.set).toReal = 1 / 2 := area_stdTriangle
  simp only [plankGap, plankCap, area] at *
  linarith

/-- **The ledger at `k = 1`**: the whole slack is the single deficit. -/
theorem ledger1 (p : Plank) :
    plankGap p - (1 - p.relWidth stdTriangle) ^ 2 * (1 / 2) = plankDeficit p := by
  have h := ie1 p
  simp only [plankDeficit]
  linear_combination h

/-- The one-plank square bound is exactly `d(p) ≥ 0`. -/
theorem ledger1_nonneg_iff (p : Plank) :
    (1 - p.relWidth stdTriangle) ^ 2 * (1 / 2) ≤ plankGap p
      ↔ 0 ≤ plankDeficit p := by
  have h := ledger1 p
  constructor <;> intro hyp <;> linarith

/-- Splitting the triangle along two planks. -/
theorem ie2 (p q : Plank) :
    pairGap p q + plankCap p + plankCap q = 1 / 2 + pairOverlap p q := by
  set A := p.set ∩ stdTriangle.set with hA
  set B := q.set ∩ stdTriangle.set with hB
  have hAm : MeasurableSet A := (measurableSet_plank p).inter measurableSet_stdTriangle
  have hBm : MeasurableSet B := (measurableSet_plank q).inter measurableSet_stdTriangle
  have hAD : A ⊆ stdTriangle.set := Set.inter_subset_right
  have hBD : B ⊆ stdTriangle.set := Set.inter_subset_right
  -- carve the triangle along `A ∪ B`, then split the union
  have hsplit : volume (stdTriangle.set ∩ (A ∪ B)) + volume (stdTriangle.set \ (A ∪ B))
      = volume stdTriangle.set := measure_inter_add_diff _ (hAm.union hBm)
  rw [Set.inter_eq_self_of_subset_right (Set.union_subset hAD hBD)] at hsplit
  have hIE : volume (A ∪ B) + volume (A ∩ B) = volume A + volume B :=
    measure_union_add_inter A hBm
  -- the two set identities: the carved gap, and the carved overlap
  have hgap : stdTriangle.set \ (A ∪ B) = stdTriangle.set \ (p.set ∪ q.set) := by
    ext P; simp only [hA, hB, Set.mem_diff, Set.mem_union, Set.mem_inter_iff]; tauto
  have hover : A ∩ B = p.set ∩ q.set ∩ stdTriangle.set := by
    ext P; simp only [hA, hB, Set.mem_inter_iff]; tauto
  -- pass to real numbers
  have tG : volume (stdTriangle.set \ (A ∪ B)) ≠ ⊤ :=
    volume_ne_top_of_subset_std Set.diff_subset
  have tU : volume (A ∪ B) ≠ ⊤ := volume_ne_top_of_subset_std (Set.union_subset hAD hBD)
  have tA : volume A ≠ ⊤ := volume_ne_top_of_subset_std hAD
  have tI : volume (A ∩ B) ≠ ⊤ :=
    volume_ne_top_of_subset_std (Set.inter_subset_left.trans hAD)
  have h1 := congrArg ENNReal.toReal hsplit
  have h2 := congrArg ENNReal.toReal hIE
  rw [ENNReal.toReal_add tU tG] at h1
  rw [ENNReal.toReal_add tU tI, ENNReal.toReal_add tA (volume_ne_top_of_subset_std hBD)]
    at h2
  have hD : (volume stdTriangle.set).toReal = 1 / 2 := area_stdTriangle
  rw [hgap] at h1
  rw [hover] at h2
  simp only [pairGap, plankCap, pairOverlap, area, hA, hB] at *
  linarith

/-- **The ledger at `k = 2`.**  Same bookkeeping, no triple term. -/
theorem ledger2 (p q : Plank) :
    pairGap p q - (1 - (p.relWidth stdTriangle + q.relWidth stdTriangle)) ^ 2 * (1 / 2)
      = plankDeficit p + plankDeficit q + pairSurplus p q := by
  have h := ie2 p q
  simp only [plankDeficit, pairSurplus]
  linear_combination h

/-- The pair slack *is* the two-plank ledger slack. -/
theorem pairSlack_eq (p q : Plank) :
    pairSlack p q
      = pairGap p q
        - (1 - (p.relWidth stdTriangle + q.relWidth stdTriangle)) ^ 2 * (1 / 2) :=
  (ledger2 p q).symm

/-- `P(p,q) ≥ 0` is equivalent to the two-plank square bound. -/
theorem pairSlack_nonneg_iff (p q : Plank) :
    0 ≤ pairSlack p q
      ↔ (1 - (p.relWidth stdTriangle + q.relWidth stdTriangle)) ^ 2 * (1 / 2)
          ≤ pairGap p q := by
  rw [pairSlack_eq]
  constructor <;> intro h <;> linarith

/-! ## §4  The three-plank slack, and the `P`-form -/

/-- The `k = 3` ledger **slack** `gap − (1 − Σw)²·|D|` — the quantity v3
bounds below by `0` on the deficit regime. -/
def slack (C : Config) : ℝ := C.gapArea - C.deficit ^ 2 * (1 / 2)

/-- `Quant.ledger`, read as a formula for the slack over the pair
surpluses: `slack = Σdᵢ + Σ surᵢⱼ − |A₁∩A₂∩A₃|`. -/
theorem slack_eq_sur (C : Config) :
    slack C
      = totalDeficit C
        + (pairSurplus (C.plank 0) (C.plank 1) + pairSurplus (C.plank 0) (C.plank 2)
            + pairSurplus (C.plank 1) (C.plank 2))
        - tripleArea C := by
  have h := ledger C
  simp only [slack, totalDeficit, pairSurplus, ← pairArea_eq, ← relW_eq]
  linear_combination h

/-- **The sub-ledger**: the three-plank slack reassembles out of the
three pairwise slacks, minus one copy of the singles (each `dᵢ` is
counted twice by the pairs) and the triple overlap. -/
theorem sub_ledger (C : Config) :
    slack C
      = (pairSlack (C.plank 0) (C.plank 1) + pairSlack (C.plank 0) (C.plank 2)
          + pairSlack (C.plank 1) (C.plank 2))
        - totalDeficit C - tripleArea C := by
  have h := slack_eq_sur C
  simp only [pairSlack, totalDeficit, ← dDef_eq] at *
  linear_combination h

/-- The square bound, restated over the pairs: the three two-plank
slacks must dominate the singles plus the triple overlap. -/
theorem sqBound_iff_pairSlacks (C : Config) :
    (0 ≤ slack C)
      ↔ totalDeficit C + tripleArea C
          ≤ pairSlack (C.plank 0) (C.plank 1) + pairSlack (C.plank 0) (C.plank 2)
            + pairSlack (C.plank 1) (C.plank 2) := by
  have h := sub_ledger C
  constructor <;> intro hyp <;> linarith

/-- **The `P`-form**: the square bound says the singles and surpluses
pay for the triple overlap. -/
theorem sqBound_iff_Pform (C : Config) :
    (0 ≤ slack C)
      ↔ tripleArea C
          ≤ totalDeficit C
            + (pairSurplus (C.plank 0) (C.plank 1) + pairSurplus (C.plank 0) (C.plank 2)
                + pairSurplus (C.plank 1) (C.plank 2)) := by
  have h := slack_eq_sur C
  constructor <;> intro hyp <;> linarith

/-! ## §5  The overlap order statistics, and the budget rearrangement -/

/-- The smallest of the three pairwise overlaps. -/
def overlapMin (C : Config) : ℝ :=
  min (min (pairArea C 0 1) (pairArea C 0 2)) (pairArea C 1 2)

/-- `G = minᵢⱼ |Aᵢ∩Aⱼ| − |A₁∩A₂∩A₃| ≥ 0`: the smallest pairwise overlap
still dominates the triple. -/
def Gterm (C : Config) : ℝ := overlapMin C - tripleArea C

/-- The sum of the two largest pairwise overlaps. -/
def sumTwoLargest (C : Config) : ℝ :=
  (pairArea C 0 1 + pairArea C 0 2 + pairArea C 1 2) - overlapMin C

/-- `sumTwoLargest` really is a sum of two of the three overlaps. -/
theorem sumTwoLargest_cases (C : Config) :
    sumTwoLargest C = pairArea C 0 2 + pairArea C 1 2
      ∨ sumTwoLargest C = pairArea C 0 1 + pairArea C 1 2
      ∨ sumTwoLargest C = pairArea C 0 1 + pairArea C 0 2 := by
  unfold sumTwoLargest overlapMin
  rcases le_total (pairArea C 0 1) (pairArea C 0 2) with h12 | h12
  · rw [min_eq_left h12]
    rcases le_total (pairArea C 0 1) (pairArea C 1 2) with h3 | h3
    · rw [min_eq_left h3]; left; ring
    · rw [min_eq_right h3]; right; right; ring
  · rw [min_eq_right h12]
    rcases le_total (pairArea C 0 2) (pairArea C 1 2) with h3 | h3
    · rw [min_eq_left h3]; right; left; ring
    · rw [min_eq_right h3]; right; right; ring

/-- `G ≥ 0`: the triple overlap sits inside each pairwise overlap. -/
theorem Gterm_nonneg (C : Config) : 0 ≤ Gterm C := by
  have h01 : tripleArea C ≤ pairArea C 0 1 := by
    refine ENNReal.toReal_mono (volume_ne_top_of_subset_std Set.inter_subset_right)
      (measure_mono fun P hP => ⟨hP.1.1, hP.2⟩)
  have h02 : tripleArea C ≤ pairArea C 0 2 := by
    refine ENNReal.toReal_mono (volume_ne_top_of_subset_std Set.inter_subset_right)
      (measure_mono fun P hP => ⟨⟨hP.1.1.1, hP.1.2⟩, hP.2⟩)
  have h12 : tripleArea C ≤ pairArea C 1 2 := by
    refine ENNReal.toReal_mono (volume_ne_top_of_subset_std Set.inter_subset_right)
      (measure_mono fun P hP => ⟨⟨hP.1.1.2, hP.1.2⟩, hP.2⟩)
  unfold Gterm overlapMin
  simp only [le_sub_iff_add_le, zero_add, le_min_iff]
  exact ⟨⟨h01, h02⟩, h12⟩

/-- **The budget rearrangement**: `slack = Σdᵢ + S₍₂₎ + S₍₃₎ + G − Σwᵢwⱼ`.
The square bound says exactly that the singles, the two largest
pairwise overlaps and `G` pay the pair budget — the 1-D union bound's
waste. -/
theorem budget_rearrangement (C : Config) :
    slack C = totalDeficit C + sumTwoLargest C + Gterm C - pairBudget C := by
  have h := ledger C
  simp only [slack, totalDeficit, sumTwoLargest, Gterm, overlapMin, pairBudget]
  linear_combination h

/-! ## §6  Mechanism (b), "triple-as-pair", and the item-5 obstruction

Negative results about proof *routes*, kept because they prune the
search space: bounding the triple overlap by the smallest pair and
paying for that works exactly where `slack ≥ G` — so it fails at every
tight configuration with `G > 0` — and any strict triple upper bound is
unpayable at a tight configuration. -/

/-- Mechanism (b): pay for the *pair bound* `minᵢⱼ |Aᵢ∩Aⱼ|` on the
triple overlap. -/
def MechanismB (C : Config) : Prop :=
  overlapMin C
    ≤ totalDeficit C
      + (pairSurplus (C.plank 0) (C.plank 1) + pairSurplus (C.plank 0) (C.plank 2)
          + pairSurplus (C.plank 1) (C.plank 2))

/-- Mechanism (b) closes exactly where the slack already dominates `G`. -/
theorem mechanismB_iff (C : Config) : MechanismB C ↔ Gterm C ≤ slack C := by
  have h := slack_eq_sur C
  simp only [MechanismB, Gterm]
  constructor <;> intro hyp <;> linarith

/-- At a tight configuration mechanism (b) fails whenever `G > 0`. -/
theorem mechanismB_fails_of_Gpos (C : Config) (htight : slack C = 0)
    (hG : 0 < Gterm C) : ¬ MechanismB C := by
  rw [mechanismB_iff, htight]
  exact not_le.mpr hG

/-- **The item-5 obstruction.**  A payable upper bound on the triple
overlap must be *exact* at every tight configuration. -/
theorem item5_obstruction (C : Config) (B : ℝ) (hB : tripleArea C ≤ B)
    (htight : slack C = 0)
    (hspend : B ≤ totalDeficit C
        + (pairSurplus (C.plank 0) (C.plank 1) + pairSurplus (C.plank 0) (C.plank 2)
            + pairSurplus (C.plank 1) (C.plank 2))) :
    B = tripleArea C := by
  have h := slack_eq_sur C
  rw [htight] at h
  linarith

/-- Contrapositive: a strictly slack triple bound cannot be paid for at
a tight configuration — refining triple upper bounds is a dead end
unless the refinement is exact on the whole equality stratum. -/
theorem item5_dead_end (C : Config) (B : ℝ) (htight : slack C = 0)
    (hstrict : tripleArea C < B) :
    ¬ (B ≤ totalDeficit C
        + (pairSurplus (C.plank 0) (C.plank 1) + pairSurplus (C.plank 0) (C.plank 2)
            + pairSurplus (C.plank 1) (C.plank 2))) := fun hspend =>
  absurd (item5_obstruction C B hstrict.le htight hspend) (ne_of_gt hstrict)

/-! ## §7  The `K`-form -/

/-- `K(u,v) = W(u)·W(v)/|det(u,v)|`: the area of the full parallelogram
`Sᵢ ∩ Sⱼ` divided by `wᵢwⱼ`.  Lemma P (`KPlankPairBudget`, to be
ported) says `K ≥ 1 = 2|D|`. -/
def Kpair (u v : ℝ × ℝ) : ℝ :=
  stdTriangle.width u * stdTriangle.width v / |u.1 * v.2 - u.2 * v.1|

/-- The **curvature budget** `w_p w_q (K − 1)` of a pair. -/
def curvBudget (p q : Plank) : ℝ :=
  p.relWidth stdTriangle * q.relWidth stdTriangle * (Kpair p.u q.u - 1)

/-- The **clipping loss** `w_p w_q K − |p ∩ q ∩ D|`: the parallelogram
area lost by clipping the overlap to the triangle. -/
def clipLoss (p q : Plank) : ℝ :=
  p.relWidth stdTriangle * q.relWidth stdTriangle * Kpair p.u q.u - pairOverlap p q

/-- **The ledger, `K`-form**: `slack = Σdᵢ + Σ Bᵢⱼ − Σ eᵢⱼ − |A₁∩A₂∩A₃|`.
The `Kᵢⱼ` cancel between the two middle sums (`Bᵢⱼ − eᵢⱼ = surᵢⱼ − wᵢwⱼ·0`
… they are bookkeeping), so the identity is as unconditional as
`Quant.ledger`; its value is that `Bᵢⱼ ≥ 0` and `eᵢⱼ ≥ 0` are the two
separately signed budgets. -/
theorem ledger_K (C : Config) :
    slack C
      = totalDeficit C
        + (curvBudget (C.plank 0) (C.plank 1) + curvBudget (C.plank 0) (C.plank 2)
            + curvBudget (C.plank 1) (C.plank 2))
        - (clipLoss (C.plank 0) (C.plank 1) + clipLoss (C.plank 0) (C.plank 2)
            + clipLoss (C.plank 1) (C.plank 2))
        - tripleArea C := by
  have h := slack_eq_sur C
  simp only [curvBudget, clipLoss, pairSurplus] at *
  linear_combination h

/-- The square bound in the `K`-form: deficits plus curvature budgets
must dominate clipping losses plus the triple overlap. -/
theorem sqBound_iff_Kform (C : Config) :
    (0 ≤ slack C)
      ↔ (clipLoss (C.plank 0) (C.plank 1) + clipLoss (C.plank 0) (C.plank 2)
            + clipLoss (C.plank 1) (C.plank 2))
          + tripleArea C
        ≤ totalDeficit C
          + (curvBudget (C.plank 0) (C.plank 1) + curvBudget (C.plank 0) (C.plank 2)
              + curvBudget (C.plank 1) (C.plank 2)) := by
  have h := ledger_K C
  constructor <;> intro hyp <;> linarith

/-! ## §8  Width-zero planks are null, and the ladder collapses -/

/-- A width-zero plank is a line, hence null. -/
theorem volume_plank_set_of_degenerate {p : Plank} (h : p.lo = p.hi) :
    volume p.set = 0 := by
  have hline : p.set ⊆ {P : ℝ × ℝ | dot p.u P = p.lo} := by
    intro P hP
    obtain ⟨h1, h2⟩ := hP
    exact le_antisymm (h ▸ h2) h1
  exact measure_mono_null hline (volume_line_eq_zero p.u_ne_zero p.lo)

theorem relWidth_of_degenerate {p : Plank} (h : p.lo = p.hi) :
    p.relWidth stdTriangle = 0 := by
  simp [Plank.relWidth, h]

theorem plankCap_of_degenerate {p : Plank} (h : p.lo = p.hi) : plankCap p = 0 := by
  rw [plankCap, area,
    measure_mono_null Set.inter_subset_left (volume_plank_set_of_degenerate h)]
  simp

/-- A width-zero plank has zero deficit. -/
theorem plankDeficit_of_degenerate {p : Plank} (h : p.lo = p.hi) :
    plankDeficit p = 0 := by
  simp [plankDeficit, relWidth_of_degenerate h, plankCap_of_degenerate h]

/-- Deleting a null plank from a pair. -/
theorem pairGap_of_degenerate (p : Plank) {q : Plank} (h : q.lo = q.hi) :
    pairGap p q = plankGap p := by
  have hset : stdTriangle.set \ (p.set ∪ q.set)
      = (stdTriangle.set \ p.set) \ q.set := by
    ext P; simp only [Set.mem_diff, Set.mem_union]; tauto
  unfold pairGap plankGap area
  rw [hset, measure_diff_null (volume_plank_set_of_degenerate h)]

/-- With a null partner the pair slack is the surviving single deficit. -/
theorem pairSlack_of_degenerate (p : Plank) {q : Plank} (h : q.lo = q.hi) :
    pairSlack p q = plankDeficit p := by
  have hnull : pairOverlap p q = 0 := by
    rw [pairOverlap, area, measure_mono_null
      (Set.inter_subset_left.trans Set.inter_subset_right)
      (volume_plank_set_of_degenerate h)]
    simp
  simp [pairSlack, pairSurplus, plankDeficit_of_degenerate h,
    relWidth_of_degenerate h, hnull]

/-- Deleting a null plank from a configuration's gap. -/
theorem gapArea_of_degenerate (C : Config) (h : (C.plank 2).lo = (C.plank 2).hi) :
    C.gapArea = pairGap (C.plank 0) (C.plank 1) := by
  have hset : C.uncovered
      = (stdTriangle.set \ ((C.plank 0).set ∪ (C.plank 1).set)) \ (C.plank 2).set := by
    unfold Config.uncovered
    ext P
    simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨hT, hn⟩
      exact ⟨⟨hT, fun hc => hn (hc.elim (fun h0 => ⟨0, h0⟩) (fun h1 => ⟨1, h1⟩))⟩,
        fun h2 => hn ⟨2, h2⟩⟩
    · rintro ⟨⟨hT, hn⟩, h2⟩
      refine ⟨hT, ?_⟩
      rintro ⟨i, hi⟩
      rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with hm | hm | hm <;>
        subst hm
      · exact hn (Or.inl hi)
      · exact hn (Or.inr hi)
      · exact h2 hi
  unfold Config.gapArea pairGap area
  rw [hset, measure_diff_null (volume_plank_set_of_degenerate h)]

/-- **A configuration with a null third plank has no content beyond its
live pair**: its square bound is the pair's two-plank bound. -/
theorem sqBound_iff_pairSlack_of_degenerate (C : Config)
    (h : (C.plank 2).lo = (C.plank 2).hi) :
    C.SqBound ↔ 0 ≤ pairSlack (C.plank 0) (C.plank 1) := by
  have hg := gapArea_of_degenerate C h
  have hw : C.relW 2 = 0 := relWidth_of_degenerate h
  have hsum : C.sumRelW = C.relW 0 + C.relW 1 := by
    simp only [Config.sumRelW, Fin.sum_univ_three, hw, add_zero]
  rw [Config.SqBound, Config.deficit, hg, hsum, pairSlack_nonneg_iff, ← relW_eq,
    ← relW_eq]

/-- …and with two null planks, none beyond the single: the content is
`d ≥ 0`, which the calibration chapter proves. -/
theorem sqBound_iff_deficit_of_degenerate (C : Config)
    (h1 : (C.plank 1).lo = (C.plank 1).hi) (h2 : (C.plank 2).lo = (C.plank 2).hi) :
    C.SqBound ↔ 0 ≤ plankDeficit (C.plank 0) := by
  have hg := gapArea_of_degenerate C h2
  have hg1 : pairGap (C.plank 0) (C.plank 1) = plankGap (C.plank 0) :=
    pairGap_of_degenerate _ h1
  have hw1 : C.relW 1 = 0 := relWidth_of_degenerate h1
  have hw2 : C.relW 2 = 0 := relWidth_of_degenerate h2
  have hsum : C.sumRelW = C.relW 0 := by
    simp only [Config.sumRelW, Fin.sum_univ_three, hw1, hw2, add_zero]
  rw [Config.SqBound, Config.deficit, hg, hg1, hsum, relW_eq]
  exact ledger1_nonneg_iff _

end Quant

end
