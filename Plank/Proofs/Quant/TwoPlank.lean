/-
# `P(p,q) ≥ 0`: the two-plank bound, its frames, and the median sectors

Port of the self-contained part of `Dim2N3/KPlankTwoPlank.lean` onto the
`Plank` vocabulary.

`Quant.pairSlack_eq` (the ledger at `k = 2`) says the pair slack
`P(p,q) = d(p) + d(q) + sur(p,q)` *is* the two-plank ledger slack, so
`P(p,q) ≥ 0` is exactly the two-plank theorem **(SQ-2)** for that pair —
no more, no less.  ★ Scope: `P(p,q) ≥ 0` is **false without
`w_p + w_q ≤ 1`** (two wide strips can cover `D` outright); the
hypothesis is automatic in the `k = 3` application, where `Σw ≤ 1`.

**The pair classes.**  Normalise each normal so its vertex values run
over `[0,1]`; the *median vertex* is the one carrying the median value.
The ancestor proves (SQ-2) in three base classes and reduces every pair
to one of them:

* **shared middle vertex** (`(1,b₀)` vs `(1,b₁)`, `b ∈ [0,1]`, subsumes
  parallel pairs) — ancestor proof rides `TightAABMargin`;
* **mixed pair** (`(1,a)` vs `(b,1)`, `a,b ∈ (0,1)`) — ancestor proof
  rides `SquareLemmaFinal` through the shear `Φ(x,y) = (x+ay, bx+y)`;
* **perp-sector pair** (edge-parallel against the remaining middle) —
  ancestor proof is `KPlankPerpSector`, in the equilateral/angle frame.

★ WHAT IS PORTED HERE: the canonical-frame widths, the (SQ-2)
vocabulary (`OK2`), and the median-sector machinery (`MedY/X/O`,
edge-parallel = sector boundary, strict middle vertices).
`PairClassReduction` is stated here as a named interface so that the
downstream units can cite it before its proof is in scope; all three
base classes are discharged further down the chain
(`PerpSector.basePerp`, `TypeA.baseTypeA`, `SquareLemma.baseMixed`) and
`SquareLemma.pairClassReduction` closes the interface.
-/
module

public import Plank.Proofs.Quant.PhiLayer

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant Proofs.Transport

namespace Quant

/-! ## §1  The canonical frames, and their widths -/

/-- `W(1, b) = 1` for `b ∈ [0,1]`: the vertex values are `0, 1, b`. -/
theorem width_frameA {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    stdTriangle.width ((1 : ℝ), b) = 1 := by
  rw [stdTriangle_width_eq]
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- `W(b, 1) = 1` for `b ∈ [0,1]`. -/
theorem width_frameB {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    stdTriangle.width (b, (1 : ℝ)) = 1 := by
  rw [stdTriangle_width_eq]
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- In frame A the relative width is the bare thickness. -/
theorem relWidth_frameA {p : Plank} {b : ℝ} (hu : p.u = ((1 : ℝ), b))
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    p.relWidth stdTriangle = p.hi - p.lo := by
  rw [Plank.relWidth, hu, width_frameA hb0 hb1, div_one]

theorem relWidth_frameB {p : Plank} {b : ℝ} (hu : p.u = (b, (1 : ℝ)))
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    p.relWidth stdTriangle = p.hi - p.lo := by
  rw [Plank.relWidth, hu, width_frameB hb0 hb1, div_one]

/-! ## §2  (SQ-2), the citable `k = 2` statement -/

/-- **The `k = 2` bound for one direction pair**: every pair of planks
with these normals and total relative width `≤ 1` has nonnegative pair
slack — equivalently (`pairSlack_nonneg_iff`) satisfies the two-plank
square bound. -/
def OK2 (u v : ℝ × ℝ) : Prop :=
  ∀ p q : Plank, p.u = u → q.u = v →
    p.relWidth stdTriangle + q.relWidth stdTriangle ≤ 1 →
    0 ≤ pairSlack p q

/-- **The pair-class reduction** — the named interface for
`sq2_general`: (SQ-2) for every pair of nonzero directions.  The
ancestor discharges it from the three base classes; its re-homing waits
on the frame substrate (see the header). -/
def PairClassReduction : Prop :=
  ∀ u v : ℝ × ℝ, u ≠ 0 → v ≠ 0 → OK2 u v

/-- Given the reduction, the two-plank square bound is immediate for
arbitrary planks with `w_p + w_q ≤ 1`. -/
theorem sq2_general_of_reduction (H : PairClassReduction) (p q : Plank)
    (hsum : p.relWidth stdTriangle + q.relWidth stdTriangle ≤ 1) :
    (1 - (p.relWidth stdTriangle + q.relWidth stdTriangle)) ^ 2 * (1 / 2)
      ≤ pairGap p q :=
  (pairSlack_nonneg_iff p q).mp
    (H p.u q.u p.u_ne_zero q.u_ne_zero p q rfl rfl hsum)

/-! ## §3  Median vertices, and Q5: edge-parallel = sector boundary

For a nonzero normal the three vertex values are `0, n₁, n₂` at
`O = (0,0)`, `X = (1,0)`, `Y = (0,1)`.  The *median sectors* of
direction space are cut out by which vertex carries the median. -/

/-- The median of `n` sits at `Y = (0,1)`. -/
def MedY (n : ℝ × ℝ) : Prop := (0 ≤ n.2 ∧ n.2 ≤ n.1) ∨ (n.1 ≤ n.2 ∧ n.2 ≤ 0)

/-- The median of `n` sits at `X = (1,0)`. -/
def MedX (n : ℝ × ℝ) : Prop := (0 ≤ n.1 ∧ n.1 ≤ n.2) ∨ (n.2 ≤ n.1 ∧ n.1 ≤ 0)

/-- The median of `n` sits at `O = (0,0)`. -/
def MedO (n : ℝ × ℝ) : Prop := (n.1 ≤ 0 ∧ 0 ≤ n.2) ∨ (n.2 ≤ 0 ∧ 0 ≤ n.1)

/-- Every direction has a median vertex. -/
theorem med_complete (n : ℝ × ℝ) : MedY n ∨ MedX n ∨ MedO n := by
  unfold MedY MedX MedO
  rcases le_total 0 n.1 with h1 | h1 <;> rcases le_total 0 n.2 with h2 | h2 <;>
    rcases le_total n.1 n.2 with h3 | h3 <;> tauto

/-- `n` is **edge-parallel** when its functional is constant on an edge
of `D`: on `OX` iff `n₁ = 0`, on `OY` iff `n₂ = 0`, on `XY` iff
`n₁ = n₂`. -/
def EdgeParallel (n : ℝ × ℝ) : Prop := n.1 = 0 ∨ n.2 = 0 ∨ n.1 = n.2

/-- **Q5: edge-parallel directions are exactly the median-sector
boundaries.**  A direction is edge-parallel iff two of its three vertex
values tie, iff it lies in two median sectors at once — on a wall of
the median partition of direction space.  (Both directions hold for
every `n`, including `n = 0`, degenerately on every wall.) -/
theorem edgeParallel_iff_sector_boundary (n : ℝ × ℝ) :
    EdgeParallel n
      ↔ (MedY n ∧ MedX n) ∨ (MedY n ∧ MedO n) ∨ (MedX n ∧ MedO n) := by
  unfold EdgeParallel MedY MedX MedO
  constructor
  · rintro (h | h | h)
    · -- `n₁ = 0`: the values `0, 0, n₂` tie `O` with `X`
      rcases le_total 0 n.2 with h2 | h2
      · exact Or.inr (Or.inr ⟨Or.inl ⟨h.ge, by linarith⟩, Or.inl ⟨h.le, h2⟩⟩)
      · exact Or.inr (Or.inr ⟨Or.inr ⟨by linarith, h.le⟩, Or.inr ⟨h2, h.ge⟩⟩)
    · -- `n₂ = 0`: the values `0, n₁, 0` tie `O` with `Y`
      rcases le_total 0 n.1 with h1 | h1
      · exact Or.inr (Or.inl ⟨Or.inl ⟨h.ge, by linarith⟩, Or.inr ⟨h.le, h1⟩⟩)
      · exact Or.inr (Or.inl ⟨Or.inr ⟨by linarith, h.le⟩, Or.inl ⟨h1, h.ge⟩⟩)
    · -- `n₁ = n₂`: the values `0, n₁, n₁` tie `X` with `Y`
      rcases le_total 0 n.1 with h1 | h1
      · exact Or.inl ⟨Or.inl ⟨by linarith, h.ge⟩, Or.inl ⟨h1, h.le⟩⟩
      · exact Or.inl ⟨Or.inr ⟨h.le, by linarith⟩, Or.inr ⟨h.ge, h1⟩⟩
  · rintro (⟨hY, hX⟩ | ⟨hY, hO⟩ | ⟨hX, hO⟩)
    · -- `Y` and `X` both median ⇒ `n₁ = n₂` (or everything collapses)
      rcases hY with ⟨p, q⟩ | ⟨p, q⟩ <;> rcases hX with ⟨r, s⟩ | ⟨r, s⟩
      · exact Or.inr (Or.inr (by linarith))
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr (by linarith))
    · -- `Y` and `O` both median ⇒ `n₂ = 0`
      rcases hY with ⟨p, q⟩ | ⟨p, q⟩ <;> rcases hO with ⟨r, s⟩ | ⟨r, s⟩ <;>
        exact Or.inr (Or.inl (by linarith))
    · -- `X` and `O` both median ⇒ `n₁ = 0`
      rcases hX with ⟨p, q⟩ | ⟨p, q⟩ <;> rcases hO with ⟨r, s⟩ | ⟨r, s⟩ <;>
        exact Or.inl (by linarith)

/-- The contrapositive form: a non-edge-parallel direction lies in
exactly one median sector. -/
theorem not_edgeParallel_unique_median {n : ℝ × ℝ} (h : ¬ EdgeParallel n) :
    ¬(MedY n ∧ MedX n) ∧ ¬(MedY n ∧ MedO n) ∧ ¬(MedX n ∧ MedO n) := by
  rw [edgeParallel_iff_sector_boundary] at h
  exact ⟨fun hc => h (Or.inl hc), fun hc => h (Or.inr (Or.inl hc)),
    fun hc => h (Or.inr (Or.inr hc))⟩

/-! ## §4  Lemma V, the vertex half: the *strict* middle vertex

Lemma V reads: band `j` is an apex partner at tail `(i, side)` **iff**
`Zᵢ(side)` is the **strict middle vertex** of `uⱼ` on `D`.  The
apex-partner side is about tails and chords and is not formalised here;
the **vertex half** — that "strict middle vertex" is well-defined,
existing and unique exactly off the edge-parallel walls — is pure
vertex ordering. -/

/-- `n` has a **strict** middle vertex at `Y` — the median sits at `Y`
and no tie makes another vertex eligible. -/
def StrictMidY (n : ℝ × ℝ) : Prop := MedY n ∧ ¬ EdgeParallel n

def StrictMidX (n : ℝ × ℝ) : Prop := MedX n ∧ ¬ EdgeParallel n

def StrictMidO (n : ℝ × ℝ) : Prop := MedO n ∧ ¬ EdgeParallel n

/-- **Existence.**  Off the edge-parallel walls every direction has a
strict middle vertex. -/
theorem strictMid_exists {n : ℝ × ℝ} (h : ¬ EdgeParallel n) :
    StrictMidY n ∨ StrictMidX n ∨ StrictMidO n := by
  rcases med_complete n with hY | hX | hO
  · exact Or.inl ⟨hY, h⟩
  · exact Or.inr (Or.inl ⟨hX, h⟩)
  · exact Or.inr (Or.inr ⟨hO, h⟩)

/-- **Uniqueness.**  No two vertices can both be the strict middle. -/
theorem strictMid_unique (n : ℝ × ℝ) :
    ¬(StrictMidY n ∧ StrictMidX n) ∧ ¬(StrictMidY n ∧ StrictMidO n)
      ∧ ¬(StrictMidX n ∧ StrictMidO n) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨h1, hep⟩, ⟨h2, -⟩⟩
    exact (not_edgeParallel_unique_median hep).1 ⟨h1, h2⟩
  · rintro ⟨⟨h1, hep⟩, ⟨h2, -⟩⟩
    exact (not_edgeParallel_unique_median hep).2.1 ⟨h1, h2⟩
  · rintro ⟨⟨h1, hep⟩, ⟨h2, -⟩⟩
    exact (not_edgeParallel_unique_median hep).2.2 ⟨h1, h2⟩

/-- **The pair reading.**  Two non-edge-parallel directions share their
strict middle vertex exactly when their median sets meet — the very
dichotomy the pair-class reduction runs on. -/
theorem strictMid_shared_iff {n m : ℝ × ℝ} (hn : ¬ EdgeParallel n)
    (hm : ¬ EdgeParallel m) :
    ((StrictMidY n ∧ StrictMidY m) ∨ (StrictMidX n ∧ StrictMidX m)
        ∨ (StrictMidO n ∧ StrictMidO m))
      ↔ ((MedY n ∧ MedY m) ∨ (MedX n ∧ MedX m) ∨ (MedO n ∧ MedO m)) := by
  unfold StrictMidY StrictMidX StrictMidO
  constructor
  · rintro (⟨⟨h1, -⟩, ⟨h2, -⟩⟩ | ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ | ⟨⟨h1, -⟩, ⟨h2, -⟩⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨⟨h1, hn⟩, ⟨h2, hm⟩⟩
    · exact Or.inr (Or.inl ⟨⟨h1, hn⟩, ⟨h2, hm⟩⟩)
    · exact Or.inr (Or.inr ⟨⟨h1, hn⟩, ⟨h2, hm⟩⟩)

end Quant

end
