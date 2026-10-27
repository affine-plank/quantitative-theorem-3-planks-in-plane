/-
# The `Φ` layer — `Φ`, `PairExcess`, and the (U1-CAP) restatement

Port of `Dim2N3/KPlankPhiLayer.lean` onto the `Config` vocabulary.  The
objects App AI/AJ/AM reason with, defined as compositions of the ledger
vocabulary — nothing new is postulated.

**Units.**  Everything is in units of `|D| = 1/2`, the convention the
appendices use; hence the explicit factors `2`:

    Φ          = 2·gap − (1 − Σ rᵢ)² − 2·Σ dᵢ
    pairBudgetD = 2·Σ rᵢrⱼ
    PairExcess = 2·Σᵢⱼ |Aᵢ∩Aⱼ| − pairBudgetD
    tripleD    = 2·|A₁∩A₂∩A₃|          (`F` at the configuration)

The chapter's content is three rearrangements of the ledger identity:
`Φ = PairExcess − F` (`jointPhi_eq_pairExcess_sub_triple`); **AM.2**, the
(U1-CAP) restatement `Φ ≥ F(s*) − F(S₀) ↔ PairExcess ≥ F(s*)` — the
positions cancel, leaving a statement about directions and widths only;
and the bridge `Φ = 2·dShort` to the short part of the ledger, which
transports AJ.3's shift law to `ΔΦ = −ΔF` in `|D|` units.
-/
module

public import Plank.Proofs.Quant.TripleOverlap

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant

namespace Quant

/-- The joint-lemma functional — the appendices' `Φ` — in `|D|` units.
(Named `jointPhi` because `Quant.Phi` is the tent CDF of the
calibration chapter.) -/
def jointPhi (C : Config) : ℝ :=
  2 * C.gapArea - (1 - C.sumRelW) ^ 2 - 2 * totalDeficit C

/-- The pair budget `2·Σ rᵢrⱼ`, in `|D|` units. -/
def pairBudgetD (C : Config) : ℝ := 2 * pairBudget C

/-- The pair overlaps, in `|D|` units. -/
def pairSumD (C : Config) : ℝ :=
  2 * (pairArea C 0 1 + pairArea C 0 2 + pairArea C 1 2)

/-- **`PairExcess`** of App AM §AM.2. -/
def PairExcess (C : Config) : ℝ := pairSumD C - pairBudgetD C

/-- The triple overlap in `|D|` units — this is `F` at the
configuration. -/
def tripleD (C : Config) : ℝ := 2 * tripleArea C

/-- `Φ` is the slack net of the singles, in `|D|` units: `Φ = 2·dShort`.
So AJ.3's sign convention (`Δ dShort = −Δ p₁₂₃`) transports to
`ΔΦ = −2·Δ p₁₂₃ = −ΔF`. -/
theorem jointPhi_eq_two_mul_dShort (C : Config) : jointPhi C = 2 * dShort C := by
  unfold jointPhi dShort slack totalDeficit Config.deficit
  ring

/-- **The ledger identity in the `Φ` variables**: `Φ = PairExcess − F`. -/
theorem jointPhi_eq_pairExcess_sub_triple (C : Config) :
    jointPhi C = PairExcess C - tripleD C := by
  have h := dShort_eq C
  rw [jointPhi_eq_two_mul_dShort, h]
  unfold PairExcess pairSumD pairBudgetD pairBudget tripleD
  simp only [pairSurplus, ← pairArea_eq, ← relW_eq]
  ring

/-- **AM.2 — the (U1-CAP) restatement.**  The positions cancel: the cap
`Φ ≥ F(s*) − F(S₀)` is equivalent to `PairExcess ≥ F(s*)`, a statement
about directions and widths only. -/
theorem U1_cap_iff_pairExcess (C : Config) (Fpeak : ℝ) :
    Fpeak - tripleD C ≤ jointPhi C ↔ Fpeak ≤ PairExcess C := by
  rw [jointPhi_eq_pairExcess_sub_triple]
  constructor <;> intro h <;> linarith

/-- `Φ` moves, in the unclipped regime, by exactly `−ΔF` (App AJ §AJ.3
in `|D|` units). -/
theorem jointPhi_shift_eq_triple_shift (C : Config) (s : Fin 3 → ℝ)
    (hdet01 : (C.plank 0).u.1 * (C.plank 1).u.2 - (C.plank 0).u.2 * (C.plank 1).u.1 ≠ 0)
    (hdet02 : (C.plank 0).u.1 * (C.plank 2).u.2 - (C.plank 0).u.2 * (C.plank 2).u.1 ≠ 0)
    (hdet12 : (C.plank 1).u.1 * (C.plank 2).u.2 - (C.plank 1).u.2 * (C.plank 2).u.1 ≠ 0)
    (h01 : Unclipped (C.plank 0) (C.plank 1))
    (h02 : Unclipped (C.plank 0) (C.plank 2))
    (h12 : Unclipped (C.plank 1) (C.plank 2))
    (h01' : Unclipped ((C.plank 0).shift (s 0)) ((C.plank 1).shift (s 1)))
    (h02' : Unclipped ((C.plank 0).shift (s 0)) ((C.plank 2).shift (s 2)))
    (h12' : Unclipped ((C.plank 1).shift (s 1)) ((C.plank 2).shift (s 2))) :
    jointPhi (C.shift s) - jointPhi C = -(tripleD (C.shift s) - tripleD C) := by
  have h := dShort_shift_eq_triple_shift C s hdet01 hdet02 hdet12
    h01 h02 h12 h01' h02' h12'
  rw [jointPhi_eq_two_mul_dShort, jointPhi_eq_two_mul_dShort]
  unfold tripleD
  linarith

end Quant

end
