/-
# (CLIP-LIN): band shifts, unclipped pairs, and the triple overlap

Port of `Dim2N3/KPlankOverlapShift.lean` (inlined as §1 — it was three
corollaries of the parallelogram formula) and
`Dim2N3/KPlankTripleOverlap.lean` onto the `Plank` vocabulary.

**§1  Sliding a plank does not change the parallelogram.**  The
parallelogram formula `volume_plank_inter` depends only on the two
thicknesses and the two directions — the positions do not appear — so
the full overlap of two non-parallel planks is invariant under sliding
either plank, independently.

**§2  Unclipped pairs.**  A pair is *unclipped* when its full
parallelogram lies inside the triangle; the triangle is then invisible
to the pair overlap, so an unclipped pair's overlap is position-free as
well.

**§3  The short part of the ledger (AJ.3).**  `dShort = slack − Σdᵢ`,
which by the ledger identity is `Σᵢⱼ surᵢⱼ − |A₁∩A₂∩A₃|`.  When all
three pairs are unclipped at both ends of a band shift, the pair sum is
exactly constant, so the short part moves by exactly the (negated)
motion of the triple overlap.  Sign: `dShort` is the short part in the
ledger's own sign, so the law is `Δ dShort = −Δ p₁₂₃` (checked in exact
rationals in `tier_494_aj3_precheck` before the ancestor formalized it).

**§4  The triple overlap under a common translation (AK.1).**
Translating the whole configuration by `v` shifts band `i` by `⟪uᵢ,v⟫`
and fixes the triple overlap.  The pair version is stronger — there the
positions move independently — and no independent-shift statement holds
for a triple, which is exactly why `p₁₂₃` is the term that moves in
AJ.3.
-/
module

public import Plank.Proofs.Quant.PairBudget

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant

namespace Quant

/-! ## §1  Sliding a plank does not change the parallelogram -/

/-- The plank slid by `s`: same normal, both levels shifted. -/
def _root_.Plank.shift (p : Plank) (s : ℝ) : Plank :=
  ⟨p.u, p.lo + s, p.hi + s, p.u_ne_zero, by linarith [p.lo_le_hi]⟩

@[simp] theorem _root_.Plank.shift_u (p : Plank) (s : ℝ) : (p.shift s).u = p.u := rfl

@[simp] theorem _root_.Plank.shift_zero (p : Plank) : p.shift 0 = p := by
  simp [Plank.shift]

/-- Sliding is invisible to the relative width. -/
@[simp] theorem relWidth_shift (p : Plank) (s : ℝ) :
    (p.shift s).relWidth stdTriangle = p.relWidth stdTriangle := by
  unfold Plank.relWidth Plank.shift
  ring_nf

/-- ★ **(CLIP-LIN) keystone** ★  The full parallelogram cut out by two
non-parallel planks has an area independent of both positions: sliding
either plank translates the parallelogram without changing its
measure. -/
theorem volume_inter_shift (p q : Plank) (s t : ℝ)
    (hdet : p.u.1 * q.u.2 - p.u.2 * q.u.1 ≠ 0) :
    volume ((p.shift s).set ∩ (q.shift t).set) = volume (p.set ∩ q.set) := by
  rw [volume_plank_inter (p.shift s) (q.shift t) hdet, volume_plank_inter p q hdet]
  simp only [Plank.shift]
  ring_nf

/-! ## §2  Unclipped pairs -/

/-- **Unclipped pair.**  The full parallelogram cut out by the two
planks lies inside the triangle: the overlap `p ∩ q ∩ D` is then the
whole parallelogram, and the triangle plays no role in it. -/
def Unclipped (p q : Plank) : Prop := p.set ∩ q.set ⊆ stdTriangle.set

/-- On an unclipped pair the triangle is invisible. -/
theorem pairOverlap_eq_of_unclipped {p q : Plank} (h : Unclipped p q) :
    pairOverlap p q = area (p.set ∩ q.set) := by
  unfold pairOverlap
  rw [inter_eq_left.mpr h]

/-- **(CLIP-LIN) for a pair.**  A pair overlap that is unclipped at both
the base and the shifted position has the same area at both — the
positions cancel by `volume_inter_shift`. -/
theorem pairOverlap_shift_eq_of_unclipped {p q : Plank} (s t : ℝ)
    (hdet : p.u.1 * q.u.2 - p.u.2 * q.u.1 ≠ 0)
    (h0 : Unclipped p q) (hs : Unclipped (p.shift s) (q.shift t)) :
    pairOverlap (p.shift s) (q.shift t) = pairOverlap p q := by
  rw [pairOverlap_eq_of_unclipped hs, pairOverlap_eq_of_unclipped h0,
    area, area, volume_inter_shift p q s t hdet]

/-! ## §3  The short part of the ledger, and AJ.3 -/

/-- The configuration slid plank-by-plank. -/
def _root_.Config.shift (C : Config) (s : Fin 3 → ℝ) : Config :=
  ⟨fun i => (C.plank i).shift (s i)⟩

@[simp] theorem _root_.Config.shift_plank (C : Config) (s : Fin 3 → ℝ) (i : Fin 3) :
    (C.shift s).plank i = (C.plank i).shift (s i) := rfl

/-- Sliding is invisible to all three relative widths. -/
@[simp] theorem _root_.Config.relW_shift (C : Config) (s : Fin 3 → ℝ) (i : Fin 3) :
    (C.shift s).relW i = C.relW i :=
  relWidth_shift _ _

/-- **The ledger's SHORT part**: the slack minus the three single-plank
deficits.  By `slack_eq_sur` it equals `Σᵢⱼ surᵢⱼ − |A₁∩A₂∩A₃|`. -/
def dShort (C : Config) : ℝ := slack C - totalDeficit C

/-- `dShort` in closed form — the ledger identity rearranged. -/
theorem dShort_eq (C : Config) :
    dShort C
      = (pairSurplus (C.plank 0) (C.plank 1) + pairSurplus (C.plank 0) (C.plank 2)
          + pairSurplus (C.plank 1) (C.plank 2))
        - tripleArea C := by
  have h := slack_eq_sur C
  unfold dShort
  linarith

/-- **AJ.3, first row.**  If all three pairs are unclipped at both
positions, the sum of the pair overlaps is exactly constant under the
band shift. -/
theorem pairSum_shift_eq (C : Config) (s : Fin 3 → ℝ)
    (hdet01 : (C.plank 0).u.1 * (C.plank 1).u.2 - (C.plank 0).u.2 * (C.plank 1).u.1 ≠ 0)
    (hdet02 : (C.plank 0).u.1 * (C.plank 2).u.2 - (C.plank 0).u.2 * (C.plank 2).u.1 ≠ 0)
    (hdet12 : (C.plank 1).u.1 * (C.plank 2).u.2 - (C.plank 1).u.2 * (C.plank 2).u.1 ≠ 0)
    (h01 : Unclipped (C.plank 0) (C.plank 1))
    (h02 : Unclipped (C.plank 0) (C.plank 2))
    (h12 : Unclipped (C.plank 1) (C.plank 2))
    (h01' : Unclipped ((C.plank 0).shift (s 0)) ((C.plank 1).shift (s 1)))
    (h02' : Unclipped ((C.plank 0).shift (s 0)) ((C.plank 2).shift (s 2)))
    (h12' : Unclipped ((C.plank 1).shift (s 1)) ((C.plank 2).shift (s 2))) :
    pairOverlap ((C.shift s).plank 0) ((C.shift s).plank 1)
      + pairOverlap ((C.shift s).plank 0) ((C.shift s).plank 2)
      + pairOverlap ((C.shift s).plank 1) ((C.shift s).plank 2)
    = pairOverlap (C.plank 0) (C.plank 1)
      + pairOverlap (C.plank 0) (C.plank 2)
      + pairOverlap (C.plank 1) (C.plank 2) := by
  simp only [Config.shift_plank]
  rw [pairOverlap_shift_eq_of_unclipped _ _ hdet01 h01 h01',
    pairOverlap_shift_eq_of_unclipped _ _ hdet02 h02 h02',
    pairOverlap_shift_eq_of_unclipped _ _ hdet12 h12 h12']

/-- **AJ.3, second row.**  In the unclipped regime the short part of the
ledger moves by exactly the negated motion of the triple overlap: all
three pair terms drop out. -/
theorem dShort_shift_eq_triple_shift (C : Config) (s : Fin 3 → ℝ)
    (hdet01 : (C.plank 0).u.1 * (C.plank 1).u.2 - (C.plank 0).u.2 * (C.plank 1).u.1 ≠ 0)
    (hdet02 : (C.plank 0).u.1 * (C.plank 2).u.2 - (C.plank 0).u.2 * (C.plank 2).u.1 ≠ 0)
    (hdet12 : (C.plank 1).u.1 * (C.plank 2).u.2 - (C.plank 1).u.2 * (C.plank 2).u.1 ≠ 0)
    (h01 : Unclipped (C.plank 0) (C.plank 1))
    (h02 : Unclipped (C.plank 0) (C.plank 2))
    (h12 : Unclipped (C.plank 1) (C.plank 2))
    (h01' : Unclipped ((C.plank 0).shift (s 0)) ((C.plank 1).shift (s 1)))
    (h02' : Unclipped ((C.plank 0).shift (s 0)) ((C.plank 2).shift (s 2)))
    (h12' : Unclipped ((C.plank 1).shift (s 1)) ((C.plank 2).shift (s 2))) :
    dShort (C.shift s) - dShort C
      = -(tripleArea (C.shift s) - tripleArea C) := by
  have E0 := dShort_eq C
  have E1 := dShort_eq (C.shift s)
  have hsum := pairSum_shift_eq C s hdet01 hdet02 hdet12 h01 h02 h12 h01' h02' h12'
  simp only [Config.shift_plank] at E1 hsum
  simp only [pairSurplus, relWidth_shift] at E0 E1
  linarith

/-! ## §4  AK.1 — the triple overlap under a common translation -/

/-- **AK.1's keystone.**  Translating the whole configuration by `v`
shifts band `i` by `⟪uᵢ, v⟫` and leaves the (unclipped) triple overlap
unchanged. -/
theorem volume_triple_translation (p₁ p₂ p₃ : Plank) (v : ℝ × ℝ) :
    volume ((p₁.shift (dot p₁.u v)).set ∩ (p₂.shift (dot p₂.u v)).set
        ∩ (p₃.shift (dot p₃.u v)).set)
      = volume (p₁.set ∩ p₂.set ∩ p₃.set) := by
  have hset : (p₁.shift (dot p₁.u v)).set ∩ (p₂.shift (dot p₂.u v)).set
        ∩ (p₃.shift (dot p₃.u v)).set
      = (fun P => P + -v) ⁻¹' (p₁.set ∩ p₂.set ∩ p₃.set) := by
    simp only [plank_set_eq, Plank.shift]
    ext P
    simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, dot,
      Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
    constructor
    · rintro ⟨⟨⟨a1, a2⟩, b1, b2⟩, c1, c2⟩
      exact ⟨⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩,
        by nlinarith, by nlinarith⟩
    · rintro ⟨⟨⟨a1, a2⟩, b1, b2⟩, c1, c2⟩
      exact ⟨⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩,
        by nlinarith, by nlinarith⟩
  rw [hset, measure_preimage_add_right]

end Quant

end
