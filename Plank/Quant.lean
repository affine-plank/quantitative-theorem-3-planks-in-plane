/-
# v3 — the quantitative gap bound `gap ≥ (1 − Σ rw)₊² · |T|`

The quantitative strengthening of v1: the uncovered area of any
three-plank configuration is at least `deficit² · |T|` (with `|T| = 1/2`
for the standard triangle). The unconditional theorem is proved in
`Plank.Proofs.Quant.TriangleSharp`; equality examples are supplied below,
while a full positive-deficit equality classification is separate.
This file is the *statement layer and reusable assembly skeleton*: the
currency (§1), the exact ledger identity that funds it (§2), the
reduction stack (§3), the Case-A/residue split (§4), and the assembly
over named interfaces (§5) that the v3 chapters discharge as they are
rebased in (P3).

Replaces: `Dim2N3/KPlankLedger.lean` (identity layer),
`Dim2N3/KPlankReductionLedger.lean` (the WLOG stack),
`Dim2N3/KPlankAssembly.lean` (currency, split, assembly).  The old
missing `LedgerToSimplexBridge` disappears: v1 and v3 now speak the same
`Config`, so the bridge is the two-line theorem `covers_sum_of_sqPos`.
-/
module

public import Plank.Symmetry
public import Plank.GapCells
public import Plank.Proofs.Quant

@[expose] public section


noncomputable section

namespace Quant

/-! ## §1  The currency -/

/-- The positive-part square bound — v3's global claim for a single
configuration.  (`Config.SqBound`, the signed version inside
`Σ rw < 1`, lives in `Plank/Core.lean`.) -/
def SqPos (C : Config) : Prop :=
  (max 0 C.deficit) ^ 2 * (1 / 2) ≤ C.gapArea

/-- `SqPos` needs proof only in the deficit regime `Σ rw < 1`. -/
theorem sqPos_of_lt_one (C : Config)
    (h : C.sumRelW < 1 → C.SqBound) : SqPos C := by
  rcases lt_or_ge C.sumRelW 1 with hlt | hge
  · -- deficit regime: the positive part IS the deficit
    have hd : 0 ≤ C.deficit := by simp only [Config.deficit]; linarith
    simpa only [SqPos, Config.SqBound, max_eq_right hd] using h hlt
  · -- over-covering: the positive part is zero and areas are nonnegative
    have hd : C.deficit ≤ 0 := by simp only [Config.deficit]; linarith
    simp only [SqPos, max_eq_left hd]
    have h0 : (0:ℝ) ≤ C.gapArea := ENNReal.toReal_nonneg
    nlinarith [h0]

/-- **v3 implies v1** — the currency conversion: for a covering the gap
is empty, so `SqPos` forces `Σ rw ≥ 1`.  (This two-liner is what the
old three-vocabulary development could not say; it retires
`LedgerToSimplexBridge`.) -/
theorem covers_sum_of_sqPos (h : ∀ C : Config, SqPos C) :
    ∀ C : Config, C.Covers → 1 ≤ C.sumRelW := by
  intro C hcov
  -- a covering has empty gap, so the square bound forces the deficit down
  have hempty : C.uncovered = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro P ⟨hT, hn⟩
    obtain ⟨i, hi⟩ := hcov P hT
    exact hn (Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hg : C.gapArea = 0 := by
    simp only [Config.gapArea, hempty, MeasureTheory.measure_empty,
      ENNReal.toReal_zero]
  have hsq := h C
  simp only [SqPos, hg] at hsq
  have hnn : 0 ≤ max 0 C.deficit := le_max_left _ _
  have hmax : max 0 C.deficit = 0 := by nlinarith
  have hdle : C.deficit ≤ 0 := by
    have hle := le_max_right 0 C.deficit
    rw [hmax] at hle; linarith
  simp only [Config.deficit] at hdle
  linarith

/-! ## §2  The ledger identity -/

/-- The area of the part of plank `i` inside the triangle. -/
def capArea (C : Config) (i : Fin 3) : ℝ :=
  (MeasureTheory.volume ((C.plank i).set ∩ stdTriangle.set)).toReal

/-- The **one-plank deficit** `dᵢ = (2wᵢ − wᵢ²)/2 − |capᵢ|`: how far
plank `i` falls short of the area a width-`wᵢ` plank can cut from the
triangle. -/
def dDef (C : Config) (i : Fin 3) : ℝ :=
  (1 / 2) * (2 * C.relW i - C.relW i ^ 2) - capArea C i

/-- The area of the pairwise overlap of planks `i`, `j` inside the
triangle. -/
def pairArea (C : Config) (i j : Fin 3) : ℝ :=
  (MeasureTheory.volume
    ((C.plank i).set ∩ (C.plank j).set ∩ stdTriangle.set)).toReal

/-- The area of the triple overlap inside the triangle. -/
def tripleArea (C : Config) : ℝ :=
  (MeasureTheory.volume
    ((C.plank 0).set ∩ (C.plank 1).set ∩ (C.plank 2).set ∩
      stdTriangle.set)).toReal

/-- **Theorem L, the exact ledger identity**: the gap minus the square
target equals one-plank deficits plus pairwise overlap excesses minus
the triple overlap.  Inclusion–exclusion plus the algebra of
`(1 − Σw)²`; every later bound is an estimate of this identity's right
side. -/
theorem ledger (C : Config) :
    C.gapArea - C.deficit ^ 2 * (1 / 2)
      = (dDef C 0 + dDef C 1 + dDef C 2)
        + ((pairArea C 0 1 - C.relW 0 * C.relW 1)
          + (pairArea C 0 2 - C.relW 0 * C.relW 2)
          + (pairArea C 1 2 - C.relW 1 * C.relW 2))
        - tripleArea C := by
  -- inclusion–exclusion over the three planks, then the algebra of `(1 − Σw)²`
  have h := Proofs.Quant.gap_inclusion_exclusion C
  simp only [Config.gapArea, Config.uncovered, Config.deficit, Config.sumRelW,
    Fin.sum_univ_three, dDef, capArea, pairArea, tripleArea]
  linear_combination h

/-! ## §3  The reduction stack

Four WLOGs, each a one-way ticket: symmetry (moves preserve both sides
of `SqBound` — `Plank/Symmetry.lean`), trimming (windows into shadow
ranges — `Plank/GapCells.lean`), scale (the gap is `μ²`-homogeneous
along homothety rays, so the scale normalization is free), and the
Case-A split (§4). -/

/-- The homothety `x ↦ c + μ(x − c)` of the plane. -/
def hom (μ : ℝ) (c : ℝ × ℝ) (P : ℝ × ℝ) : ℝ × ℝ :=
  (c.1 + μ * (P.1 - c.1), c.2 + μ * (P.2 - c.2))

/-- The pullback of a window level along `hom μ c` for a plank with
normal `u`. -/
def pullLevel (μ : ℝ) (c : ℝ × ℝ) (u : ℝ × ℝ) (l : ℝ) : ℝ :=
  (l - (1 - μ) * dot u c) / μ

/-- **(RED-SCALE)** The uncovered area is degree-2 homogeneous along
homothety rays: the gap of the shrunk triangle against the original
planks is `μ²` times the gap of the triangle against the pulled-back
planks.  The scale degree of freedom is not a degree of freedom. -/
theorem gap_hom_homogeneity {μ : ℝ} (hμ : 0 < μ) (c : ℝ × ℝ) (C : Config) :
    MeasureTheory.volume
        ((hom μ c '' stdTriangle.set) \ ⋃ i, (C.plank i).set)
      = ENNReal.ofReal (μ ^ 2) *
        MeasureTheory.volume (stdTriangle.set \
          ⋃ i, {x | pullLevel μ c (C.plank i).u (C.plank i).lo ≤
              dot (C.plank i).u x ∧
            dot (C.plank i).u x ≤
              pullLevel μ c (C.plank i).u (C.plank i).hi}) := by
  have hμ' : μ ≠ 0 := ne_of_gt hμ
  -- the homothety pulls a plank back to a plank, level by level
  have hpre : (hom μ c) ⁻¹' (⋃ i, (C.plank i).set)
      = ⋃ i, {x | pullLevel μ c (C.plank i).u (C.plank i).lo ≤
            dot (C.plank i).u x ∧
          dot (C.plank i).u x ≤ pullLevel μ c (C.plank i).u (C.plank i).hi} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, Plank.set,
      pullLevel, hom, dot]
    constructor
    · rintro ⟨i, h1, h2⟩
      simp only [dot] at h1 h2
      exact ⟨i, by rw [div_le_iff₀ hμ]; nlinarith [h1],
        by rw [le_div_iff₀ hμ]; nlinarith [h2]⟩
    · rintro ⟨i, h1, h2⟩
      rw [div_le_iff₀ hμ] at h1
      rw [le_div_iff₀ hμ] at h2
      refine ⟨i, ?_, ?_⟩ <;> simp only [dot] <;> nlinarith [h1, h2]
  rw [← Set.image_diff_preimage, hpre]
  -- and it scales area by μ²
  have hhom : hom μ c = ⇑(AffineMap.homothety c μ) := by
    funext P
    simp only [hom, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul]
    constructor <;> ring
  rw [hhom, MeasureTheory.Measure.addHaar_image_homothety]
  congr 1
  rw [abs_of_nonneg (by positivity)]
  norm_num

/-! ## §4  Case A and the residue box -/

/-- The pairwise product budget `Σ_{i<j} wᵢwⱼ`. -/
def pairBudget (C : Config) : ℝ :=
  C.relW 0 * C.relW 1 + C.relW 0 * C.relW 2 + C.relW 1 * C.relW 2

/-- The total one-plank deficit `Σᵢ dᵢ`. -/
def totalDeficit (C : Config) : ℝ := dDef C 0 + dDef C 1 + dDef C 2

/-- **Case A**: when the one-plank deficits pay for the pairwise
budget, the ledger identity closes the square bound outright. -/
theorem sqBound_of_deficit_large (C : Config)
    (h : pairBudget C ≤ totalDeficit C) : C.SqBound := by
  have hL := ledger C
  -- the triple overlap is inside one of the pairwise overlaps, and the other
  -- two pairwise terms are areas
  have htriple : tripleArea C ≤ pairArea C 0 1 := by
    refine ENNReal.toReal_mono (Proofs.Quant.volume_cap_ne_top _)
      (MeasureTheory.measure_mono ?_)
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  have hp02 : (0:ℝ) ≤ pairArea C 0 2 := ENNReal.toReal_nonneg
  have hp12 : (0:ℝ) ≤ pairArea C 1 2 := ENNReal.toReal_nonneg
  simp only [Config.SqBound]
  simp only [totalDeficit, pairBudget] at h
  linarith

/-- The **residue box**: the complementary regime, where all remaining
v3 content lives. -/
def Residue (C : Config) : Prop := totalDeficit C < pairBudget C

/-- Every configuration is closed by Case A or lands in the residue
box. -/
theorem caseA_or_residue (C : Config) : C.SqBound ∨ Residue C := by
  -- the split is the definition of the residue box: either the deficit
  -- pays for the pair budget, or it does not
  rcases lt_or_ge (totalDeficit C) (pairBudget C) with h | h
  · exact Or.inr h
  · exact Or.inl (sqBound_of_deficit_large C h)

/-! ## §5  The assembly skeleton

The residue box is discharged chamber-by-chamber by the v3 chapters
(collars, slivers, the hexagonal-family ball, the certified sweep, the
ABC remainder).  During the P3 rebase each chapter lands as a closed
case predicate; until then the assembly is stated over named
interfaces, so the theorem shape is fixed while the chapter list can
grow. -/

/-- An interface: a case predicate together with the claim that it
implies the square bound. -/
def Closes (P : Config → Prop) : Prop := ∀ C, P C → C.SqBound

/-- **The v3 assembly**: if a family of case predicates covers the
residue box and each closes, then every configuration satisfies the
positive-part square bound. -/
theorem v3_main_of {ι : Type} (arm : ι → Config → Prop)
    (hcover : ∀ C, Residue C → C.sumRelW < 1 → ∃ k, arm k C)
    (hclose : ∀ k, Closes (arm k)) :
    ∀ C : Config, SqPos C := by
  intro C
  -- only the deficit regime needs an argument, and there the case split
  -- either pays outright or lands in the residue box, which the arms cover
  refine sqPos_of_lt_one C (fun hlt => ?_)
  rcases caseA_or_residue C with hb | hres
  · exact hb
  · obtain ⟨k, hk⟩ := hcover C hres hlt
    exact hclose k C hk

/-! ## §6  The equality chapter (statements; P3 fills from the ancestor)

(`sq_equality_of_tight` stood here until tier_602 §2: trivially true —
tight gives gap `0` and deficit `0` — so it advertised equality content
the branch does not have.  Deleted; the ancestor's real content is the
CAL-δ attainment package below, split into an unconditional and a
conditional half. The general floor is now proved independently in
`Plank.Proofs.Quant.TriangleSharp`, which also combines it with the
attainment theorem below to obtain unconditional leastness. Keeping this
statement layer independent avoids a circular import.) -/

/-- The gap areas achievable by three planks with the given normals and
relative widths, as the window offsets range.  (Ancestor:
`KPlankAttain.gapValues`.) -/
def gapValues (u : Fin 3 → ℝ × ℝ) (w : Fin 3 → ℝ) : Set ℝ :=
  {g | ∃ C : Config, (∀ i, (C.plank i).u = u i) ∧
    (∀ i, C.relW i = w i) ∧ g = C.gapArea}

/-- **Attainment, unconditional and constructive**: for slope-sorted
normals `(1, −cᵢ)` and any admissible width triple, the shared-middle
CAL-δ stacking realises the floor value `(1 − Σw)²/2`.  (Ancestor:
`KPlankAttain.deltaSq_mem_gapValues`, kernel-proved.) -/
theorem deltaSq_mem_gapValues (c w : Fin 3 → ℝ)
    (hc0 : 0 ≤ c 0) (hc01 : c 0 ≤ c 1) (hc12 : c 1 ≤ c 2)
    (hw : ∀ i, 0 ≤ w i) (ht : w 0 + w 1 + w 2 ≤ 1) :
    (1 - (w 0 + w 1 + w 2)) ^ 2 / 2
      ∈ gapValues (fun i => ((1 : ℝ), -c i)) w := by
  have hc1 : (0:ℝ) ≤ c 1 := le_trans hc0 hc01
  have hc2 : (0:ℝ) ≤ c 2 := le_trans hc1 hc12
  refine ⟨Proofs.Quant.stackConfig (c 0) (c 1) (c 2) (w 0) (w 1) (w 2)
      hc0 hc1 hc2 (hw 0) (hw 1) (hw 2), fun i => ?_, fun i => ?_,
    (Proofs.Quant.stackConfig_gapArea hc01 hc12 ht).symm⟩
  · rw [Proofs.Quant.stackConfig_u i]
    rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with h | h | h <;> subst h <;> rfl
  · rw [Proofs.Quant.stackConfig_relW i]
    rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with h | h | h <;> subst h <;> rfl

/-- **Leastness, conditional on the floor**: given the floor over this
family as an explicit hypothesis, the attained value is the least
gap value.  The floor hypothesis is *local* to the normal family,
following the ancestor (`KPlankAttain.isLeast_gapValues_of_floor`)
rather than a global `GapFloor` prop: sharper, and what the ancestor
actually proved. -/
theorem isLeast_gapValues_of_floor (c w : Fin 3 → ℝ)
    (hc0 : 0 ≤ c 0) (hc01 : c 0 ≤ c 1) (hc12 : c 1 ≤ c 2)
    (hw : ∀ i, 0 ≤ w i) (ht : w 0 + w 1 + w 2 ≤ 1)
    (hfloor : ∀ g ∈ gapValues (fun i => ((1 : ℝ), -c i)) w,
      (1 - (w 0 + w 1 + w 2)) ^ 2 / 2 ≤ g) :
    IsLeast (gapValues (fun i => ((1 : ℝ), -c i)) w)
      ((1 - (w 0 + w 1 + w 2)) ^ 2 / 2) :=
  ⟨deltaSq_mem_gapValues c w hc0 hc01 hc12 hw ht, hfloor⟩

end Quant

end
