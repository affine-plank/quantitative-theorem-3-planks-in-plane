module
/-
# Gap cells — the 2³ decomposition of the uncovered set

A point of the triangle missed by all three planks chooses, for each
plank, a side to miss it on.  The uncovered set therefore splits into
`2³` **gap cells**, indexed by a sign vector `σ : Fin 3 → Bool`, and

    the configuration covers  ⟺  all eight cells are empty.

Each cell is an open convex polygon cut from the triangle by three
half-planes; emptiness of a cell is a finite family of linear
inequalities on the configuration.  This finiteness is what makes the
conjecture case-checkable and is the engine of both v1 and v3.

The second half of the file is the **tightness reduction**: windows may
be trimmed into the triangle's shadow range for free, and a covering
with `Σ rw < 1` can be fattened to one with `Σ rw = 1` — so only tight
configurations (studied in `Plank/Tight.lean`) need to be understood.

Replaces: `Dim2N3/Geometry/GapCell.lean`, the cell predicates of
`Dim2N3/TightCoverings.lean`, `Dim2N3/GapCellFarkas.lean` (LP view),
and the trim/fatten machinery of `Dim2N3/TightNoWasteFattening.lean`.
-/
public import Plank.Core
public import Plank.Proofs.GapCells

@[expose] public section


public section

noncomputable section

open Proofs.Basic Proofs.Transport Proofs.GapCells

/-! ## §1  The cells -/

/-- A gap-cell index: one side choice per plank (`false` = below `lo`,
`true` = above `hi`). -/
@[expose] abbrev CellIndex := Fin 3 → Bool

/-- The side of plank `p` selected by `s`: strictly below its window
(`false`) or strictly above it (`true`). -/
@[expose] def Plank.side (p : Plank) (s : Bool) : Set (ℝ × ℝ) :=
  if s then {x | p.hi < dot p.u x} else {x | dot p.u x < p.lo}

/-- The **gap cell** of `σ`: the points of the standard triangle missing
every plank on the side `σ` prescribes. -/
@[expose] def Config.cell (C : Config) (σ : CellIndex) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ ⋂ i, (C.plank i).side (σ i)

/-- The uncovered set is precisely the union of the eight gap cells. -/
theorem Config.uncovered_eq_iUnion_cell (C : Config) :
    C.uncovered = ⋃ σ : CellIndex, C.cell σ := by
  ext P
  constructor
  · rintro ⟨hP, hn⟩
    have hn' : ∀ i, ¬ (P ∈ C.plank i) := fun i hi =>
      hn (Set.mem_iUnion.mpr ⟨i, hi⟩)
    refine Set.mem_iUnion.mpr ⟨fun i => if (C.plank i).hi < dot (C.plank i).u P
      then true else false, hP, Set.mem_iInter.mpr fun i => ?_⟩
    by_cases hb : (C.plank i).hi < dot (C.plank i).u P
    · simpa [Plank.side, hb] using hb
    · have hlt : dot (C.plank i).u P < (C.plank i).lo := by
        push_neg at hb
        by_contra hc
        push_neg at hc
        exact hn' i ⟨hc, hb⟩
      simpa [Plank.side, hb] using hlt
  · intro hmem
    obtain ⟨σ, hP, hcell⟩ := Set.mem_iUnion.mp hmem
    refine ⟨hP, fun hu => ?_⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
    have hside := Set.mem_iInter.mp hcell i
    have hi' : (C.plank i).lo ≤ dot (C.plank i).u P ∧
        dot (C.plank i).u P ≤ (C.plank i).hi := hi
    cases hb : σ i with
    | false =>
      simp only [Plank.side, hb, Bool.false_eq_true, if_false,
        Set.mem_setOf_eq] at hside
      linarith [hi'.1]
    | true =>
      simp only [Plank.side, hb, if_true, Set.mem_setOf_eq] at hside
      linarith [hi'.2]

/-- **The cell criterion**: a configuration covers the triangle iff all
eight gap cells are empty. -/
theorem Config.covers_iff_cells_empty (C : Config) :
    C.Covers ↔ ∀ σ : CellIndex, C.cell σ = ∅ := by
  constructor
  · intro hcov σ
    rw [Set.eq_empty_iff_forall_notMem]
    intro P hP
    have hunc : P ∈ C.uncovered := by
      rw [C.uncovered_eq_iUnion_cell]; exact Set.mem_iUnion.mpr ⟨σ, hP⟩
    obtain ⟨i, hi⟩ := hcov P hunc.1
    exact hunc.2 (Set.mem_iUnion.mpr ⟨i, hi⟩)
  · intro h P hP
    by_contra hc
    push_neg at hc
    have hunc : P ∈ C.uncovered :=
      ⟨hP, fun hu => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu; exact hc i hi⟩
    rw [C.uncovered_eq_iUnion_cell] at hunc
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hunc
    rw [h σ] at hσ
    exact hσ

/-- Each gap cell is convex (an intersection of half-planes with the
triangle) — so cells are empty or full-dimensional pieces. -/
theorem Config.cell_convex (C : Config) (σ : CellIndex) :
    Convex ℝ (C.cell σ) := by
  refine Convex.inter (convex_triangle stdTriangle) (convex_iInter fun i => ?_)
  cases hb : σ i with
  | false =>
    simpa only [Plank.side, hb, Bool.false_eq_true, if_false]
      using convex_dot_lt (C.plank i).u (C.plank i).lo
  | true =>
    simpa only [Plank.side, hb, if_true]
      using convex_lt_dot (C.plank i).u (C.plank i).hi

/-- The cell interiors are relatively open in the triangle: a nonempty
cell off the triangle's boundary has positive area.  (The LP/witness
view: cell emptiness is decidable from finitely many linear margins.) -/
theorem Config.cell_nonempty_iff_pos_area (C : Config) (σ : CellIndex)
    (h : (C.cell σ ∩ interior stdTriangle.set).Nonempty) :
    0 < MeasureTheory.volume (C.cell σ) := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  have hopen : IsOpen (interior stdTriangle.set ∩ ⋂ i, (C.plank i).side (σ i)) := by
    refine IsOpen.inter isOpen_interior (isOpen_iInter_of_finite fun i => ?_)
    cases hb : σ i with
    | false =>
      simpa only [Plank.side, hb, Bool.false_eq_true, if_false]
        using isOpen_dot_lt (C.plank i).u (C.plank i).lo
    | true =>
      simpa only [Plank.side, hb, if_true]
        using isOpen_lt_dot (C.plank i).u (C.plank i).hi
  have hsub : interior stdTriangle.set ∩ ⋂ i, (C.plank i).side (σ i) ⊆ C.cell σ :=
    fun x hx => ⟨interior_subset hx.1, hx.2⟩
  exact lt_of_lt_of_le (volume_pos_of_isOpen hopen ⟨z, hz₂, hz₁.2⟩)
    (MeasureTheory.measure_mono hsub)

/-- **The middle-plank pigeonhole**: two triangle points each missing
planks 0 and 2 whose plank-1 levels differ by more than plank 1's
width cannot both be covered — plank 1's window is an interval and
cannot hold both levels.  The reusable engine of the chamber-D
emptiness proofs (`aab_no_tight_covering`, `Plank/Tight.lean`); other
index roles follow by a relabel move. -/
theorem Config.not_covers_of_pigeonhole (C : Config) {P Q : ℝ × ℝ}
    (hP : P ∈ stdTriangle) (hQ : Q ∈ stdTriangle)
    (hP0 : P ∉ C.plank 0) (hP2 : P ∉ C.plank 2)
    (hQ0 : Q ∉ C.plank 0) (hQ2 : Q ∉ C.plank 2)
    (hgap : (C.plank 1).hi - (C.plank 1).lo <
      |dot (C.plank 1).u P - dot (C.plank 1).u Q|) :
    ¬ C.Covers := by
  intro hcov
  have hmid : ∀ X : ℝ × ℝ, X ∈ stdTriangle → X ∉ C.plank 0 → X ∉ C.plank 2 →
      X ∈ C.plank 1 := by
    intro X hX h0 h2
    obtain ⟨i, hi⟩ := hcov X hX
    fin_cases i
    · exact absurd hi h0
    · exact hi
    · exact absurd hi h2
  have h1 := hmid P hP hP0 hP2
  have h2 := hmid Q hQ hQ0 hQ2
  rcases abs_cases (dot (C.plank 1).u P - dot (C.plank 1).u Q) with ⟨he, _⟩ | ⟨he, _⟩ <;>
    rw [he] at hgap <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## §2  Trimming — windows inside the shadow range for free -/

/-- The smallest vertex shadow of the standard triangle along the `i`-th
normal (the elementary `rangeInf`). -/
@[expose] def Config.shadowMin (C : Config) (i : Fin 3) : ℝ :=
  min (0 : ℝ) (min (C.plank i).u.1 (C.plank i).u.2)

/-- The largest vertex shadow of the standard triangle along the `i`-th
normal. -/
@[expose] def Config.shadowMax (C : Config) (i : Fin 3) : ℝ :=
  max (0 : ℝ) (max (C.plank i).u.1 (C.plank i).u.2)

/-- A configuration is **trimmed** if every window sits inside its
shadow range: no plank wastes width outside the triangle's shadow. -/
@[expose] def Config.Trimmed (C : Config) : Prop :=
  ∀ i, C.shadowMin i ≤ (C.plank i).lo ∧ (C.plank i).hi ≤ C.shadowMax i

/-- **Trimming is free**: any covering configuration can be replaced by
a trimmed covering configuration with no larger ledger. -/
theorem Config.exists_trimmed (C : Config) (hcov : C.Covers) :
    ∃ C' : Config, C'.Covers ∧ C'.Trimmed ∧
      C'.sumRelW ≤ C.sumRelW ∧ ∀ i, (C'.plank i).u = (C.plank i).u := by
  refine ⟨⟨fun i => ⟨(C.plank i).u,
      clamp (C.shadowMin i) (C.shadowMax i) (C.plank i).lo,
      clamp (C.shadowMin i) (C.shadowMax i) (C.plank i).hi,
      (C.plank i).u_ne_zero, clamp_mono _ _ (C.plank i).lo_le_hi⟩⟩,
    ?_, ?_, ?_, fun i => rfl⟩
  · intro P hP
    obtain ⟨i, hi⟩ := hcov P hP
    obtain ⟨hs₁, hs₂⟩ := dot_shadow_bounds (C.plank i).u hP
    exact ⟨i, clamp_le_of_mem hs₁ hi.1, le_clamp_of_mem hs₂ hi.2⟩
  · exact fun i => ⟨clamp_ge _ _ _,
      clamp_le _ _ _ (shadowMin_le_shadowMax (C.plank i).u)⟩
  · refine Finset.sum_le_sum fun i _ => ?_
    have hW : 0 < stdTriangle.width (C.plank i).u :=
      width_pos _ (C.plank i).u_ne_zero
    simp only [Config.relW, Plank.relWidth]
    exact (div_le_div_iff_of_pos_right hW).mpr
      (clamp_sub_le _ _ _ _ (C.plank i).lo_le_hi)

/-! ## §3  Fattening — the reduction to tight configurations -/

/-- The **margin** of plank `p` at a point: its distance-in-level to the
nearer window edge — positive strictly inside the window, zero on its
edges, negative outside. -/
@[expose] def Plank.margin (p : Plank) (x : ℝ × ℝ) : ℝ :=
  min (dot p.u x - p.lo) (p.hi - dot p.u x)

/-- The configuration's margin at a point: the best plank's margin —
positive iff some plank contains the point strictly. -/
@[expose] def Config.margin (C : Config) (x : ℝ × ℝ) : ℝ :=
  (C.plank 0).margin x ⊔ (C.plank 1).margin x ⊔ (C.plank 2).margin x

/-- The **minimal margin** `M(C) = min_{x ∈ T} max_i marginᵢ(x)`: the
one number that decides whether the covering has room to breathe. -/
@[expose] def Config.minMargin (C : Config) : ℝ :=
  sInf (C.margin '' stdTriangle.set)

/-- The configuration covers **openly**: every point of the triangle is
in some plank's open window.  Openly-covering configurations survive
small perturbations. -/
@[expose] def Config.CoversOpenly (C : Config) : Prop :=
  ∀ P ∈ stdTriangle, ∃ i,
    (C.plank i).lo < dot (C.plank i).u P ∧
      dot (C.plank i).u P < (C.plank i).hi

/-- The configuration's margin, spelled as a nested `max`. -/
theorem Config.margin_eq (C : Config) (x : ℝ × ℝ) :
    C.margin x = max (max ((C.plank 0).margin x) ((C.plank 1).margin x))
      ((C.plank 2).margin x) := rfl

/-- The margin function is continuous: a max of mins of affine
functions. -/
theorem Config.continuous_margin (C : Config) : Continuous C.margin := by
  have hp : ∀ p : Plank, Continuous p.margin := fun p =>
    Continuous.min ((continuous_dot p.u).sub continuous_const)
      (continuous_const.sub (continuous_dot p.u))
  have he : C.margin = fun x => max (max ((C.plank 0).margin x)
      ((C.plank 1).margin x)) ((C.plank 2).margin x) := funext fun x => C.margin_eq x
  rw [he]
  exact ((hp _).max (hp _)).max (hp _)

/-- Each plank's margin is at most the configuration's. -/
theorem Config.le_margin (C : Config) (x : ℝ × ℝ) (i : Fin 3) :
    (C.plank i).margin x ≤ C.margin x := by
  rw [C.margin_eq]
  fin_cases i
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

/-- …and the max is attained by one of them. -/
theorem Config.exists_margin_eq (C : Config) (x : ℝ × ℝ) :
    ∃ i, C.margin x = (C.plank i).margin x := by
  rw [C.margin_eq]
  rcases le_total ((C.plank 0).margin x) ((C.plank 1).margin x) with h | h
  · rcases le_total ((C.plank 1).margin x) ((C.plank 2).margin x) with h₂ | h₂
    · exact ⟨2, by rw [max_eq_right h, max_eq_right h₂]⟩
    · exact ⟨1, by rw [max_eq_right h, max_eq_left h₂]⟩
  · rcases le_total ((C.plank 0).margin x) ((C.plank 2).margin x) with h₂ | h₂
    · exact ⟨2, by rw [max_eq_left h, max_eq_right h₂]⟩
    · exact ⟨0, by rw [max_eq_left h, max_eq_left h₂]⟩

/-- Open covering is exactly positive minimal margin: the margin is
continuous and the triangle compact, so pointwise strictness has a
uniform witness. -/
theorem Config.coversOpenly_iff_minMargin_pos (C : Config) :
    C.CoversOpenly ↔ 0 < C.minMargin := by
  constructor
  · intro h
    obtain ⟨z, hz, hzeq⟩ :=
      exists_min_on_stdTriangle (f := C.margin) C.continuous_margin
    rw [Config.minMargin, ← hzeq]
    obtain ⟨i, h₁, h₂⟩ := h z hz
    refine lt_of_lt_of_le ?_ (C.le_margin z i)
    exact lt_min (by linarith) (by linarith)
  · intro h P hP
    have hle : C.minMargin ≤ C.margin P :=
      sInf_le_of_mem (f := C.margin) C.continuous_margin hP
    obtain ⟨i, hi⟩ := C.exists_margin_eq P
    have hpos : 0 < (C.plank i).margin P := by rw [← hi]; linarith
    simp only [Plank.margin, lt_min_iff] at hpos
    exact ⟨i, by linarith [hpos.1], by linarith [hpos.2]⟩

/-- The minimal margin is attained: a compactness consequence, giving
the **contact point** of a non-open covering. -/
theorem Config.exists_margin_eq_minMargin (C : Config) :
    ∃ z ∈ stdTriangle, C.margin z = C.minMargin :=
  exists_min_on_stdTriangle (f := C.margin) C.continuous_margin

/-- At a contact point of a non-open covering, every plank holds the
point only at or beyond a window edge — the derived form of the old
"stuck contact" (the primitive predicate is gone; this is a lemma about
`minMargin`). -/
theorem Config.exists_contact_of_minMargin_nonpos (C : Config)
    (hcov : C.Covers) (h : C.minMargin ≤ 0) :
    ∃ z ∈ stdTriangle, (∃ i, dot (C.plank i).u z = (C.plank i).lo ∨
        dot (C.plank i).u z = (C.plank i).hi) ∧
      ∀ i, dot (C.plank i).u z ≤ (C.plank i).lo ∨
        (C.plank i).hi ≤ dot (C.plank i).u z := by
  obtain ⟨z, hz, hzeq⟩ := C.exists_margin_eq_minMargin
  obtain ⟨i₀, hi₀⟩ := hcov z hz
  have hnonneg : 0 ≤ C.margin z :=
    le_trans (le_min (by linarith [hi₀.1]) (by linarith [hi₀.2])) (C.le_margin z i₀)
  have hzero : C.margin z = 0 := le_antisymm (hzeq ▸ h) hnonneg
  obtain ⟨i₁, hi₁⟩ := C.exists_margin_eq z
  refine ⟨z, hz, ⟨i₁, ?_⟩, fun i => ?_⟩
  · have hm : (C.plank i₁).margin z = 0 := by rw [← hi₁, hzero]
    simp only [Plank.margin] at hm
    rcases min_cases (dot (C.plank i₁).u z - (C.plank i₁).lo)
      ((C.plank i₁).hi - dot (C.plank i₁).u z) with ⟨he, _⟩ | ⟨he, _⟩
    · left; rw [he] at hm; linarith
    · right; rw [he] at hm; linarith
  · have hle : (C.plank i).margin z ≤ 0 := hzero ▸ C.le_margin z i
    simp only [Plank.margin] at hle
    rcases min_le_iff.mp hle with h' | h'
    · left; linarith
    · right; linarith

/-- **The fattening conclusion is unsatisfiable at a flush plank**
(P1r7 finding).  If any window already starts at its shadow minimum,
no configuration with the same normals can be trimmed AND have that
window start strictly lower: trimmedness pins `lo'` at or above the
shadow minimum, which is where `lo` already is.  Dually at the top.

This is not about coverings — it is a two-line consequence of
`Trimmed` — and it is what makes the strict two-sided growth clause of
`Config.exists_tight_fattening` unreachable, since nothing in that
lemma's hypotheses excludes a flush input (trimmed coverings are
routinely flush; every edge-tiling member is). -/
theorem no_strict_growth_at_flush {C C' : Config} {i : Fin 3}
    (htr' : C'.Trimmed) (hu : ∀ j, (C'.plank j).u = (C.plank j).u)
    (hflush : (C.plank i).lo = C.shadowMin i) :
    ¬ (C'.plank i).lo < (C.plank i).lo := by
  have hs : C'.shadowMin i = C.shadowMin i := by
    simp only [Config.shadowMin, hu i]
  have := (htr' i).1
  rw [hs, ← hflush] at this
  linarith

/-- **The tightness reduction**: a trimmed covering with `Σ rw < 1`
fattens to a *tight, still trimmed* configuration — same normals,
windows grown (non-strictly; a flush side takes no growth, and
`no_strict_growth_at_flush` above is exactly why no strict clause can
stand here).  The former horn is gone: `CoversOpenly` is unreachable
under `Trimmed`, full stop (a point whose every covering plank meets it
at the shadow minimum has margin `0` in every trimmed configuration
with those normals — fattening cannot repair what trimming forbids;
tier_600 §1).  Consumer: the CHAMBER-E branch only
(tier_601 — the umbrella bounds T, C, D without tightness); there the
assembly contradicts `Config.IsHex.not_shrinkable` (`Plank/Tight.lean`)
with the *input* `C` sitting inside the fattened tight `C'` at strictly
smaller ledger. -/
theorem Config.exists_tight_fattening (C : Config) (hcov : C.Covers)
    (htrim : C.Trimmed) (hlt : C.sumRelW < 1) :
    ∃ C' : Config, C'.Covers ∧ C'.sumRelW = 1 ∧ C'.Trimmed ∧
      (∀ i, (C'.plank i).u = (C.plank i).u) ∧
      (∀ i, (C'.plank i).lo ≤ (C.plank i).lo ∧
        (C.plank i).hi ≤ (C'.plank i).hi) := by
  -- The spread construction (tier_600 §2.3).
  have hW : ∀ i, 0 < stdTriangle.width (C.plank i).u := fun i =>
    width_pos _ (C.plank i).u_ne_zero
  have hWeq : ∀ i, stdTriangle.width (C.plank i).u = C.shadowMax i - C.shadowMin i := by
    intro i
    rw [stdTriangle_width_eq]
    simp only [Config.shadowMin, Config.shadowMax]
  have hrw1 : ∀ i, C.relW i ≤ 1 := by
    intro i
    have h1 := (htrim i).1
    have h2 := (htrim i).2
    simp only [Config.relW, Plank.relWidth]
    rw [div_le_one (hW i), hWeq i]
    linarith
  have hSsum : C.relW 0 + C.relW 1 + C.relW 2 = C.sumRelW := by
    simp [Config.sumRelW, Fin.sum_univ_three]
  have hden : (0 : ℝ) < 3 - C.sumRelW := by linarith
  -- the per-plank shares
  set d : Fin 3 → ℝ := fun i => (1 - C.sumRelW) * (1 - C.relW i) / (3 - C.sumRelW) with hd
  have hd0 : ∀ i, 0 ≤ d i := fun i => by
    simp only [hd]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith [hrw1 i])) (by linarith)
  have hdle : ∀ i, d i ≤ 1 - C.relW i := by
    intro i
    simp only [hd]
    rw [div_le_iff₀ hden]
    nlinarith [hrw1 i]
  have hdsum : d 0 + d 1 + d 2 = 1 - C.sumRelW := by
    simp only [hd, ← add_div]
    rw [div_eq_iff (ne_of_gt hden)]
    linear_combination (C.sumRelW - 1) * hSsum
  -- the per-plank two-sided split
  set up : Fin 3 → ℝ := fun i =>
    min (stdTriangle.width (C.plank i).u * d i) (C.shadowMax i - (C.plank i).hi) with hup
  set dn : Fin 3 → ℝ := fun i => stdTriangle.width (C.plank i).u * d i - up i with hdn
  have hup0 : ∀ i, 0 ≤ up i := fun i =>
    le_min (mul_nonneg (hW i).le (hd0 i)) (by linarith [(htrim i).2])
  have hupmax : ∀ i, up i ≤ C.shadowMax i - (C.plank i).hi := fun i => min_le_right _ _
  have hdn0 : ∀ i, 0 ≤ dn i := fun i => by
    simp only [hdn]; linarith [min_le_left (stdTriangle.width (C.plank i).u * d i)
      (C.shadowMax i - (C.plank i).hi)]
  have hdnlo : ∀ i, dn i ≤ (C.plank i).lo - C.shadowMin i := by
    intro i
    have hhead : stdTriangle.width (C.plank i).u * d i
        ≤ (C.shadowMax i - (C.plank i).hi) + ((C.plank i).lo - C.shadowMin i) := by
      have h1 : stdTriangle.width (C.plank i).u * d i
          ≤ stdTriangle.width (C.plank i).u * (1 - C.relW i) :=
        mul_le_mul_of_nonneg_left (hdle i) (hW i).le
      have h2 : stdTriangle.width (C.plank i).u * (1 - C.relW i)
          = stdTriangle.width (C.plank i).u - ((C.plank i).hi - (C.plank i).lo) := by
        simp only [Config.relW, Plank.relWidth]
        rw [mul_sub, mul_one, mul_div_cancel₀ _ (ne_of_gt (hW i))]
      rw [h2, hWeq i] at h1
      rw [hWeq i]
      linarith
    have hdni : dn i = stdTriangle.width (C.plank i).u * d i - up i := rfl
    rw [hdni]
    rcases min_cases (stdTriangle.width (C.plank i).u * d i)
      (C.shadowMax i - (C.plank i).hi) with ⟨he, -⟩ | ⟨he, -⟩
    · have hui : up i = stdTriangle.width (C.plank i).u * d i := he
      rw [hui]; linarith [(htrim i).1]
    · have hui : up i = C.shadowMax i - (C.plank i).hi := he
      rw [hui]; linarith
  have hsplit : ∀ i, up i + dn i = stdTriangle.width (C.plank i).u * d i := fun i => by
    simp only [hdn]; ring
  refine ⟨⟨fun i => ⟨(C.plank i).u, (C.plank i).lo - dn i, (C.plank i).hi + up i,
      (C.plank i).u_ne_zero, by linarith [(C.plank i).lo_le_hi, hdn0 i, hup0 i]⟩⟩,
    ?_, ?_, ?_, fun i => rfl, fun i => ⟨by linarith [hdn0 i], by linarith [hup0 i]⟩⟩
  · -- covers: every window grew
    intro P hP
    obtain ⟨i, hmem⟩ := hcov P hP
    exact ⟨i, by linarith [hmem.1, hdn0 i], by linarith [hmem.2, hup0 i]⟩
  · -- the ledger is exactly one
    have hrel : ∀ i, ((C.plank i).hi + up i - ((C.plank i).lo - dn i))
        / stdTriangle.width (C.plank i).u = C.relW i + d i := by
      intro i
      have : (C.plank i).hi + up i - ((C.plank i).lo - dn i)
          = ((C.plank i).hi - (C.plank i).lo) + stdTriangle.width (C.plank i).u * d i := by
        linarith [hsplit i]
      rw [this, add_div, mul_div_cancel_left₀ _ (ne_of_gt (hW i))]
      rfl
    show Config.sumRelW ⟨_⟩ = 1
    simp only [Config.sumRelW, Fin.sum_univ_three, Config.relW, Plank.relWidth]
    rw [hrel 0, hrel 1, hrel 2]
    linarith [hSsum, hdsum]
  · -- trimmed: each share stays inside its own headroom
    intro i
    exact ⟨show C.shadowMin i ≤ (C.plank i).lo - dn i by linarith [hdnlo i],
      show (C.plank i).hi + up i ≤ C.shadowMax i by linarith [hupmax i]⟩


end
