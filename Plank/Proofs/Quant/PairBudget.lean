/-
# Lemma P: the pairwise curvature budget is nonnegative

Port of `Dim2N3/KPlankPairBudget.lean` onto the `Plank` vocabulary.
In the `K`-form of the ledger (`Quant.ledger_K`) the pair term splits
into the curvature budget `w_p w_q (K − 1)` and the clipping loss
`w_p w_q K − |p ∩ q ∩ D|`; this chapter proves **both are
nonnegative**, so each pair helps the square bound.

**Lemma P** is `K(u,v) ≥ 1`, i.e. `W(u)·W(v) ≥ |det(u,v)|`.  The width
`W(u)` is the range of `⟪u,·⟫` over the vertices `(0,0), (1,0), (0,1)`,
so it dominates `|u₁|`, `|u₂|` and `|u₁ − u₂|`; the lemma is then the
purely algebraic **box bound for a 2×2 determinant**
(`det_le_mul_of_ranges`):

> `|a|, |b|, |a−b| ≤ A` and `|c|, |d|, |c−d| ≤ C` ⟹ `|ad − bc| ≤ A·C`

— "a triangle with a vertex at the origin, inscribed in an `A × C` box,
has area at most half the box".  Splitting on the signs of `a, b`
leaves a same-sign branch (where `ad` and `bc` share a sign) and an
opposite-sign branch (where `|a| + |b| = |a − b| ≤ A` pays directly);
each case is one two-term Positivstellensatz certificate.  Sharp at the
edge normals `(1,0), (0,1)`.

**The clipping loss** is nonnegative because the unclipped overlap is a
parallelogram of area exactly `w_p w_q K` — the strips straighten to a
coordinate box under `P ↦ (⟪u,P⟫, ⟪v,P⟫)`, whose determinant is
`det(u,v)`, and Haar measure scales by `|det|⁻¹` under a linear
preimage (`volume_plank_inter`) — and clipping to the triangle only
removes area.
-/
module

public import Plank.Proofs.Quant.Ledger

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant Proofs.Transport

namespace Quant

/-! ## §1  The box bound for a 2×2 determinant -/

/-- The same-sign branch, one direction.  With `a, b ∈ [0, A]` the four
sign positions of `(c, d)` each carry a two-term certificate; only the
`c ≤ 0 ≤ d` position consumes the bound on `d − c`. -/
private theorem key_pos {a b c d A C : ℝ}
    (ha0 : 0 ≤ a) (haA : a ≤ A) (hb0 : 0 ≤ b) (hbA : b ≤ A)
    (hc1 : -C ≤ c) (hc2 : c ≤ C) (_hd1 : -C ≤ d) (hd2 : d ≤ C)
    (hdc : d - c ≤ C) : a * d - b * c ≤ A * C := by
  have hC : 0 ≤ C := by linarith
  have hA : 0 ≤ A := by linarith
  rcases le_total 0 c with hsc | hsc <;> rcases le_total 0 d with hsd | hsd
  · -- `a·d ≤ A·d ≤ A·C` and `b·c ≥ 0`
    nlinarith [mul_nonneg hb0 hsc, mul_nonneg (sub_nonneg.mpr haA) hsd,
      mul_nonneg hA (sub_nonneg.mpr hd2)]
  · -- `a·d ≤ 0 ≤ b·c`
    nlinarith [mul_nonneg ha0 (neg_nonneg.mpr hsd), mul_nonneg hb0 hsc,
      mul_nonneg hA hC]
  · -- `a·d − b·c ≤ A·d − A·c = A(d − c) ≤ A·C`
    nlinarith [mul_nonneg (sub_nonneg.mpr haA) hsd,
      mul_nonneg (sub_nonneg.mpr hbA) (neg_nonneg.mpr hsc),
      mul_nonneg hA (sub_nonneg.mpr hdc)]
  · -- `a·d ≤ 0` and `−b·c ≤ A(−c) ≤ A·C`
    nlinarith [mul_nonneg ha0 (neg_nonneg.mpr hsd),
      mul_nonneg (sub_nonneg.mpr hbA) (neg_nonneg.mpr hsc),
      mul_nonneg hA (by linarith : (0:ℝ) ≤ C + c)]

/-- The opposite-sign branch, one direction.  Here `|a| + |b| = a − b ≤ A`
and the whole estimate is `a·d − b·c ≤ (a − b)·C ≤ A·C` — no split on
`(c, d)` is needed. -/
private theorem key_opp {a b c d A C : ℝ}
    (ha0 : 0 ≤ a) (hb0 : b ≤ 0) (hab : a - b ≤ A)
    (hc2 : c ≤ C) (hd2 : d ≤ C) (hC : 0 ≤ C) : a * d - b * c ≤ A * C := by
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hd2),
    mul_nonneg (neg_nonneg.mpr hb0) (sub_nonneg.mpr hc2),
    mul_nonneg (sub_nonneg.mpr hab) hC]

/-- One direction of the box bound.  Four sign positions of `(a, b)`; the
two same-sign ones go to `key_pos` (after negating all four variables in
the `a, b ≤ 0` position), the two opposite-sign ones to `key_opp`. -/
private theorem det_dir {a b c d A C : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ A) (hab : |a - b| ≤ A)
    (hc : |c| ≤ C) (hd : |d| ≤ C) (hcd : |c - d| ≤ C) :
    a * d - b * c ≤ A * C := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hab1, hab2⟩ := abs_le.mp hab
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  obtain ⟨hcd1, hcd2⟩ := abs_le.mp hcd
  have hC : 0 ≤ C := by linarith
  rcases le_total 0 a with hsa | hsa <;> rcases le_total 0 b with hsb | hsb
  · exact key_pos hsa ha2 hsb hb2 hc1 hc2 hd1 hd2 (by linarith)
  · exact key_opp hsa hsb (by linarith) hc2 hd2 hC
  · -- `(a,b,c,d) ↦ (b,a,−d,−c)` turns this into the previous position
    have h := key_opp (a := b) (b := a) (c := -d) (d := -c) (A := A) (C := C) hsb hsa
      (by linarith) (by linarith) (by linarith) hC
    linarith
  · -- `(a,b,c,d) ↦ (−a,−b,−c,−d)` fixes `a·d − b·c`
    have h := key_pos (a := -a) (b := -b) (c := -c) (d := -d) (A := A) (C := C)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith

/-- **The box bound for a 2×2 determinant.**  If `a, b` and their
difference are bounded by `A`, and `c, d` and their difference by `C`,
then `|ad − bc| ≤ A·C`.  Geometrically: a triangle with a vertex at the
origin, inscribed in an `A × C` box, has area at most half the box. -/
theorem det_le_mul_of_ranges {a b c d A C : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ A) (hab : |a - b| ≤ A)
    (hc : |c| ≤ C) (hd : |d| ≤ C) (hcd : |c - d| ≤ C) :
    |a * d - b * c| ≤ A * C := by
  rw [abs_le]
  refine ⟨?_, det_dir ha hb hab hc hd hcd⟩
  have h := det_dir hb ha (by rw [abs_sub_comm]; exact hab) hd hc
    (by rw [abs_sub_comm]; exact hcd)
  linarith

/-! ## §2  The width dominates the three vertex differences

`stdTriangle.width u` is the range of `0, u₁, u₂` — the shadows of the
three vertices — so it bounds each pairwise difference. -/

theorem abs_fst_le_width (u : ℝ × ℝ) : |u.1| ≤ stdTriangle.width u := by
  rw [stdTriangle_width_eq, abs_le]
  have h1 : u.1 ≤ max 0 (max u.1 u.2) := le_max_of_le_right (le_max_left _ _)
  have h2 : min 0 (min u.1 u.2) ≤ 0 := min_le_left _ _
  have h3 : min 0 (min u.1 u.2) ≤ u.1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have h4 : (0:ℝ) ≤ max 0 (max u.1 u.2) := le_max_left _ _
  constructor <;> linarith

theorem abs_snd_le_width (u : ℝ × ℝ) : |u.2| ≤ stdTriangle.width u := by
  rw [stdTriangle_width_eq, abs_le]
  have h1 : u.2 ≤ max 0 (max u.1 u.2) := le_max_of_le_right (le_max_right _ _)
  have h2 : min 0 (min u.1 u.2) ≤ 0 := min_le_left _ _
  have h3 : min 0 (min u.1 u.2) ≤ u.2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have h4 : (0:ℝ) ≤ max 0 (max u.1 u.2) := le_max_left _ _
  constructor <;> linarith

theorem abs_sub_le_width (u : ℝ × ℝ) : |u.1 - u.2| ≤ stdTriangle.width u := by
  rw [stdTriangle_width_eq, abs_le]
  have h1 : u.1 ≤ max 0 (max u.1 u.2) := le_max_of_le_right (le_max_left _ _)
  have h2 : u.2 ≤ max 0 (max u.1 u.2) := le_max_of_le_right (le_max_right _ _)
  have h3 : min 0 (min u.1 u.2) ≤ u.1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have h4 : min 0 (min u.1 u.2) ≤ u.2 := le_trans (min_le_right _ _) (min_le_right _ _)
  constructor <;> linarith

/-! ## §3  Lemma P, and the curvature budget -/

/-- **Lemma P.**  `|det(u, v)| ≤ W(u)·W(v)` for every pair of normals:
the widths' box contains the determinant.  Sharp at the pair of edge
normals `(1,0), (0,1)`. -/
theorem abs_det_le_width_mul (u v : ℝ × ℝ) :
    |u.1 * v.2 - u.2 * v.1| ≤ stdTriangle.width u * stdTriangle.width v :=
  det_le_mul_of_ranges (abs_fst_le_width u) (abs_snd_le_width u) (abs_sub_le_width u)
    (abs_fst_le_width v) (abs_snd_le_width v) (abs_sub_le_width v)

/-- **Lemma P, in the form the ledger uses**: for non-parallel normals
`K(u,v) ≥ 1 = 2|D|` — the parallelogram cut by two strips of relative
widths `w_p, w_q` has area at least `2|D|·w_p w_q`. -/
theorem one_le_Kpair {u v : ℝ × ℝ} (hdet : u.1 * v.2 - u.2 * v.1 ≠ 0) :
    1 ≤ Kpair u v := by
  have hpos : 0 < |u.1 * v.2 - u.2 * v.1| := abs_pos.mpr hdet
  rw [Kpair, le_div_iff₀ hpos, one_mul]
  exact abs_det_le_width_mul u v

/-- A plank's relative width is nonnegative. -/
theorem relWidth_nonneg (p : Plank) : 0 ≤ p.relWidth stdTriangle :=
  div_nonneg (by linarith [p.lo_le_hi])
    (width_pos stdTriangle p.u_ne_zero).le

/-- **The curvature budget is nonnegative**: `w_p w_q (K − 1) ≥ 0` for
every non-parallel pair. -/
theorem curvBudget_nonneg (p q : Plank)
    (hdet : p.u.1 * q.u.2 - p.u.2 * q.u.1 ≠ 0) : 0 ≤ curvBudget p q :=
  mul_nonneg (mul_nonneg (relWidth_nonneg p) (relWidth_nonneg q))
    (by linarith [one_le_Kpair hdet])

/-! ## §4  The clipping loss is nonnegative

`clipLoss ≥ 0` says that clipping the parallelogram `p ∩ q` to the
triangle can only remove area.  The parallelogram's area is computed by
pulling the box `[lo_p, hi_p] × [lo_q, hi_q]` back along the linear map
`P ↦ (⟪u,P⟫, ⟪v,P⟫)`, whose determinant is `det(u,v)`; Haar measure
scales by `|det|⁻¹` under a linear preimage. -/

/-- The linear map `P ↦ (⟪u,P⟫, ⟪v,P⟫)` straightening the two strips
into a coordinate box. -/
def pairMap (u v : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun P := (dot u P, dot v P)
  map_add' P Q := by
    simp only [dot, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  map_smul' r P := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

private theorem det_pairMap (u v : ℝ × ℝ) :
    LinearMap.det (pairMap u v) = u.1 * v.2 - u.2 * v.1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, pairMap, dot, Module.Basis.finTwoProd]

/-- Two planks meet in the pullback of a coordinate box. -/
private theorem plank_inter_eq_preimage (p q : Plank) :
    p.set ∩ q.set
      = pairMap p.u q.u ⁻¹' (Set.Icc p.lo p.hi ×ˢ Set.Icc q.lo q.hi) := by
  rw [plank_set_eq, plank_set_eq]
  ext P
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_prod, Set.mem_Icc, pairMap, LinearMap.coe_mk, AddHom.coe_mk]

/-- **The parallelogram area.**  Two non-parallel planks of thicknesses
`hi_p − lo_p` and `hi_q − lo_q` meet in a parallelogram of area
`(hi_p − lo_p)(hi_q − lo_q)/|det(u,v)|`. -/
theorem volume_plank_inter (p q : Plank)
    (hdet : p.u.1 * q.u.2 - p.u.2 * q.u.1 ≠ 0) :
    volume (p.set ∩ q.set)
      = ENNReal.ofReal |(p.u.1 * q.u.2 - p.u.2 * q.u.1)⁻¹|
          * (ENNReal.ofReal (p.hi - p.lo) * ENNReal.ofReal (q.hi - q.lo)) := by
  rw [plank_inter_eq_preimage,
    Measure.addHaar_preimage_linearMap volume
      (by rw [det_pairMap]; exact hdet), det_pairMap]
  congr 1
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

/-- `w_p w_q K` is exactly the parallelogram's area. -/
theorem relWidth_mul_Kpair (p q : Plank)
    (hdet : p.u.1 * q.u.2 - p.u.2 * q.u.1 ≠ 0) :
    p.relWidth stdTriangle * q.relWidth stdTriangle * Kpair p.u q.u
      = (p.hi - p.lo) * (q.hi - q.lo) / |p.u.1 * q.u.2 - p.u.2 * q.u.1| := by
  have hp := (width_pos stdTriangle p.u_ne_zero).ne'
  have hq := (width_pos stdTriangle q.u_ne_zero).ne'
  have hd : |p.u.1 * q.u.2 - p.u.2 * q.u.1| ≠ 0 := abs_ne_zero.mpr hdet
  unfold Plank.relWidth Kpair
  field_simp

/-- **The clipped overlap never exceeds the full parallelogram**
`w_p w_q K`. -/
theorem pairOverlap_le (p q : Plank)
    (hdet : p.u.1 * q.u.2 - p.u.2 * q.u.1 ≠ 0) :
    pairOverlap p q
      ≤ p.relWidth stdTriangle * q.relWidth stdTriangle * Kpair p.u q.u := by
  have hd : (0:ℝ) < |p.u.1 * q.u.2 - p.u.2 * q.u.1| := abs_pos.mpr hdet
  have hvol := volume_plank_inter p q hdet
  have hne : volume (p.set ∩ q.set) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hmono : pairOverlap p q ≤ area (p.set ∩ q.set) :=
    ENNReal.toReal_mono hne (measure_mono Set.inter_subset_left)
  have hcalc : area (p.set ∩ q.set)
      = (p.hi - p.lo) * (q.hi - q.lo) / |p.u.1 * q.u.2 - p.u.2 * q.u.1| := by
    unfold area
    rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by linarith [p.lo_le_hi]),
      ENNReal.toReal_ofReal (by linarith [q.lo_le_hi]), abs_inv]
    field_simp
  rw [relWidth_mul_Kpair p q hdet]
  linarith [hmono, hcalc.le, hcalc.ge]

/-- **The clipping loss is nonnegative** for every non-parallel pair. -/
theorem clipLoss_nonneg (p q : Plank)
    (hdet : p.u.1 * q.u.2 - p.u.2 * q.u.1 ≠ 0) : 0 ≤ clipLoss p q := by
  have := pairOverlap_le p q hdet
  unfold clipLoss
  linarith

end Quant

end
