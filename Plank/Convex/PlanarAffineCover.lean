/- Three affine windows on a compact planar convex set have total relative
width at least one. Reflect the affine relation, normalize by attained ranges,
and make its coefficients positive by a small common perturbation. -/
module
public import Plank.Convex.PlanarFiniteCover
public import Plank.Convex.PlanarAffineRelation
public import Plank.Convex.PlanarTight.ExactRangeNormalization
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Algebra.BigOperators.Field
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarAffineCover
open scoped BigOperators
open DeficientHeightTilt PlanarTight
open ExactRangeNormalization (chart endpoint)

abbrev Point := Fin 3 → ℝ

/-- A common perturbation makes a nonnegative nonzero normal positive. The unit box
controls both the widened windows and the perturbed directional ranges. -/
private theorem normalized_nonnegative
    (K : Set Point) (hcompact : IsCompact K) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 ≤ A i) (hpos : ∃ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i*x i = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) :
    1 ≤ ∑ i, (hi i-lo i) := by
  by_contra! hdef
  let S := ∑ i, (hi i - lo i)
  let e := (1-S)/24
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (horder i))
  have he : 0 < e := div_pos (sub_pos.mpr hdef) (by norm_num)
  have hd : 0 < 1-3*e := by dsimp [e]; linarith
  have hsum (x : Point) (hx : x ∈ K) : 0 ≤ ∑ i, x i ∧ (∑ i, x i) ≤ 3 := by
    constructor
    · exact Finset.sum_nonneg (fun i _ => (hbox x hx i).1)
    · simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hbox x hx i).2)
  let g : Fin 3 → Point →ᵃ[ℝ] ℝ := fun i =>
    AffineMap.proj i - e • ∑ j : Fin 3, AffineMap.proj j
  have hg (i : Fin 3) (x : Point) : g i x = x i - e * ∑ j, x j := by
    simp [g, Fin.sum_univ_three, mul_add]
  have hnear (x : Point) (hx : x ∈ K) (i : Fin 3) :
      x i - 3*e ≤ g i x ∧ g i x ≤ x i := by
    rw [hg]
    have H := mul_le_mul_of_nonneg_left (hsum x hx).2 he.le
    have L := mul_nonneg he.le (hsum x hx).1
    constructor <;> linarith only [H, L]
  obtain ⟨z, hz, _⟩ := hL 0
  obtain ⟨m, hb, hmin, hmax⟩ := ExactRangeNormalization.exists_ranges K hcompact ⟨z, hz⟩ g
  let W : Point := fun i => rangeWidth K (g i)
  have hWbound (i : Fin 3) : 1-3*e ≤ W i := by
    obtain ⟨x, hx, hxi⟩ := hL i
    obtain ⟨y, hy, hyi⟩ := hU i
    have H := (hb y hy i).2
    have L := (hb x hx i).1
    have X := (hnear x hx i).2
    have Y := (hnear y hy i).1
    rw [hxi] at X
    rw [hyi] at Y
    linarith only [H, L, X, Y]
  have hW (i : Fin 3) : 0 < W i := hd.trans_le (hWbound i)
  have hsumA : 0 < ∑ i, A i := by
    obtain ⟨i, hi⟩ := hpos
    exact hi.trans_le (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i))
  let B : Point := fun i => (1-3*e)*A i + e*∑ j, A j
  have hB (i : Fin 3) : 0 < B i :=
    add_pos_of_nonneg_of_pos (mul_nonneg hd.le (hA i)) (mul_pos he hsumA)
  have hp (x : Point) (hx : x ∈ K) : ∑ i, B i*g i x = (1-3*e)*D := by
    rw [← hplane x hx]
    simp only [B, hg, Fin.sum_univ_three]
    ring
  let l : Point := fun i => lo i-3*e
  have hl (i : Fin 3) : l i ≤ hi i := by dsimp [l]; linarith only [horder i, he]
  have hc : ∀ x ∈ K, ∃ i, l i ≤ g i x ∧ g i x ≤ hi i := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact ⟨i, (sub_le_sub_right hi.1 _).trans (hnear x hx i).1,
      (hnear x hx i).2.trans hi.2⟩
  have H := PlanarFrozenMinimum.width_bound (chart g m W '' K) (Convex.affine_image _ hK)
    (ExactRangeNormalization.box K g m W hW hb)
    (ExactRangeNormalization.zero_contacts K g m W hmin)
    (ExactRangeNormalization.unit_contacts K g m W hW hmax)
    (fun i => B i*W i) ((1-3*e)*D - ∑ i, B i*m i)
    (fun i => mul_pos (hB i) (hW i))
    (ExactRangeNormalization.plane K g m W B _ (fun i => (hW i).ne') hp)
    (endpoint m W l) (endpoint m W hi)
    (ExactRangeNormalization.ordered m W l hi hW hl)
    ((ExactRangeNormalization.cover_iff K g m W l hi hW).mpr hc)
  simp only [ExactRangeNormalization.width_eq] at H
  have hcost : (∑ i, (hi i-l i)/W i) ≤ (S+9*e)/(1-3*e) := by
    calc
      _ ≤ ∑ i, (hi i-l i)/(1-3*e) := Finset.sum_le_sum (fun i _ =>
        div_le_div_of_nonneg_left (sub_nonneg.mpr (hl i)) hd (hWbound i))
      _ = _ := by rw [← Finset.sum_div]; congr 1; simp [S, l, Fin.sum_univ_three]; ring
  have hsmall : (S+9*e)/(1-3*e) < 1 := by
    apply (div_lt_one hd).mpr
    dsimp [e]
    change S < 1 at hdef
    linarith only [hdef]
  exact (H.trans hcost).not_gt hsmall

/-- Any nontrivial affine relation reduces the cover directly to the normalized
statement. Some coefficients may vanish; every relative width is preserved. -/
theorem relation_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : Set E) (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Point)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, lo i ≤ hi i)
    (a : Point) (d : ℝ) (ha : ∃ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i * f i x = d)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) / rangeWidth K (f i) := by
  let g : Fin 3 → E →ᵃ[ℝ] ℝ := fun i => if a i < 0 then -f i else f i
  let l : Point := fun i => if a i < 0 then -hi i else lo i
  let h : Point := fun i => if a i < 0 then -lo i else hi i
  have hgW (i : Fin 3) : rangeWidth K (g i) = rangeWidth K (f i) := by
    by_cases hn : a i < 0
    · simp only [g, if_pos hn]
      have hb := (hK.image (f i).continuous_of_finiteDimensional).isBounded
      have hbn := (hK.image (-f i).continuous_of_finiteDimensional).isBounded
      rw [rangeWidth, rangeWidth, Body.width, Body.width, ← Real.diam_eq hb, ← Real.diam_eq hbn]
      have he : (-f i) '' K = Neg.neg '' (f i '' K) := by
        rw [Set.image_image]
        rfl
      rw [he, isometry_neg.diam_image]
    · simp only [g, if_neg hn]
  have hgpos (i : Fin 3) : 0 < rangeWidth K (g i) := by rw [hgW]; exact hW i
  have hw (i : Fin 3) : h i - l i = hi i - lo i := by
    dsimp [h, l]
    split_ifs <;> ring
  have hlh (i : Fin 3) : l i ≤ h i := by
    dsimp [h, l]
    split_ifs
    · exact neg_le_neg (horder i)
    · exact horder i
  have hcov : ∀ x ∈ K, ∃ i, l i ≤ g i x ∧ g i x ≤ h i := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    refine ⟨i, ?_⟩
    dsimp [g, l, h]
    split_ifs
    · exact ⟨neg_le_neg hi.2, neg_le_neg hi.1⟩
    · exact hi
  have hp : ∀ x ∈ K, ∑ i, |a i| * g i x = d := by
    intro x hx
    convert hplane x hx using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hn : a i < 0
    · simp [g, hn, abs_of_neg hn]
    · simp [g, hn, abs_of_nonneg (le_of_not_gt hn)]
  obtain ⟨m, hb, hL, hU⟩ := ExactRangeNormalization.exists_ranges K hK hne g
  let W : Point := fun i => rangeWidth K (g i)
  have hpos : ∃ i, 0 < |a i| * W i := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨i, mul_pos (abs_pos.mpr hi) (hgpos i)⟩
  have H := normalized_nonnegative (chart g m W '' K)
    (hK.image (chart g m W).continuous_of_finiteDimensional)
    (Convex.affine_image _ hconv)
    (ExactRangeNormalization.box K g m W hgpos hb)
    (ExactRangeNormalization.zero_contacts K g m W hL)
    (ExactRangeNormalization.unit_contacts K g m W hgpos hU)
    (fun i => |a i| * W i) (d - ∑ i, |a i| * m i)
    (fun i => mul_nonneg (abs_nonneg _) (hgpos i).le) hpos
    (ExactRangeNormalization.plane K g m W (fun i => |a i|) d (fun i => (hgpos i).ne') hp)
    (endpoint m W l) (endpoint m W h)
    (ExactRangeNormalization.ordered m W l h hgpos hlh)
    ((ExactRangeNormalization.cover_iff K g m W l h hgpos).mpr hcov)
  simpa only [ExactRangeNormalization.width_eq, hw, W, hgW] using H

/-- Apply the planar argument in any real space of dimension at most two,
without changing the body or its affine functions. -/
theorem width_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E ≤ 2)
    (K : Set E) (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) / rangeWidth K (f i) := by
  obtain ⟨a, ha, d, hp⟩ := PlanarAffineRelation.exists_relation_of_finrank_le_two hdim f
  exact relation_bound K hK hne hconv
    f lo hi hW horder a d ha (fun x _ => hp x) hcover

end Plank.Convex.PlanarAffineCover
