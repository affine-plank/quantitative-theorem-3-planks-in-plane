/- A mixed-sign affine relation removes one cut from an empty strict cell.
This is the geometric entry point for the six planar escape-pattern cases. -/
module
public import Plank.Convex.ConvexCellSeparation
public import Plank.Convex.StrictCellDualCertificate
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.MixedPlaneCapReduction
open scoped BigOperators
open StrictCellDualCertificate

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

private theorem remove_cut_nonneg (S : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (r : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hrp : ∃ i, 0 < r i) (hrn : ∃ i, r i < 0)
    (hrel : ∀ v ∈ S, ∑ i, r i * f i v = d)
    (hcert : HasEmptyCertificate S f) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ 0 < ∑ i, b i ∧
      (∃ i, 0 < r i ∧ b i = 0) ∧ ∀ v ∈ S, ∑ i, b i * f i v ≤ 0 := by
  classical
  obtain ⟨a, ha, hasum, hrows⟩ := hcert
  let J := Finset.univ.filter (fun i => 0 < r i)
  have hJ : J.Nonempty := by
    obtain ⟨i, hi⟩ := hrp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hiJ, hmin⟩ := Finset.exists_min_image J (fun j => a j / r j) hJ
  have hri : 0 < r i := (Finset.mem_filter.mp hiJ).2
  let t := a i / r i
  let b := fun j => a j - t * r j
  have ht : 0 ≤ t := div_nonneg (ha i) hri.le
  have hb (j : ι) : 0 ≤ b j := by
    by_cases hj : 0 < r j
    · have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      have hle : t * r j ≤ a j := (le_div_iff₀ hj).mp (hmin j hjJ)
      exact sub_nonneg.mpr hle
    · exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos ht
        (le_of_not_gt hj)).trans (ha j))
  have hbi : b i = 0 := by
    dsimp [b, t]
    rw [div_mul_cancel₀ _ hri.ne', sub_self]
  have hbsum : 0 < ∑ j, b j := by
    by_cases ht0 : t = 0
    · simp [b, ht0, hasum]
    · obtain ⟨j, hj⟩ := hrn
      have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hbj : 0 < b j := by
        dsimp [b]
        have hprod := mul_neg_of_pos_of_neg htpos hj
        linarith [ha j]
      exact Finset.sum_pos' (fun j _ => hb j) ⟨j, Finset.mem_univ j, hbj⟩
  refine ⟨b, hb, hbsum, ⟨i, hri, hbi⟩, ?_⟩
  intro v hv
  have heq : (∑ j, b j * f j v) = (∑ j, a j * f j v) - t * d := by
    rw [← hrel v hv, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [b]
    ring
  rw [heq]
  exact sub_nonpos.mpr ((hrows v hv).trans (mul_nonneg ht hd))

/-- Perturb a separating certificate along a mixed-sign affine relation.
One coefficient becomes zero while every coefficient stays nonnegative;
the certificate remains nonzero. No sign restriction on the offset is needed. -/
theorem exists_zero_multiplier (S : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (r : ι → ℝ) (d : ℝ)
    (hrp : ∃ i, 0 < r i) (hrn : ∃ i, r i < 0)
    (hrel : ∀ v ∈ S, ∑ i, r i * f i v = d)
    (hcert : HasEmptyCertificate S f) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ 0 < ∑ i, b i ∧
      (∃ i, b i = 0) ∧ ∀ v ∈ S, ∑ i, b i * f i v ≤ 0 := by
  by_cases hd : 0 ≤ d
  · obtain ⟨b, hb, hs, ⟨i, -, hi⟩, hr⟩ := remove_cut_nonneg S f r d hd hrp hrn hrel hcert
    exact ⟨b, hb, hs, ⟨i, hi⟩, hr⟩
  · have hrp' : ∃ i, 0 < -r i := by
      obtain ⟨i, hi⟩ := hrn
      exact ⟨i, neg_pos.mpr hi⟩
    have hrn' : ∃ i, -r i < 0 := by
      obtain ⟨i, hi⟩ := hrp
      exact ⟨i, neg_neg_of_pos hi⟩
    have hrel' (v) (hv : v ∈ S) : ∑ i, -r i * f i v = -d := by
      simpa only [neg_mul, Finset.sum_neg_distrib] using congrArg Neg.neg (hrel v hv)
    obtain ⟨b, hb, hs, ⟨i, -, hi⟩, hr⟩ :=
      remove_cut_nonneg S f (fun i => -r i) (-d) (by linarith) hrp' hrn' hrel' hcert
    exact ⟨b, hb, hs, ⟨i, hi⟩, hr⟩

private theorem empty_without_cut (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (b : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (hs : 0 < ∑ j, b j)
    (hr : ∀ x ∈ K, ∑ j, b j * f j x ≤ 0) (i : ι) (hi : b i = 0) :
    ¬ ∃ x ∈ K, ∀ j, j ≠ i → 0 < f j x := by
  classical
  rintro ⟨x, hx, hf⟩
  obtain ⟨j, -, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hb j)).mp hs
  have hji : j ≠ i := by intro h; subst j; rw [hi] at hj; exact lt_irrefl _ hj
  have hpos : 0 < ∑ k, b k * f k x := by
    apply Finset.sum_pos'
    · intro k _
      by_cases hk : k = i
      · simp [hk, hi]
      · exact mul_nonneg (hb k) (hf k hk).le
    · exact ⟨j, Finset.mem_univ j, mul_pos hj (hf j hji)⟩
  exact not_le_of_gt hpos (hr x hx)

/-- A mixed-sign affine relation removes a cut on any convex set and for
any finite cut family. No finite hull, compactness or continuity is needed. -/
theorem exists_redundant_cut_convex [Nonempty ι] (K : Set E) (hK : Convex ℝ K)
    (f : ι → E →ᵃ[ℝ] ℝ) (r : ι → ℝ) (d : ℝ)
    (hrp : ∃ i, 0 < r i) (hrn : ∃ i, r i < 0)
    (hrel : ∀ x ∈ K, ∑ i, r i * f i x = d)
    (he : ¬ ∃ x ∈ K, ∀ i, 0 < f i x) :
    ∃ i, ¬ ∃ x ∈ K, ∀ j, j ≠ i → 0 < f j x := by
  obtain ⟨b, hb, hs, ⟨i, hi⟩, hr⟩ := exists_zero_multiplier K f r d hrp hrn hrel
    (ConvexCellSeparation.exists_weights K hK f he)
  exact ⟨i, empty_without_cut K f b hb hs hr i hi⟩

/-- With a nonnegative offset, the removed cut can have positive relation
coefficient. The sign information is retained for any finite cut family. -/
theorem exists_redundant_positive_cut_convex [Nonempty ι] (K : Set E) (hK : Convex ℝ K)
    (f : ι → E →ᵃ[ℝ] ℝ) (r : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hrp : ∃ i, 0 < r i) (hrn : ∃ i, r i < 0)
    (hrel : ∀ x ∈ K, ∑ i, r i * f i x = d)
    (he : ¬ ∃ x ∈ K, ∀ i, 0 < f i x) :
    ∃ i, 0 < r i ∧ ¬ ∃ x ∈ K, ∀ j, j ≠ i → 0 < f j x := by
  obtain ⟨b, hb, hs, ⟨i, hri, hi⟩, hr⟩ := remove_cut_nonneg K f r d hd hrp hrn hrel
    (ConvexCellSeparation.exists_weights K hK f he)
  exact ⟨i, hri, empty_without_cut K f b hb hs hr i hi⟩

/-- For a nonnegative relation offset, a cut with positive relation
coefficient can be removed. This retains the sign information lost by the
unrestricted three-cut alternative. -/
theorem exists_redundant_positive_cut [Nonempty ι] (S : Set E) (hS : S.Finite)
    (f : ι → E →ᵃ[ℝ] ℝ) (r : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hrp : ∃ i, 0 < r i) (hrn : ∃ i, r i < 0)
    (hrel : ∀ v ∈ S, ∑ i, r i * f i v = d)
    (hempty : ¬ ∃ x ∈ convexHull ℝ S, ∀ i, 0 < f i x) :
    ∃ i, 0 < r i ∧ ¬ ∃ x ∈ convexHull ℝ S, ∀ j, j ≠ i → 0 < f j x := by
  classical
  obtain ⟨a, ha, hs, hr⟩ := ConvexCellSeparation.exists_weights
    (convexHull ℝ S) (convex_convexHull ℝ S) f hempty
  have hc : HasEmptyCertificate S f :=
    ⟨a, ha, hs, fun x hx => hr x (subset_convexHull ℝ S hx)⟩
  obtain ⟨b, hb, hsum, ⟨i, hri, hi⟩, hrows⟩ :=
    remove_cut_nonneg S f r d hd hrp hrn hrel hc
  refine ⟨i, hri, ?_⟩
  apply empty_without_cut (convexHull ℝ S) f b hb hsum ?_ i hi
  intro x hx
  simpa using weighted_le_on_hull S f 0 b 0 (by simpa using hrows) x hx

/-- If the middle coefficient is negative, some coefficient is positive,
and the offset is nonnegative, one adjacent pair cell is empty. No topology or finite generation of K is needed. -/
theorem empty_adjacent_pair_of_nonneg_relation (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (r : Fin 3 → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hr1 : r 1 < 0) (hrp : ∃ i, 0 < r i)
    (hrel : ∀ v ∈ K, ∑ i, r i * f i v = d)
    (hempty : ¬ ∃ x ∈ K, ∀ i, 0 < f i x) :
    (¬ ∃ x ∈ K, 0 < f 0 x ∧ 0 < f 1 x) ∨
    (¬ ∃ x ∈ K, 0 < f 1 x ∧ 0 < f 2 x) := by
  obtain ⟨i, hri, hi⟩ := exists_redundant_positive_cut_convex K hK f r d hd hrp ⟨1, hr1⟩
    hrel hempty
  fin_cases i
  · right
    rintro ⟨x, hx, h1, h2⟩
    exact hi ⟨x, hx, by intro j hj; fin_cases j; exact (hj rfl).elim; exact h1; exact h2⟩
  · exact (not_lt_of_ge hri.le hr1).elim
  · left
    rintro ⟨x, hx, h0, h1⟩
    exact hi ⟨x, hx, by intro j hj; fin_cases j; exact h0; exact h1; exact (hj rfl).elim⟩

/-- If a finite hull misses the strict cell and the cuts have a mixed-sign
affine relation on its generators, it already misses a cell with one cut removed. -/
theorem exists_redundant_cut [Nonempty ι] (S : Set E) (hS : S.Finite)
    (f : ι → E →ᵃ[ℝ] ℝ) (r : ι → ℝ) (d : ℝ)
    (hrp : ∃ i, 0 < r i) (hrn : ∃ i, r i < 0)
    (hrel : ∀ v ∈ S, ∑ i, r i * f i v = d)
    (hempty : ¬ ∃ x ∈ convexHull ℝ S, ∀ i, 0 < f i x) :
    ∃ i, ¬ ∃ x ∈ convexHull ℝ S, ∀ j, j ≠ i → 0 < f j x := by
  classical
  obtain ⟨a, ha, hs, hr⟩ := ConvexCellSeparation.exists_weights
    (convexHull ℝ S) (convex_convexHull ℝ S) f hempty
  have hc : HasEmptyCertificate S f :=
    ⟨a, ha, hs, fun x hx => hr x (subset_convexHull ℝ S hx)⟩
  obtain ⟨b, hb, hsum, ⟨i, hi⟩, hrows⟩ :=
    exists_zero_multiplier S f r d hrp hrn hrel hc
  refine ⟨i, ?_⟩
  apply empty_without_cut (convexHull ℝ S) f b hb hsum ?_ i hi
  intro x hx
  simpa using weighted_le_on_hull S f 0 b 0 (by simpa using hrows) x hx

/-- Three mixed cuts on a finite planar hull reduce to an empty pair.
The relation, rather than an ambient-dimension hypothesis, is explicit. -/
theorem empty_pair_of_empty_triple (S : Set E) (hS : S.Finite)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (r : Fin 3 → ℝ) (d : ℝ)
    (hrp : ∃ i, 0 < r i) (hrn : ∃ i, r i < 0)
    (hrel : ∀ v ∈ S, ∑ i, r i * f i v = d)
    (hempty : ¬ ∃ x ∈ convexHull ℝ S, ∀ i, 0 < f i x) :
    (¬ ∃ x ∈ convexHull ℝ S, 0 < f 0 x ∧ 0 < f 1 x) ∨
    (¬ ∃ x ∈ convexHull ℝ S, 0 < f 1 x ∧ 0 < f 2 x) ∨
    (¬ ∃ x ∈ convexHull ℝ S, 0 < f 2 x ∧ 0 < f 0 x) := by
  obtain ⟨i, hi⟩ := exists_redundant_cut S hS f r d hrp hrn hrel hempty
  fin_cases i
  · right; left; simpa [Fin.forall_fin_succ, and_comm] using hi
  · right; right; simpa [Fin.forall_fin_succ, and_comm] using hi
  · left; simpa [Fin.forall_fin_succ] using hi

/-- The three-cut result holds on every convex set by direct cut removal.
No compactness or closure is needed. -/
theorem empty_pair_of_empty_triple_convex (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (r : Fin 3 → ℝ) (d : ℝ)
    (hrp : ∃ i, 0 < r i) (hrn : ∃ i, r i < 0)
    (hrel : ∀ v ∈ K, ∑ i, r i * f i v = d)
    (hempty : ¬ ∃ x ∈ K, ∀ i, 0 < f i x) :
    (¬ ∃ x ∈ K, 0 < f 0 x ∧ 0 < f 1 x) ∨
    (¬ ∃ x ∈ K, 0 < f 1 x ∧ 0 < f 2 x) ∨
    (¬ ∃ x ∈ K, 0 < f 2 x ∧ 0 < f 0 x) := by
  obtain ⟨i, hi⟩ := exists_redundant_cut_convex K hK f r d hrp hrn hrel hempty
  fin_cases i
  · right; left; simpa [Fin.forall_fin_succ, and_comm] using hi
  · right; right; simpa [Fin.forall_fin_succ, and_comm] using hi
  · left; simpa [Fin.forall_fin_succ] using hi

end Plank.Convex.MixedPlaneCapReduction

/-- info: 'Plank.Convex.MixedPlaneCapReduction.exists_zero_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.MixedPlaneCapReduction.exists_zero_multiplier

/-- info: 'Plank.Convex.MixedPlaneCapReduction.exists_redundant_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.MixedPlaneCapReduction.exists_redundant_cut

/-- info: 'Plank.Convex.MixedPlaneCapReduction.empty_pair_of_empty_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.MixedPlaneCapReduction.empty_pair_of_empty_triple

/-- info: 'Plank.Convex.MixedPlaneCapReduction.empty_pair_of_empty_triple_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.MixedPlaneCapReduction.empty_pair_of_empty_triple_convex

/-- info: 'Plank.Convex.MixedPlaneCapReduction.exists_redundant_positive_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.MixedPlaneCapReduction.exists_redundant_positive_cut

/-- info: 'Plank.Convex.MixedPlaneCapReduction.empty_adjacent_pair_of_nonneg_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.MixedPlaneCapReduction.empty_adjacent_pair_of_nonneg_relation

/-- info: 'Plank.Convex.MixedPlaneCapReduction.exists_redundant_cut_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.MixedPlaneCapReduction.exists_redundant_cut_convex

/-- info: 'Plank.Convex.MixedPlaneCapReduction.exists_redundant_positive_cut_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.MixedPlaneCapReduction.exists_redundant_positive_cut_convex
