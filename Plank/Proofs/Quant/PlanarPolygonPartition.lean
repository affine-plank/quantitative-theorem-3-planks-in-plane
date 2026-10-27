/- Finite boundary intersections construct the actual vertical polygon partition. -/
module

public import Plank.Proofs.Quant.PlanarPolygonSlabs
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Choose

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPolygonPartition

open Set MeasureTheory PlanarPolygonSlabs

/-- Sort the cuts lying between two endpoints and repeat the last endpoint
after the finite partition. No open piece contains another prescribed cut. -/
theorem exists_partition_no_internal_cuts {a b : ℝ} (hab : a ≤ b) (cuts : Finset ℝ) :
    ∃ n ≤ cuts.card+1, ∃ r : ℕ → ℝ, Monotone r ∧ r 0 = a ∧ r n = b ∧
      (∀ k, r k ∈ insert a (insert b cuts)) ∧
      ∀ k < n, ∀ x ∈ cuts, x ∉ Ioo (r k) (r (k+1)) := by
  classical
  let T := (insert a (insert b cuts)).filter (fun x => a ≤ x ∧ x ≤ b)
  have hTa : a ∈ T := by simp [T, hab]
  have hTb : b ∈ T := by simp [T, hab]
  have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨a, hTa⟩
  have hTbnds (x : ℝ) (hx : x ∈ T) : a ≤ x ∧ x ≤ b := (Finset.mem_filter.mp hx).2
  let n := T.card-1
  have hncard : n < T.card := Nat.sub_lt hTpos (by decide)
  let e : Fin T.card ↪o ℝ := T.orderEmbOfFin rfl
  let idx (k : ℕ) : Fin T.card := ⟨min k n, (Nat.min_le_right k n).trans_lt hncard⟩
  let r (k : ℕ) : ℝ := e (idx k)
  have hrT (k : ℕ) : r k ∈ T := T.orderEmbOfFin_mem rfl (idx k)
  have honto (x : ℝ) (hx : x ∈ T) : ∃ j, e j = x := by
    have hrange : Set.range e = (T : Set ℝ) := Finset.range_orderEmbOfFin T rfl
    have hmem : x ∈ Set.range e := by rw [hrange]; exact hx
    exact hmem
  have hmono : Monotone r := by
    intro k l hkl
    apply e.monotone
    change min k n ≤ min l n
    exact min_le_min_right n hkl
  have hr0 : r 0 = a := by
    obtain ⟨j, hj⟩ := honto a hTa
    apply le_antisymm
    · rw [← hj]
      apply e.monotone
      change min 0 n ≤ j.val
      simp
    · exact (hTbnds _ (hrT 0)).1
  have hrn : r n = b := by
    obtain ⟨j, hj⟩ := honto b hTb
    apply le_antisymm
    · exact (hTbnds _ (hrT n)).2
    · rw [← hj]
      apply e.monotone
      change j.val ≤ min n n
      have hjlt := j.isLt
      dsimp [n]
      omega
  have hn : n ≤ cuts.card+1 := by
    have hfilter := Finset.card_filter_le (insert a (insert b cuts)) (fun x => a ≤ x ∧ x ≤ b)
    have ha := Finset.card_insert_le a (insert b cuts)
    have hb := Finset.card_insert_le b cuts
    dsimp [n, T]
    omega
  refine ⟨n, hn, r, hmono, hr0, hrn, ?_, ?_⟩
  · intro k
    exact (Finset.mem_filter.mp (hrT k)).1
  · intro k hk x hx hbetween
    have hxT : x ∈ T := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx), ?_⟩
      exact ⟨(hTbnds _ (hrT k)).1.trans hbetween.1.le,
        hbetween.2.le.trans (hTbnds _ (hrT (k+1))).2⟩
    obtain ⟨j, hj⟩ := honto x hxT
    have hleft : idx k < j := e.lt_iff_lt.mp (by simpa only [r, hj] using hbetween.1)
    have hright : j < idx (k+1) := e.lt_iff_lt.mp (by simpa only [r, hj] using hbetween.2)
    have hl : min k n < j.val := hleft
    have hr : j.val < min (k+1) n := hright
    omega

/-- All vertical projections of intersections of nonparallel boundary lines.
The family includes lower and upper constraints and permits repeated slopes. -/
def crossingSet {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ls lc : ι → ℝ) (us uc : κ → ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.filter (fun pq : (ι ⊕ κ) × (ι ⊕ κ) =>
    Sum.elim ls us pq.1 ≠ Sum.elim ls us pq.2)).image (fun pq =>
      (Sum.elim lc uc pq.2-Sum.elim lc uc pq.1)/
        (Sum.elim ls us pq.1-Sum.elim ls us pq.2))

theorem crossing_mem {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ls lc : ι → ℝ) (us uc : κ → ℝ) (p q : ι ⊕ κ)
    (hne : Sum.elim ls us p ≠ Sum.elim ls us q) :
    (Sum.elim lc uc q-Sum.elim lc uc p)/(Sum.elim ls us p-Sum.elim ls us q) ∈
      crossingSet ls lc us uc := by
  classical
  exact Finset.mem_image.mpr ⟨(p, q), by simp [hne], rfl⟩

/-- Every finite half-plane intersection has an ordered vertical partition
with no boundary crossing inside a piece. The number of pieces is bounded
by the finite set of candidate intersections. -/
theorem exists_noncrossing_partition {ι κ : Type*} [Fintype ι] [Fintype κ]
    {a b : ℝ} (hab : a ≤ b) (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    ∃ n ≤ (crossingSet ls lc us uc).card+1, ∃ r : ℕ → ℝ,
      Monotone r ∧ r 0 = a ∧ r n = b ∧
      (∀ k, r k ∈ insert a (insert b (crossingSet ls lc us uc))) ∧
      ∀ k < n, NoCrossing (r k) (r (k+1)) ls lc us uc := by
  obtain ⟨n, hn, r, hmono, hzero, hlast, hmem, hno⟩ :=
    exists_partition_no_internal_cuts hab (crossingSet ls lc us uc)
  refine ⟨n, hn, r, hmono, hzero, hlast, hmem, ?_⟩
  intro k hk p q hpq
  exact hno k hk _ (crossing_mem ls lc us uc p q hpq)

/-- The geometric slab certificates needed by the actual area calculation
exist for every finite family of lower and upper lines. The construction
includes empty pieces, parallel lines, coincident crossings and degeneracies. -/
theorem exists_polygon_slab_certificates {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] {a b : ℝ} (hab : a ≤ b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    ∃ n ≤ (crossingSet ls lc us uc).card+1, ∃ r : ℕ → ℝ,
      Monotone r ∧ r 0 = a ∧ r n = b ∧
      (∀ k, r k ∈ insert a (insert b (crossingSet ls lc us uc))) ∧
      ∃ (i : ℕ → ι) (j : ℕ → κ), ∀ k < n,
        ActiveFacets (r k) (r (k+1)) ls lc us uc (i k) (j k) ∨
        (us (j k)*r k+uc (j k) ≤ ls (i k)*r k+lc (i k) ∧
          us (j k)*r (k+1)+uc (j k) ≤ ls (i k)*r (k+1)+lc (i k)) := by
  classical
  obtain ⟨n, hn, r, hmono, hzero, hlast, hmem, hno⟩ :=
    exists_noncrossing_partition hab ls lc us uc
  have hex (k : ℕ) : ∃ (i : ι) (j : κ), k < n →
      ActiveFacets (r k) (r (k+1)) ls lc us uc i j ∨
        (us j*r k+uc j ≤ ls i*r k+lc i ∧ us j*r (k+1)+uc j ≤ ls i*r (k+1)+lc i) := by
    by_cases hk : k < n
    · obtain ⟨i, j, hij⟩ := exists_active_or_empty (hmono (Nat.le_succ k))
        ls lc us uc (hno k hk)
      exact ⟨i, j, fun _ => hij⟩
    · exact ⟨Classical.arbitrary ι, Classical.arbitrary κ, fun h => (hk h).elim⟩
  choose i j hij using hex
  exact ⟨n, hn, r, hmono, hzero, hlast, hmem, i, j, hij⟩

/-- An unconditional finite trapezoid formula for the actual area of any
finite lower/upper half-plane intersection in a bounded horizontal interval.
The partition and contributing facets are constructed from the input lines.
The area uses the same `Fin 2 → ℝ` coordinates as the quantitative target. -/
theorem exists_actual_area_decomposition {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] {a b : ℝ} (hab : a ≤ b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    ∃ n ≤ (crossingSet ls lc us uc).card+1, ∃ (r : ℕ → ℝ) (i : ℕ → ι) (j : ℕ → κ),
      Monotone r ∧ r 0 = a ∧ r n = b ∧
      (∀ k, r k ∈ insert a (insert b (crossingSet ls lc us uc))) ∧
      (volume (coordinateSlab a b ls lc us uc)).toReal =
        ∑ k ∈ Finset.range n, max 0
          ((r (k+1)-r k)*((us (j k)-ls (i k))*(r k+r (k+1))+2*(uc (j k)-lc (i k)))/2) := by
  classical
  obtain ⟨n, hn, r, hmono, hzero, hlast, hmem, i, j, hij⟩ :=
    exists_polygon_slab_certificates hab ls lc us uc
  let val (k : ℕ) :=
    (r (k+1)-r k)*((us (j k)-ls (i k))*(r k+r (k+1))+2*(uc (j k)-lc (i k)))/2
  have hpieces (k : ℕ) (hk : k ∈ Finset.range n) :
      volume (slab (r k) (r (k+1)) ls lc us uc) = ENNReal.ofReal (max 0 (val k)) := by
    rcases hij k (Finset.mem_range.mp hk) with hactive | hempty
    · have hnonneg := trapezoid_nonneg hactive.ordered hactive.left_height hactive.right_height
      rw [max_eq_right hnonneg]
      exact measure_slab_of_active hactive.ordered ls lc us uc (i k) (j k)
        hactive.lower hactive.upper hactive.left_height hactive.right_height
    · have hheight : (us (j k)-ls (i k))*(r k+r (k+1))+2*(uc (j k)-lc (i k)) ≤ 0 := by
        nlinarith only [hempty.1, hempty.2]
      have hnonpos : val k ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hmono (Nat.le_succ k))) hheight)
        (by norm_num)
      rw [max_eq_left hnonpos, ENNReal.ofReal_zero]
      exact measure_slab_zero ls lc us uc (i k) (j k) hempty.1 hempty.2
  refine ⟨n, hn, r, i, j, hmono, hzero, hlast, hmem, ?_⟩
  calc
    (volume (coordinateSlab a b ls lc us uc)).toReal =
        (volume (slab a b ls lc us uc)).toReal := congrArg ENNReal.toReal
      (measure_coordinateSlab a b ls lc us uc)
    _ = (∑ k ∈ Finset.range n, volume (slab (r k) (r (k+1)) ls lc us uc)).toReal :=
      congrArg ENNReal.toReal (by
        simpa only [hzero, hlast] using measure_slab_sum r hmono ls lc us uc n)
    _ = ∑ k ∈ Finset.range n, max 0 (val k) := by
      rw [ENNReal.toReal_sum (fun k hk => by rw [hpieces k hk]; exact ENNReal.ofReal_ne_top)]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hpieces k hk, ENNReal.toReal_ofReal (le_max_left _ _)]

end Plank.PlanarPolygonPartition
