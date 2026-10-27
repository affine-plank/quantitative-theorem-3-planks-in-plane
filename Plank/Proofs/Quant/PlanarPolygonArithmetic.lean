/- Finite arithmetic certificates for the area of a boxed polygon. -/
module

public import Plank.Proofs.Quant.PlanarPolygonHalfplanes

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPolygonArithmetic

open Set MeasureTheory PlanarQuantitative PlanarPolygonSlabs
open PlanarPolygonPartition PlanarPolygonHalfplanes
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def trapezoids (ls lc : ι → ℝ) (us uc : κ → ℝ)
    (n : ℕ) (r : ℕ → ℝ) (i : ℕ → ι) (j : ℕ → κ) : ℝ :=
  ∑ k ∈ Finset.range n, max 0
    ((r (k+1)-r k)*((us (j k)-ls (i k))*(r k+r (k+1))+2*(uc (j k)-lc (i k)))/2)

/-- Every condition examines a bounded finite prefix. The endpoints come
from a finite set of explicit line intersections, and the pieces use only
endpoint comparisons. No measure or geometric-set predicate occurs. -/
def SlabTest (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ) (z : ℝ) : Prop :=
  ∃ n ≤ (crossingSet ls lc us uc).card+1,
    ∃ (r : ℕ → ℝ) (i : ℕ → ι) (j : ℕ → κ),
      (∀ k < n, r k ≤ r (k+1)) ∧ r 0 = a ∧ r n = b ∧
      (∀ k ≤ n, r k ∈ insert a (insert b (crossingSet ls lc us uc))) ∧
      (∀ k < n, ActiveFacets (r k) (r (k+1)) ls lc us uc (i k) (j k) ∨
        (us (j k)*r k+uc (j k) ≤ ls (i k)*r k+lc (i k) ∧
          us (j k)*r (k+1)+uc (j k) ≤ ls (i k)*r (k+1)+lc (i k))) ∧
      z = trapezoids ls lc us uc n r i j

theorem area_of_pieces (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ)
    (n : ℕ) (r : ℕ → ℝ) (i : ℕ → ι) (j : ℕ → κ)
    (hnext : ∀ k < n, r k ≤ r (k+1)) (hzero : r 0 = a) (hlast : r n = b)
    (hij : ∀ k < n, ActiveFacets (r k) (r (k+1)) ls lc us uc (i k) (j k) ∨
      (us (j k)*r k+uc (j k) ≤ ls (i k)*r k+lc (i k) ∧
        us (j k)*r (k+1)+uc (j k) ≤ ls (i k)*r (k+1)+lc (i k))) :
    (volume (closedSlab a b ls lc us uc)).toReal = trapezoids ls lc us uc n r i j := by
  let q : ℕ → ℝ := fun k => r (min k n)
  have hq (k : ℕ) (hk : k ≤ n) : q k = r k := by simp [q,Nat.min_eq_left hk]
  have hmono : Monotone q := by
    apply monotone_nat_of_le_succ
    intro k
    by_cases hk : k < n
    · rw [hq k hk.le,hq (k+1) (Nat.succ_le_of_lt hk)]
      exact hnext k hk
    · simp only [q,Nat.min_eq_right (Nat.le_of_not_gt hk),
        Nat.min_eq_right ((Nat.le_of_not_gt hk).trans (Nat.le_succ k)),le_refl]
  let val (k : ℕ) :=
    (r (k+1)-r k)*((us (j k)-ls (i k))*(r k+r (k+1))+2*(uc (j k)-lc (i k)))/2
  have hpieces (k : ℕ) (hk : k ∈ Finset.range n) :
      volume (slab (q k) (q (k+1)) ls lc us uc) = ENNReal.ofReal (max 0 (val k)) := by
    have hkn := Finset.mem_range.mp hk
    rw [hq k hkn.le,hq (k+1) (Nat.succ_le_of_lt hkn)]
    rcases hij k hkn with ha | he
    · have hn := trapezoid_nonneg ha.ordered ha.left_height ha.right_height
      rw [max_eq_right hn]
      exact measure_slab_of_active ha.ordered ls lc us uc (i k) (j k)
        ha.lower ha.upper ha.left_height ha.right_height
    · have hh : (us (j k)-ls (i k))*(r k+r (k+1))+2*(uc (j k)-lc (i k)) ≤ 0 := by
        nlinarith only [he.1,he.2]
      have hn : val k ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hnext k hkn)) hh) (by norm_num)
      rw [max_eq_left hn,ENNReal.ofReal_zero]
      exact measure_slab_zero ls lc us uc (i k) (j k) he.1 he.2
  rw [measure_closedSlab,measure_coordinateSlab]
  have hs := measure_slab_sum q hmono ls lc us uc n
  rw [hq 0 (Nat.zero_le n),hq n le_rfl,hzero,hlast] at hs
  rw [hs,ENNReal.toReal_sum (fun k hk => by rw [hpieces k hk]; exact ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun k hk => by rw [hpieces k hk,ENNReal.toReal_ofReal (le_max_left _ _)]

/-- The arithmetic certificate is sound and complete for actual area. -/
theorem slabTest_iff [Nonempty ι] [Nonempty κ] {a b : ℝ} (hab : a ≤ b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) (z : ℝ) :
    SlabTest a b ls lc us uc z ↔ (volume (closedSlab a b ls lc us uc)).toReal = z := by
  constructor
  · rintro ⟨n,_,r,i,j,hn,h0,h1,_,hp,hz⟩
    rw [hz]
    exact area_of_pieces a b ls lc us uc n r i j hn h0 h1 hp
  · intro hz
    obtain ⟨n,hn,r,hm,h0,h1,hr,i,j,hp⟩ := exists_polygon_slab_certificates hab ls lc us uc
    refine ⟨n,hn,r,i,j,fun k _ => hm (Nat.le_succ k),h0,h1,fun k _ => hr k,hp,?_⟩
    exact hz.symm.trans (area_of_pieces a b ls lc us uc n r i j
      (fun k _ => hm (Nat.le_succ k)) h0 h1 hp)

abbrev LowerKey (A B : ι → ℝ) := Option {i // B i = 0 ∧ A i < 0}
abbrev UpperKey (A B : ι → ℝ) := Option {i // B i = 0 ∧ 0 < A i}

def lowerValues (a : ℝ) (A B C : ι → ℝ) : LowerKey A B → ℝ :=
  withBound (fun i => C i/A i) a
def upperValues (b : ℝ) (A B C : ι → ℝ) : UpperKey A B → ℝ :=
  withBound (fun i => C i/A i) b

def Consistent (A B C : ι → ℝ) : Prop := ∀ i, A i = 0 → B i = 0 → 0 ≤ C i

def VerticalTest (a b : ℝ) (A B C : ι → ℝ) (l : LowerKey A B) (u : UpperKey A B) : Prop :=
  Consistent A B C ∧
    (∀ k, lowerValues a A B C k ≤ lowerValues a A B C l) ∧
    (∀ k, upperValues b A B C u ≤ upperValues b A B C k)

omit [Fintype ι] in
theorem vertical_iff {a b : ℝ} {A B C : ι → ℝ} {l : LowerKey A B} {u : UpperKey A B}
    (hv : VerticalTest a b A B C l u) (x : ℝ) :
    x ∈ Icc (lowerValues a A B C l) (upperValues b A B C u) ↔
      x ∈ Icc a b ∧ ∀ i, B i = 0 → A i*x ≤ C i := by
  constructor
  · intro hx
    have hl (k) := (hv.2.1 k).trans hx.1
    have hu (k) := hx.2.trans (hv.2.2 k)
    refine ⟨⟨hl none,hu none⟩,fun i hBi => ?_⟩
    rcases lt_trichotomy (A i) 0 with hi | hi | hi
    · have hh := (div_le_iff_of_neg hi).mp (hl (some ⟨i,hBi,hi⟩))
      simpa only [mul_comm] using hh
    · simpa only [hi,zero_mul] using hv.1 i hi hBi
    · have hh := (le_div_iff₀ hi).mp (hu (some ⟨i,hBi,hi⟩))
      simpa only [mul_comm] using hh
  · rintro ⟨hx,h⟩
    constructor
    · cases l with
      | none => exact hx.1
      | some i =>
        apply (div_le_iff_of_neg i.property.2).mpr
        simpa only [mul_comm] using h i i.property.1
    · cases u with
      | none => exact hx.2
      | some i =>
        apply (le_div_iff₀ i.property.2).mpr
        simpa only [mul_comm] using h i i.property.1

/-- A finite arithmetic area test for arbitrary boxed half-plane systems.
Zero normals, empty boxes, vertical edges and coincident vertices are allowed.
The only witnesses outside finite row indices are bounded prefixes whose
entries are chosen from the finite explicit crossing set. -/
def BoxTest (a b c d : ℝ) (A B C : ι → ℝ) (z : ℝ) : Prop :=
  (¬Consistent A B C ∧ z = 0) ∨
    ∃ (l : LowerKey A B) (u : UpperKey A B), VerticalTest a b A B C l u ∧
      ((upperValues b A B C u < lowerValues a A B C l ∧ z = 0) ∨
        (lowerValues a A B C l ≤ upperValues b A B C u ∧
          SlabTest (lowerValues a A B C l) (upperValues b A B C u)
            (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
            (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d) z))

omit [Fintype ι] in
theorem empty_of_inconsistent {a b c d : ℝ} {A B C : ι → ℝ}
    (hz : ¬Consistent A B C) : boxedRegion a b c d A B C = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply hz
  intro i hA hB
  simpa only [hA,hB,zero_mul,add_zero] using hx.2.2 i

/-- This is an iff for the area of the actual polygon, not a certificate
that assumes an area formula. Both directions are proved from the facets. -/
theorem boxTest_iff (a b c d : ℝ) (A B C : ι → ℝ) (z : ℝ) :
    BoxTest a b c d A B C z ↔ (volume (boxedRegion a b c d A B C)).toReal = z := by
  classical
  have hempty {l u : ℝ} (hlu : u < l) :
      closedSlab l u (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
        (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_le_of_gt hlu) (hx.1.1.trans hx.1.2)
  constructor
  · rintro (⟨hz,rfl⟩ | ⟨l,u,hv,hh⟩)
    · simp only [empty_of_inconsistent hz,measure_empty,ENNReal.toReal_zero]
    · rw [boxedRegion_eq_closedSlab_of_vertical_interval a b c d _ _ A B C (vertical_iff hv)]
      rcases hh with ⟨hh,rfl⟩ | ⟨hh,ht⟩
      · simp only [hempty hh,measure_empty,ENNReal.toReal_zero]
      · exact (slabTest_iff hh _ _ _ _ z).mp ht
  · intro hz
    by_cases hc : Consistent A B C
    · obtain ⟨l,_,hl⟩ := Finset.exists_max_image Finset.univ (lowerValues a A B C) Finset.univ_nonempty
      obtain ⟨u,_,hu⟩ := Finset.exists_min_image Finset.univ (upperValues b A B C) Finset.univ_nonempty
      have hv : VerticalTest a b A B C l u := ⟨hc,fun k => hl k (Finset.mem_univ k),
        fun k => hu k (Finset.mem_univ k)⟩
      refine Or.inr ⟨l,u,hv,?_⟩
      rw [boxedRegion_eq_closedSlab_of_vertical_interval a b c d _ _ A B C (vertical_iff hv)] at hz
      by_cases hle : lowerValues a A B C l ≤ upperValues b A B C u
      · exact Or.inr ⟨hle,(slabTest_iff hle _ _ _ _ z).mpr hz⟩
      · have hlt := lt_of_not_ge hle
        exact Or.inl ⟨hlt,by simpa only [hempty hlt,measure_empty,ENNReal.toReal_zero] using hz.symm⟩
    · exact Or.inl ⟨hc,by simpa only [empty_of_inconsistent hc,measure_empty,ENNReal.toReal_zero] using hz.symm⟩

end Plank.PlanarPolygonArithmetic

/-- info: 'Plank.PlanarPolygonArithmetic.boxTest_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarPolygonArithmetic.boxTest_iff
