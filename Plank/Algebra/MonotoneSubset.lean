/- A finite side assignment from nonnegative additive interactions. -/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Defs

@[expose] public section
set_option autoImplicit false

open scoped BigOperators

namespace Plank.MonotoneSubset

/-- A largest strictly feasible subset places selected coordinates above their
upper thresholds and all remaining coordinates at or below their lower ones.
Only additive order and nonnegative interactions are needed. -/
theorem exists_side_assignment {ι R : Type*} [Fintype ι]
    [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    (b : ι → R) (q : ι → ι → R) (hq : ∀ i j, 0 ≤ q i j)
    (lo hi : ι → R) (hdiag : ∀ i, hi i - lo i ≤ q i i) :
    ∃ S : Finset ι,
      (∀ i ∈ S, hi i < b i + ∑ j ∈ S, q j i) ∧
      (∀ i ∉ S, b i + ∑ j ∈ S, q j i ≤ lo i) := by
  classical
  let V (S : Finset ι) (i : ι) := b i + ∑ j ∈ S, q j i
  let feasible (S : Finset ι) := ∀ i ∈ S, hi i < V S i
  let candidates := Finset.univ.filter feasible
  have hempty : (∅ : Finset ι) ∈ candidates := by simp [candidates, feasible]
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  have hgood : feasible S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hgood, ?_⟩
  intro i hiS
  by_contra hbad
  have hlow : lo i < V S i := lt_of_not_ge hbad
  have hincrement (j : ι) : V (insert i S) j = V S j + q i j := by
    dsimp only [V]
    rw [Finset.sum_insert hiS, ← add_assoc]
    exact add_right_comm _ _ _
  have hinsert : feasible (insert i S) := by
    intro j hj
    rw [hincrement]
    rcases Finset.mem_insert.mp hj with rfl | hj
    · calc
        hi j = (hi j - lo j) + lo j := (sub_add_cancel _ _).symm
        _ ≤ q j j + lo j := add_le_add_left (hdiag j) _
        _ < q j j + V S j := add_lt_add_right hlow _
        _ = V S j + q j j := add_comm _ _
    · exact (hgood j hj).trans_le (le_add_of_nonneg_right (hq i j))
  have hmem : insert i S ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinsert⟩
  exact (not_lt_of_ge (hmax (insert i S) hmem))
    (Finset.card_lt_card (Finset.ssubset_insert hiS))

end Plank.MonotoneSubset
