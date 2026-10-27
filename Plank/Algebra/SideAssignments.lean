/- A common finite side-assignment condition and its closure under blocks. -/
module

public import Plank.Algebra.SymmetricSubset
public import Plank.Algebra.MonotoneSubset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Sum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SideAssignments

variable {ι κ : Type*}

/-- Every translated coordinate vector can be assigned to exterior sides.
Rows index forms, columns index steps, and the diagonal is the window width. -/
def Admits (q : ι → ι → ℝ) : Prop :=
  ∀b : ι → ℝ,∃s : Finset ι,
    (∀i∈s,q i i≤b i+s.sum (q i)) ∧
    (∀i∉s,b i+s.sum (q i)≤0)

/-- The condition persists after arbitrary nonnegative scaling of the steps. -/
def Stable (q : ι → ι → ℝ) : Prop :=
  ∀ρ : ι → ℝ,(∀i,0≤ρ i) → Admits (fun i j => ρ j*q i j)

theorem of_weighted_symmetry [Fintype ι] (q : ι → ι → ℝ) (a : ι → ℝ)
    (ha : ∀i,0<a i) (hsym : ∀i j,a i*q i j=a j*q j i) : Admits q := by
  intro b
  obtain ⟨s,hh,hl⟩ := SymmetricSubset.exists_side_assignment a b (fun _ => 0)
    (fun i => q i i) q ha (by intro i; simp) hsym
  exact ⟨s,hh,hl⟩

theorem of_nonnegative [Fintype ι] (q : ι → ι → ℝ) (hq : ∀i j,0≤q i j) : Admits q := by
  intro b
  obtain ⟨s,hh,hl⟩ := MonotoneSubset.exists_side_assignment b (fun j i => q i j)
    (fun i j => hq j i) (fun _ => 0) (fun i => q i i) (by intro i; simp)
  exact ⟨s,fun i hi => (hh i hi).le,hl⟩

/-- Solve the second block first. First-block steps leave its rows unchanged,
while interactions in the opposite direction are unrestricted. -/
theorem sum (q : (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (hleft : Admits (fun i j => q (.inl i) (.inl j)))
    (hright : Admits (fun i j => q (.inr i) (.inr j)))
    (hzero : ∀i j,q (.inr j) (.inl i)=0) : Admits q := by
  intro b
  classical
  obtain ⟨t,hth,htl⟩ := hright (fun j => b (.inr j))
  obtain ⟨s,hsh,hsl⟩ := hleft (fun i => b (.inl i)+t.sum (fun j => q (.inl i) (.inr j)))
  refine ⟨s.disjSum t,?_,?_⟩
  · intro k hk
    cases k with
    | inl i =>
      have h := hsh i (Finset.inl_mem_disjSum.mp hk)
      simpa only [Finset.sum_disjSum,add_assoc,add_comm,add_left_comm] using h
    | inr j =>
      have h := hth j (Finset.inr_mem_disjSum.mp hk)
      simpa only [Finset.sum_disjSum,hzero,Finset.sum_const_zero,zero_add] using h
  · intro k hk
    cases k with
    | inl i =>
      have h := hsl i (fun hi => hk (Finset.inl_mem_disjSum.mpr hi))
      simpa only [Finset.sum_disjSum,add_assoc,add_comm,add_left_comm] using h
    | inr j =>
      have h := htl j (fun hj => hk (Finset.inr_mem_disjSum.mpr hj))
      simpa only [Finset.sum_disjSum,hzero,Finset.sum_const_zero,zero_add] using h

/-- Coordinates whose columns vanish may be assigned after solving the
remaining coordinates. This includes zero-width steps without a limit argument. -/
theorem of_zero_columns [Fintype ι] (q : ι → ι → ℝ) (t : Finset ι)
    (hz : ∀j,j∉t → ∀i,q i j=0)
    (ht : Admits (fun (i j : t) => q i j)) : Admits q := by
  intro b
  classical
  obtain ⟨s,hh,hl⟩ := ht (fun i => b i)
  let U : Finset ι := s.map ⟨Subtype.val,Subtype.val_injective⟩
  let Z : Finset ι := Finset.univ.filter (fun i => i∉t ∧ 0≤b i+U.sum (q i))
  have hUT : ∀i∈U,i∈t := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  have hmemU (i : t) : (i : ι)∈U ↔ i∈s := Finset.mem_map' _
  have hsumU (i : ι) : U.sum (q i)=s.sum (fun j : t => q i j) := by
    simp only [U,Finset.sum_map,Function.Embedding.coeFn_mk]
  have hdis : Disjoint U Z := by
    apply Finset.disjoint_left.mpr
    intro i hi hzi
    exact (Finset.mem_filter.mp hzi).2.1 (hUT i hi)
  have hsum (i : ι) : (U∪Z).sum (q i)=U.sum (q i) := by
    rw [Finset.sum_union hdis]
    have hZ : Z.sum (q i)=0 := Finset.sum_eq_zero fun j hj =>
      hz j (Finset.mem_filter.mp hj).2.1 i
    rw [hZ,add_zero]
  refine ⟨U∪Z,?_,?_⟩
  · intro i hi
    rw [hsum]
    rcases Finset.mem_union.mp hi with hi | hi
    · have h := hh ⟨i,hUT i hi⟩ ((hmemU ⟨i,hUT i hi⟩).mp hi)
      simpa only [hsumU] using h
    · have h := (Finset.mem_filter.mp hi).2
      rw [hz i h.1 i]
      exact h.2
  · intro i hi
    rw [hsum]
    by_cases hit : i∈t
    · have hn : (⟨i,hit⟩ : t)∉s := fun h => hi (Finset.mem_union_left Z ((hmemU _).mpr h))
      simpa only [hsumU] using hl ⟨i,hit⟩ hn
    · apply le_of_lt
      apply lt_of_not_ge
      intro h
      exact hi (Finset.mem_union_right U (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit,h⟩))

theorem stable_of_weighted_symmetry [Fintype ι] (q : ι → ι → ℝ) (a : ι → ℝ)
    (ha : ∀i,0<a i) (hsym : ∀i j,a i*q i j=a j*q j i) : Stable q := by
  intro ρ hρ
  classical
  let t : Finset ι := Finset.univ.filter (fun i => 0<ρ i)
  apply of_zero_columns (fun i j => ρ j*q i j) t
  · intro j hj i
    have hn : ¬0<ρ j := by simpa only [t,Finset.mem_filter,Finset.mem_univ,true_and] using hj
    have he : ρ j=0 := le_antisymm (le_of_not_gt hn) (hρ j)
    rw [he,zero_mul]
  · apply of_weighted_symmetry _ (fun i : t => a i*ρ i)
    · intro i
      exact mul_pos (ha i) (Finset.mem_filter.mp i.property).2
    · intro i j
      calc
        _ = (ρ i*ρ j)*(a i*q i j) := by ring
        _ = (ρ i*ρ j)*(a j*q j i) := by rw [hsym]
        _ = _ := by ring

theorem stable_of_nonnegative [Fintype ι] (q : ι → ι → ℝ)
    (hq : ∀i j,0≤q i j) : Stable q := by
  intro ρ hρ
  exact of_nonnegative _ (fun i j => mul_nonneg (hρ j) (hq i j))

theorem stable_sum (q : (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (hleft : Stable (fun i j => q (.inl i) (.inl j)))
    (hright : Stable (fun i j => q (.inr i) (.inr j)))
    (hzero : ∀i j,q (.inr j) (.inl i)=0) : Stable q := by
  intro ρ hρ
  exact sum _ (hleft (fun i => ρ (.inl i)) (fun i => hρ (.inl i)))
    (hright (fun j => ρ (.inr j)) (fun j => hρ (.inr j)))
    (fun i j => by rw [hzero,mul_zero])

end Plank.SideAssignments
