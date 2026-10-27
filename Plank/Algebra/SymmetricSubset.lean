/- A finite side assignment from a weighted symmetric potential. -/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Plank.SymmetricSubset

variable {ι : Type*}

/-- A quadratic score on finite subsets, with each symmetric interaction
counted once. -/
def score (a : ι → ℝ) (b : ι → ι → ℝ) (s : Finset ι) : ℝ :=
  s.sum a + (s.sum fun i => s.sum (b i)) / 2

theorem score_insert [DecidableEq ι] (a : ι → ℝ) (b : ι → ι → ℝ)
    (hsym : ∀ i j, b i j = b j i) (hdiag : ∀ i, b i i = 0)
    (s : Finset ι) (i : ι) (hi : i ∉ s) :
    score a b (insert i s) = score a b s + a i + s.sum (b i) := by
  have hcol : s.sum (fun j => b j i) = s.sum (b i) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hsym j i
  have hrows : ((insert i s).sum fun j => (insert i s).sum (b j)) =
      (s.sum fun j => s.sum (b j)) + 2 * s.sum (b i) := by
    simp only [Finset.sum_insert hi, hdiag, zero_add, Finset.sum_add_distrib]
    rw [hcol]
    ring
  unfold score
  rw [Finset.sum_insert hi, hrows]
  ring

/-- The Bang subset potential for weighted interactions. The diagonal is
omitted from the score; it supplies the distance between the two thresholds. -/
noncomputable def potential (w x lo : ι → ℝ) (q : ι → ι → ℝ)
    (s : Finset ι) : ℝ := by
  classical
  exact score (fun i => w i * (x i - lo i))
    (fun i j => if i = j then 0 else w i * q i j) s

/-- The gain from adding a coordinate is its weighted displacement from its
lower threshold. -/
theorem potential_insert [DecidableEq ι] (w x lo : ι → ℝ) (q : ι → ι → ℝ)
    (hsym : ∀ i j, w i * q i j = w j * q j i)
    (s : Finset ι) (i : ι) (hi : i ∉ s) :
    potential w x lo q (insert i s) = potential w x lo q s +
      w i * (x i + s.sum (q i) - lo i) := by
  classical
  let a : ι → ℝ := fun i => w i * (x i - lo i)
  let b : ι → ι → ℝ := fun i j => if i = j then 0 else w i * q i j
  have hb : ∀ i j, b i j = b j i := by
    intro i j
    by_cases h : i = j
    · subst j
      rfl
    · simp only [b, h, Ne.symm h, ↓reduceIte]
      exact hsym i j
  have hdiag : ∀ i, b i i = 0 := by simp [b]
  have hrepr (r : Finset ι) : potential w x lo q r = score a b r := by
    unfold potential
    congr 1
    funext i j
    by_cases hij : i = j <;> simp [b, hij]
  rw [hrepr, hrepr]
  rw [score_insert a b hb hdiag s i hi]
  have hrow : s.sum (b i) = w i * s.sum (q i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp only [b, hij, ↓reduceIte]
  rw [hrow]
  dsimp only [a]
  ring

/-- Every maximizer of the finite Bang potential places each coordinate on
its assigned side of the corresponding interval. No sign condition is imposed
on the off-diagonal interactions. -/
theorem side_assignment_of_maximal [Fintype ι]
    (w x lo hi : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ i, 0 < w i) (hdiag : ∀ i, q i i = hi i - lo i)
    (hsym : ∀ i j, w i * q i j = w j * q j i)
    (s : Finset ι)
    (hmax : ∀ r, potential w x lo q r ≤ potential w x lo q s) :
    (∀ i ∈ s, hi i ≤ x i + s.sum (q i)) ∧
    (∀ i ∉ s, x i + s.sum (q i) ≤ lo i) := by
  classical
  constructor
  · intro i his
    have hm := hmax (s.erase i)
    have he : insert i (s.erase i) = s := Finset.insert_erase his
    have hd := potential_insert w x lo q hsym (s.erase i) i
      (Finset.notMem_erase i s)
    rw [he] at hd
    have hlo : lo i ≤ x i + (s.erase i).sum (q i) := by
      nlinarith [hw i]
    have hsum : s.sum (q i) = q i i + (s.erase i).sum (q i) := by
      conv_lhs => rw [← he]
      exact Finset.sum_insert (Finset.notMem_erase i s)
    rw [hsum, hdiag]
    linarith
  · intro i his
    have hm := hmax (insert i s)
    rw [potential_insert w x lo q hsym s i his] at hm
    nlinarith [hw i]

/-- Weighted symmetric interactions admit a simultaneous finite side
assignment, obtained by maximizing a quadratic potential. -/
theorem exists_side_assignment [Fintype ι]
    (w x lo hi : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ i, 0 < w i) (hdiag : ∀ i, q i i = hi i - lo i)
    (hsym : ∀ i j, w i * q i j = w j * q j i) :
    ∃ s : Finset ι,
      (∀ i ∈ s, hi i ≤ x i + s.sum (q i)) ∧
      (∀ i ∉ s, x i + s.sum (q i) ≤ lo i) := by
  classical
  obtain ⟨s, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset ι)) (potential w x lo q) Finset.univ_nonempty
  exact ⟨s, side_assignment_of_maximal w x lo hi q hw hdiag hsym s
    (fun r => hmax r (Finset.mem_univ _))⟩

end Plank.SymmetricSubset
