/- Equality-safe clipping for normalized three-plank covers. Positive windows
lie in their actual directional ranges; no restriction is imposed on zero windows. -/
module
public import Plank.Convex.PlanarThreePlankTheorem
public import Plank.Convex.AffineSlabNormalization
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight
open scoped BigOperators
open AffineSlabNormalization

/-- Equality in clipping the length of a positive interval forces both endpoints
to lie in the unit interval. -/
theorem endpoints_of_clamp_width_eq (l h : ℝ) (hpos : l < h)
    (heq : clamp h - clamp l = h - l) : 0 ≤ l ∧ h ≤ 1 := by
  dsimp [clamp] at heq
  constructor <;> by_contra! hbad <;>
    simp only [max_def, min_def] at heq <;> split_ifs at heq <;> linarith

/-- A normalized covering inequality implies that every window preserves its
length under clipping at equality. This also applies to zero windows. -/
theorem clamp_width_eq_of_tight {I E : Type*} [Fintype I]
    (K : Set E) (f : I → E → ℝ)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ f i x ∧ f i x ≤ 1)
    (hbound : ∀ l u : I → ℝ, (∀ i, l i ≤ u i) →
      (∀ x ∈ K, ∃ i, l i ≤ f i x ∧ f i x ≤ u i) →
      1 ≤ ∑ i, (u i - l i))
    (lo hi : I → ℝ) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i)
    (hsum : (∑ i, (hi i - lo i)) ≤ 1) (i : I) :
    clamp (hi i) - clamp (lo i) = hi i - lo i := by
  have hle (j : I) := clamp_sub_le (lo j) (hi j) (horder j)
  have hcov : ∀ x ∈ K, ∃ j, clamp (lo j) ≤ f j x ∧ f j x ≤ clamp (hi j) := by
    intro x hx
    obtain ⟨j, hj⟩ := hcover x hx
    exact ⟨j, clamp_interval _ _ _ (hbox x hx j) hj⟩
  have hlower := hbound (fun j => clamp (lo j)) (fun j => clamp (hi j))
    (fun j => clamp_mono (horder j)) hcov
  have heq : (∑ j, (clamp (hi j) - clamp (lo j))) = ∑ j, (hi j - lo j) :=
    le_antisymm (Finset.sum_le_sum (fun j _ => hle j)) (hsum.trans hlower)
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp heq i (Finset.mem_univ i)

/-- On a normalized positive plane, a tight cover spends no positive width
outside the body. Compactness and nonempty interior are unnecessary. -/
theorem positive_window_no_waste (K : Set (Fin 3 → ℝ)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Fin 3 → ℝ) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (lo hi : Fin 3 → ℝ) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hsum : (∑ i, (hi i - lo i)) ≤ 1) (i : Fin 3) (hpos : lo i < hi i) :
    0 ≤ lo i ∧ hi i ≤ 1 := by
  apply endpoints_of_clamp_width_eq _ _ hpos
  exact clamp_width_eq_of_tight K (fun j x => x j) hbox
    (fun l u ho hc => PlanarThreePlankWidth.width_bound
      K hK hbox hL hU A D hA hplane l u ho hc)
    lo hi horder hcover hsum i

end Plank.Convex.PlanarTight

/-- info: 'Plank.Convex.PlanarTight.positive_window_no_waste' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.positive_window_no_waste
