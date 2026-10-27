/- Exhaustive normalized equality families with at least one zero-width plank. -/
module
public import Plank.Convex.PlanarTight.TwoPlankComplete
public import Plank.Convex.ZeroWidthSlabRemoval
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.ZeroWidthClassification

abbrev Point := Fin 3 → ℝ

/-- The zero-width member is arbitrary. The remaining two have the
explicit positive triangular/quadrilateral or zero-plus-full normal form. -/
def Normal (K : Set Point) (lo hi : Point) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), lo (σ 0) = hi (σ 0) ∧
    TwoPlankComplete.Normal K (AffineMap.proj (σ 1)) (AffineMap.proj (σ 2))
      (lo (σ 1)) (hi (σ 1)) (lo (σ 2)) (hi (σ 2))

/-- Complete equality classification whenever at least one normalized
window has zero width. No clipping, compactness, or plane equation is needed. -/
theorem tight_iff (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hL : ∀ i, ∃ p ∈ K, p i = 0) (hU : ∀ i, ∃ p ∈ K, p i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i) (hzero : ∃ i, lo i = hi i) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ p ∈ K, ∃ i, lo i ≤ p i ∧ p i ≤ hi i) ↔
      Normal K lo hi := by
  have H (i j : Fin 3) : TwoPlankClassification.Ranges K (AffineMap.proj i) (AffineMap.proj j) :=
    ⟨fun p hp => ⟨hbox p hp i, hbox p hp j⟩, hL i, hU i, hL j, hU j⟩
  constructor
  · rintro ⟨hs, hc⟩
    obtain ⟨k, hk⟩ := hzero
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 k
    have hσ : σ 0 = k := Equiv.swap_apply_left 0 k
    have hz : lo (σ 0) = hi (σ 0) := by simpa only [hσ] using hk
    obtain ⟨p, hp, hpk⟩ : ∃ p ∈ K, p k ≠ lo k := by
      by_cases hlo : lo k = 0
      · obtain ⟨p, hp, hpk⟩ := hU k
        exact ⟨p, hp, by rw [hpk, hlo]; exact one_ne_zero⟩
      · obtain ⟨p, hp, hpk⟩ := hL k
        exact ⟨p, hp, by rw [hpk]; exact Ne.symm hlo⟩
    have hrem := ZeroWidthSlabRemoval.cover_without_zero K hK
      (fun i => ContinuousLinearMap.proj i) lo hi k hk p hp hpk hc
    refine ⟨σ, hz, (TwoPlankComplete.tight_iff K hK _ _ (H (σ 1) (σ 2))
      (lo (σ 1)) (hi (σ 1)) (lo (σ 2)) (hi (σ 2)) (horder _) (horder _)).mp ⟨?_, ?_⟩⟩
    · rw [← Equiv.sum_comp σ (fun i => hi i - lo i), Fin.sum_univ_three, ← hz,
        sub_self, zero_add] at hs
      exact hs
    · intro x hx
      obtain ⟨i, hik, hmem⟩ := hrem x hx
      change lo i ≤ x i ∧ x i ≤ hi i at hmem
      have hne : σ.symm i ≠ 0 := by
        intro he
        apply hik
        calc
          i = σ (σ.symm i) := (σ.apply_symm_apply i).symm
          _ = k := by rw [he, hσ]
      have hm : lo (σ (σ.symm i)) ≤ x (σ (σ.symm i)) ∧
          x (σ (σ.symm i)) ≤ hi (σ (σ.symm i)) := by
        simpa only [σ.apply_symm_apply] using hmem
      generalize σ.symm i = j at hne hm
      fin_cases j
      · exact False.elim (hne rfl)
      · exact Or.inl hm
      · exact Or.inr hm
  · rintro ⟨σ, hz, hn⟩
    have ht := (TwoPlankComplete.tight_iff K hK _ _ (H (σ 1) (σ 2))
      (lo (σ 1)) (hi (σ 1)) (lo (σ 2)) (hi (σ 2)) (horder _) (horder _)).mpr hn
    refine ⟨?_, ?_⟩
    · rw [← Equiv.sum_comp σ (fun i => hi i - lo i), Fin.sum_univ_three, ← hz,
        sub_self, zero_add]
      exact ht.1
    · intro p hp
      rcases ht.2 p hp with h | h
      · exact ⟨σ 1, h⟩
      · exact ⟨σ 2, h⟩

end Plank.Convex.PlanarTight.ZeroWidthClassification

/-- info: 'Plank.Convex.PlanarTight.ZeroWidthClassification.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ZeroWidthClassification.tight_iff
