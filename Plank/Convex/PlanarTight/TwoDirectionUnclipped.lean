/- The split two-direction families retain every original normalized endpoint. -/
module
public import Plank.Convex.PlanarTight.TwoDirectionClassification
public import Plank.Convex.PlanarTight.TwoPlankComplete
public import Plank.Convex.TwoDirectionThreePlanks
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.TwoDirectionUnclipped
open AffineSlabNormalization
open TwoDirectionClassification (Tight Normal)

abbrev E := Fin 2 → ℝ
abbrev P := Fin 3 → ℝ

def coordinate (i : Fin 3) (x : E) : ℝ := if i = 2 then x 1 else x 0

theorem width_bound (K : Set E) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∃ x ∈ K, x 0 = 0) (hR : ∃ x ∈ K, x 0 = 1)
    (hB : ∃ x ∈ K, x 1 = 0) (hT : ∃ x ∈ K, x 1 = 1)
    (lo hi : P) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ coordinate i x ∧ coordinate i x ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) := by
  have hb := TwoDirectionThreePlanks.sum_ge_one K hK hbox hL hR hB hT
    (lo 0) (hi 0) (lo 1) (hi 1) (clamp (lo 2)) (clamp (hi 2))
    (horder 0) (horder 1) (clamp_mono (horder 2))
    (clamp_nonneg _) (clamp_le_one _) (by
      intro x hx
      obtain ⟨i, hi'⟩ := hcover x hx
      fin_cases i
      · exact Or.inl hi'
      · exact Or.inr (Or.inl hi')
      · exact Or.inr (Or.inr (clamp_interval _ _ _ (hbox x hx 1) hi')))
  have hc := clamp_sub_le (lo 2) (hi 2) (horder 2)
  rw [Fin.sum_univ_three]
  linarith only [hb, hc]

theorem normal_tight (K : Set E) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∃ x ∈ K, x 0 = 0) (hR : ∃ x ∈ K, x 0 = 1)
    (hB : ∃ x ∈ K, x 1 = 0) (hT : ∃ x ∈ K, x 1 = 1)
    (lo hi : P) (hw : ∀ i, lo i < hi i)
    (hn : Normal K (AffineMap.proj 0) (AffineMap.proj 1)
      (lo 0) (hi 0) (lo 1) (hi 1) (lo 2) (hi 2)) :
    Tight K (AffineMap.proj 0) (AffineMap.proj 1)
      (lo 0) (hi 0) (lo 1) (hi 1) (lo 2) (hi 2) := by
  have H : TwoPlankClassification.Ranges K (AffineMap.proj 0) (AffineMap.proj 1) :=
    ⟨fun x hx => ⟨hbox x hx 0, hbox x hx 1⟩, hL, hR, hB, hT⟩
  rcases hn with ⟨ht, hn⟩ | ⟨ht, hn⟩
  · apply (TwoDirectionClassification.split_tight_iff K _ _ _ _ _ _ _ _
      (hw 0).le (hw 1).le ht).mpr
    have hmerged : lo 0 < hi 1 := by linarith only [hw 0, hw 1, ht]
    apply (TwoPlankComplete.tight_iff K hK _ _ H _ _ _ _ hmerged.le (hw 2).le).mpr
    exact Or.inl ⟨hmerged, hw 2, hn⟩
  · apply (TwoDirectionClassification.tight_swap K _ _ _ _ _ _ _ _).mp
    apply (TwoDirectionClassification.split_tight_iff K _ _ _ _ _ _ _ _
      (hw 1).le (hw 0).le ht).mpr
    have hmerged : lo 1 < hi 0 := by linarith only [hw 0, hw 1, ht]
    apply (TwoPlankComplete.tight_iff K hK _ _ H _ _ _ _ hmerged.le (hw 2).le).mpr
    exact Or.inl ⟨hmerged, hw 2, hn⟩

/-- Complete positive two-direction equality without assuming any clipping
of the input windows. Equality forces the original endpoints into the unit range. -/
theorem tight_iff (K : Set E) (hK : Convex ℝ K) (hfull : (interior K).Nonempty)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∃ x ∈ K, x 0 = 0) (hR : ∃ x ∈ K, x 0 = 1)
    (hB : ∃ x ∈ K, x 1 = 0) (hT : ∃ x ∈ K, x 1 = 1)
    (lo hi : P) (hw : ∀ i, lo i < hi i) :
    Tight K (AffineMap.proj 0) (AffineMap.proj 1)
      (lo 0) (hi 0) (lo 1) (hi 1) (lo 2) (hi 2) ↔
    Normal K (AffineMap.proj 0) (AffineMap.proj 1)
      (lo 0) (hi 0) (lo 1) (hi 1) (lo 2) (hi 2) := by
  constructor
  · intro ht
    have hc : ∀ x ∈ K, ∃ i, lo i ≤ coordinate i x ∧ coordinate i x ≤ hi i := by
      intro x hx
      rcases ht.2 x hx with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    have hs : (∑ i, (hi i - lo i)) ≤ 1 := by
      rw [Fin.sum_univ_three]
      exact ht.1.le
    have hend (i : Fin 3) : 0 ≤ lo i ∧ hi i ≤ 1 := by
      apply endpoints_of_clamp_width_eq _ _ (hw i)
      apply clamp_width_eq_of_tight K coordinate ?_
        (width_bound K hK hbox hL hR hB hT) lo hi (fun j => (hw j).le) hc hs i
      intro x hx j
      dsimp [coordinate]
      split_ifs
      · exact hbox x hx 1
      · exact hbox x hx 0
    exact (TwoDirectionClassification.tight_iff K hK hfull hbox hL hR hB hT
      _ _ _ _ _ _ (hw 0) (hw 1) (hw 2)
      (hend 0).1 (hend 0).2 (hend 1).1 (hend 1).2 (hend 2).1 (hend 2).2).mp ht
  · exact normal_tight K hK hbox hL hR hB hT lo hi hw

end Plank.Convex.PlanarTight.TwoDirectionUnclipped

/-- info: 'Plank.Convex.PlanarTight.TwoDirectionUnclipped.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoDirectionUnclipped.tight_iff
