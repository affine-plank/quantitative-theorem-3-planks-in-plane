/- Three normalized planar directions have a full relation or a repeated independent pair. -/
module
public import Plank.Convex.PlanarTight.NormalizedParallelDirections
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.DirectionDichotomy
open OrientedCommonChord (coordinates)
open TwoPlankClassification (reflect)

abbrev E := Fin 2 → ℝ
abbrev Forms := Fin 3 → E →ᵃ[ℝ] ℝ

def FullRelation (f : Forms) : Prop :=
  ∃ (a : Fin 3 → ℝ) (d : ℝ), (∀ i, a i ≠ 0) ∧ ∀ x, ∑ i, a i * f i x = d

def Repeated (f : Forms) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool),
    coordinates flip (fun i => f (σ i)) 0 = coordinates flip (fun i => f (σ i)) 1 ∧
    LinearIndependent ℝ ![(coordinates flip (fun i => f (σ i)) 0).linear,
      (coordinates flip (fun i => f (σ i)) 2).linear]

private theorem full_of_independent (f : Forms)
    (h01 : LinearIndependent ℝ ![(f 0).linear, (f 1).linear])
    (h02 : LinearIndependent ℝ ![(f 0).linear, (f 2).linear])
    (h12 : LinearIndependent ℝ ![(f 1).linear, (f 2).linear]) : FullRelation f := by
  obtain ⟨a, b, c, ha, hb, hrel⟩ := ThreePlanarDirections.exists_coefficients
    (f 0) (f 1) (f 2) h01 h02 h12
  refine ⟨![a, b, -1], -c, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · norm_num
  · intro x
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, neg_one_mul]
    linarith only [hrel x]

private theorem full_of_parallel (f : Forms)
    (h1 : f 1 = f 0 ∨ f 1 = reflect (f 0))
    (h2 : f 2 = f 0 ∨ f 2 = reflect (f 0)) : FullRelation f := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · refine ⟨![1, 1, -2], 0, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · intro x
      rw [Fin.sum_univ_three]
      change 1 * f 0 x + 1 * f 1 x + (-2) * f 2 x = 0
      rw [h1, h2]
      ring
  · refine ⟨![1, 1, 2], 2, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · intro x
      rw [Fin.sum_univ_three]
      change 1 * f 0 x + 1 * f 1 x + 2 * f 2 x = 2
      rw [h1, h2]
      simp only [TwoPlankClassification.reflect_apply]
      ring
  · refine ⟨![1, -1, -2], -1, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · intro x
      rw [Fin.sum_univ_three]
      change 1 * f 0 x + (-1) * f 1 x + (-2) * f 2 x = -1
      rw [h1, h2]
      simp only [TwoPlankClassification.reflect_apply]
      ring
  · refine ⟨![1, -1, 2], 1, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · intro x
      rw [Fin.sum_univ_three]
      change 1 * f 0 x + (-1) * f 1 x + 2 * f 2 x = 1
      rw [h1, h2]
      simp only [TwoPlankClassification.reflect_apply]
      ring

private theorem repeated_of_pair (f : Forms) (σ : Equiv.Perm (Fin 3))
    (heq : f (σ 1) = f (σ 0) ∨ f (σ 1) = reflect (f (σ 0)))
    (hind : LinearIndependent ℝ ![(f (σ 0)).linear, (f (σ 2)).linear]) :
    Repeated f := by
  rcases heq with heq | heq
  · refine ⟨σ, fun _ => false, ?_, ?_⟩
    · simpa only [coordinates, Bool.false_eq_true, if_false] using heq.symm
    · simpa only [coordinates, Bool.false_eq_true, if_false] using hind
  · refine ⟨σ, fun i => decide (i = 1), ?_, ?_⟩
    · ext x
      simp [coordinates, heq, TwoPlankClassification.reflect_apply]
    · simpa [coordinates] using hind

/-- Exhaustive direction split. The full-relation alternative includes
three distinct directions and the completely parallel case. The other
alternative has two identical normalized functions and an independent third. -/
theorem full_or_repeated (K : Set E) (f : Forms)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1) :
    FullRelation f ∨ Repeated f := by
  have hp (i j : Fin 3) (h : ¬ LinearIndependent ℝ ![(f i).linear, (f j).linear]) :
      f j = f i ∨ f j = reflect (f i) :=
    NormalizedParallelDirections.eq_or_reflect K (f i) (f j)
      (fun x hx => ⟨hbox x hx i, hbox x hx j⟩) (hL i) (hU i) (hL j) (hU j) h
  by_cases h01 : LinearIndependent ℝ ![(f 0).linear, (f 1).linear]
  · by_cases h02 : LinearIndependent ℝ ![(f 0).linear, (f 2).linear]
    · by_cases h12 : LinearIndependent ℝ ![(f 1).linear, (f 2).linear]
      · exact Or.inl (full_of_independent f h01 h02 h12)
      · apply Or.inr
        apply repeated_of_pair f (Equiv.swap 0 1 * Equiv.swap 1 2)
        · simpa [Equiv.swap_apply_def] using hp 1 2 h12
        · simpa [Equiv.swap_apply_def] using (LinearIndependent.pair_symm_iff.mp h01)
    · apply Or.inr
      apply repeated_of_pair f (Equiv.swap 1 2)
      · simpa [Equiv.swap_apply_def] using hp 0 2 h02
      · simpa [Equiv.swap_apply_def] using h01
  · by_cases h02 : LinearIndependent ℝ ![(f 0).linear, (f 2).linear]
    · exact Or.inr (repeated_of_pair f (Equiv.refl _) (hp 0 1 h01) h02)
    · exact Or.inl (full_of_parallel f (hp 0 1 h01) (hp 0 2 h02))

end Plank.Convex.PlanarTight.DirectionDichotomy

/-- info: 'Plank.Convex.PlanarTight.DirectionDichotomy.full_or_repeated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.DirectionDichotomy.full_or_repeated
