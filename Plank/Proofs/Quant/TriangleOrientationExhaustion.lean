/- Every triple has a common extreme vertex or three distinct strict middles. -/
module
public import Plank.Proofs.Quant.TriangleCommonExtremeCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleOrientationExhaustion
open Proofs.Basic TriangleCommonExtremeCatalogue

def AtMiddle (T : Triangle) (p : Plank) : Prop :=
  (dot p.u T.B < dot p.u T.A ∧ dot p.u T.A < dot p.u T.C) ∨
  (dot p.u T.C < dot p.u T.A ∧ dot p.u T.A < dot p.u T.B)

theorem not_extreme_iff (T : Triangle) (p : Plank) :
    ¬ AtExtreme T p ↔ AtMiddle T p := by
  unfold AtExtreme AtMinimum AtMiddle
  constructor
  · intro h
    simp only [not_or,not_and_or,not_le] at h
    rcases h with ⟨hb | hc, hb' | hc'⟩
    · linarith
    · exact Or.inl ⟨hb,hc'⟩
    · exact Or.inr ⟨hc,hb'⟩
    · linarith
  · rintro (⟨hb,hc⟩ | ⟨hc,hb⟩) (⟨ha,hd⟩ | ⟨ha,hd⟩) <;> linarith

theorem middle_vertex_unique (T : Triangle) (p : Plank) (v w : Fin 3)
    (hv : AtMiddle (atVertex T v) p) (hw : AtMiddle (atVertex T w) p) : v=w := by
  fin_cases v <;> fin_cases w <;> try rfl
  all_goals
    dsimp [AtMiddle,atVertex,rotate] at hv hw
    rcases hv with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
      rcases hw with ⟨hc,hd⟩ | ⟨hc,hd⟩ <;> linarith

def HasCommonExtreme (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  ∃ v : Fin 3, ∀ i, AtExtreme (atVertex T v) (p i)

def StrictCyclic (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∀ v, AtMiddle (atVertex T v) (p (σ v))

/-- This is a geometric orientation dichotomy, with no equality, width,
position, clipping, or distinct-direction assumption. -/
theorem exhaustive (T : Triangle) (p : Fin 3 → Plank) :
    HasCommonExtreme T p ∨ StrictCyclic T p := by
  classical
  by_cases h : HasCommonExtreme T p
  · exact Or.inl h
  · unfold HasCommonExtreme at h
    push Not at h
    choose f hf using h
    have hi : Function.Injective f := by
      intro v w he
      apply middle_vertex_unique T (p (f v)) v w
      · exact (not_extreme_iff _ _).mp (hf v)
      · rw [he]
        exact (not_extreme_iff _ _).mp (hf w)
    exact Or.inr ⟨Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩,
      fun v => (not_extreme_iff _ _).mp (hf v)⟩

theorem exclusive (T : Triangle) (p : Fin 3 → Plank) :
    HasCommonExtreme T p → ¬ StrictCyclic T p := by
  rintro ⟨v,hv⟩ ⟨σ,hσ⟩
  exact (not_extreme_iff _ _).mpr (hσ v) (hv (σ v))

/-- Any direction parallel to a triangle edge forces the common-extreme side
of the dichotomy, including either tied minimum or tied maximum. -/
theorem common_extreme_of_tied_edge (T : Triangle) (p : Fin 3 → Plank) (j : Fin 3)
    (ht : dot (p j).u T.A = dot (p j).u T.B ∨
      dot (p j).u T.A = dot (p j).u T.C ∨ dot (p j).u T.B = dot (p j).u T.C) :
    HasCommonExtreme T p := by
  rcases exhaustive T p with h | ⟨σ,hσ⟩
  · exact h
  · exfalso
    obtain ⟨v,hv⟩ := σ.surjective j
    have hm := hσ v
    rw [hv] at hm
    fin_cases v <;> dsimp [AtMiddle,atVertex,rotate] at hm
    all_goals
      rcases ht with ht | ht | ht <;>
        rcases hm with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> linarith

/-- Two directions always admit a shared extreme vertex. -/
theorem pair_common_extreme (T : Triangle) (p : Fin 2 → Plank) :
    ∃ v : Fin 3, ∀ i, AtExtreme (atVertex T v) (p i) := by
  classical
  by_contra h
  push Not at h
  choose f hf using h
  have hi : Function.Injective f := by
    intro v w he
    apply middle_vertex_unique T (p (f v)) v w
    · exact (not_extreme_iff _ _).mp (hf v)
    · rw [he]
      exact (not_extreme_iff _ _).mp (hf w)
  have hc := Fintype.card_le_of_injective f hi
  norm_num at hc

end Quant.TriangleOrientationExhaustion

/-- info: 'Quant.TriangleOrientationExhaustion.exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleOrientationExhaustion.exhaustive

/-- info: 'Quant.TriangleOrientationExhaustion.pair_common_extreme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleOrientationExhaustion.pair_common_extreme
