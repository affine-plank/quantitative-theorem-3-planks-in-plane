/- All common-minimum direction triples reduce to three geometric charts. -/
module
public import Plank.Proofs.Quant.TriangleFarCatalogue
public import Plank.Proofs.Quant.TriangleStrictCommonMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCommonMinimumDirections
open TriangleStrictCommonMinimum CommonVertexTranslationEquality

/-- Relabel the original bands and optionally interchange the two other
triangle vertices. These operations preserve every individual width. -/
def present (C : Config) (flip : Bool) (σ : Equiv.Perm (Fin 3)) : Config :=
  if flip then reflected ⟨C.plank ∘ σ⟩ else ⟨C.plank ∘ σ⟩

theorem present_equiv (C : Config) (flip : Bool) (σ : Equiv.Perm (Fin 3)) :
    C.Equiv (present C flip σ) := by
  have hr : C.Equiv (⟨C.plank ∘ σ⟩ : Config) := Relation.EqvGen.rel _ _ (Move.relabel C σ)
  cases flip
  · exact hr
  · exact Relation.EqvGen.trans _ _ _ hr (reflected_equiv _)

theorem present_width (C : Config) (flip : Bool) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (present C flip σ).relW i=C.relW (σ i) := by
  cases flip
  · rfl
  · exact reflected_width ⟨C.plank ∘ σ⟩ i

theorem present_deficit (C : Config) (flip : Bool) (σ : Equiv.Perm (Fin 3)) :
    (present C flip σ).deficit=C.deficit := by
  simp only [Config.deficit,← (present_equiv C flip σ).sumRelW_eq]

theorem present_nonneg (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (flip : Bool) (σ : Equiv.Perm (Fin 3)) :
    ∀ i, 0 ≤ ((present C flip σ).plank i).u.1 ∧ 0 ≤ ((present C flip σ).plank i).u.2 := by
  intro i
  cases flip
  · exact hu (σ i)
  · exact ⟨(hu (σ i)).2,(hu (σ i)).1⟩

def cycle : Equiv.Perm (Fin 3) :=
  ⟨![1,2,0],![2,0,1],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩

theorem exists_first_two (i j : Fin 3) (h : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0=i ∧ σ 1=j := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (h rfl).elim
    | exact ⟨Equiv.refl _,by decide,by decide⟩
    | exact ⟨Equiv.swap 1 2,by decide,by decide⟩
    | exact ⟨Equiv.swap 0 1,by decide,by decide⟩
    | exact ⟨cycle,by decide,by decide⟩
    | exact ⟨cycle.symm,by decide,by decide⟩
    | exact ⟨Equiv.swap 0 2,by decide,by decide⟩

def StackChart (C : Config) : Prop := ∀ i, (C.plank i).u.2 ≤ (C.plank i).u.1

def MixedChart (C : Config) : Prop :=
  ∃ a b c : ℝ, (0 ≤ a ∧ a < 1) ∧ (0 ≤ b ∧ b < 1) ∧ (0 ≤ c ∧ c < 1) ∧
    (C.plank 0).u=(1,b) ∧ (C.plank 1).u=(1,c) ∧ (C.plank 2).u=(a,1)

def FarChart (C : Config) : Prop :=
  ∃ a b : ℝ, (0 ≤ a ∧ a < 1) ∧ (0 ≤ b ∧ b < 1) ∧
    (C.plank 0).u=(1,b) ∧ (C.plank 1).u=(a,1) ∧ (C.plank 2).u=(1,1)

/-- No strict-extremum assumption: edge directions, tied maxima, and
repeated directions are included in this finite direction exhaustion. -/
theorem exhaustive (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hm : ∀ i, max (C.plank i).u.1 (C.plank i).u.2=1) :
    ∃ flip : Bool, ∃ σ : Equiv.Perm (Fin 3),
      StackChart (present C flip σ) ∨ MixedChart (present C flip σ) ∨
        FarChart (present C flip σ) := by
  have hx (i) : (C.plank i).u.1 ≤ 1 := (le_max_left _ _).trans_eq (hm i)
  have hy (i) : (C.plank i).u.2 ≤ 1 := (le_max_right _ _).trans_eq (hm i)
  have hone (i) : (C.plank i).u.1=1 ∨ (C.plank i).u.2=1 := by
    rcases le_total (C.plank i).u.1 (C.plank i).u.2 with h | h
    · exact Or.inr (by simpa only [max_eq_right h] using hm i)
    · exact Or.inl (by simpa only [max_eq_left h] using hm i)
  by_cases hallx : ∀ i, (C.plank i).u.1=1
  · refine ⟨false,Equiv.refl _,Or.inl ?_⟩
    intro i
    change (C.plank i).u.2 ≤ (C.plank i).u.1
    rw [hallx i]
    exact hy i
  by_cases hally : ∀ i, (C.plank i).u.2=1
  · refine ⟨true,Equiv.refl _,Or.inl ?_⟩
    intro i
    change (C.plank i).u.1 ≤ (C.plank i).u.2
    rw [hally i]
    exact hx i
  push_neg at hallx hally
  obtain ⟨i,hiy⟩ := hally
  obtain ⟨j,hjx⟩ := hallx
  have hix : (C.plank i).u.1=1 := (hone i).resolve_right hiy
  have hjy : (C.plank j).u.2=1 := (hone j).resolve_left hjx
  have hib : 0 ≤ (C.plank i).u.2 ∧ (C.plank i).u.2 < 1 :=
    ⟨(hu i).2,lt_of_le_of_ne (hy i) hiy⟩
  have hja : 0 ≤ (C.plank j).u.1 ∧ (C.plank j).u.1 < 1 :=
    ⟨(hu j).1,lt_of_le_of_ne (hx j) hjx⟩
  have hij : i ≠ j := by intro he; subst j; exact hjx hix
  obtain ⟨σ,hσ0,hσ1⟩ := exists_first_two i j hij
  have hi : (C.plank i).u=(1,(C.plank i).u.2) := Prod.ext hix rfl
  have hj : (C.plank j).u=((C.plank j).u.1,1) := Prod.ext rfl hjy
  by_cases hkx : (C.plank (σ 2)).u.1=1
  · by_cases hky : (C.plank (σ 2)).u.2=1
    · refine ⟨false,σ,Or.inr (Or.inr ?_)⟩
      refine ⟨(C.plank j).u.1,(C.plank i).u.2,hja,hib,?_,?_,?_⟩
      · simpa only [present,Bool.false_eq_true,if_false,Function.comp_apply,hσ0] using hi
      · simpa only [present,Bool.false_eq_true,if_false,Function.comp_apply,hσ1] using hj
      · exact Prod.ext hkx hky
    · refine ⟨false,(Equiv.swap 1 2).trans σ,Or.inr (Or.inl ?_)⟩
      refine ⟨(C.plank j).u.1,(C.plank i).u.2,(C.plank (σ 2)).u.2,
        hja,hib,⟨(hu (σ 2)).2,lt_of_le_of_ne (hy (σ 2)) hky⟩,?_,?_,?_⟩
      · simpa [present,Equiv.trans_apply,Equiv.swap_apply_def,hσ0] using hi
      · simpa [present,Equiv.trans_apply,Equiv.swap_apply_def] using
          (Prod.ext hkx rfl : (C.plank (σ 2)).u=(1,(C.plank (σ 2)).u.2))
      · simpa [present,Equiv.trans_apply,Equiv.swap_apply_def,hσ1] using hj
  · have hky : (C.plank (σ 2)).u.2=1 := (hone (σ 2)).resolve_left hkx
    refine ⟨true,cycle.trans σ,Or.inr (Or.inl ?_)⟩
    refine ⟨(C.plank i).u.2,(C.plank j).u.1,(C.plank (σ 2)).u.1,
      hib,hja,⟨(hu (σ 2)).1,lt_of_le_of_ne (hx (σ 2)) hkx⟩,?_,?_,?_⟩
    · change ((C.plank (σ 1)).u.2,(C.plank (σ 1)).u.1)=(1,(C.plank j).u.1)
      rw [hσ1,hjy]
    · change ((C.plank (σ 2)).u.2,(C.plank (σ 2)).u.1)=(1,(C.plank (σ 2)).u.1)
      rw [hky]
    · change ((C.plank (σ 0)).u.2,(C.plank (σ 0)).u.1)=((C.plank i).u.2,1)
      rw [hσ0,hix]

end Quant.TriangleCommonMinimumDirections

/-- info: 'Quant.TriangleCommonMinimumDirections.exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCommonMinimumDirections.exhaustive
