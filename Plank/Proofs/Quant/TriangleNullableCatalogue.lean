/- Complete nullable/noncyclic triangle catalogue; strict cyclic remainder. -/
module
public import Plank.Proofs.Quant.TriangleSingleCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleNullableCatalogue
open Set MeasureTheory Proofs.Basic Proofs.Transport CommonMiddleNullWindow
open TriangleOrientationExhaustion
open scoped BigOperators

def Equality (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  (volume (T.set \ ⋃ i, (p i).set)).toReal =
    (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal

def Zero (p : Fin 3 → Plank) : Prop := ∀ i, (p i).lo=(p i).hi
def One (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  0 < (p 0).relWidth T ∧ (p 1).lo=(p 1).hi ∧ (p 2).lo=(p 2).hi
def Two (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  0 < (p 0).relWidth T ∧ 0 < (p 1).relWidth T ∧ (p 2).lo=(p 2).hi
def Positive (T : Triangle) (p : Fin 3 → Plank) : Prop := ∀ i, 0 < (p i).relWidth T

theorem width_nonneg (T : Triangle) (p : Plank) : 0 ≤ p.relWidth T :=
  div_nonneg (sub_nonneg.mpr p.lo_le_hi) (width_pos T p.u_ne_zero).le

theorem null_of_not_positive (T : Triangle) (p : Plank) (hp : ¬ 0 < p.relWidth T) : p.lo=p.hi := by
  have hw : 0 < T.width p.u := width_pos T p.u_ne_zero
  have hz : p.relWidth T=0 := le_antisymm (le_of_not_gt hp) (width_nonneg T p)
  have hn : p.hi-p.lo=0 := (div_eq_zero_iff).mp hz |>.resolve_right hw.ne'
  linarith only [hn]

theorem activity_split (T : Triangle) (p : Fin 3 → Plank) :
    Zero p ∨ (∃ σ : Equiv.Perm (Fin 3), One T (p ∘ σ)) ∨
      (∃ σ : Equiv.Perm (Fin 3), Two T (p ∘ σ)) ∨ Positive T p := by
  have hn (i) := null_of_not_positive T (p i)
  by_cases h0 : 0 < (p 0).relWidth T
  · by_cases h1 : 0 < (p 1).relWidth T
    · by_cases h2 : 0 < (p 2).relWidth T
      · exact Or.inr (Or.inr (Or.inr (Proofs.Symmetry.forall_fin_three h0 h1 h2)))
      · exact Or.inr (Or.inr (Or.inl ⟨Equiv.refl _,h0,h1,hn 2 h2⟩))
    · by_cases h2 : 0 < (p 2).relWidth T
      · right; right; left
        refine ⟨Equiv.swap 1 2,?_⟩
        simpa [Two,Function.comp_apply,Equiv.swap_apply_def] using And.intro h0 (And.intro h2 (hn 1 h1))
      · exact Or.inr (Or.inl ⟨Equiv.refl _,h0,hn 1 h1,hn 2 h2⟩)
  · by_cases h1 : 0 < (p 1).relWidth T
    · by_cases h2 : 0 < (p 2).relWidth T
      · right; right; left
        refine ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1),?_⟩
        simpa [Two,Function.comp_apply,Equiv.swap_apply_def] using And.intro h1 (And.intro h2 (hn 0 h0))
      · right; left
        refine ⟨Equiv.swap 0 1,?_⟩
        simpa [One,Function.comp_apply,Equiv.swap_apply_def] using And.intro h1 (And.intro (hn 0 h0) (hn 2 h2))
    · by_cases h2 : 0 < (p 2).relWidth T
      · right; left
        refine ⟨Equiv.swap 0 2,?_⟩
        simpa [One,Function.comp_apply,Equiv.swap_apply_def] using And.intro h2 (And.intro (hn 1 h1) (hn 0 h0))
      · left
        exact Proofs.Symmetry.forall_fin_three (hn 0 h0) (hn 1 h1) (hn 2 h2)

theorem union_three (p : Fin 3 → Plank) : (⋃ i, (p i).set)=(p 0).set ∪ (p 1).set ∪ (p 2).set := by
  ext z
  simp [Fin.exists_fin_succ,or_assoc]

theorem sum_permute (T : Triangle) (p : Fin 3 → Plank) (σ : Equiv.Perm (Fin 3)) :
    (∑ i, (p (σ i)).relWidth T)=∑ i, (p i).relWidth T :=
  Equiv.sum_comp σ (fun i => (p i).relWidth T)

theorem equality_permute (T : Triangle) (p : Fin 3 → Plank) (σ : Equiv.Perm (Fin 3)) :
    Equality T (p ∘ σ) ↔ Equality T p := by
  simp only [Equality,Function.comp_apply,
    σ.surjective.iUnion_comp (fun i => (p i).set),sum_permute]

theorem zero_equality (T : Triangle) (p : Fin 3 → Plank) (hz : Zero p) : Equality T p := by
  unfold Equality
  rw [union_three,Fin.sum_univ_three]
  exact TriangleSingleCatalogue.all_null_equality T (p 0) (p 1) (p 2) (hz 0) (hz 1) (hz 2)

theorem one_equality_iff (T : Triangle) (p : Fin 3 → Plank) (h : One T p)
    (hR : (∑ i, (p i).relWidth T) < 1) :
    Equality T p ↔ TriangleSingleCatalogue.Family T (p 0) := by
  have hr : (p 0).relWidth T < 1 := by
    simpa only [Fin.sum_univ_three,null_relWidth T (p 1) h.2.1,
      null_relWidth T (p 2) h.2.2,add_zero] using hR
  unfold Equality
  rw [union_three,Fin.sum_univ_three]
  exact TriangleSingleCatalogue.two_null_equality_iff_family T (p 0) (p 1) (p 2)
    h.1 hr h.2.1 h.2.2

theorem two_equality_iff (T : Triangle) (p : Fin 3 → Plank) (h : Two T p)
    (hR : (∑ i, (p i).relWidth T) < 1) :
    Equality T p ↔ TrianglePairAffineCatalogue.Catalogue T (p 0) (p 1) := by
  have hr : (p 0).relWidth T+(p 1).relWidth T < 1 := by
    simpa only [Fin.sum_univ_three,null_relWidth T (p 2) h.2.2,add_zero] using hR
  unfold Equality
  rw [union_three,Fin.sum_univ_three]
  exact TrianglePairAffineCatalogue.null_third_equality_iff_catalogue T (p 0) (p 1) (p 2)
    h.1 h.2.1 h.2.2 hr

/-- A purely geometric list: arbitrary null lines; one calibrated band;
an ordered pair or inward edge plus calibrated band; or the four
common-extreme positive families. The strict cyclic sector is separate. -/
def Families (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  Zero p ∨
  (∃ σ : Equiv.Perm (Fin 3), One T (p ∘ σ) ∧ TriangleSingleCatalogue.Family T (p (σ 0))) ∨
  (∃ σ : Equiv.Perm (Fin 3), Two T (p ∘ σ) ∧ TrianglePairAffineCatalogue.Catalogue T (p (σ 0)) (p (σ 1))) ∨
  (Positive T p ∧ TriangleCommonExtremeExhaustion.Catalogue T p)

def CyclicRemainder (T : Triangle) (p : Fin 3 → Plank) : Prop := Positive T p ∧ StrictCyclic T p

theorem equality_of_families (T : Triangle) (p : Fin 3 → Plank)
    (hR : (∑ i, (p i).relWidth T) < 1) (hf : Families T p) : Equality T p := by
  rcases hf with hz | ⟨σ,h,hf⟩ | ⟨σ,h,hf⟩ | ⟨hp,hf⟩
  · exact zero_equality T p hz
  · apply (equality_permute T p σ).mp
    exact (one_equality_iff T (p ∘ σ) h (by simpa only [Function.comp_apply,sum_permute] using hR)).mpr hf
  · apply (equality_permute T p σ).mp
    exact (two_equality_iff T (p ∘ σ) h (by simpa only [Function.comp_apply,sum_permute] using hR)).mpr hf
  · obtain ⟨v,hv,hcat⟩ := hf
    exact (TriangleCommonExtremeCatalogue.vertex_equality_iff_catalogue T p v hv hp hR).mpr hcat

/-- Complete equality iff outside the explicitly isolated strict cyclic
positive sector. In particular every null-width stratum is exhausted. -/
theorem equality_iff_families (T : Triangle) (p : Fin 3 → Plank)
    (hR : (∑ i, (p i).relWidth T) < 1) (hc : ¬ CyclicRemainder T p) :
    Equality T p ↔ Families T p := by
  refine ⟨?_,equality_of_families T p hR⟩
  intro he
  rcases activity_split T p with hz | ⟨σ,h⟩ | ⟨σ,h⟩ | hp
  · exact Or.inl hz
  · right; left
    refine ⟨σ,h,?_⟩
    exact (one_equality_iff T (p ∘ σ) h (by simpa only [Function.comp_apply,sum_permute] using hR)).mp
      ((equality_permute T p σ).mpr he)
  · right; right; left
    refine ⟨σ,h,?_⟩
    exact (two_equality_iff T (p ∘ σ) h (by simpa only [Function.comp_apply,sum_permute] using hR)).mp
      ((equality_permute T p σ).mpr he)
  · exact Or.inr (Or.inr (Or.inr ⟨hp,
      (TriangleCommonExtremeExhaustion.noncyclic_equality_iff_catalogue T p
        (fun hs => hc ⟨hp,hs⟩) hp hR).mp he⟩))

theorem null_equality_iff_families (T : Triangle) (p : Fin 3 → Plank)
    (hR : (∑ i, (p i).relWidth T) < 1) (j : Fin 3) (hn : (p j).lo=(p j).hi) :
    Equality T p ↔ Families T p := by
  apply equality_iff_families T p hR
  rintro ⟨hp,_⟩
  have hj := hp j
  rw [null_relWidth T (p j) hn] at hj
  exact (lt_irrefl 0) hj

/-- Exhaustive reduction of every subcritical triangle equality to the
proved catalogue or three positive bands with different strict middles. -/
theorem families_or_strict_cyclic (T : Triangle) (p : Fin 3 → Plank)
    (hR : (∑ i, (p i).relWidth T) < 1) (he : Equality T p) :
    Families T p ∨ CyclicRemainder T p := by
  classical
  by_cases hc : CyclicRemainder T p
  · exact Or.inr hc
  · exact Or.inl ((equality_iff_families T p hR hc).mp he)

end Quant.TriangleNullableCatalogue

/-- info: 'Quant.TriangleNullableCatalogue.equality_iff_families' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleNullableCatalogue.equality_iff_families

/-- info: 'Quant.TriangleNullableCatalogue.families_or_strict_cyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleNullableCatalogue.families_or_strict_cyclic
