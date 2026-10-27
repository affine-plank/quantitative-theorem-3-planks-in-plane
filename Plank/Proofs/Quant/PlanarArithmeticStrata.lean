/- Complete two-plank strata and one-support three-plank arithmetic families. -/
module

public import Plank.Proofs.Quant.PlanarFourPointClassification
public import Plank.Proofs.Quant.PlanarEqualityReductions
public import Plank.Proofs.Quant.PlanarOneSupportTripleShape

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarArithmeticStrata

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open PlanarAffineEquality PlanarFourPointClassification
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- All two-plank equality strata, including the two trivial budget
regimes. The positive-deficit branch uses the explicit arithmetic family. -/
def TwoPlankFamily (K : Set Point) (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2) : Prop :=
  budget K f p = 0 ∨
    (1 ≤ budget K f p ∧ K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) ∨
    (0 < budget K f p ∧ budget K f p < 1 ∧ Family K f p.1 p.2)

/-- Exhaustive equality classification for two actual closed planks on
every compact convex positive-area planar body, with no restriction on R. -/
theorem two_plank_iff {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i) :
    Equality K f p.1 p.2 ↔ TwoPlankFamily K f p := by
  have hnonneg : 0 ≤ budget K f p := Finset.sum_nonneg fun i _ =>
    div_nonneg (sub_nonneg.mpr (ho i)) (hW i).le
  constructor
  · intro he
    by_cases hz : budget K f p = 0
    · exact Or.inl hz
    by_cases hb : 1 ≤ budget K f p
    · exact Or.inr (Or.inl ⟨hb,(PlanarEqualityReductions.equality_iff_cover_of_one_le
        hK hc hV f p hb).mp he⟩)
    · have hp := lt_of_le_of_ne hnonneg (Ne.symm hz)
      have hl := lt_of_not_ge hb
      have he' : gapArea K f p = (1-budget K f p)^2*(volume K).toReal := by
        change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at he
        rwa [max_eq_right (sub_pos.mpr hl).le] at he
      exact Or.inr (Or.inr ⟨hp,hl,
        (PlanarFourPointClassification.two_plank_iff hK hc hne hV f p hW ho hp hl).mp he'⟩)
  · rintro (hz | ⟨hb,hcover⟩ | ⟨_,_,hf⟩)
    · exact PlanarEqualityReductions.equality_of_budget_zero hne f p hW ho hz
    · exact (PlanarEqualityReductions.equality_iff_cover_of_one_le hK hc hV f p hb).mpr hcover
    · exact family_sound f p.1 p.2 hW ho hf

/-- The same explicit family is exhaustive for triples with either side
of one physical window at a support level, when the other two have positive
total relative width. The first window can be chosen by reindexing. -/
theorem one_support_triple_iff {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f 0 x ≤ f 0 a) (hmin : ∀ x ∈ K, f 0 b ≤ f 0 x)
    (hface : f 0 b = p.1 0 ∨ f 0 a = p.2 0)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hS : 0 < ∑ i : Fin 2, (p.2 i.succ-p.1 i.succ)/rangeWidth K (f i.succ))
    (hR : budget K f p < 1) :
    Equality K f p.1 p.2 ↔ Family K f p.1 p.2 := by
  constructor
  · intro he
    have hset : (⋃ i : Fin 3, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) =
        {x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} ∪
          ⋃ i : Fin 2, {x | p.1 i.succ ≤ f i.succ x ∧ f i.succ x ≤ p.2 i.succ} := by
      ext x
      simp only [mem_iUnion,mem_union,Fin.exists_fin_succ]
    have hs := PlanarOneSupportTripleShape.four_vertices_of_support hK hc hV (f 0)
      (fun i : Fin 2 => f i.succ) a b ha hb hmax hmin (p.1 0) (p.2 0)
      (fun i => p.1 i.succ) (fun i => p.2 i.succ) hface (ho 0)
      (fun i => ho i.succ) (hW 0) (fun i => hW i.succ) hS
      (by simpa only [budget,Fin.sum_univ_succ] using hR)
      (by simpa only [Equality,hset,Fin.sum_univ_succ,sub_add_eq_sub_sub] using he)
    exact (equality_iff_of_four_vertices hV hs f p.1 p.2 hW ho).mp he
  · exact family_sound f p.1 p.2 hW ho

end Plank.PlanarArithmeticStrata

/-- info: 'Plank.PlanarArithmeticStrata.two_plank_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarArithmeticStrata.two_plank_iff
/-- info: 'Plank.PlanarArithmeticStrata.one_support_triple_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarArithmeticStrata.one_support_triple_iff
