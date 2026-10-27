/- Equality with equal or complementary normalized coordinates is parallel. -/
module

public import Plank.Proofs.Quant.PlanarCriticalLocations
public import Plank.Proofs.Quant.PlanarParallelConsequences

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPairedShape

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open Plank.Convex.PlanarTight TwoPlankClassification PlanarParallelTranslations

/-- Agreement or complementarity is needed only on the actual body.
The existing parallel classification then forces at most four vertices. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (H : Ranges K (f 0) (f 1)) (p : Endpoints 2) (hp : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hpair : PlanarCriticalLocations.Paired K (f 0) (f 1)) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨a,ha,hfa⟩ := H.maxX
  obtain ⟨b,hb,hfb⟩ := H.minX
  obtain ⟨hW0,hW1⟩ := PlanarCriticalNormalForm.rangeWidth_eq_one (f 0) (f 1) H
  have hbudget : budget K f p = (p.2 0-p.1 0)+(p.2 1-p.1 1) := by
    simp only [budget,Fin.sum_univ_two,hW0,hW1,div_one]
  have hfinish (lo hi : Fin 2 → ℝ) (ho : ∀ i, lo i ≤ hi i)
      (ht : total lo hi = budget K f p)
      (hgap : K \ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} =
        K \ ⋃ i, LinearBands.closedBand (f 0) (lo i) (hi i)) :
      ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
    obtain ⟨c,d,hshape⟩ := PlanarParallelClassification.equality_implies_four_vertices
      hK hconv hV lo hi ho (by rwa [ht]) (by rwa [ht]) (f 0) a b ha hb hfa hfb
      (fun x hx => (H.box x hx).1) (by simpa only [← hgap,ht,gapArea] using heq)
    exact ⟨a,b,c,d,hshape⟩
  rcases hpair with hsame | hcomp
  · apply hfinish p.1 p.2 hp
    · simp only [total,widths,budget,Fin.sum_univ_two,hW0,hW1,div_one]
    · ext x
      by_cases hx : x ∈ K
      · simp only [mem_sdiff,mem_iUnion,Fin.exists_fin_two,LinearBands.closedBand,
          mem_ofPred_eq,hsame x hx]
      · simp only [mem_sdiff,hx,false_and]
  · let lo : Fin 2 → ℝ := ![p.1 0,1-p.2 1]
    let hi : Fin 2 → ℝ := ![p.2 0,1-p.1 1]
    apply hfinish lo hi
    · intro i
      fin_cases i
      · exact hp 0
      · change 1-p.2 1 ≤ 1-p.1 1
        linarith only [hp 1]
    · rw [hbudget]
      simp only [total,widths,Fin.sum_univ_two,lo,hi,Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
    · ext x
      by_cases hx : x ∈ K
      · have hs : (p.1 1 ≤ f 1 x ∧ f 1 x ≤ p.2 1) ↔
            (1-p.2 1 ≤ f 0 x ∧ f 0 x ≤ 1-p.1 1) := by
          rw [hcomp x hx]
          constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith only [h1,h2]
        simp only [mem_sdiff,mem_iUnion,Fin.exists_fin_two,LinearBands.closedBand,
          mem_ofPred_eq,lo,hi,Matrix.cons_val_zero,Matrix.cons_val_one,hs]
      · simp only [mem_sdiff,hx,false_and]

end Plank.PlanarPairedShape

/-- info: 'Plank.PlanarPairedShape.four_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarPairedShape.four_vertices
