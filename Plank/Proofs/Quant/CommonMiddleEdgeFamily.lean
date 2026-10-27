/- The exact edge-band plus common-extreme ordered-pair family on a triangle. -/
module
public import Plank.Proofs.Quant.TriangleEdgeReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CommonMiddleEdgeFamily
open Set MeasureTheory Proofs.Basic Proofs.Transport
open CommonMiddleAffineTransport CommonMiddleNullWindow CommonMiddleSupportReduction
open CrossedQuadrilateralAttainment CrossedQuadrilateralCommonSupport
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem endpoint_rescale (t r s b w : ℝ) (ht : t < 1) :
    ((1-(r+s))*b+w-t*b)/(1-t) =
      (1-(r/(1-t)+s/(1-t)))*b+w/(1-t) := by
  field_simp [(sub_pos.mpr ht).ne']
  ring

/-- The pair-stack positions are unchanged in original coordinates when
an edge band is removed. Its width is separate from the pair's budget. -/
theorem pair_stack_iff_pulled (T : Triangle) (t : ℝ) (ht : t < 1) (p q : Plank)
    (hp : CommonExtremes T p) (hq : CommonExtremes T q) :
    PairOrderedStack T (pulled T t ht p) (pulled T t ht q) ↔
      PairOrderedStack T p q := by
  constructor
  · exact pair_stack_of_pulled T t ht p q hp hq
  · intro hs
    simp only [PairOrderedStack,pulled_slope,pulled_width,pulled_lower T t ht p hp,
      pulled_lower T t ht q hq]
    rcases hs with ⟨hb,hpl,hql⟩ | ⟨hb,hql,hpl⟩
    · left
      refine ⟨hb,?_,?_⟩
      · rw [hpl]
        simpa only [add_zero,zero_div] using
          endpoint_rescale t (p.relWidth T) (q.relWidth T) (slope T p) 0 ht
      · rw [hql]
        exact endpoint_rescale t (p.relWidth T) (q.relWidth T) (slope T q) (p.relWidth T) ht
    · right
      refine ⟨hb,?_,?_⟩
      · rw [hql]
        simpa only [add_zero,zero_div] using
          endpoint_rescale t (p.relWidth T) (q.relWidth T) (slope T q) 0 ht
      · rw [hpl]
        exact endpoint_rescale t (p.relWidth T) (q.relWidth T) (slope T p) (q.relWidth T) ht

/-- An inward band along AB, together with two positive planks whose
minimum and maximum vertices are A,B, is tight exactly when those two
planks form the displayed ordered stack. The edge width t is arbitrary
and nonnegative subject only to the total budget; it need not be positive. -/
theorem equality_iff_pairStack (T : Triangle) (hK : IsCompact T.set)
    (F : Point →ᵃ[ℝ] ℝ) (hA : F T.A=0) (hB : F T.B=0) (hC : F T.C=1)
    (p : Fin 2 → Plank) (hc : ∀ i, CommonExtremes T (p i))
    (hw : ∀ i, 0 < (p i).relWidth T) (t : ℝ) (ht : 0 ≤ t)
    (hR : t+((p 0).relWidth T+(p 1).relWidth T) < 1) :
    (volume (T.set \ ({z | 0 ≤ F z ∧ F z ≤ t} ∪ ⋃ i, (p i).set))).toReal =
      (1-t-((p 0).relWidth T+(p 1).relWidth T))^2*(volume T.set).toReal ↔
      PairOrderedStack T (p 0) (p 1) := by
  have ht1 : t < 1 := by linarith only [hR,hw 0,hw 1]
  let G (i : Fin 2) := direction (p i).u
  have hwidth (i) : rangeWidth T.set (G i) = T.width (p i).u := range_triangle T _ (hc i)
  have hsum : (∑ i, ((p i).hi-(p i).lo)/rangeWidth T.set (G i)) =
      (p 0).relWidth T+(p 1).relWidth T := by
    simp only [hwidth,Fin.sum_univ_two,Plank.relWidth]
  let P (i : Fin 2) := pulled T t ht1 (p i)
  have hsmall : (P 0).relWidth T+(P 1).relWidth T < 1 := by
    simp only [P,pulled_width,← add_div]
    exact (div_lt_one (sub_pos.mpr ht1)).mpr (by linarith only [hR])
  have hred := TriangleEdgeReduction.equality_iff_pulled T hK F hA hB hC G
    (fun i => (p i).lo) (fun i => (p i).hi) (fun i => (p i).lo_le_hi)
    (fun i => by rw [hwidth]; exact width_pos T (p i).u_ne_zero) t ht (by rwa [hsum])
  rw [hsum] at hred
  simp only [hwidth] at hred
  change ((volume (T.set \ ({z | 0 ≤ F z ∧ F z ≤ t} ∪ ⋃ i, (p i).set))).toReal =
      (1-t-((p 0).relWidth T+(p 1).relWidth T))^2*(volume T.set).toReal) ↔
    (volume (T.set \ ⋃ i, (P i).set)).toReal =
      (1-∑ i, (P i).relWidth T)^2*(volume T.set).toReal at hred
  have hpair : ((volume (T.set \ ⋃ i, (P i).set)).toReal =
      (1-∑ i, (P i).relWidth T)^2*(volume T.set).toReal) ↔
      PairOrderedStack T (P 0) (P 1) := by
    let n : Plank := ⟨(p 0).u,0,0,(p 0).u_ne_zero,le_rfl⟩
    have hp := CommonMiddleNullWindow.equality_iff_pairStack T (P 0) (P 1) n (hc 0) (hc 1)
      (by dsimp only [P]; rw [pulled_width]; exact div_pos (hw 0) (sub_pos.mpr ht1))
      (by dsimp only [P]; rw [pulled_width]; exact div_pos (hw 1) (sub_pos.mpr ht1)) rfl hsmall
    rw [area_remove_null T (P 0) (P 1) n rfl,null_relWidth T n rfl,add_zero] at hp
    simpa only [union_two,Fin.sum_univ_two] using hp
  exact hred.trans (hpair.trans (pair_stack_iff_pulled T t ht1 (p 0) (p 1) (hc 0) (hc 1)))

end Quant.CommonMiddleEdgeFamily

/-- info: 'Quant.CommonMiddleEdgeFamily.equality_iff_pairStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonMiddleEdgeFamily.equality_iff_pairStack
