/- Splitting an edge band gives a further exact triangle equality family. -/
module
public import Plank.Proofs.Quant.CommonMiddleEdgeFamily

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleSplitEdgeFamily
open Set MeasureTheory CommonMiddleAffineTransport CommonMiddleNullWindow
open CrossedQuadrilateralAttainment Plank.Convex.DeficientHeightTilt

theorem halves_union (p : Plank) : (halfLo p).set ∪ (halfHi p).set = p.set := by
  ext z
  change ((p.lo ≤ dot p.u z ∧ dot p.u z ≤ (p.lo+p.hi)/2) ∨
    ((p.lo+p.hi)/2 ≤ dot p.u z ∧ dot p.u z ≤ p.hi)) ↔
    (p.lo ≤ dot p.u z ∧ dot p.u z ≤ p.hi)
  have hh := p.lo_le_hi
  constructor
  · rintro (h | h) <;> constructor <;> linarith
  · intro h
    by_cases hm : dot p.u z ≤ (p.lo+p.hi)/2
    · exact Or.inl ⟨h.1,hm⟩
    · exact Or.inr ⟨(not_le.mp hm).le,h.2⟩

theorem halves_stack_iff (T : Triangle) (p : Plank) (hp : CommonExtremes T p) :
    PairOrderedStack T (halfLo p) (halfHi p) ↔
      lower T p=(1-p.relWidth T)*slope T p := by
  have hu := upper_eq_lower_add_width T p hp
  simp only [PairOrderedStack,slope_halfLo,slope_halfHi,lower_halfLo,lower_halfHi,
    halfLo_relWidth,halfHi_relWidth,le_refl,true_and]
  constructor
  · rintro (⟨h,_⟩ | ⟨h,h'⟩)
    · linarith only [h]
    · have hw := div_nonneg (sub_nonneg.mpr p.lo_le_hi)
        ((width_eq_span T p hp).symm ▸ (span_pos T p hp).le)
      change 0 ≤ p.relWidth T at hw
      nlinarith only [h,h',hu,hw]
  · intro h
    left
    constructor <;> nlinarith only [h,hu]

/-- A band along the edge joining the minimum and maximum of p preserves
the single-plank calibration of p. The edge width is independent of its
position, subject only to the total budget. -/
theorem edge_single_iff (T : Triangle) (hK : IsCompact T.set)
    (F : (ℝ × ℝ) →ᵃ[ℝ] ℝ) (hA : F T.A=0) (hB : F T.B=0) (hC : F T.C=1)
    (p : Plank) (hp : CommonExtremes T p) (hw : 0 < p.relWidth T)
    (t : ℝ) (ht : 0 ≤ t) (hR : t+p.relWidth T < 1) :
    (volume (T.set \ ({z | 0 ≤ F z ∧ F z ≤ t} ∪ p.set))).toReal =
      (1-t-p.relWidth T)^2*(volume T.set).toReal ↔
      lower T p=(1-p.relWidth T)*slope T p := by
  let q : Fin 2 → Plank := ![halfLo p,halfHi p]
  have hc : ∀ i, CommonExtremes T (q i) := by intro i; fin_cases i <;> exact hp
  have hwq : ∀ i, 0 < (q i).relWidth T := by
    intro i
    fin_cases i
    · exact (halfLo_relWidth T p).symm ▸ half_pos hw
    · exact (halfHi_relWidth T p).symm ▸ half_pos hw
  have hsum : (q 0).relWidth T+(q 1).relWidth T=p.relWidth T := by
    simp only [q,Matrix.cons_val_zero,Matrix.cons_val_one,halfLo_relWidth,halfHi_relWidth]
    ring
  have he := CommonMiddleEdgeFamily.equality_iff_pairStack T hK F hA hB hC q hc hwq t ht
    (by rwa [hsum])
  rw [hsum,CommonMiddleSupportReduction.union_two] at he
  change ((volume (T.set \ ({z | 0 ≤ F z ∧ F z ≤ t} ∪
      ((halfLo p).set ∪ (halfHi p).set)))).toReal =
      (1-t-p.relWidth T)^2*(volume T.set).toReal) ↔
    PairOrderedStack T (halfLo p) (halfHi p) at he
  rw [halves_union] at he
  exact he.trans (halves_stack_iff T p hp)

theorem adjacent_edge_union (F : (ℝ × ℝ) →ᵃ[ℝ] ℝ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    {z | 0 ≤ F z ∧ F z ≤ s} ∪ {z | s ≤ F z ∧ F z ≤ t} =
      {z | 0 ≤ F z ∧ F z ≤ t} := by
  ext z
  constructor
  · rintro (h | h)
    · exact ⟨h.1,h.2.trans hst⟩
    · exact ⟨hs.trans h.1,h.2⟩
  · intro h
    by_cases hz : F z ≤ s
    · exact Or.inl ⟨h.1,hz⟩
    · exact Or.inr ⟨(not_le.mp hz).le,h.2⟩

/-- Exact actual-area iff for two adjacent pieces of an edge band and one
positive band. Both edge pieces use their actual relative widths; neither
piece is required to have positive width. -/
theorem split_edge_equality_iff (T : Triangle) (hK : IsCompact T.set)
    (F : (ℝ × ℝ) →ᵃ[ℝ] ℝ) (hA : F T.A=0) (hB : F T.B=0) (hC : F T.C=1)
    (p : Plank) (hp : CommonExtremes T p) (hw : 0 < p.relWidth T)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (hR : t+p.relWidth T < 1) :
    (volume (T.set \ (({z | 0 ≤ F z ∧ F z ≤ s} ∪
      {z | s ≤ F z ∧ F z ≤ t}) ∪ p.set))).toReal =
      (1-(s/rangeWidth T.set F+(t-s)/rangeWidth T.set F+p.relWidth T))^2*
        (volume T.set).toReal ↔
      lower T p=(1-p.relWidth T)*slope T p := by
  rw [adjacent_edge_union F s t hs hst,TriangleEdgeReduction.edge_rangeWidth T F hA hB hC]
  simp only [div_one]
  rw [show 1-(s+(t-s)+p.relWidth T)=1-t-p.relWidth T by ring]
  exact edge_single_iff T hK F hA hB hC p hp hw t (hs.trans hst) hR

end Quant.TriangleSplitEdgeFamily

/-- info: 'Quant.TriangleSplitEdgeFamily.split_edge_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleSplitEdgeFamily.split_edge_equality_iff
