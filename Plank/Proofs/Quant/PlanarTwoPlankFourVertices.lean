/- Every positive-deficit two-plank equality has at most four vertices. -/
module

public import Plank.Proofs.Quant.PlanarPairedShape
public import Plank.Proofs.Quant.PlanarTwoPlankPolygon

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarTwoPlankFourVertices

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open Plank.Convex.PlanarTight TwoPlankClassification
open scoped BigOperators Topology

/-- An equality which is not already on a four-vertex body has all
window endpoints strictly inside their normalized support ranges. -/
theorem strict_of_not_four {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : Ranges K (f 0) (f 1))
    (p : Endpoints 2) (hp : p ∈ domain K f)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hf : ¬ ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) :
    ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1 := by
  have hz : ¬ ∃ i, p.1 i = p.2 i := fun h => hf
    (PlanarOnlyOnePositive.two_of_zero_window hK hconv hne hV f p hW
      (fun i => (hp.1 i).2.1) h hR0 hR1 heq)
  have hs (i) : p.1 i < p.2 i :=
    lt_of_le_of_ne (hp.1 i).2.1 (fun he => hz ⟨i,he⟩)
  obtain ⟨hW0,hW1⟩ := PlanarCriticalNormalForm.rangeWidth_eq_one (f 0) (f 1) H
  have hbudget : budget K f p = (p.2 0-p.1 0)+(p.2 1-p.1 1) := by
    simp only [budget,Fin.sum_univ_two,hW0,hW1,div_one]
  have hunion : (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) =
      {x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} ∪
      {x | p.1 1 ≤ f 1 x ∧ f 1 x ≤ p.2 1} := by
    ext x
    simp only [mem_iUnion,Fin.exists_fin_two,mem_union]
  have harea : (volume (K \
      ({x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} ∪
       {x | p.1 1 ≤ f 1 x ∧ f 1 x ≤ p.2 1}))).toReal =
      (1-((p.2 0-p.1 0)+(p.2 1-p.1 1)))^2*(volume K).toReal := by
    simpa only [gapArea,hunion,hbudget] using heq
  have hface (i : Fin 2) (hi : p.1 i = 0 ∨ p.2 i = 1) : False := by
    apply hf
    fin_cases i
    · exact PlanarBoundaryShape.support_pair hK hconv hV (f 0) (f 1) H
        (p.1 0) (p.2 0) (p.1 1) (p.2 1) hi (hp.1 0).2.1 (hs 1)
        (by rwa [← hbudget]) harea
    · apply PlanarBoundaryShape.support_pair hK hconv hV (f 1) (f 0) H.swap
        (p.1 1) (p.2 1) (p.1 0) (p.2 0) hi (hp.1 1).2.1 (hs 0)
      · rw [add_comm,← hbudget]
        exact hR1
      · simpa only [union_comm,add_comm (p.2 1-p.1 1) (p.2 0-p.1 0)] using harea
  intro i
  exact ⟨lt_of_le_of_ne (hp.1 i).1 (fun he => hface i (Or.inl he.symm)),hs i,
    lt_of_le_of_ne (hp.1 i).2.2 (fun he => hface i (Or.inr he))⟩

/-- Simultaneous collapse on an actual equality line has no exceptional
nonquadrilateral stratum. Strict endpoints and interpolation provide the
support-clearance conditions; the complementary cases use parallel rigidity. -/
theorem simultaneous_four {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : Ranges K (f 0) (f 1))
    (hW : ∀ i, 0 < rangeWidth K (f i)) (p z : Endpoints 2) (c : ℝ)
    (hp : ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (hu : ∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2)
    (τ : ℝ) (hτ : 0 < τ) (hq : p+τ • z ∈ domain K f)
    (hz : ∀ i, (p+τ • z).1 i = (p+τ • z).2 i) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨hc,hcrit⟩ := PlanarSimultaneousCollapse.critical_cover_and_copies_at
    hK hconv hne hV f hW p z c (fun i => (hp i).2.1.le) hR0 hR1 heq hd hu τ hτ hz
  let q := p+τ • z
  let r := p+(-(c⁻¹)) • z
  have hrstrict : ∀ i, r.1 i < r.2 i :=
    PlanarCriticalShapeAlternatives.strict_backward p z (fun i => (hp i).2.1)
      τ hτ hz _ (neg_neg_of_pos (inv_pos.mpr hc))
  rcases PlanarCriticalShapeAlternatives.critical_cover_alternatives hconv f H r
      hcrit.1 hrstrict hcrit.2.2.1 with hf | hn
  · exact hf
  have hmix : (1-budget K f p) • q+(1-(1-budget K f p)) • r = p :=
    PlanarSimultaneousExtreme.endpoint_mix f p z c hc.ne' hd τ hz
  have hlo (i) : (1-budget K f p)*q.1 i+budget K f p*r.1 i = p.1 i := by
    have hh := congrArg (fun a : Endpoints 2 => a.1 i) hmix
    change (1-budget K f p)*q.1 i+(1-(1-budget K f p))*r.1 i = p.1 i at hh
    convert hh using 1
    ring
  have hhi (i) : (1-budget K f p)*q.1 i+budget K f p*r.2 i = p.2 i := by
    have hh := congrArg (fun a : Endpoints 2 => a.2 i) hmix
    change (1-budget K f p)*q.2 i+(1-(1-budget K f p))*r.2 i = p.2 i at hh
    rw [← hz i] at hh
    convert hh using 1
    ring
  have hclear (i) : (r.1 i = 0 → 0 < q.1 i) ∧ (r.2 i = 1 → q.1 i < 1) := by
    constructor
    · intro hi
      have hh := hlo i
      rw [hi,mul_zero,add_zero] at hh
      have hpos : 0 < (1-budget K f p)*q.1 i := by rw [hh]; exact (hp i).1
      exact (mul_pos_iff_of_pos_left (sub_pos.mpr hR1)).mp hpos
    · intro hi
      have hh := hhi i
      rw [hi,mul_one] at hh
      have hpos : 0 < (1-budget K f p)*(1-q.1 i) := by nlinarith only [hh,(hp i).2.2]
      exact sub_pos.mp ((mul_pos_iff_of_pos_left (sub_pos.mpr hR1)).mp hpos)
  have hlocations := PlanarSimultaneousExtreme.critical_extreme_locations hK hconv hne hV f hW
    p z c (fun i => (hp i).2.1.le) hR0 hR1 heq hd hu τ hτ hz
  have hloc : PlanarCriticalLocations.Locations K (f 0) (f 1)
      (q.1 0) (q.1 1) (r.1 0) (r.2 0) (r.1 1) (r.2 1) := by
    intro x hx
    rcases hlocations x hx with ⟨i,hi⟩ | ⟨s,hs⟩
    · fin_cases i
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
    · classical
      refine Or.inr (Or.inr ⟨decide (0 ∈ s),decide (1 ∈ s),?_⟩)
      have he : PlanarSingletonCorners.corner K (f 0) (f 1)
          (r.1 0) (r.2 0) (r.1 1) (r.2 1) (decide (0 ∈ s)) (decide (1 ∈ s)) =
          signCell K f r.1 r.2 s := by
        ext y
        by_cases h0 : (0 : Fin 2) ∈ s <;> by_cases h1 : (1 : Fin 2) ∈ s <;>
          simp [PlanarSingletonCorners.corner,signCell,LinearBands.weakCell,
            Fin.forall_fin_two,h0,h1,and_assoc] <;> tauto
      exact he.trans hs
  rcases PlanarCriticalLocations.normal_case hK hconv (f 0) (f 1) H
      (q.1 0) (q.1 1) (r.1 0) (r.2 0) (r.1 1) (r.2 1)
      ⟨(hq.1 0).1,(hq.1 0).2.1.trans (hq.1 0).2.2⟩
      ⟨(hq.1 1).1,(hq.1 1).2.1.trans (hq.1 1).2.2⟩
      ⟨(hclear 0).1,(hclear 0).2,(hclear 1).1,(hclear 1).2⟩ hloc hn with hf | hpair
  · exact hf
  · exact PlanarPairedShape.four_vertices hK hconv hV f H p
      (fun i => (hp i).2.1.le) hR0 hR1 heq hpair

/-- Every normalized two-plank equality with 0<R<1 is on a triangle or
quadrilateral. All line, collapse, cell-count and independence assumptions
are derived from the actual equality. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : Ranges K (f 0) (f 1))
    (p : Endpoints 2) (hp : p ∈ domain K f)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  by_cases hf : ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}
  · exact hf
  obtain ⟨hW0,hW1⟩ := PlanarCriticalNormalForm.rangeWidth_eq_one (f 0) (f 1) H
  have hW : ∀ i, 0 < rangeWidth K (f i) := by
    intro i
    fin_cases i
    · change 0 < rangeWidth K (f 0)
      rw [hW0]
      exact zero_lt_one
    · change 0 < rangeWidth K (f 1)
      rw [hW1]
      exact zero_lt_one
  have hps := strict_of_not_four hK hconv hne hV f H p hp hW hR0 hR1 heq hf
  have hpint := mem_interior_of_strict K f hps hR1
  obtain ⟨z,hzne,c,hc,hd,hu,hline⟩ := PlanarEqualityFullLine.exists_line
    hK hconv hne hV f hW p hpint hR1 heq
  obtain ⟨t,ht,hq,hqnot⟩ := PlanarEqualityChartExit.exists_ray_endpoint
    (isCompact_domain K f) p z hpint hzne
  have hfactor : 0 < 1+t*c := by positivity
  obtain ⟨hqeq,_⟩ := hline t hfactor.le (fun i => (hq.1 i).2.1)
  have hb : budget K f (p+t • z) ≤ budget K f p := by
    have hh := affine_eval_line (deficit K f 1) p z t
    simp only [deficit_apply] at hh
    rw [hd] at hh
    have hn := mul_nonneg (mul_nonneg ht.le (sub_pos.mpr hR1).le) hc
    nlinarith only [hh,hn]
  by_cases hB : 0 < budget K f (p+t • z)
  · exact PlanarBoundaryShape.four_vertices hK hconv hne hV f H
      (p+t • z) hq hqnot hB (hb.trans_lt hR1) hqeq
  · have hB0 : budget K f (p+t • z) = 0 :=
      le_antisymm (le_of_not_gt hB) (budget_nonneg f hW hq)
    have hall : ∀ i, (p+t • z).1 i = (p+t • z).2 i := by
      have hn (i : Fin 2) : 0 ≤ ((p+t • z).2 i-(p+t • z).1 i)/rangeWidth K (f i) :=
        div_nonneg (sub_nonneg.mpr (hq.1 i).2.1) (hW i).le
      intro i
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hB0 i
        (Finset.mem_univ i)
      exact (sub_eq_zero.mp ((div_eq_zero_iff).mp hh |>.resolve_right (hW i).ne')).symm
    exact simultaneous_four hK hconv hne hV f H hW p z c hps hR0 hR1 heq hd hu t ht hq hall

end Plank.PlanarTwoPlankFourVertices

/-- info: 'Plank.PlanarTwoPlankFourVertices.four_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarTwoPlankFourVertices.four_vertices
