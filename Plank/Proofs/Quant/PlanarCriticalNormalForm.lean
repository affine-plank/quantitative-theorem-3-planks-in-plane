/- The critical cover arising from simultaneous collapse has an explicit normal form. -/
module

public import Plank.Proofs.Quant.PlanarSimultaneousCollapse
public import Plank.Convex.PlanarTight.TwoPlankComplete

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCriticalNormalForm

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts
open PlanarShiftedDomain (deficit)
open Plank.Convex.DeficientHeightTilt
open Plank.Convex.PlanarTight
open scoped BigOperators

/-- The attained unit ranges used by the full-cover classification have
exactly the actual widths in the quantitative formula. -/
theorem rangeWidth_eq_one {K : Set Point} (X Y : Point →ᵃ[ℝ] ℝ)
    (H : TwoPlankClassification.Ranges K X Y) :
    rangeWidth K X = 1 ∧ rangeWidth K Y = 1 := by
  have hwidth (X : Point →ᵃ[ℝ] ℝ) (hbox : ∀ x ∈ K, 0 ≤ X x ∧ X x ≤ 1)
      (hmin : ∃ x ∈ K, X x = 0) (hmax : ∃ x ∈ K, X x = 1) : rangeWidth K X = 1 := by
    obtain ⟨a,ha,hXa⟩ := hmax
    obtain ⟨b,hb,hXb⟩ := hmin
    have hh : rangeWidth K X = X a-X b := Body.width_eq_of_realisers ha hb
      (fun x hx => (hbox x hx).2.trans_eq hXa.symm)
      (fun x hx => hXb.trans_le (hbox x hx).1)
    simpa only [hXa,hXb,sub_zero] using hh
  exact ⟨hwidth X (fun x hx => (H.box x hx).1) H.minX H.maxX,
    hwidth Y (fun x hx => (H.box x hx).2) H.minY H.maxY⟩

/-- A total-relative-width-one actual cover has one of the explicit
full-cover normal forms, with no clipping or positive-window premise. -/
theorem normal_of_critical_cover {K : Set Point} (hconv : Convex ℝ K)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (H : TwoPlankClassification.Ranges K (f 0) (f 1)) (r : Endpoints 2)
    (hR : budget K f r = 1) (ho : ∀ i, r.1 i ≤ r.2 i)
    (hcover : K ⊆ ⋃ i, {x | r.1 i ≤ f i x ∧ f i x ≤ r.2 i}) :
    TwoPlankComplete.Normal K (f 0) (f 1) (r.1 0) (r.2 0) (r.1 1) (r.2 1) := by
  obtain ⟨hW0,hW1⟩ := rangeWidth_eq_one (f 0) (f 1) H
  apply (TwoPlankComplete.tight_iff K hconv (f 0) (f 1) H
    (r.1 0) (r.2 0) (r.1 1) (r.2 1) (ho 0) (ho 1)).mp
  refine ⟨?_,?_⟩
  · simpa only [budget,Fin.sum_univ_two,hW0,hW1,div_one] using hR
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover hx)
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi

/-- Simultaneous collapse produces the existing explicit full-cover
normal form together with its exact singleton centers and cell copies.
The critical total-width-one condition is derived from actual equality. -/
theorem normal_and_copies {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (H : TwoPlankClassification.Ranges K (f 0) (f 1))
    (p z : Endpoints 2) (c : ℝ) (hp : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (hu : ∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2)
    (τ : ℝ) (hτ : 0 < τ)
    (hz : ∀ i, (p+τ • z).1 i = (p+τ • z).2 i) :
    ∃ r : Endpoints 2,
      TwoPlankComplete.Normal K (f 0) (f 1) (r.1 0) (r.2 0) (r.1 1) (r.2 1) ∧
      ∀ s, 0 < (volume (signCell K f p.1 p.2 s)).toReal →
        ∃ y : Point, signCell K f r.1 r.2 s = {y} ∧
          signCell K f p.1 p.2 s = AffineMap.homothety y (1-budget K f p) ''
            signCell K f (p+τ • z).1 (p+τ • z).2 s := by
  obtain ⟨hW0,hW1⟩ := rangeWidth_eq_one (f 0) (f 1) H
  have hW : ∀ i, 0 < rangeWidth K (f i) := by
    intro i
    fin_cases i
    · change 0 < rangeWidth K (f 0)
      rw [hW0]
      exact zero_lt_one
    · change 0 < rangeWidth K (f 1)
      rw [hW1]
      exact zero_lt_one
  obtain ⟨_,r,hr,ho,hcover,hcopy⟩ := PlanarSimultaneousCollapse.critical_cover_and_copies
    hK hconv hne hV f hW p z c hp hR0 hR1 heq hd hu τ hτ hz
  exact ⟨r,normal_of_critical_cover hconv f H r hr ho hcover,hcopy⟩

end Plank.PlanarCriticalNormalForm

/-- info: 'Plank.PlanarCriticalNormalForm.normal_and_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCriticalNormalForm.normal_and_copies
