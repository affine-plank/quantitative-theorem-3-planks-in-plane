/- Extreme-point locations along a simultaneous-collapse equality line. -/
module

public import Plank.Proofs.Quant.PlanarSimultaneousCollapse
public import Plank.Proofs.Quant.PlanarExtremeCells
public import Plank.Proofs.Quant.PlanarStrictCellPositivity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSimultaneousExtreme

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts PlanarCellOffsetLines
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Zero total width at the positive endpoint identifies the exact affine
interpolation between that partition and the critical backward cover. -/
theorem endpoint_mix {m : ℕ} {K : Set Point} (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (p z : Endpoints m) (c : ℝ) (hc : c ≠ 0)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (τ : ℝ) (hz : ∀ i, (p+τ • z).1 i = (p+τ • z).2 i) :
    (1-budget K f p) • (p+τ • z)+(1-(1-budget K f p)) • (p+(-(c⁻¹)) • z) = p := by
  have hB0 : budget K f (p+τ • z) = 0 := by simp [budget,hz]
  have htotal : (1-budget K f p)*(1+τ*c) = 1 := by
    have hh := affine_eval_line (deficit K f 1) p z τ
    simp only [deficit_apply] at hh
    rw [hB0,hd] at hh
    nlinarith only [hh]
  have ht : (-(c⁻¹))*c = -1 := by field_simp
  have hcoef : (1-budget K f p)*τ+(1-(1-budget K f p))*(-(c⁻¹)) = 0 := by
    apply mul_left_cancel₀ hc
    have hh : (1-budget K f p)*(τ*c) = budget K f p := by nlinarith only [htotal]
    calc
      _ = (1-budget K f p)*(τ*c)+(1-(1-budget K f p))*((-(c⁻¹))*c) := by ring
      _ = c*0 := by rw [hh,ht]; ring
  calc
    _ = ((1-budget K f p)+(1-(1-budget K f p))) • p+
        ((1-budget K f p)*τ+(1-(1-budget K f p))*(-(c⁻¹))) • z := by module
    _ = p := by rw [add_sub_cancel,hcoef,one_smul,zero_smul,add_zero]

/-- Every extreme point of the actual body lies on one of the zero-width
partition lines or is itself the singleton of a critical exterior cell.
The equality-line hypotheses are supplied by the existing actual-equality
line theorem. No positive-cell-count premise is needed. -/
theorem critical_extreme_locations {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p z : Endpoints 2) (c : ℝ) (hp : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (hu : ∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2)
    (τ : ℝ) (hτ : 0 < τ) (hz : ∀ i, (p+τ • z).1 i = (p+τ • z).2 i) :
    ∀ x ∈ K.extremePoints ℝ,
      (∃ i, f i x = (p+τ • z).1 i) ∨
      ∃ s, signCell K f (p+(-(c⁻¹)) • z).1 (p+(-(c⁻¹)) • z).2 s = {x} := by
  classical
  obtain ⟨hc,hcrit⟩ := PlanarSimultaneousCollapse.critical_cover_and_copies_at
    hK hconv hne hV f hW p z c hp hR0 hR1 heq hd hu τ hτ hz
  let q := p+τ • z
  let r := p+(-(c⁻¹)) • z
  have hmix : (1-budget K f p) • q+(1-(1-budget K f p)) • r = p :=
    endpoint_mix f p z c hc.ne' hd τ hz
  have hf : 0 < 1+τ*c := by positivity
  have hscale := (PlanarEqualityFullLine.scaling_eq hK hconv hne f hW p z c hp hR1
    heq hd hu τ hf.le (fun i => (hz i).le)).2
  intro x hx
  by_cases hcut : ∃ i, f i x = q.1 i
  · exact Or.inl hcut
  let s := Finset.univ.filter (fun i : Fin 2 => q.1 i < f i x)
  have hs (i : Fin 2) : i ∈ s ↔ q.1 i < f i x := by simp [s]
  have hstrict (i) : cutForms f s i x < cutOffsets f q.1 q.2 s i := by
    have he := affine_eval (f i) x
    by_cases hi : i ∈ s
    · have hh := (hs i).mp hi
      simp only [cutForms,cutOffsets,hi,if_pos]
      change -(f i).linear x < f i 0-q.2 i
      have hqi : q.2 i = q.1 i := (hz i).symm
      rw [hqi]
      linarith only [he,hh]
    · have hh : f i x < q.1 i := lt_of_le_of_ne
        (le_of_not_gt (fun h => hi ((hs i).mpr h))) (fun h => hcut ⟨i,h⟩)
      simp only [cutForms,cutOffsets,hi]
      change (f i).linear x < q.1 i-f i 0
      linarith only [he,hh]
  have hqpos : 0 < (volume (signCell K f q.1 q.2 s)).toReal := by
    rw [signCell_eq_cell]
    exact PlanarStrictCellPositivity.positive_of_strict hK hconv hV _ _ x hx.1 hstrict
  have hppos : 0 < (volume (signCell K f p.1 p.2 s)).toReal := by
    have hh := hscale s
    change (volume (signCell K f q.1 q.2 s)).toReal = _ at hh
    rw [hh] at hqpos
    exact (mul_pos_iff_of_pos_right (sq_pos_of_pos hf)).mp hqpos
  obtain ⟨y,hy,hcopy⟩ := hcrit.2.2.2 s hppos
  have hyv : y ∈ PlanarCellArea.cell K (cutForms f s) (cutOffsets f r.1 r.2 s) := by
    rw [← signCell_eq_cell]
    change y ∈ signCell K f (p+(-(c⁻¹)) • z).1 (p+(-(c⁻¹)) • z).2 s
    rw [hy]
    exact mem_singleton y
  have hm : PlanarCellArea.cell K (cutForms f s)
      ((1-budget K f p) • cutOffsets f q.1 q.2 s+
        (1-(1-budget K f p)) • cutOffsets f r.1 r.2 s) =
      AffineMap.homothety y (1-budget K f p) ''
        PlanarCellArea.cell K (cutForms f s) (cutOffsets f q.1 q.2 s) := by
    rw [← cutOffsets_mix f s q r _ _ (by ring),hmix,← signCell_eq_cell,← signCell_eq_cell]
    exact hcopy
  have hxy := PlanarExtremeCells.extreme_fixed_of_strict_cuts hconv (cutForms f s)
    (cutOffsets f q.1 q.2 s) (cutOffsets f r.1 r.2 s) (1-budget K f p)
    (sub_pos.mpr hR1) (by linarith only [hR0]) y hyv hm x hx hstrict
  refine Or.inr ⟨s,?_⟩
  rw [hxy]
  exact hy

end Plank.PlanarSimultaneousExtreme

/-- info: 'Plank.PlanarSimultaneousExtreme.critical_extreme_locations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSimultaneousExtreme.critical_extreme_locations
