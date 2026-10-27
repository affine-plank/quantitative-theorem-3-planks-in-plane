/- The exact cell geometry when an equality line collapses both plank widths. -/
module

public import Plank.Proofs.Quant.PlanarEqualityFullLine
public import Plank.Proofs.Quant.PlanarCellSetRigidity
public import Plank.Proofs.Quant.PlanarCellOffsetLines

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSimultaneousCollapse

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts PlanarCellOffsetLines
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

/-- If both windows of a common-scaling equality line reach zero width
at a positive time, its backward continuation reaches an actual full cover
of total relative width one. Every initially positive sign cell ends at a
single point in that cover, and the initial cell is an exact homothetic
copy of the corresponding cell at the zero-width configuration. -/
theorem critical_cover_and_copies_at {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p z : Endpoints 2) (c : ℝ) (hp : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (hu : ∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2)
    (τ : ℝ) (hτ : 0 < τ)
    (hzero : ∀ i, (p+τ • z).1 i = (p+τ • z).2 i) :
    0 < c ∧ let r : Endpoints 2 := p+(-(c⁻¹)) • z
      budget K f r = 1 ∧
      (∀ i, r.1 i ≤ r.2 i) ∧
      K ⊆ ⋃ i, {x | r.1 i ≤ f i x ∧ f i x ≤ r.2 i} ∧
      ∀ s, 0 < (volume (signCell K f p.1 p.2 s)).toReal →
        ∃ y : Point, signCell K f r.1 r.2 s = {y} ∧
          signCell K f p.1 p.2 s = AffineMap.homothety y (1-budget K f p) ''
            signCell K f (p+τ • z).1 (p+τ • z).2 s := by
  have hdef (t : ℝ) : 1-budget K f (p+t • z) = (1-budget K f p)*(1+t*c) := by
    have hh := affine_eval_line (deficit K f 1) p z t
    simp only [deficit_apply] at hh
    rw [hd] at hh
    nlinarith only [hh]
  have hB0 : budget K f (p+τ • z) = 0 := by
    unfold budget
    apply Finset.sum_eq_zero
    intro i _
    rw [hzero i,sub_self,zero_div]
  have htotal : (1-budget K f p)*(1+τ*c) = 1 := by
    have hh := hdef τ
    rw [hB0,sub_zero] at hh
    exact hh.symm
  have hq : 0 < 1-budget K f p := sub_pos.mpr hR1
  have hc : 0 < c := by
    have hprod : 0 < (1-budget K f p)*(τ*c) := by nlinarith only [htotal,hR0]
    exact (mul_pos_iff_of_pos_left hτ).mp ((mul_pos_iff_of_pos_left hq).mp hprod)
  let t₀ := -(c⁻¹)
  have ht₀c : t₀*c = -1 := by dsimp [t₀]; field_simp
  have ht₀ : t₀ < 0 := neg_neg_of_pos (inv_pos.mpr hc)
  let r := p+t₀ • z
  have horder (t : ℝ) (ht : t ≤ τ) : ∀ i, (p+t • z).1 i ≤ (p+t • z).2 i := by
    intro i
    have hh : p.1 i+τ*z.1 i = p.2 i+τ*z.2 i := hzero i
    have hw : z.2 i-z.1 i ≤ 0 := by nlinarith only [hh,hp i,hτ]
    have hn := mul_nonneg (sub_nonneg.mpr ht) (neg_nonneg.mpr hw)
    change p.1 i+t*z.1 i ≤ p.2 i+t*z.2 i
    nlinarith only [hh,hn]
  have hscale (t : ℝ) (ht : 0 ≤ 1+t*c) (hto : t ≤ τ) :=
    PlanarEqualityFullLine.scaling_eq hK hconv hne f hW p z c hp hR1 heq hd hu
      t ht (horder t hto)
  have hBr : budget K f r = 1 := by
    have hh := hdef t₀
    rw [ht₀c,add_neg_cancel,mul_zero] at hh
    exact sub_eq_zero.mp hh |>.symm
  have hrcov : K ⊆ ⋃ i, {x | r.1 i ≤ f i x ∧ f i x ≤ r.2 i} := by
    apply (PlanarGapAnalysis.gap_area_eq_zero_iff_cover hK hconv hV f r.1 r.2).mp
    have hh := (hscale t₀ (by rw [ht₀c]; norm_num) (ht₀.le.trans hτ.le)).1
    rw [hBr,sub_self,zero_pow (by norm_num),zero_mul] at hh
    exact hh
  refine ⟨hc,hBr,horder t₀ (ht₀.le.trans hτ.le),hrcov,?_⟩
  intro s hs
  have hne₀ : (signCell K f r.1 r.2 s).Nonempty := by
    have hclosed := isClosed_feasible_line hK f s p z
    have hsub : Ioc t₀ 0 ⊆ {t : ℝ | (signCell K f (p+t • z).1 (p+t • z).2 s).Nonempty} := by
      intro t ht
      have hfactor : 0 < 1+t*c := by
        have hh := mul_lt_mul_of_pos_right ht.1 hc
        rw [ht₀c] at hh
        linarith only [hh]
      apply PlanarCellChartCalculus.nonempty_of_area_pos
      rw [(hscale t hfactor.le (ht.2.trans hτ.le)).2 s]
      exact mul_pos hs (sq_pos_of_pos hfactor)
    have hmem : t₀ ∈ closure (Ioc t₀ (0 : ℝ)) := by
      rw [closure_Ioc ht₀.ne]
      exact ⟨le_rfl,ht₀.le⟩
    have hh : t₀ ∈ {t : ℝ | (signCell K f (p+t • z).1 (p+t • z).2 s).Nonempty} :=
      hclosed.closure_subset_iff.mpr hsub hmem
    exact hh
  have hτfactor : 0 < 1+τ*c := by positivity
  have hτarea := (hscale τ hτfactor.le le_rfl).2 s
  have hτpos : 0 < (volume (signCell K f (p+τ • z).1 (p+τ • z).2 s)).toReal := by
    rw [hτarea]
    exact mul_pos hs (sq_pos_of_pos hτfactor)
  have hτne := PlanarCellChartCalculus.nonempty_of_area_pos K f s (p+τ • z) hτpos
  have hcoef : (1-budget K f p)*τ+(1-(1-budget K f p))*t₀ = 0 := by
    apply mul_left_cancel₀ hc.ne'
    have hh : (1-budget K f p)*(τ*c) = budget K f p := by nlinarith only [htotal]
    calc
      _ = (1-budget K f p)*(τ*c)+(1-(1-budget K f p))*(t₀*c) := by ring
      _ = c*0 := by rw [hh,ht₀c]; ring
  have hmix : (1-budget K f p) • (p+τ • z)+(1-(1-budget K f p)) • r = p := by
    calc
      _ = ((1-budget K f p)+(1-(1-budget K f p))) • p+
          ((1-budget K f p)*τ+(1-(1-budget K f p))*t₀) • z := by dsimp [r]; module
      _ = p := by rw [add_sub_cancel,hcoef,one_smul,zero_smul,add_zero]
  have hoff : (1-budget K f p) • cutOffsets f (p+τ • z).1 (p+τ • z).2 s+
      (1-(1-budget K f p)) • cutOffsets f r.1 r.2 s = cutOffsets f p.1 p.2 s := by
    rw [← cutOffsets_mix f s (p+τ • z) r _ _ (by ring),hmix]
  have harea : (volume (PlanarCellArea.cell K (cutForms f s)
      ((1-budget K f p) • cutOffsets f (p+τ • z).1 (p+τ • z).2 s+
      (1-(1-budget K f p)) • cutOffsets f r.1 r.2 s))).toReal =
      (1-budget K f p)^2*(volume (PlanarCellArea.cell K (cutForms f s)
        (cutOffsets f (p+τ • z).1 (p+τ • z).2 s))).toReal := by
    rw [hoff,← signCell_eq_cell,← signCell_eq_cell,hτarea]
    have hh : (1-budget K f p)^2*(1+τ*c)^2 = 1 := by rw [← mul_pow,htotal,one_pow]
    calc
      _ = (volume (signCell K f p.1 p.2 s)).toReal*1 := (mul_one _).symm
      _ = (volume (signCell K f p.1 p.2 s)).toReal*((1-budget K f p)^2*(1+τ*c)^2) := by rw [hh]
      _ = _ := by ring
  obtain ⟨y,hy,hcopy⟩ := PlanarCellSetRigidity.endpoint_singleton_of_tight_interpolation
    hK hconv (cutForms f s) (cutOffsets f (p+τ • z).1 (p+τ • z).2 s)
    (cutOffsets f r.1 r.2 s) (by rwa [← signCell_eq_cell]) (by rwa [← signCell_eq_cell])
    (by rwa [← signCell_eq_cell]) hq (by linarith only [hR0]) harea
  refine ⟨y,by simpa only [← signCell_eq_cell] using hy,?_⟩
  rw [hoff] at hcopy
  simpa only [← signCell_eq_cell] using hcopy

/-- Existential version of the explicit critical-time result, preserving
the public interface used by the boundary-alternative theorems. -/
theorem critical_cover_and_copies {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p z : Endpoints 2) (c : ℝ) (hp : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (hu : ∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2)
    (τ : ℝ) (hτ : 0 < τ)
    (hzero : ∀ i, (p+τ • z).1 i = (p+τ • z).2 i) :
    0 < c ∧ ∃ r : Endpoints 2, budget K f r = 1 ∧
      (∀ i, r.1 i ≤ r.2 i) ∧
      K ⊆ ⋃ i, {x | r.1 i ≤ f i x ∧ f i x ≤ r.2 i} ∧
      ∀ s, 0 < (volume (signCell K f p.1 p.2 s)).toReal →
        ∃ y : Point, signCell K f r.1 r.2 s = {y} ∧
          signCell K f p.1 p.2 s = AffineMap.homothety y (1-budget K f p) ''
            signCell K f (p+τ • z).1 (p+τ • z).2 s := by
  have h := critical_cover_and_copies_at hK hconv hne hV f hW p z c hp hR0 hR1 heq hd hu
    τ hτ hzero
  exact ⟨h.1,p+(-(c⁻¹)) • z,h.2⟩

end Plank.PlanarSimultaneousCollapse

/-- info: 'Plank.PlanarSimultaneousCollapse.critical_cover_and_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSimultaneousCollapse.critical_cover_and_copies
