/- The physical endpoints uniquely determine a positive ordered stack. -/
module
public import Plank.Proofs.Quant.CommonMiddleAffineTransport
public import Mathlib.Order.WellFounded

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CommonMiddleStackUnique
open Set
open scoped BigOperators

/-- The three lower-endpoint identities of an ordered stack. -/
def Stack (d : ℝ) (l w b : Fin 3 → ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), b (σ 0) ≤ b (σ 1) ∧ b (σ 1) ≤ b (σ 2) ∧
    l (σ 0) = d*b (σ 0) ∧
    l (σ 1) = d*b (σ 1)+w (σ 0) ∧
    l (σ 2) = d*b (σ 2)+w (σ 0)+w (σ 1)

private theorem lower_strictMono {d : ℝ} {l w b : Fin 3 → ℝ}
    (hd : 0 ≤ d) (hw : ∀ i, 0 < w i) (σ : Equiv.Perm (Fin 3))
    (hb01 : b (σ 0) ≤ b (σ 1)) (hb12 : b (σ 1) ≤ b (σ 2))
    (hl0 : l (σ 0) = d*b (σ 0))
    (hl1 : l (σ 1) = d*b (σ 1)+w (σ 0))
    (hl2 : l (σ 2) = d*b (σ 2)+w (σ 0)+w (σ 1)) :
    StrictMono (fun i => l (σ i)) := by
  have h01 : l (σ 0) < l (σ 1) := by
    rw [hl0,hl1]
    linarith only [mul_le_mul_of_nonneg_left hb01 hd,hw (σ 0)]
  have h12 : l (σ 1) < l (σ 2) := by
    rw [hl1,hl2]
    linarith only [mul_le_mul_of_nonneg_left hb12 hd,hw (σ 1)]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact h01 | exact h01.trans h12 | exact h12 | norm_num at hij

/-- With positive widths and deficit, equal physical endpoints force equal
middle-vertex values, including tied or boundary slopes. -/
theorem unique {d : ℝ} {l w b c : Fin 3 → ℝ}
    (hd : 0 < d) (hw : ∀ i, 0 < w i)
    (hb : Stack d l w b) (hc : Stack d l w c) : b = c := by
  obtain ⟨σ,hb01,hb12,hl0,hl1,hl2⟩ := hb
  obtain ⟨τ,hc01,hc12,hl0',hl1',hl2'⟩ := hc
  have hs := lower_strictMono hd.le hw σ hb01 hb12 hl0 hl1 hl2
  have ht := lower_strictMono hd.le hw τ hc01 hc12 hl0' hl1' hl2'
  have hr : Set.range (fun i => l (σ i)) = Set.range (fun i => l (τ i)) := by
    change Set.range (l ∘ σ) = Set.range (l ∘ τ)
    rw [Set.range_comp,Set.range_comp,σ.surjective.range_eq,τ.surjective.range_eq]
  have he := (hs.range_inj ht).mp hr
  have hl : Function.Injective l := by
    intro i j hij
    have hh : σ.symm i = σ.symm j := hs.injective (by simpa using hij)
    exact σ.symm.injective hh
  have hστ : σ = τ := by
    apply Equiv.ext
    intro i
    exact hl (congrFun he i)
  subst τ
  funext i
  obtain ⟨j,rfl⟩ := σ.surjective i
  fin_cases j
  · change b (σ 0) = c (σ 0)
    exact mul_left_cancel₀ hd.ne' (hl0.symm.trans hl0')
  · change b (σ 1) = c (σ 1)
    apply mul_left_cancel₀ hd.ne'
    linarith only [hl1,hl1']
  · change b (σ 2) = c (σ 2)
    apply mul_left_cancel₀ hd.ne'
    linarith only [hl2,hl2']

open CommonMiddleAffineTransport

theorem stack_of_orderedStack (T : Triangle) (p : Fin 3 → Plank)
    (h : OrderedStack T p) :
    Stack (1-∑ i, (p i).relWidth T) (fun i => lower T (p i))
      (fun i => (p i).relWidth T) (fun i => slope T (p i)) := by
  obtain ⟨σ,h01,h12,hl0,_,hl1,_,hl2,_⟩ := h
  exact ⟨σ,h01,h12,hl0,hl1,hl2⟩

/-- Two triangles sharing their minimum and maximum vertices cannot both
be tight for the same three positive planks unless every plank has equal
normalized values at their third vertices. -/
theorem slope_eq_of_equalities (T U : Triangle) (p : Fin 3 → Plank)
    (hA : T.A = U.A) (hB : T.B = U.B)
    (hT : ∀ i, CommonExtremes T (p i)) (hU : ∀ i, CommonExtremes U (p i))
    (hw : ∀ i, 0 < (p i).relWidth T)
    (hR0 : 0 < ∑ i, (p i).relWidth T) (hR1 : (∑ i, (p i).relWidth T) < 1)
    (heT : (MeasureTheory.volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2 * (MeasureTheory.volume T.set).toReal)
    (heU : (MeasureTheory.volume (U.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth U)^2 * (MeasureTheory.volume U.set).toReal) :
    ∀ i, slope T (p i) = slope U (p i) := by
  have hs (i) : span T (p i) = span U (p i) := by simp only [span,hA,hB]
  have hl (i) : lower T (p i) = lower U (p i) := by simp only [lower,hs,hA]
  have hwidth (i) : (p i).relWidth T = (p i).relWidth U := by
    simp only [Plank.relWidth,width_eq_span T (p i) (hT i),
      width_eq_span U (p i) (hU i),hs]
  have heT' := (equality_iff_orderedStack T p hT hw hR0 hR1).mp heT
  have heU' := (equality_iff_orderedStack U p hU
    (fun i => by rw [← hwidth]; exact hw i)
    (by simpa only [← hwidth] using hR0) (by simpa only [← hwidth] using hR1)).mp heU
  have ht := stack_of_orderedStack T p heT'
  have hu := stack_of_orderedStack U p heU'
  simp only [← hl,← hwidth] at hu
  exact congrFun (unique (sub_pos.mpr hR1) hw ht hu)

end Quant.CommonMiddleStackUnique

/-- info: 'Quant.CommonMiddleStackUnique.slope_eq_of_equalities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonMiddleStackUnique.slope_eq_of_equalities
