/- Continuous partial derivatives of the actual polygonal plank gap area. -/
module

public import Plank.Proofs.Quant.PlanarDirectionDerivatives

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParameterDerivatives

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarPlankCellCharts
open PlanarDirectionDerivatives

/-- Actual uncovered area, on the full pair of endpoint functions. -/
def area {κ : Type*} (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ) (e : EndpointSpace κ) : ℝ :=
  (volume (K \ ⋃ i, {x | e.1 i ≤ f i x ∧ f i x ≤ e.2 i})).toReal

/-- Keep all endpoints except those of the distinguished plank. -/
def otherEndpoints {κ : Type*} (i : κ) (e : EndpointSpace κ) : EndpointSpace {j // j ≠ i} :=
  (fun j => e.1 j, fun j => e.2 j)

theorem continuous_otherEndpoints {κ : Type*} (i : κ) : Continuous (otherEndpoints i) := by
  unfold otherEndpoints
  apply Continuous.prodMk
  · exact continuous_pi (fun j => (continuous_apply (j : κ)).comp continuous_fst)
  · exact continuous_pi (fun j => (continuous_apply (j : κ)).comp continuous_snd)

theorem gap_eq_distinguished {κ : Type*} (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ)
    (lo hi : κ → ℝ) (i : κ) :
    K \ ⋃ j, {x | lo j ≤ f j x ∧ f j x ≤ hi j} =
      distinguishedGap K (fun j : {j // j ≠ i} => f j) (f i)
        (fun j => lo j) (fun j => hi j) (lo i) (hi i) := by
  ext x
  simp only [distinguishedGap, mem_sdiff, mem_iUnion, mem_ofPred_eq, not_exists]
  constructor
  · intro hx
    exact ⟨⟨hx.1, fun j => hx.2 j⟩, hx.2 i⟩
  · intro hx
    refine ⟨hx.1.1, fun j => ?_⟩
    by_cases hji : j = i
    · simpa only [hji] using hx.2
    · exact hx.1.2 ⟨j, hji⟩

theorem area_lower_update {κ : Type*} [DecidableEq κ]
    (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ) (e : EndpointSpace κ) (i : κ) (t : ℝ) :
    area K f (Function.update e.1 i t, e.2) =
      (volume (distinguishedGap K (fun j : {j // j ≠ i} => f j) (f i)
        (fun j => e.1 j) (fun j => e.2 j) t (e.2 i))).toReal := by
  have heq : (fun j : {j : κ // j ≠ i} => Function.update e.1 i t j) =
      (fun j : {j : κ // j ≠ i} => e.1 j) := by
    funext j
    exact Function.update_of_ne j.property t e.1
  simp only [area]
  rw [gap_eq_distinguished K f (Function.update e.1 i t) e.2 i, heq]
  simp only [Function.update_self]

theorem area_upper_update {κ : Type*} [DecidableEq κ]
    (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ) (e : EndpointSpace κ) (i : κ) (t : ℝ) :
    area K f (e.1, Function.update e.2 i t) =
      (volume (distinguishedGap K (fun j : {j // j ≠ i} => f j) (f i)
        (fun j => e.1 j) (fun j => e.2 j) (e.1 i) t)).toReal := by
  have heq : (fun j : {j : κ // j ≠ i} => Function.update e.2 i t j) =
      (fun j : {j : κ // j ≠ i} => e.2 j) := by
    funext j
    exact Function.update_of_ne j.property t e.2
  simp only [area]
  rw [gap_eq_distinguished K f e.1 (Function.update e.2 i t) i, heq]
  simp only [Function.update_self]

/-- Every actual endpoint partial derivative exists for strictly ordered
windows, and one globally continuous coefficient function gives each
partial. The compact finite-half-plane body and all plank directions are
the original geometric data, not an assumed differentiable area model. -/
theorem exists_continuous_partials {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (K : Set Point) (hcompact : IsCompact K)
    (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (hK : K = {x | ∀ j, F j x ≤ C j})
    (f : κ → Point →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (hbody : ∀ i j, cross (f i) (F j) ≠ 0)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) :
    ∃ Dlo Dhi : κ → EndpointSpace κ → ℝ,
      (∀ i, Continuous (Dlo i) ∧ Continuous (Dhi i)) ∧
      ∀ e : EndpointSpace κ, (∀ i, e.1 i < e.2 i) → ∀ i,
        HasDerivAt (fun t => area K f (Function.update e.1 i t, e.2)) (Dlo i e) (e.1 i) ∧
        HasDerivAt (fun t => area K f (e.1, Function.update e.2 i t)) (Dhi i e) (e.2 i) := by
  classical
  have hex (i : κ) := exists_continuous_endpoint_derivatives K hcompact F C hK
    (f i) (hf i) (hbody i) (fun j : {j // j ≠ i} => f j)
    (fun j => hpairs i j (Ne.symm j.property))
  choose L hLc hLd using hex
  refine ⟨(fun i e => L i (otherEndpoints i e, e.1 i)),
    (fun i e => -L i (otherEndpoints i e, e.2 i)), ?_, ?_⟩
  · intro i
    exact ⟨(hLc i).comp ((continuous_otherEndpoints i).prodMk
        ((continuous_apply i).comp continuous_fst)),
      ((hLc i).comp ((continuous_otherEndpoints i).prodMk
        ((continuous_apply i).comp continuous_snd))).neg⟩
  · intro e he i
    have hd := hLd i (fun j => e.1 j) (fun j => e.2 j)
      (fun j => (he j).le) (e.1 i) (e.2 i) (he i)
    exact ⟨hd.1.congr_of_eventuallyEq (Filter.Eventually.of_forall
        (fun t => area_lower_update K f e i t)),
      hd.2.congr_of_eventuallyEq (Filter.Eventually.of_forall
        (fun t => area_upper_update K f e i t))⟩

end Plank.PlanarParameterDerivatives
