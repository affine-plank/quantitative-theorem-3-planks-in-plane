/- Chart transposition and label permutations preserve actual geometry. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralOneAxisExclusion
public import Plank.Proofs.Quant.CrossedQuadrilateralTwoAxesExclusion
public import Plank.Proofs.Quant.CrossedQuadrilateralDiagonalPairAffine

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralChartSymmetry
open Plank Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarEqualityReductions
open CrossedQuadrilateralSupportOriginal
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def swap : Point ≃ᵃ[ℝ] Point :=
  ((ParallelProductPlane.coordinates.toLinearEquiv.trans (LinearEquiv.prodComm ℝ ℝ ℝ)).trans
    ParallelProductPlane.coordinates.symm.toLinearEquiv).toAffineEquiv

@[simp] theorem swap_apply (x : Point) : swap x = ![x 1,x 0] := by
  ext i; fin_cases i <;> rfl

@[simp] theorem swap_linear_x : swap.linear ![1,0] = ![0,1] := by
  ext i; fin_cases i <;> rfl

@[simp] theorem swap_linear_y : swap.linear ![0,1] = ![1,0] := by
  ext i; fin_cases i <;> rfl

theorem swap_body (S : CrossedQuadrilateralAttainment.Shape) :
    swap '' CrossedQuadrilateralFormDirections.body (CrossedQuadrilateralSupport.transpose S) =
      CrossedQuadrilateralFormDirections.body S := by
  have he := CrossedQuadrilateralSupport.swap_body (CrossedQuadrilateralSupport.transpose S)
  have ht : CrossedQuadrilateralSupport.transpose (CrossedQuadrilateralSupport.transpose S) = S := by
    cases S; rfl
  rw [ht] at he
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change ParallelProductPlane.coordinates (swap y) ∈ S.body
    rw [← he]
    exact ⟨ParallelProductPlane.coordinates y,hy,rfl⟩
  · intro hx
    change ParallelProductPlane.coordinates x ∈ S.body at hx
    rw [← he] at hx
    obtain ⟨y,hy,heq⟩ := hx
    refine ⟨ParallelProductPlane.coordinates.symm y,?_,?_⟩
    · change ParallelProductPlane.coordinates (ParallelProductPlane.coordinates.symm y) ∈ (CrossedQuadrilateralSupport.transpose S).body
      simpa using hy
    · apply ParallelProductPlane.coordinates.injective
      change CrossedQuadrilateralSupport.swap
        (ParallelProductPlane.coordinates (ParallelProductPlane.coordinates.symm y)) = _
      rw [ParallelProductPlane.coordinates.apply_symm_apply]
      exact heq

def transposed (T : Point ≃ᵃ[ℝ] Point) : Point ≃ᵃ[ℝ] Point := swap.trans T

theorem transposed_body (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point) :
    transposed T '' CrossedQuadrilateralFormDirections.body (CrossedQuadrilateralSupport.transpose S) =
      T '' CrossedQuadrilateralFormDirections.body S := by
  rw [← swap_body S,Set.image_image]
  rfl

@[simp] theorem transposed_linear_x (T : Point ≃ᵃ[ℝ] Point) :
    (transposed T).linear ![1,0] = T.linear ![0,1] := by
  change T.linear (swap.linear ![1,0]) = _
  rw [swap_linear_x]

@[simp] theorem transposed_linear_y (T : Point ≃ᵃ[ℝ] Point) :
    (transposed T).linear ![0,1] = T.linear ![1,0] := by
  change T.linear (swap.linear ![0,1]) = _
  rw [swap_linear_y]

def endpoints (e : Equiv.Perm (Fin 3)) (p : Endpoints 3) : Endpoints 3 :=
  (fun i => p.1 (e i),fun i => p.2 (e i))

theorem budget_permute (e : Equiv.Perm (Fin 3)) (K : Set Point)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) :
    budget K (fun i => f (e i)) (endpoints e p) = budget K f p :=
  Equiv.sum_comp e (fun i => (p.2 i-p.1 i)/rangeWidth K (f i))

theorem gap_permute (e : Equiv.Perm (Fin 3)) (K : Set Point)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) :
    gapArea K (fun i => f (e i)) (endpoints e p) =
      gapArea K f p := by
  unfold gapArea
  congr 2
  ext x
  simp only [mem_diff,mem_iUnion,mem_ofPred_eq,endpoints]
  constructor
  · rintro ⟨hx,hn⟩
    refine ⟨hx,?_⟩
    rintro ⟨i,hi⟩
    exact hn ⟨e.symm i,by simpa using hi⟩
  · rintro ⟨hx,hn⟩
    exact ⟨hx,fun ⟨i,hi⟩ => hn ⟨e i,hi⟩⟩

theorem equality_permute (e : Equiv.Perm (Fin 3)) (K : Set Point)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) :
    Equality K (fun i => f (e i)) (endpoints e p) ↔ Equality K f p := by
  change gapArea K (fun i => f (e i)) (endpoints e p) =
    (max 0 (1-budget K (fun i => f (e i)) (endpoints e p)))^2*(volume K).toReal ↔ _
  rw [gap_permute,budget_permute]
  rfl

end Quant.CrossedQuadrilateralChartSymmetry
