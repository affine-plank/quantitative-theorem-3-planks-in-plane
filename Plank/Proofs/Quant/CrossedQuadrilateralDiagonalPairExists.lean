/- Every positive three-plank equality has a repeated diagonal direction. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralChartSymmetry

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralDiagonalPairExists
open Plank Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarEqualityReductions
open CrossedQuadrilateralChartSymmetry
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def PairChart (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) : Prop :=
  ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point)
    (e : Equiv.Perm (Fin 3)), K = T '' CrossedQuadrilateralFormDirections.body S ∧
      (f (e 0)).linear (T.linear ![0,1]) = 0 ∧
      (f (e 1)).linear (T.linear ![0,1]) = 0

theorem two_axes_permuted {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) (he : Equality K f p) (e : Equiv.Perm (Fin 3))
    (hx : (f (e 0)).linear (T.linear ![0,1]) = 0)
    (hy : (f (e 1)).linear (T.linear ![1,0]) = 0)
    (hbx : (f (e 2)).linear (T.linear ![1,0]) ≠ 0)
    (hby : (f (e 2)).linear (T.linear ![0,1]) ≠ 0) : False :=
  CrossedQuadrilateralTwoAxesExclusion.original_not_tight hG hV S T hbody
    (fun i => f (e i)) (endpoints e p) (fun i => hW (e i)) (fun i => ho (e i))
    (by rwa [budget_permute]) hx hy hbx hby ((equality_permute e K f p).mpr he)

theorem horizontal_first {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) (he : Equality K f p)
    (h0 : (f 0).linear (T.linear ![1,0]) = 0) : PairChart K f := by
  classical
  have ht : K = transposed T ''
      CrossedQuadrilateralFormDirections.body (CrossedQuadrilateralSupport.transpose S) := by
    rwa [transposed_body]
  by_cases h1x : (f 1).linear (T.linear ![1,0]) = 0
  · exact ⟨CrossedQuadrilateralSupport.transpose S,transposed T,Equiv.refl _,ht,
      by simpa [Equiv.swap_apply_def] using h0,by simpa [Equiv.swap_apply_def] using h1x⟩
  by_cases h2x : (f 2).linear (T.linear ![1,0]) = 0
  · exact ⟨CrossedQuadrilateralSupport.transpose S,transposed T,Equiv.swap 1 2,ht,
      by simpa [Equiv.swap_apply_def] using h0,by simpa [Equiv.swap_apply_def] using h2x⟩
  by_cases h1y : (f 1).linear (T.linear ![0,1]) = 0
  · by_cases h2y : (f 2).linear (T.linear ![0,1]) = 0
    · refine ⟨S,T,(Equiv.swap 1 2).trans (Equiv.swap 0 1),hbody,?_,?_⟩
      · simpa [Equiv.swap_apply_def] using h1y
      · simpa [Equiv.swap_apply_def] using h2y
    · exact (two_axes_permuted hG hV S T hbody f p hW ho hR he (Equiv.swap 0 1)
        (by simpa [Equiv.swap_apply_def] using h1y) (by simpa [Equiv.swap_apply_def] using h0) (by simpa [Equiv.swap_apply_def] using h2x)
        (by simpa [Equiv.swap_apply_def] using h2y)).elim
  by_cases h2y : (f 2).linear (T.linear ![0,1]) = 0
  · exact (two_axes_permuted hG hV S T hbody f p hW ho hR he
      ((Equiv.swap 1 2).trans (Equiv.swap 0 2))
      (by simpa [Equiv.swap_apply_def] using h2y) (by simpa [Equiv.swap_apply_def] using h0) (by simpa [Equiv.swap_apply_def] using h1x)
      (by simpa [Equiv.swap_apply_def] using h1y)).elim
  exact (CrossedQuadrilateralOneAxisExclusion.original_not_tight hG hV S T hbody f p hW ho hR
    h0 (by intro i; fin_cases i; exact h1x; exact h2x)
    (by intro i; fin_cases i; exact h1y; exact h2y) he).elim

/-- The repeated direction and chart are obtained from equality. No prescribed
pair parallelism, overlap, orientation, calibration or cell pattern is assumed. -/
theorem exists_pair {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) (he : Equality K f p) : PairChart K f := by
  classical
  obtain ⟨S,T,hbody⟩ := CrossedQuadrilateralGenuine.exists_model hG hV
  have hR0 : 0 < budget K f p :=
    Finset.sum_pos (fun i _ => div_pos (sub_pos.mpr (ho i)) (hW i)) Finset.univ_nonempty
  obtain ⟨i,_,hi⟩ := CrossedQuadrilateralOneDiagonal.original_in_chart hG hV S T hbody f p
    hW (fun i => (ho i).le) hR0 hR he
  let e := Equiv.swap (0 : Fin 3) i
  let g := fun j => f (e j)
  let q := endpoints e p
  have hgW (j) : 0 < rangeWidth K (g j) := hW (e j)
  have hqo (j) : q.1 j < q.2 j := ho (e j)
  have hqR : budget K g q < 1 := by simpa only [g,q,budget_permute] using hR
  have hqe : Equality K g q := (equality_permute e K f p).mpr he
  have hp : PairChart K g := by
    rcases hi with hx|hy
    · exact horizontal_first hG hV S T hbody g q hgW hqo hqR hqe (by simpa [g,e] using hx)
    · apply horizontal_first hG hV (CrossedQuadrilateralSupport.transpose S) (transposed T)
        (by rwa [transposed_body]) g q hgW hqo hqR hqe
      simpa [g,e] using hy
  obtain ⟨S',T',e',hb,h0,h1⟩ := hp
  exact ⟨S',T',e'.trans e,hb,h0,h1⟩

end Quant.CrossedQuadrilateralDiagonalPairExists

/-- info: 'Quant.CrossedQuadrilateralDiagonalPairExists.exists_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralDiagonalPairExists.exists_pair
