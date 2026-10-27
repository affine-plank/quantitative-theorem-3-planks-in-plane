/- The complete two-family catalogue for three positive planks on a quadrilateral. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralDiagonalPairExists

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralTripleCatalogue
open Plank Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarEqualityReductions
open CrossedQuadrilateralChartSymmetry CrossedQuadrilateralPhysicalCoordinates
open CrossedQuadrilateralCrossEncoding CrossedQuadrilateralSupportOriginal
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Actual whole bands and their individual relative widths, in a diagonal chart. -/
def Presented (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point)
    (e : Equiv.Perm (Fin 3)) (P : Fin 3 → _root_.Plank) : Prop :=
  ∀ i, (P i).set = {z | p.1 (e i) ≤ productFamily T f (e i) z ∧
      productFamily T f (e i) z ≤ p.2 (e i)} ∧
    CrossedQuadrilateralAttainment.relativeWidth S (P i) =
      (p.2 (e i)-p.1 (e i))/rangeWidth K (f (e i))

/-- Up to an invertible affine chart and relabelling: three adjacent pieces
of one calibrated diagonal band, or two adjacent pieces of one calibrated
diagonal band together with a calibrated band in the other diagonal direction. -/
def Catalogue (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) : Prop :=
  ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point)
    (e : Equiv.Perm (Fin 3)) (P : Fin 3 → _root_.Plank),
    K = T '' CrossedQuadrilateralFormDirections.body S ∧ Presented K f p S T e P ∧
      CrossedQuadrilateralDiagonalPairCatalogue.Catalogue S P

theorem presented_budget (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point)
    (e : Equiv.Perm (Fin 3)) (P : Fin 3 → _root_.Plank)
    (hp : Presented K f p S T e P) :
    (∑ i, CrossedQuadrilateralAttainment.relativeWidth S (P i)) = budget K f p := by
  simp_rw [fun i => (hp i).2]
  exact Equiv.sum_comp e (fun i => (p.2 i-p.1 i)/rangeWidth K (f i))

theorem presented_area (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point)
    (e : Equiv.Perm (Fin 3)) (P : Fin 3 → _root_.Plank)
    (hp : Presented K f p S T e P) :
    (volume (S.body \ ⋃ i, (P i).set)).toReal =
      physicalArea S (productFamily T (fun i => f (e i))) (endpoints e p) := by
  simp_rw [fun i => (hp i).1]
  rfl

/-- Necessity has no direction, overlap, cell-count, chart or pair hypothesis. -/
theorem of_equality {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) (he : Equality K f p) : Catalogue K f p := by
  obtain ⟨S,T,e,hbody,hy0,hy1⟩ :=
    CrossedQuadrilateralDiagonalPairExists.exists_pair hG hV f p hW ho hR he
  let g := fun i => f (e i)
  let q := endpoints e p
  let G := productFamily T g
  have hw (i) : 0 < rangeWidth S.body (G i) := by rw [width S T hbody]; exact hW (e i)
  let P := fun i => CrossedQuadrilateralCommonSupportAffine.physical S (G i)
    (q.1 i) (q.2 i) (ho (e i)).le (hw i)
  have hp (i) : (P i).lo < (P i).hi := sub_lt_sub_right (ho (e i)) _
  have hpres : Presented K f p S T e P := by
    intro i
    constructor
    · exact CrossedQuadrilateralCommonSupportAffine.physical_set S (G i) _ _ _ _
    · calc
        CrossedQuadrilateralAttainment.relativeWidth S (P i) =
            (q.2 i-q.1 i)/rangeWidth S.body (G i) :=
          CrossedQuadrilateralCommonSupportAffine.physical_relativeWidth S (G i) _ _ _ _
        _ = (p.2 (e i)-p.1 (e i))/rangeWidth K (f (e i)) := by
          rw [width S T hbody g i]
          rfl
  have hb := presented_budget K f p S T e P hpres
  have hqe : gapArea K g q = (1-budget K g q)^2*(volume K).toReal := by
    have hh := (equality_permute e K f p).mpr he
    change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal at hh
    have hhR : budget K g q < 1 := by simpa only [g,q,budget_permute] using hR
    rwa [max_eq_right (sub_pos.mpr hhR).le] at hh
  have hphys := physical_equality S T hbody g q hqe
  have heP : (volume (S.body \ ⋃ i, (P i).set)).toReal =
      (1-∑ i, CrossedQuadrilateralAttainment.relativeWidth S (P i))^2*(volume S.body).toReal := by
    rw [presented_area K f p S T e P hpres,hb]
    rw [budget_eq S T hbody g q,budget_permute] at hphys
    exact hphys
  refine ⟨S,T,e,P,hbody,hpres,?_⟩
  apply (CrossedQuadrilateralDiagonalPairCatalogue.equality_iff_catalogue S P hp ?_ ?_
    (by rwa [hb])).mp heP
  · change (G 0).linear (0,1) = 0
    rw [(coefficients T g 0).2]
    exact hy0
  · change (G 1).linear (0,1) = 0
    rw [(coefficients T g 1).2]
    exact hy1

/-- Every listed physical family really attains the actual quantitative bound. -/
theorem equality_of_catalogue {K : Set Point} (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hR : budget K f p < 1) (hc : Catalogue K f p) : Equality K f p := by
  obtain ⟨S,T,e,P,hbody,hpres,hcat⟩ := hc
  have hb := presented_budget K f p S T e P hpres
  have heP := CrossedQuadrilateralDiagonalPairCatalogue.equality_of_catalogue S P
    (by rwa [hb]) hcat
  rw [presented_area K f p S T e P hpres,hb] at heP
  let g := fun i => f (e i)
  let q := endpoints e p
  apply (equality_permute e K f p).mp
  change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal
  rw [area_eq S T hbody g q,budget_permute,max_eq_right (sub_pos.mpr hR).le,
    body_area S T hbody,heP]
  ring

/-- An exhaustive geometric iff for every three-positive-plank genuine-quadrilateral
configuration at subcritical actual total width. -/
theorem equality_iff_catalogue {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) : Equality K f p ↔ Catalogue K f p :=
  ⟨of_equality hG hV f p hW ho hR,equality_of_catalogue f p hR⟩

end Quant.CrossedQuadrilateralTripleCatalogue

/-- info: 'Quant.CrossedQuadrilateralTripleCatalogue.equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralTripleCatalogue.equality_iff_catalogue
