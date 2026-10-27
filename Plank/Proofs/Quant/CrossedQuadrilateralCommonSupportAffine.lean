/- Common-support stack classification for arbitrary original affine forms. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonSupportCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCommonSupportAffine
open Set MeasureTheory
open CrossedQuadrilateralAttainment CrossedQuadrilateralDiagonalSplit
open CrossedQuadrilateralCommonSupportCatalogue
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Remove an affine constant while preserving the entire physical band. -/
def physical (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (ho : lo ≤ hi) (hW : 0 < rangeWidth S.body F) : Plank where
  u := (F.linear (1,0),F.linear (0,1))
  lo := lo-F 0
  hi := hi-F 0
  lo_le_hi := sub_le_sub_right ho _
  u_ne_zero := by
    intro hz
    have hx : F.linear (1,0) = 0 := congrArg Prod.fst hz
    have hy : F.linear (0,1) = 0 := congrArg Prod.snd hz
    rcases CrossedQuadrilateralSupport.nonzero_coefficient S F hW with hn | hn
    · exact hn hx
    · exact hn hy

theorem physical_eval (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (ho : lo ≤ hi) (hW : 0 < rangeWidth S.body F) (z : Point) :
    dot (physical S F lo hi ho hW).u z = F z-F 0 := by
  rw [CrossedQuadrilateralSupport.eval_linear F z]
  change F.linear (1,0)*z.1+F.linear (0,1)*z.2 = _
  ring

theorem physical_set (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (ho : lo ≤ hi) (hW : 0 < rangeWidth S.body F) :
    (physical S F lo hi ho hW).set = {z | lo ≤ F z ∧ F z ≤ hi} := by
  ext z
  change (lo-F 0 ≤ dot (physical S F lo hi ho hW).u z ∧
    dot (physical S F lo hi ho hW).u z ≤ hi-F 0) ↔ _
  rw [physical_eval]
  simp only [sub_le_sub_iff_right,Set.mem_ofPred_eq]

theorem physical_width (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (ho : lo ≤ hi) (hW : 0 < rangeWidth S.body F) :
    rangeWidth S.body (direction (physical S F lo hi ho hW).u) = rangeWidth S.body F := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Plank.Body.exists_realisers (compact_body S)
    ⟨0,zero_mem S⟩ F.continuous_of_finiteDimensional
  have hw : rangeWidth S.body F = F a-F b := Plank.Body.width_eq_of_realisers ha hb hmax hmin
  have hp : rangeWidth S.body (direction (physical S F lo hi ho hW).u) =
      (F a-F 0)-(F b-F 0) := by
    have hh := Plank.Body.width_eq_of_realisers (f := direction (physical S F lo hi ho hW).u)
      ha hb (fun z hz => by simpa only [direction_apply,physical_eval,sub_le_sub_iff_right] using hmax z hz)
      (fun z hz => by simpa only [direction_apply,physical_eval,sub_le_sub_iff_right] using hmin z hz)
    change rangeWidth S.body (direction (physical S F lo hi ho hW).u) =
      direction (physical S F lo hi ho hW).u a-direction (physical S F lo hi ho hW).u b at hh
    simpa only [direction_apply,physical_eval] using hh
  rw [hp,hw]
  ring

theorem physical_relativeWidth (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (ho : lo ≤ hi) (hW : 0 < rangeWidth S.body F) :
    relativeWidth S (physical S F lo hi ho hW) = (hi-lo)/rangeWidth S.body F := by
  rw [relativeWidth,physical_width]
  change ((hi-F 0)-(lo-F 0))/_ = _
  ring

def inChart (T : Point ≃ᵃ[ℝ] Point) (F : Point →ᵃ[ℝ] ℝ) : Point →ᵃ[ℝ] ℝ :=
  F.comp T.toAffineMap

theorem width_inChart (S : Shape) (T : Point ≃ᵃ[ℝ] Point) (F : Point →ᵃ[ℝ] ℝ) :
    rangeWidth S.body (inChart T F) = rangeWidth (T '' S.body) F := by
  exact Plank.Body.width_comp_image S.body T.toAffineMap F

def family (S : Shape) (T : Point ≃ᵃ[ℝ] Point) (F : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hW : ∀ i, 0 < rangeWidth (T '' S.body) (F i)) : Fin 3 → Plank :=
  fun i => physical S (inChart T (F i)) (lo i) (hi i) (ho i)
    (by rw [width_inChart]; exact hW i)

theorem family_set (S : Shape) (T : Point ≃ᵃ[ℝ] Point) (F : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hW : ∀ i, 0 < rangeWidth (T '' S.body) (F i)) (i : Fin 3) :
    T '' (family S T F lo hi ho hW i).set = {z | lo i ≤ F i z ∧ F i z ≤ hi i} := by
  rw [family,physical_set]
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hz
    refine ⟨T.symm z,?_,T.apply_symm_apply z⟩
    simpa only [Set.mem_ofPred_eq,inChart,AffineMap.comp_apply,AffineEquiv.coe_toAffineMap,
      T.apply_symm_apply] using hz

theorem family_width (S : Shape) (T : Point ≃ᵃ[ℝ] Point) (F : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hW : ∀ i, 0 < rangeWidth (T '' S.body) (F i)) (i : Fin 3) :
    relativeWidth S (family S T F lo hi ho hW i) = (hi i-lo i)/rangeWidth (T '' S.body) (F i) := by
  rw [family,physical_relativeWidth,width_inChart]

/-- All sets, widths and endpoints here are the original ones. The four
support inequalities per form are the explicit chart-sector assumption.
The right side is precisely the adjacent calibrated band family, including
its direction condition; direction rigidity is not a premise. -/
theorem equality_iff_adjacent (S : Shape) (T : Point ≃ᵃ[ℝ] Point)
    (F : Fin 3 → Point →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (ho : ∀ i, lo i < hi i) (hW : ∀ i, 0 < rangeWidth (T '' S.body) (F i))
    (hs : ∀ i j, F i (T (-S.c,0)) ≤ F i (T (0,S.Y j)) ∧
      F i (T (0,S.Y j)) ≤ F i (T (S.a,0)))
    (hR : (∑ i, (hi i-lo i)/rangeWidth (T '' S.body) (F i)) < 1) :
    (volume ((T '' S.body) \ ⋃ i, {z | lo i ≤ F i z ∧ F i z ≤ hi i})).toReal =
      (1-∑ i, (hi i-lo i)/rangeWidth (T '' S.body) (F i))^2*(volume (T '' S.body)).toReal ↔
      Adjacent S (family S T F lo hi (fun i => (ho i).le) hW) := by
  let P := family S T F lo hi (fun i => (ho i).le) hW
  have hP (i) : CrossedQuadrilateralCommonSupport.CommonSupports S (P i) := by
    intro j
    change dot (P i).u (-S.c,0) ≤ dot (P i).u (0,S.Y j) ∧
      dot (P i).u (0,S.Y j) ≤ dot (P i).u (S.a,0)
    dsimp only [P,family]
    simp only [physical_eval,sub_le_sub_iff_right]
    exact hs i j
  have he := CrossedQuadrilateralCommonSupportCatalogue.equality_iff_adjacent S P hP
    (fun i => by rw [family_width]; exact div_pos (sub_pos.mpr (ho i)) (hW i))
    (by simpa only [P,family_width] using hR)
  have hu : T '' (⋃ i, (P i).set) = ⋃ i, {z | lo i ≤ F i z ∧ F i z ≤ hi i} := by
    rw [Set.image_iUnion]
    exact iUnion_congr fun i => family_set S T F lo hi (fun i => (ho i).le) hW i
  have ht := CrossedQuadrilateralAffine.image_equality_iff T S.body (⋃ i, (P i).set)
    ((1-∑ i, relativeWidth S (P i))^2)
  rw [hu] at ht
  simp only [P,family_width] at he ht
  exact ht.trans he

end Quant.CrossedQuadrilateralCommonSupportAffine

/-- info: 'Quant.CrossedQuadrilateralCommonSupportAffine.equality_iff_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCommonSupportAffine.equality_iff_adjacent
