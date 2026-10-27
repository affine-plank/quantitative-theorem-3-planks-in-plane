/- A continuous physical model for diagonal cuts and two oblique bands. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralBoundaryNeighborhood

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralBoundaryModel
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralInnerPacking
open CrossedQuadrilateralResidualArea CrossedQuadrilateralThinExtension
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

abbrev State := Plank.PlanarParameterDomain.Endpoints 4

def badLo (p : State) : Fin 2 → ℝ := ![p.1 2,p.1 3]
def badHi (p : State) : Fin 2 → ℝ := ![p.2 2,p.2 3]
def badBudget (S : Shape) (k : Fin 2 → ℝ) (p : State) : ℝ :=
  total S k (badLo p) (badHi p)
def fullBudget (S : Shape) (k : Fin 2 → ℝ) (p : State) : ℝ :=
  budget S (p.1 0) (p.2 0) (p.1 1) (p.2 1)+badBudget S k p
def gap (S : Shape) (k : Fin 2 → ℝ) (p : State) : Set Point :=
  axisGap S (p.1 0) (p.2 0) (p.1 1) (p.2 1) \
    ⋃ i, band (k i) (badLo p i) (badHi p i)
def area (S : Shape) (k : Fin 2 → ℝ) (p : State) : ℝ := (volume (gap S k p)).toReal
def Ordered (p : State) : Prop := ∀ i, p.1 i ≤ p.2 i
def Tight (S : Shape) (k : Fin 2 → ℝ) (p : State) : Prop :=
  area S k p = (1-fullBudget S k p)^2*(volume S.body).toReal

def forms (k : Fin 2 → ℝ) : Fin 4 → Point →ᵃ[ℝ] ℝ :=
  ![direction (1,0),direction (0,1),direction (1,k 0),direction (1,k 1)]

theorem form_width_pos (S : Shape) (k : Fin 2 → ℝ) (i : Fin 4) :
    0 < rangeWidth S.body (forms k i) := by
  fin_cases i <;> simp only [forms,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals apply direction_width_pos S
  all_goals intro h; cases Prod.mk.inj h <;> norm_num at *

theorem gap_eq (S : Shape) (k : Fin 2 → ℝ) (p : State) :
    gap S k p = S.body \ ⋃ i, {z | p.1 i ≤ forms k i z ∧ forms k i z ≤ p.2 i} := by
  ext z
  simp [gap,axisGap,band,CrossedQuadrilateralPlacement.band,
    CrossedQuadrilateralPlacement.coord,forms,badLo,badHi,Fin.exists_fin_succ,
    Fin.forall_fin_succ,dot] <;> tauto

theorem continuous_product_gap {m : ℕ} (S : Shape) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth S.body (f i)) :
    Continuous (fun p : Plank.PlanarParameterDomain.Endpoints m =>
      (volume (S.body \ ⋃ i, {z | p.1 i ≤ f i z ∧ f i z ≤ p.2 i})).toReal) := by
  let K := ParallelProductPlane.coordinates ⁻¹' S.body
  let g (i) := ParallelProductPlane.pullForm (f i)
  have hK : IsCompact K := ParallelProductPlane.compact_preimage (compact_body S)
  have hne : K.Nonempty := ⟨ParallelProductPlane.coordinates.symm 0,by
    change ParallelProductPlane.coordinates (ParallelProductPlane.coordinates.symm 0) ∈ S.body
    simpa using zero_mem S⟩
  have hg (i) : 0 < rangeWidth K (g i) := by
    rw [CrossedQuadrilateralDirections.width_preimage]
    exact hW i
  have hc := Plank.PlanarParameterDomain.continuous_gapArea hK hne g hg
  have he : Plank.PlanarParameterDomain.gapArea K g =
      (fun p : Plank.PlanarParameterDomain.Endpoints m =>
        (volume (S.body \ ⋃ i, {z | p.1 i ≤ f i z ∧ f i z ≤ p.2 i})).toReal) := by
    funext p
    unfold Plank.PlanarParameterDomain.gapArea
    have hs : (K \ ⋃ i, {z | p.1 i ≤ g i z ∧ g i z ≤ p.2 i}) =
        ParallelProductPlane.coordinates ⁻¹' (S.body \ ⋃ i, {z | p.1 i ≤ f i z ∧ f i z ≤ p.2 i}) := by
      ext z
      simp only [K,g,ParallelProductPlane.pullForm_apply,mem_sdiff,mem_preimage,mem_iUnion,mem_ofPred_eq]
    rw [hs,ParallelProductPlane.volume_preimage]
  rwa [he] at hc

theorem continuous_area (S : Shape) (k : Fin 2 → ℝ) : Continuous (area S k) := by
  have he : area S k = (fun p : State =>
      (volume (S.body \ ⋃ i, {z | p.1 i ≤ forms k i z ∧ forms k i z ≤ p.2 i})).toReal) :=
    funext (fun p => congrArg (fun A : Set Point => (volume A).toReal) (gap_eq S k p))
  rw [he]
  exact continuous_product_gap S (forms k) (form_width_pos S k)

theorem continuous_badBudget (S : Shape) (k : Fin 2 → ℝ) : Continuous (badBudget S k) := by
  unfold badBudget total badLo badHi
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_succ]
  fun_prop

theorem continuous_fullBudget (S : Shape) (k : Fin 2 → ℝ) : Continuous (fullBudget S k) := by
  unfold fullBudget
  have hc : Continuous (fun p : State => budget S (p.1 0) (p.2 0) (p.1 1) (p.2 1)) := by
    unfold budget
    fun_prop
  exact hc.add (continuous_badBudget S k)

theorem bad_ordered {p : State} (hp : Ordered p) (i : Fin 2) : badLo p i ≤ badHi p i := by
  fin_cases i <;> exact hp _

theorem badBudget_nonneg (S : Shape) (k : Fin 2 → ℝ) {p : State} (hp : Ordered p) :
    0 ≤ badBudget S k p := by
  unfold badBudget total
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sub_nonneg.mpr (bad_ordered hp i))
    (direction_width_pos S (u := (1,k i)) (by
      intro h; have hh := congrArg Prod.fst h; norm_num at hh)).le

theorem bad_widths_zero (S : Shape) (k : Fin 2 → ℝ) {p : State} (hp : Ordered p)
    (hz : badBudget S k p = 0) : ∀ i, badLo p i = badHi p i := by
  have hn (i) : 0 ≤ (badHi p i-badLo p i)/rangeWidth S.body (direction (1,k i)) :=
    div_nonneg (sub_nonneg.mpr (bad_ordered hp i))
      (direction_width_pos S (by intro h; have hh := congrArg Prod.fst h; norm_num at hh)).le
  intro i
  change (∑ j, (badHi p j-badLo p j)/rangeWidth S.body (direction (1,k j))) = 0 at hz
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hn j)).mp hz i (Finset.mem_univ i)
  have hw := direction_width_pos S (u := (1,k i)) (by
    intro h; have hh := congrArg Prod.fst h; norm_num at hh)
  have hd := (div_eq_zero_iff).mp hh
  exact (sub_eq_zero.mp (hd.resolve_right hw.ne')).symm

theorem area_eq_axis (S : Shape) (k : Fin 2 → ℝ) {p : State} (hp : Ordered p)
    (hz : badBudget S k p = 0) :
    area S k p = (volume (axisGap S (p.1 0) (p.2 0) (p.1 1) (p.2 1))).toReal := by
  have he := bad_widths_zero S k hp hz
  have hnull (i) : volume (band (k i) (badLo p i) (badHi p i)) = 0 := by
    rw [he i]
    have hs : band (k i) (badHi p i) (badHi p i) =
        {z : Point | dot (1,k i) z = badHi p i} := by
      ext z
      simp only [band,mem_ofPred_eq,dot,one_mul]
      exact ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩
    rw [hs]
    exact volume_line (by intro h; have hh := congrArg Prod.fst h; norm_num at hh) _
  unfold area gap
  rw [measure_sdiff_null (measure_iUnion_null hnull)]

theorem balanced_of_null_tight (S : Shape) (k : Fin 2 → ℝ) {p : State} (hp : Ordered p)
    (hz : badBudget S k p = 0) (hR : fullBudget S k p < 1) (he : Tight S k p) :
    (p.2 0 = p.1 0 ∨ p.2 0/S.a = -p.1 0/S.c) ∧
    (p.2 1 = p.1 1 ∨ p.2 1/S.b = -p.1 1/S.d) := by
  have hb : fullBudget S k p = budget S (p.1 0) (p.2 0) (p.1 1) (p.2 1) := by
    rw [fullBudget,hz,add_zero]
  unfold Tight at he
  rw [area_eq_axis S k hp hz,hb] at he
  rw [hb] at hR
  apply (CrossedQuadrilateralPlacement.arbitrary_placement_equality_iff S _ _ _ _
    (hp 0) (hp 1) hR).mp
  have hh : 1-(p.2 0-p.1 0)/(S.a+S.c)-(p.2 1-p.1 1)/(S.b+S.d) =
      1-budget S (p.1 0) (p.2 0) (p.1 1) (p.2 1) := by unfold budget; ring
  rwa [hh]

end Quant.CrossedQuadrilateralBoundaryModel

/-- info: 'Quant.CrossedQuadrilateralBoundaryModel.balanced_of_null_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralBoundaryModel.balanced_of_null_tight
