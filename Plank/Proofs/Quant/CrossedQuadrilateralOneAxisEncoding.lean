/- A physical realization of one diagonal band and two arbitrary oblique bands. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralPhysicalCoordinates

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralOneAxisEncoding
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralEndpointRescale
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

abbrev Triple := Plank.PlanarParameterDomain.Endpoints 3

def forms (k : Fin 2 → ℝ) : Fin 3 → Point →ᵃ[ℝ] ℝ :=
  ![direction (0,1),direction (1,k 0),direction (1,k 1)]

def encode (s c : Fin 3 → ℝ) (p : Triple) : CrossedQuadrilateralBoundaryModel.State :=
  (![0,lower (s 0) (c 0) (p.1 0) (p.2 0),lower (s 1) (c 1) (p.1 1) (p.2 1),
      lower (s 2) (c 2) (p.1 2) (p.2 2)],
   ![0,upper (s 0) (c 0) (p.1 0) (p.2 0),upper (s 1) (c 1) (p.1 1) (p.2 1),
      upper (s 2) (c 2) (p.1 2) (p.2 2)])

theorem continuous_encode (s c : Fin 3 → ℝ) : Continuous (encode s c) := by
  have hl (i : Fin 3) : Continuous (fun p : Triple => lower (s i) (c i) (p.1 i) (p.2 i)) :=
    (continuous_lower (s i) (c i)).comp (show Continuous (fun p : Triple => (p.1 i,p.2 i)) from by fun_prop)
  have hu (i : Fin 3) : Continuous (fun p : Triple => upper (s i) (c i) (p.1 i) (p.2 i)) :=
    (continuous_upper (s i) (c i)).comp (show Continuous (fun p : Triple => (p.1 i,p.2 i)) from by fun_prop)
  unfold encode
  apply Continuous.prodMk
  all_goals apply continuous_pi; intro i; fin_cases i
  all_goals first
    | exact hl 0 | exact hl 1 | exact hl 2
    | exact hu 0 | exact hu 1 | exact hu 2
    | exact continuous_const

theorem ordered_encode {s c : Fin 3 → ℝ} (hs : ∀ i, s i ≠ 0) {p : Triple}
    (ho : ∀ i, p.1 i ≤ p.2 i) : CrossedQuadrilateralBoundaryModel.Ordered (encode s c p) := by
  intro i
  fin_cases i
  · exact le_rfl
  · exact ordered (hs 0) (ho 0)
  · exact ordered (hs 1) (ho 1)
  · exact ordered (hs 2) (ho 2)

theorem budget_encode (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (k : Fin 2 → ℝ)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple) :
    CrossedQuadrilateralBoundaryModel.fullBudget S k (encode s c p) =
      CrossedQuadrilateralCrossEncoding.physicalBudget S G p := by
  have hw (i) := relative_width_eq S (G i) (forms k i) (hs i) (hG i) (p.1 i) (p.2 i)
  simp only [CrossedQuadrilateralCrossEncoding.physicalBudget,Fin.sum_univ_three,hw]
  simp [CrossedQuadrilateralBoundaryModel.fullBudget,CrossedQuadrilateralInnerPacking.budget,
    CrossedQuadrilateralBoundaryModel.badBudget,CrossedQuadrilateralThinExtension.total,
    CrossedQuadrilateralBoundaryModel.badLo,CrossedQuadrilateralBoundaryModel.badHi,
    encode,forms,Fin.sum_univ_two,(coordinate_widths S).1,(coordinate_widths S).2,add_assoc]

theorem gap_encode (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (k : Fin 2 → ℝ)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple) :
    CrossedQuadrilateralBoundaryModel.gap S k (encode s c p) =
      (S.body \ ⋃ i, {z | p.1 i ≤ G i z ∧ G i z ≤ p.2 i}) \
        CrossedQuadrilateralResidualArea.band 0 0 0 := by
  rw [CrossedQuadrilateralBoundaryModel.gap_eq]
  have he (i) := band_eq (G i) (forms k i) (hs i) (hG i) (p.1 i) (p.2 i)
  simp_rw [he]
  ext z
  simp [encode,forms,CrossedQuadrilateralBoundaryModel.forms,CrossedQuadrilateralResidualArea.band,
    Fin.exists_fin_succ,Fin.forall_fin_succ,dot] <;> tauto

theorem area_encode (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (k : Fin 2 → ℝ)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple) :
    CrossedQuadrilateralBoundaryModel.area S k (encode s c p) =
      CrossedQuadrilateralCrossEncoding.physicalArea S G p := by
  unfold CrossedQuadrilateralBoundaryModel.area
  rw [gap_encode S G k s c hs hG,
    measure_sdiff_null (CrossedQuadrilateralCrossEncoding.null_band 0 0)]
  rfl

theorem tight_encode (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (k : Fin 2 → ℝ)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple)
    (he : CrossedQuadrilateralCrossEncoding.physicalArea S G p =
      (1-CrossedQuadrilateralCrossEncoding.physicalBudget S G p)^2*(volume S.body).toReal) :
    CrossedQuadrilateralBoundaryModel.Tight S k (encode s c p) := by
  unfold CrossedQuadrilateralBoundaryModel.Tight
  rwa [area_encode S G k s c hs hG,budget_encode S G k s c hs hG]

theorem positive_bad_iff (S : Shape) (k : Fin 2 → ℝ) (s c : Fin 3 → ℝ)
    (hs : ∀ i, s i ≠ 0) (p : Triple) (ho : ∀ i, p.1 i ≤ p.2 i) :
    0 < CrossedQuadrilateralBoundaryModel.badBudget S k (encode s c p) ↔
      p.1 1 < p.2 1 ∨ p.1 2 < p.2 2 := by
  have hw (i : Fin 2) : 0 < rangeWidth S.body (direction (1,k i)) :=
    direction_width_pos S (by intro h; have hh := congrArg Prod.fst h; norm_num at hh)
  let w (j : Fin 3) (i : Fin 2) :=
    (upper (s j) (c j) (p.1 j) (p.2 j)-lower (s j) (c j) (p.1 j) (p.2 j)) /
      rangeWidth S.body (direction (1,k i))
  have hn (j : Fin 3) (i : Fin 2) : 0 ≤ w j i :=
    div_nonneg (sub_nonneg.mpr (ordered (hs j) (ho j))) (hw i).le
  have hp (j : Fin 3) (i : Fin 2) : 0 < w j i ↔ p.1 j < p.2 j := by
    dsimp only [w]
    rw [div_pos_iff_of_pos_right (hw i),sub_pos,positive_iff (hs j)]
  have hb : CrossedQuadrilateralBoundaryModel.badBudget S k (encode s c p) = w 1 0+w 2 1 := by
    simp [CrossedQuadrilateralBoundaryModel.badBudget,CrossedQuadrilateralThinExtension.total,
      CrossedQuadrilateralBoundaryModel.badLo,CrossedQuadrilateralBoundaryModel.badHi,encode,
      Fin.sum_univ_two,w]
  rw [hb]
  constructor
  · intro h
    by_contra hno
    have h1 : ¬0 < w 1 0 := fun h1 => hno (Or.inl ((hp 1 0).mp h1))
    have h2 : ¬0 < w 2 1 := fun h2 => hno (Or.inr ((hp 2 1).mp h2))
    linarith
  · rintro (h|h)
    · exact add_pos_of_pos_of_nonneg ((hp 1 0).mpr h) (hn 2 1)
    · exact add_pos_of_nonneg_of_pos (hn 1 0) ((hp 2 1).mpr h)

theorem bad_witness (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (k : Fin 2 → ℝ)
    (hk : ∀ i, k i ≠ 0) (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple)
    (ho : ∀ i, p.1 i ≤ p.2 i)
    (hp : 0 < CrossedQuadrilateralBoundaryModel.badBudget S k (encode s c p)) :
    ∃ i, p.1 i < p.2 i ∧ ¬((G i).linear (1,0) = 0 ∨ (G i).linear (0,1) = 0) := by
  rcases (positive_bad_iff S k s c hs p ho).mp hp with h|h
  · have hc := coefficients (G 1) (1,k 0) (hG 1)
    refine ⟨1,h,?_⟩
    rw [hc.1,hc.2,mul_one]
    exact not_or.mpr ⟨hs 1,mul_ne_zero (hs 1) (hk 0)⟩
  · have hc := coefficients (G 2) (1,k 1) (hG 2)
    refine ⟨2,h,?_⟩
    rw [hc.1,hc.2,mul_one]
    exact not_or.mpr ⟨hs 2,mul_ne_zero (hs 2) (hk 1)⟩

end Quant.CrossedQuadrilateralOneAxisEncoding

/-- info: 'Quant.CrossedQuadrilateralOneAxisEncoding.tight_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralOneAxisEncoding.tight_encode
