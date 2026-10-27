/- A continuous physical realization of two diagonal bands and one oblique band. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralEndpointRescale

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCrossEncoding
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralEndpointRescale
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

abbrev Triple := Plank.PlanarParameterDomain.Endpoints 3

def forms (k : ℝ) : Fin 3 → Point →ᵃ[ℝ] ℝ :=
  ![direction (1,0),direction (0,1),direction (1,k)]

def encode (s c : Fin 3 → ℝ) (p : Triple) : CrossedQuadrilateralBoundaryModel.State :=
  (![lower (s 0) (c 0) (p.1 0) (p.2 0),lower (s 1) (c 1) (p.1 1) (p.2 1),
      lower (s 2) (c 2) (p.1 2) (p.2 2),0],
   ![upper (s 0) (c 0) (p.1 0) (p.2 0),upper (s 1) (c 1) (p.1 1) (p.2 1),
      upper (s 2) (c 2) (p.1 2) (p.2 2),0])

def physicalBudget (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Triple) : ℝ :=
  ∑ i, (p.2 i-p.1 i)/rangeWidth S.body (G i)

def physicalArea (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Triple) : ℝ :=
  (volume (S.body \ ⋃ i, {z | p.1 i ≤ G i z ∧ G i z ≤ p.2 i})).toReal

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
  · exact ordered (hs 0) (ho 0)
  · exact ordered (hs 1) (ho 1)
  · exact ordered (hs 2) (ho 2)
  · exact le_rfl

theorem budget_encode (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (k : ℝ)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple) :
    CrossedQuadrilateralBoundaryModel.fullBudget S ![k,k] (encode s c p) = physicalBudget S G p := by
  have hw (i) := relative_width_eq S (G i) (forms k i) (hs i) (hG i) (p.1 i) (p.2 i)
  simp only [physicalBudget,Fin.sum_univ_three,hw]
  simp [CrossedQuadrilateralBoundaryModel.fullBudget,CrossedQuadrilateralInnerPacking.budget,
    CrossedQuadrilateralBoundaryModel.badBudget,CrossedQuadrilateralThinExtension.total,
    CrossedQuadrilateralBoundaryModel.badLo,CrossedQuadrilateralBoundaryModel.badHi,
    encode,forms,Fin.sum_univ_two,(coordinate_widths S).1,(coordinate_widths S).2]

theorem null_band (k t : ℝ) : volume (CrossedQuadrilateralResidualArea.band k t t) = 0 := by
  have he : CrossedQuadrilateralResidualArea.band k t t = {z : Point | dot (1,k) z = t} := by
    ext z
    simp only [CrossedQuadrilateralResidualArea.band,mem_ofPred_eq,dot,one_mul]
    exact ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩
  rw [he]
  exact volume_line (by intro h; have hh := congrArg Prod.fst h; norm_num at hh) _

theorem gap_encode (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (k : ℝ)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple) :
    CrossedQuadrilateralBoundaryModel.gap S ![k,k] (encode s c p) =
      (S.body \ ⋃ i, {z | p.1 i ≤ G i z ∧ G i z ≤ p.2 i}) \
        CrossedQuadrilateralResidualArea.band k 0 0 := by
  rw [CrossedQuadrilateralBoundaryModel.gap_eq]
  have he (i) := band_eq (G i) (forms k i) (hs i) (hG i) (p.1 i) (p.2 i)
  simp_rw [he]
  ext z
  simp [encode,forms,CrossedQuadrilateralBoundaryModel.forms,CrossedQuadrilateralResidualArea.band,
    Fin.exists_fin_succ,Fin.forall_fin_succ,dot] <;> tauto

theorem area_encode (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (k : ℝ)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple) :
    CrossedQuadrilateralBoundaryModel.area S ![k,k] (encode s c p) = physicalArea S G p := by
  unfold CrossedQuadrilateralBoundaryModel.area
  rw [gap_encode S G k s c hs hG,measure_sdiff_null (null_band k 0)]
  rfl

theorem tight_encode (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) (k : ℝ)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple)
    (he : physicalArea S G p = (1-physicalBudget S G p)^2*(volume S.body).toReal) :
    CrossedQuadrilateralBoundaryModel.Tight S ![k,k] (encode s c p) := by
  unfold CrossedQuadrilateralBoundaryModel.Tight
  rwa [area_encode S G k s c hs hG,budget_encode S G k s c hs hG]

theorem positive_bad_iff (S : Shape) (k : ℝ) (s c : Fin 3 → ℝ) (hs : s 2 ≠ 0) (p : Triple) :
    0 < CrossedQuadrilateralBoundaryModel.badBudget S ![k,k] (encode s c p) ↔ p.1 2 < p.2 2 := by
  have hw : 0 < rangeWidth S.body (direction (1,k)) :=
    direction_width_pos S (by intro h; have hh := congrArg Prod.fst h; norm_num at hh)
  simp [CrossedQuadrilateralBoundaryModel.badBudget,CrossedQuadrilateralThinExtension.total,
    CrossedQuadrilateralBoundaryModel.badLo,CrossedQuadrilateralBoundaryModel.badHi,
    encode,Fin.sum_univ_two,div_pos_iff_of_pos_right hw,sub_pos,positive_iff hs]

theorem bad_witness (S : Shape) (G : Fin 3 → Point →ᵃ[ℝ] ℝ) {k : ℝ} (hk : k ≠ 0)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hG : ∀ i z, G i z = s i*forms k i z+c i) (p : Triple)
    (hp : 0 < CrossedQuadrilateralBoundaryModel.badBudget S ![k,k] (encode s c p)) :
    p.1 2 < p.2 2 ∧ ¬((G 2).linear (1,0) = 0 ∨ (G 2).linear (0,1) = 0) := by
  have hc := coefficients (G 2) (1,k) (hG 2)
  refine ⟨(positive_bad_iff S k s c (hs 2) p).mp hp,?_⟩
  rw [hc.1,hc.2,mul_one]
  exact not_or.mpr ⟨hs 2,mul_ne_zero (hs 2) hk⟩

end Quant.CrossedQuadrilateralCrossEncoding

/-- info: 'Quant.CrossedQuadrilateralCrossEncoding.tight_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCrossEncoding.tight_encode
