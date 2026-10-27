/- One diagonal band and two non-diagonal bands cannot be sharp. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralOneAxisEncoding

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralOneAxisExclusion
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarEqualityReductions
open CrossedQuadrilateralPhysicalCoordinates CrossedQuadrilateralSupportOriginal
open CrossedQuadrilateralOneAxisEncoding
open Plank.Convex.DeficientHeightTilt

theorem realization_not_tight {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (k : Fin 2 → ℝ) (hk : ∀ i, k i ≠ 0)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hf : ∀ i z, productFamily T f i z = s i*forms k i z+c i)
    (p : Endpoints 3) (hp : p ∈ domain K f) (hR : budget K f p < 1)
    (hpos : p.1 1 < p.2 1 ∨ p.1 2 < p.2 2)
    (he : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) : False := by
  apply CrossedQuadrilateralMixedCompact.no_equality_of_realization hG hV S T hbody f hnorm hunit
    k hk (encode s c) (continuous_encode s c) (fun q hq => ordered_encode hs hq)
    (fun q => (budget_encode S _ k s c hs hf q).trans (budget_eq S T hbody f q))
    (fun q _ hq => tight_encode S _ k s c hs hf q (physical_equality S T hbody f q hq))
    ?_ p hp hR ((positive_bad_iff S k s c hs p (fun i => (hp.1 i).2.1)).mpr hpos) he
  intro q hqo hq
  obtain ⟨i,hpos,hbad⟩ := bad_witness S _ k hk s c hs hf q hqo hq
  refine ⟨i,hpos,?_⟩
  rwa [(coefficients T f i).1,(coefficients T f i).2] at hbad

theorem normalized_not_tight {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1)
    (hgood : (f 0).linear (T.linear ![1,0]) = 0)
    (hbadx : ∀ i : Fin 2, (f i.succ).linear (T.linear ![1,0]) ≠ 0)
    (hbady : ∀ i : Fin 2, (f i.succ).linear (T.linear ![0,1]) ≠ 0)
    (he : Equality K f p) : False := by
  let G := productFamily T f
  have hw (i) : 0 < rangeWidth S.body (G i) := by
    rw [width S T hbody f i,hunit]
    exact zero_lt_one
  have h0x : (G 0).linear (1,0) = 0 := by rwa [(coefficients T f 0).1]
  have h0y : (G 0).linear (0,1) ≠ 0 :=
    (CrossedQuadrilateralSupport.nonzero_coefficient S (G 0) (hw 0)).resolve_left
      (not_not.mpr h0x)
  have hix (i : Fin 2) : (G i.succ).linear (1,0) ≠ 0 := by
    rw [(coefficients T f i.succ).1]; exact hbadx i
  have hiy (i : Fin 2) : (G i.succ).linear (0,1) ≠ 0 := by
    rw [(coefficients T f i.succ).2]; exact hbady i
  let k : Fin 2 → ℝ := fun i => (G i.succ).linear (0,1)/(G i.succ).linear (1,0)
  have hk (i) : k i ≠ 0 := div_ne_zero (hiy i) (hix i)
  let s : Fin 3 → ℝ := ![(G 0).linear (0,1),(G 1).linear (1,0),(G 2).linear (1,0)]
  let c : Fin 3 → ℝ := fun i => G i 0
  have hs (i) : s i ≠ 0 := by
    fin_cases i
    · exact h0y
    · exact hix 0
    · exact hix 1
  have hmul (i : Fin 2) : (G i.succ).linear (1,0)*k i = (G i.succ).linear (0,1) := by
    dsimp only [k]
    field_simp [hix i]
  have hf (i : Fin 3) (z : CrossedQuadrilateralAttainment.Point) :
      G i z = s i*forms k i z+c i := by
    fin_cases i
    · change G 0 z = (G 0).linear (0,1)*CrossedQuadrilateralAttainment.direction (0,1) z+G 0 0
      rw [CrossedQuadrilateralSupport.eval_linear,h0x]
      simp [CrossedQuadrilateralAttainment.direction_apply,dot]
    · change G 1 z = (G 1).linear (1,0)*CrossedQuadrilateralAttainment.direction (1,k 0) z+G 1 0
      rw [CrossedQuadrilateralSupport.eval_linear]
      simp only [CrossedQuadrilateralAttainment.direction_apply,dot,one_mul]
      have hh : (G 1).linear (1,0)*k 0 = (G 1).linear (0,1) := hmul 0
      rw [mul_add,← mul_assoc,hh]
    · change G 2 z = (G 2).linear (1,0)*CrossedQuadrilateralAttainment.direction (1,k 1) z+G 2 0
      rw [CrossedQuadrilateralSupport.eval_linear]
      simp only [CrossedQuadrilateralAttainment.direction_apply,dot,one_mul]
      have hh : (G 2).linear (1,0)*k 1 = (G 2).linear (0,1) := hmul 1
      rw [mul_add,← mul_assoc,hh]
  have hp := interior_subset
    (CrossedQuadrilateralTripleInterior.mem_interior hG hV f p hnorm hunit ho hR he)
  apply realization_not_tight hG hV S T hbody f hnorm hunit k hk s c hs hf p hp hR (Or.inl (ho 1))
  change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at he
  rwa [max_eq_right (sub_pos.mpr hR).le] at he

/-- All original scales, orientations, placements and overlaps are permitted.
The first plank is diagonal and the other two are non-diagonal, possibly parallel. -/
theorem original_not_tight {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1)
    (hgood : (f 0).linear (T.linear ![1,0]) = 0)
    (hbadx : ∀ i : Fin 2, (f i.succ).linear (T.linear ![1,0]) ≠ 0)
    (hbady : ∀ i : Fin 2, (f i.succ).linear (T.linear ![0,1]) ≠ 0) (he : Equality K f p) : False := by
  have hK := genuine_compact hG
  have hne : K.Nonempty := by
    rw [hbody]
    exact (CrossedQuadrilateralContainedOriginal.body_nonempty S).image T
  choose g a hg hnorm hunit using fun i => PlanarNormalization.exists_unit_form hK hne (f i) (hW i)
  let q : Endpoints 3 := (fun i => (p.1 i-a i)/rangeWidth K (f i),
    fun i => (p.2 i-a i)/rangeWidth K (f i))
  have hqo (i) : q.1 i < q.2 i :=
    (div_lt_div_iff_of_pos_right (hW i)).mpr (sub_lt_sub_right (ho i) _)
  have hband (i) : {x | q.1 i ≤ g i x ∧ g i x ≤ q.2 i} =
      {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
    ext x
    simp only [mem_ofPred_eq,hg]
    dsimp only [q]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  have hb : budget K g q = budget K f p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hunit]
    dsimp only [q]
    ring
  have hgap : gapArea K g q = gapArea K f p := by simp only [gapArea,hband]
  have hEq : Equality K g q := by
    change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal
    rwa [hgap,hb]
  have hlin (i) := PlanarTransverseNormalization.linear_eq_of_formula (f i) (g i) (a i) _ (hg i)
  have hz (i) (v : Point) (h : (f i).linear v = 0) : (g i).linear v = 0 := by
    rw [hlin,LinearMap.smul_apply,smul_eq_mul,h,mul_zero]
  have hn (i) (v : Point) (h : (f i).linear v ≠ 0) : (g i).linear v ≠ 0 := by
    rw [hlin,LinearMap.smul_apply,smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero (hW i).ne') h
  exact normalized_not_tight hG hV S T hbody g q hnorm hunit hqo (by rwa [hb])
    (hz 0 _ hgood) (fun i => hn i.succ _ (hbadx i)) (fun i => hn i.succ _ (hbady i)) hEq


end Quant.CrossedQuadrilateralOneAxisExclusion

/-- info: 'Quant.CrossedQuadrilateralOneAxisExclusion.original_not_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralOneAxisExclusion.original_not_tight
