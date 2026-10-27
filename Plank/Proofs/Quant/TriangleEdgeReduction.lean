/- An edge band leaves exactly a homothetic triangle, up to its null boundary. -/
module
public import Plank.Proofs.Quant.CommonMiddleSupportReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleEdgeReduction
open Set MeasureTheory Proofs.Basic Proofs.Transport
open CrossedQuadrilateralAttainment CrossedQuadrilateralCommonSupport
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem affine_barycentric (F : Point →ᵃ[ℝ] ℝ) (A B C : Point)
    (a b c : ℝ) (hs : a+b+c=1) :
    F (a • A+b • B+c • C) = a*F A+b*F B+c*F C := by
  rw [F.decomp]
  simp only [Pi.add_apply,map_add,map_smul,smul_eq_mul]
  have h0 := congrArg (fun x : ℝ => x*F 0) hs
  nlinarith only [h0]

theorem edge_bounds (T : Triangle) (F : Point →ᵃ[ℝ] ℝ)
    (hA : F T.A=0) (hB : F T.B=0) (hC : F T.C=1) :
    ∀ z ∈ T.set, 0 ≤ F z ∧ F z ≤ 1 := by
  rintro z ⟨a,b,c,ha,hb,hc,hs,rfl⟩
  rw [affine_barycentric F T.A T.B T.C a b c hs,hA,hB,hC]
  exact ⟨by simpa using hc,by nlinarith only [ha,hb,hs]⟩

theorem edge_rangeWidth (T : Triangle) (F : Point →ᵃ[ℝ] ℝ)
    (hA : F T.A=0) (hB : F T.B=0) (hC : F T.C=1) :
    rangeWidth T.set F = 1 := by
  have hF := edge_bounds T F hA hB hC
  have hw := Plank.Body.width_eq_of_realisers (f := F) (mem_C T) (mem_A T)
    (fun z hz => by rw [hC]; exact (hF z hz).2)
    (fun z hz => by rw [hA]; exact (hF z hz).1)
  change rangeWidth T.set F = F T.C-F T.A at hw
  simpa only [hC,hA,sub_zero] using hw

/-- The band is based on the entire edge AB; the remaining triangle is
the homothet towards C with ratio 1-t. No other planks enter this identity. -/
theorem edge_cover (T : Triangle) (F : Point →ᵃ[ℝ] ℝ)
    (hA : F T.A=0) (hB : F T.B=0) (hC : F T.C=1)
    (t : ℝ) (ht : t < 1) :
    T.set ⊆ {z | 0 ≤ F z ∧ F z ≤ t} ∪
      AffineMap.homothety T.C (1-t) '' T.set := by
  rintro z ⟨a,b,c,ha,hb,hc,hs,rfl⟩
  have hF : F (a • T.A+b • T.B+c • T.C) = c := by
    rw [affine_barycentric F T.A T.B T.C a b c hs,hA,hB,hC]
    ring
  by_cases hct : c ≤ t
  · exact Or.inl (by simpa only [mem_ofPred_eq,hF] using And.intro hc hct)
  · right
    have hq := sub_pos.mpr ht
    let z := (a/(1-t)) • T.A+(b/(1-t)) • T.B+((c-t)/(1-t)) • T.C
    refine ⟨z,⟨a/(1-t),b/(1-t),(c-t)/(1-t),div_nonneg ha hq.le,
      div_nonneg hb hq.le,div_nonneg (sub_nonneg.mpr (le_of_not_ge hct)) hq.le,?_,rfl⟩,?_⟩
    · field_simp [hq.ne']
      linarith only [hs]
    · simp only [AffineMap.homothety_apply,vadd_eq_add,vsub_eq_sub,z,
        smul_add,smul_sub,smul_smul]
      rw [mul_div_cancel₀ _ hq.ne',mul_div_cancel₀ _ hq.ne',mul_div_cancel₀ _ hq.ne']
      module

/-- Removing an actual edge band is an equivalence with the two original
planks pulled through the homothety. There is no residual cover hypothesis. -/
theorem equality_iff_pulled (T : Triangle) (hK : IsCompact T.set)
    (F : Point →ᵃ[ℝ] ℝ) (hA : F T.A=0) (hB : F T.B=0) (hC : F T.C=1)
    (G : Fin 2 → Point →ᵃ[ℝ] ℝ) (l u : Fin 2 → ℝ)
    (ho : ∀ i, l i ≤ u i) (hW : ∀ i, 0 < rangeWidth T.set (G i))
    (t : ℝ) (ht : 0 ≤ t) (hR : t+∑ i, (u i-l i)/rangeWidth T.set (G i) < 1) :
    (volume (T.set \ ({z | 0 ≤ F z ∧ F z ≤ t} ∪
      ⋃ i, {z | l i ≤ G i z ∧ G i z ≤ u i}))).toReal =
      (1-t-∑ i, (u i-l i)/rangeWidth T.set (G i))^2*(volume T.set).toReal ↔
    (volume (T.set \ ⋃ i, {z | (l i-t*G i T.C)/(1-t) ≤ G i z ∧
      G i z ≤ (u i-t*G i T.C)/(1-t)})).toReal =
      (1-∑ i, ((u i-t*G i T.C)/(1-t)-(l i-t*G i T.C)/(1-t))/
        rangeWidth T.set (G i))^2*(volume T.set).toReal := by
  let C := ParallelProductPlane.coordinates
  let K := C ⁻¹' T.set
  let f := ParallelProductPlane.pullForm F
  let g (i) := ParallelProductPlane.pullForm (G i)
  have hF := edge_bounds T F hA hB hC
  have ht1 : t < 1 := by
    have hsum : 0 ≤ ∑ i, (u i-l i)/rangeWidth T.set (G i) :=
      Finset.sum_nonneg fun i _ => div_nonneg (sub_nonneg.mpr (ho i)) (hW i).le
    linarith only [hR,hsum]
  have hV : 0 < (volume T.set).toReal := by
    rw [AffineTransport.area_triangle]
    exact mul_pos (abs_pos.mpr (det3_ne_zero T)) (by norm_num)
  have hw (i) : rangeWidth (C ⁻¹' T.set) (g i) = rangeWidth T.set (G i) :=
    CrossedQuadrilateralDirections.width_preimage T.set (G i)
  have hg : volume ((C ⁻¹' T.set) \ ({z | 0 ≤ f z ∧ f z ≤ t} ∪
      ⋃ i, {z | l i ≤ g i z ∧ g i z ≤ u i})) =
      volume (T.set \ ({z | 0 ≤ F z ∧ F z ≤ t} ∪
      ⋃ i, {z | l i ≤ G i z ∧ G i z ≤ u i})) := by
    rw [← ParallelProductPlane.volume_preimage]
    simp only [preimage_sdiff,preimage_union,preimage_iUnion]
    rfl
  have hGa (i) : g i (C.symm T.C) = G i T.C := by simp [g,C]
  have hpull : volume ((C ⁻¹' T.set) \ ⋃ i, {z | (l i-t*G i T.C)/(1-t) ≤ g i z ∧
      g i z ≤ (u i-t*G i T.C)/(1-t)}) =
      volume (T.set \ ⋃ i, {z | (l i-t*G i T.C)/(1-t) ≤ G i z ∧
      G i z ≤ (u i-t*G i T.C)/(1-t)}) := by
    rw [← ParallelProductPlane.volume_preimage]
    simp only [preimage_sdiff,preimage_iUnion]
    rfl
  have hcover : K ⊆ ({z | 0 ≤ f z ∧ f z ≤ t} ∪
      ⋃ i, {z | l i ≤ g i z ∧ g i z ≤ u i}) ∪
      AffineMap.homothety (C.symm T.C) (1-t) '' K := by
    intro z hz
    rcases edge_cover T F hA hB hC t ht1 hz with hf | ⟨x,hx,he⟩
    · exact Or.inl (Or.inl hf)
    · right
      refine ⟨C.symm x,by simpa [K,C] using hx,?_⟩
      apply C.injective
      simpa only [AffineMap.homothety_apply,vadd_eq_add,vsub_eq_sub,
        map_add,map_sub,map_smul,C.apply_symm_apply] using he
  have he := Plank.PlanarSupportReduction.equality_three_iff_reduced
    (K := K)
    (ParallelProductPlane.compact_preimage hK) ((convex_triangle T).linear_preimage C.toLinearMap)
    (by rw [ParallelProductPlane.volume_preimage]; exact hV) f g (C.symm T.C) (C.symm T.A)
    (by change C (C.symm T.C) ∈ T.set; rw [C.apply_symm_apply]; exact mem_C T)
    (by change C (C.symm T.A) ∈ T.set; rw [C.apply_symm_apply]; exact mem_A T)
    (by simpa [f,C] using hC) (by simpa [f,C] using hA) (fun z hz => hF (C z) hz)
    t l u ht ho (fun i => by change 0 < rangeWidth (C ⁻¹' T.set) (g i); rw [hw]; exact hW i)
    (by change t+∑ i, (u i-l i)/rangeWidth (C ⁻¹' T.set) (g i) < 1; simpa only [hw] using hR)
  rw [and_iff_left hcover] at he
  dsimp only [K,C] at hw hGa hg hpull he
  simp only [Plank.PlanarSupportPairReduction.pulledEndpoint] at he
  simp_rw [hGa] at he
  simp_rw [hw] at he
  simpa only [Plank.PlanarSupportPairReduction.pulledEndpoint,hGa,hw,hg,hpull,
    ParallelProductPlane.volume_preimage] using he

end Quant.TriangleEdgeReduction

/-- info: 'Quant.TriangleEdgeReduction.equality_iff_pulled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleEdgeReduction.equality_iff_pulled
