/- Affine transport of the mixed-direction quadrilateral restrictions. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralTwoWindows

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralImageStrata
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarSevenCellArea PlanarDirectionDerivatives PlanarEqualityReductions
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Express an original affine form in a specified coordinate chart. -/
def pre (T : Point ≃ᵃ[ℝ] Point) (f : Point →ᵃ[ℝ] ℝ) : Point →ᵃ[ℝ] ℝ :=
  f.comp T.toAffineMap

@[simp] theorem pre_apply (T : Point ≃ᵃ[ℝ] Point) (f : Point →ᵃ[ℝ] ℝ) (x : Point) :
    pre T f x = f (T x) := rfl

def factor (T : Point ≃ᵃ[ℝ] Point) : ℝ := |LinearMap.det T.linear.toLinearMap|

theorem factor_pos (T : Point ≃ᵃ[ℝ] Point) : 0 < factor T :=
  abs_pos.mpr T.linear.isUnit_det'.ne_zero

theorem volume_image (T : Point ≃ᵃ[ℝ] Point) (A : Set Point) :
    volume (T '' A) = ENNReal.ofReal (factor T)*volume A := by
  have h (x : Point) : T x = T 0+T.linear x := by
    simpa [add_comm] using T.map_vadd 0 x
  have he : T '' A = (fun x : Point => T 0+x) '' (T.linear '' A) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact h x
  rw [he,Set.image_add_left,measure_preimage_add]
  exact Measure.addHaar_image_linearMap volume T.linear.toLinearMap A

theorem area_image (T : Point ≃ᵃ[ℝ] Point) (A : Set Point) :
    (volume (T '' A)).toReal = factor T*(volume A).toReal := by
  rw [volume_image,ENNReal.toReal_mul,ENNReal.toReal_ofReal (factor_pos T).le]

theorem width_pre (T : Point ≃ᵃ[ℝ] Point) (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) :
    rangeWidth K (pre T f) = rangeWidth (T '' K) f := by
  exact Body.width_comp_image K T.toAffineMap f

theorem budget_pre {m : ℕ} (T : Point ≃ᵃ[ℝ] Point) (K : Set Point)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) :
    budget K (fun i => pre T (f i)) p = budget (T '' K) f p := by
  simp only [budget,width_pre]

theorem image_gap {m : ℕ} (T : Point ≃ᵃ[ℝ] Point) (K : Set Point)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) :
    T '' (K \ ⋃ i, plank (pre T (f i)) (p.1 i) (p.2 i)) =
      (T '' K) \ ⋃ i, plank (f i) (p.1 i) (p.2 i) := by
  rw [Set.image_sdiff T.injective,Set.image_iUnion]
  congr 1
  apply iUnion_congr
  intro i
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hy
    exact ⟨T.symm y,by simpa [plank] using hy,T.apply_symm_apply y⟩

theorem gap_scale {m : ℕ} (T : Point ≃ᵃ[ℝ] Point) (K : Set Point)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) :
    gapArea (T '' K) f p = factor T*gapArea K (fun i => pre T (f i)) p := by
  change (volume ((T '' K) \ ⋃ i, plank (f i) (p.1 i) (p.2 i))).toReal = _
  rw [← image_gap,area_image]
  rfl

theorem equality_iff {m : ℕ} (T : Point ≃ᵃ[ℝ] Point) (K : Set Point)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) :
    Equality (T '' K) f p ↔ Equality K (fun i => pre T (f i)) p := by
  unfold Equality
  rw [gap_scale,area_image,budget_pre]
  rw [show (max 0 (1-budget (T '' K) f p))^2*(factor T*(volume K).toReal) =
    factor T*((max 0 (1-budget (T '' K) f p))^2*(volume K).toReal) by ring]
  exact ⟨mul_left_cancel₀ (factor_pos T).ne',fun h => congrArg (fun x => factor T*x) h⟩

theorem image_cell {m : ℕ} (T : Point ≃ᵃ[ℝ] Point) (K : Set Point)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m) (s : Finset (Fin m)) :
    T '' signCell K (fun i => pre T (f i)) p.1 p.2 s =
      signCell (T '' K) f p.1 p.2 s := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx.1,rfl⟩,hx.2⟩
  · rintro ⟨⟨x,hx,rfl⟩,hy⟩
    exact ⟨x,⟨hx,hy⟩,rfl⟩

theorem nonempty_cells_eq (T : Point ≃ᵃ[ℝ] Point) (K : Set Point)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) :
    PlanarSevenNonemptyCells.nonemptyCells K (fun i => pre T (f i)) p =
      PlanarSevenNonemptyCells.nonemptyCells (T '' K) f p := by
  ext s
  rw [PlanarSevenNonemptyCells.mem_nonemptyCells,PlanarSevenNonemptyCells.mem_nonemptyCells]
  change (signCell K (fun i => pre T (f i)) p.1 p.2 s).Nonempty ↔
    (signCell (T '' K) f p.1 p.2 s).Nonempty
  rw [← image_cell,Set.image_nonempty]

theorem cross_pre_ne_zero (T : Point ≃ᵃ[ℝ] Point) (f g : Point →ᵃ[ℝ] ℝ)
    (hf : (pre T f).linear ≠ 0) (hcross : cross f g ≠ 0) :
    cross (pre T f) (pre T g) ≠ 0 := by
  change cross (f.comp T.toAffineMap) (g.comp T.toAffineMap) ≠ 0
  rw [PlanarPairArea.cross_comp]
  exact mul_ne_zero hcross T.linear.isUnit_det'.ne_zero

theorem pair_pre_subset (T : Point ≃ᵃ[ℝ] Point) (K : Set Point)
    (f g : Point →ᵃ[ℝ] ℝ) (lo hi lo' hi' : ℝ)
    (hc : plank f lo hi ∩ plank g lo' hi' ⊆ T '' K) :
    plank (pre T f) lo hi ∩ plank (pre T g) lo' hi' ⊆ K := by
  intro x hx
  obtain ⟨y,hy,he⟩ := hc hx
  exact T.injective he ▸ hy

theorem triple_null_pre (T : Point ≃ᵃ[ℝ] Point)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hn : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0) :
    volume {x | ∀ i, p.1 i ≤ pre T (f i) x ∧ pre T (f i) x ≤ p.2 i} = 0 := by
  have hs : T '' {x | ∀ i, p.1 i ≤ pre T (f i) x ∧ pre T (f i) x ≤ p.2 i} =
      {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hy
      exact ⟨T.symm y,by simpa using hy,T.apply_symm_apply y⟩
  rw [← hs,volume_image] at hn
  exact (mul_eq_zero.mp hn).resolve_left (ENNReal.ofReal_pos.mpr (factor_pos T)).ne'

theorem concurrent_pre (T : Point ≃ᵃ[ℝ] Point) (K : Set Point)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hc : CrossedQuadrilateralConcurrent.Concurrent (T '' K) f p) :
    CrossedQuadrilateralConcurrent.Concurrent K (fun i => pre T (f i)) p := by
  obtain ⟨z,hz⟩ := hc
  refine ⟨T.symm z,fun i => ?_⟩
  have hi : pre T (f i) '' K = f i '' (T '' K) := by
    rw [Set.image_image]
    rfl
  simpa only [width_pre,pre_apply,T.apply_symm_apply,hi] using hz i

/-- Actual seven-cell strictness on every invertible affine image of the
quadrilateral model. The input forms and widths are in the original coordinates. -/
theorem seven_nonempty_strict (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (T '' CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget (T '' CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcount : 7 ≤ (PlanarSevenNonemptyCells.nonemptyCells
      (T '' CrossedQuadrilateralFormDirections.body S) f p).card) :
    (1-budget (T '' CrossedQuadrilateralFormDirections.body S) f p)^2*
      (volume (T '' CrossedQuadrilateralFormDirections.body S)).toReal <
      gapArea (T '' CrossedQuadrilateralFormDirections.body S) f p := by
  have hs := CrossedQuadrilateralContainedOriginal.seven_nonempty_strict S
    (fun i => pre T (f i)) p (fun i => by rw [width_pre]; exact hW i) ho
    (by rwa [budget_pre]) (by rwa [nonempty_cells_eq])
  rw [budget_pre] at hs
  rw [gap_scale,area_image]
  nlinarith only [mul_lt_mul_of_pos_left hs (factor_pos T)]

theorem at_most_six_of_equality (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (T '' CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget (T '' CrossedQuadrilateralFormDirections.body S) f p < 1)
    (he : Equality (T '' CrossedQuadrilateralFormDirections.body S) f p) :
    (PlanarSevenNonemptyCells.nonemptyCells (T '' CrossedQuadrilateralFormDirections.body S) f p).card ≤ 6 := by
  have hs := CrossedQuadrilateralContainedOriginal.at_most_six_of_equality S
    (fun i => pre T (f i)) p (fun i => by rw [width_pre]; exact hW i) ho
    (by rwa [budget_pre]) ((equality_iff T _ f p).mp he)
  rwa [nonempty_cells_eq] at hs

/-- The vanishing linear coefficients state alignment with the transformed
diagonal directions, without choosing a Euclidean normalization of the forms. -/
theorem directions_of_four_cells (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth (T '' CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget (T '' CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcell : ∀ s, (signCell (T '' CrossedQuadrilateralFormDirections.body S) f p.1 p.2 s).Nonempty)
    (he : Equality (T '' CrossedQuadrilateralFormDirections.body S) f p) :
    ∀ i, (f i).linear (T.linear ![1,0]) = 0 ∨ (f i).linear (T.linear ![0,1]) = 0 := by
  have hc (s) : (signCell (CrossedQuadrilateralFormDirections.body S)
      (fun i => pre T (f i)) p.1 p.2 s).Nonempty := by
    have hh := hcell s
    rw [← image_cell,Set.image_nonempty] at hh
    exact hh
  exact CrossedQuadrilateralTwoWindows.directions_of_four_cells S (fun i => pre T (f i)) p
    (fun i => by rw [width_pre]; exact hW i) ho (by rwa [budget_pre]) hc ((equality_iff T _ f p).mp he)

/-- The contained-pair/null-triple exclusion in original coordinates on
an arbitrary invertible affine image of the quadrilateral model. -/
theorem contained_null_strict (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (T '' CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i) (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hR : budget (T '' CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hc : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆
      T '' CrossedQuadrilateralFormDirections.body S)
    (ht : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0) :
    (1-budget (T '' CrossedQuadrilateralFormDirections.body S) f p)^2*
      (volume (T '' CrossedQuadrilateralFormDirections.body S)).toReal <
      gapArea (T '' CrossedQuadrilateralFormDirections.body S) f p := by
  have hW' (i) : 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (pre T (f i)) := by
    rw [width_pre]
    exact hW i
  have hf (i) := linear_ne_zero_of_rangeWidth_pos (CrossedQuadrilateralContainedOriginal.body_nonempty S)
    (pre T (f i)) (hW' i)
  have hs := CrossedQuadrilateralContainedOriginal.strict_gap S (fun i => pre T (f i)) p hW' ho
    (fun i j hij => cross_pre_ne_zero T (f i) (f j) (hf i) (hpairs i j hij))
    (by rwa [budget_pre]) (fun i j hij => pair_pre_subset T _ _ _ _ _ _ _ (hc i j hij))
    (triple_null_pre T f p ht)
  rw [budget_pre] at hs
  rw [gap_scale,area_image]
  nlinarith only [mul_lt_mul_of_pos_left hs (factor_pos T)]

/-- Positive triple overlap is allowed in the concurrent-anchor exclusion,
with concurrency expressed by actual minima and widths in the original plane. -/
theorem contained_concurrent_strict (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (T '' CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i) (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hR : budget (T '' CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hc : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆
      T '' CrossedQuadrilateralFormDirections.body S)
    (ha : CrossedQuadrilateralConcurrent.Concurrent (T '' CrossedQuadrilateralFormDirections.body S) f p) :
    (1-budget (T '' CrossedQuadrilateralFormDirections.body S) f p)^2*
      (volume (T '' CrossedQuadrilateralFormDirections.body S)).toReal <
      gapArea (T '' CrossedQuadrilateralFormDirections.body S) f p := by
  have hW' (i) : 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (pre T (f i)) := by
    rw [width_pre]
    exact hW i
  have hf (i) := linear_ne_zero_of_rangeWidth_pos (CrossedQuadrilateralContainedOriginal.body_nonempty S)
    (pre T (f i)) (hW' i)
  have hs := CrossedQuadrilateralConcurrent.strict_gap S (fun i => pre T (f i)) p hW' ho
    (fun i j hij => cross_pre_ne_zero T (f i) (f j) (hf i) (hpairs i j hij))
    (by rwa [budget_pre]) (fun i j hij => pair_pre_subset T _ _ _ _ _ _ _ (hc i j hij))
    (concurrent_pre T _ f p ha)
  rw [budget_pre] at hs
  rw [gap_scale,area_image]
  nlinarith only [mul_lt_mul_of_pos_left hs (factor_pos T)]

end Quant.CrossedQuadrilateralImageStrata

/-- info: 'Quant.CrossedQuadrilateralImageStrata.seven_nonempty_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralImageStrata.seven_nonempty_strict
