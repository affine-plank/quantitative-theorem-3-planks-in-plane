/- Actual individual rigidity for two transverse windows with contained overlap. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralConcurrent
public import Plank.Proofs.Quant.PlanarTwoPlankCells

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralTwoWindows
open Plank
open Set MeasureTheory Filter Topology PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarSevenCellArea PlanarPairArea PlanarDirectionDerivatives PlanarNormalization
open PlanarTransverseNormalization PlanarBodySectionDensity PlanarUnitSectionDensity
open PlanarPairwiseGapUpper PlanarEqualityReductions
open CrossedQuadrilateralContainedOriginal
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def path (c r : Fin 2 → ℝ) (t : ℝ) : Endpoints 2 :=
  (fun i => (1-r i)*c i+t*(-r i*c i),
    fun i => c i+(1-c i)*r i+t*(r i*(1-c i)))

theorem path_width (c r : Fin 2 → ℝ) (t : ℝ) (i : Fin 2) :
    (path c r t).2 i-(path c r t).1 i = (1+t)*r i := by
  dsimp [path]
  ring

def pairArea (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2) : ℝ :=
  (volume (plank (f 0) (p.1 0) (p.2 0) ∩ plank (f 1) (p.1 1) (p.2 1))).toReal

theorem gap_identity {K : Set Point} (hK : IsCompact K)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2) :
    gapArea K f p = (volume K).toReal-∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+
      (volume ((K ∩ plank (f 0) (p.1 0) (p.2 0)) ∩
        (K ∩ plank (f 1) (p.1 1) (p.2 1)))).toReal := by
  let A (i : Fin 2) := K ∩ plank (f i) (p.1 i) (p.2 i)
  have hm (i) : MeasurableSet (A i) := hK.measurableSet.inter (isClosed_plank _ _ _).measurableSet
  have hfin (i) : volume (A i) ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hK.measure_ne_top
  have hab := measureReal_union_add_inter (μ := volume) (s := A 0) (hm 1) (hfin 0) (hfin 1)
  have hd := measureReal_sdiff_add_inter (μ := volume) (s := K) ((hm 0).union (hm 1)) hK.measure_ne_top
  rw [inter_eq_right.mpr (union_subset inter_subset_left inter_subset_left)] at hd
  have hs : K \ (A 0 ∪ A 1) = K \ ⋃ i, plank (f i) (p.1 i) (p.2 i) := by
    ext x
    simp only [A,mem_inter_iff,Set.mem_sdiff,mem_union,mem_iUnion,Fin.exists_fin_two]
    tauto
  rw [hs] at hd
  change gapArea K f p+(volume (A 0 ∪ A 1)).toReal = (volume K).toReal at hd
  change (volume (A 0 ∪ A 1)).toReal+(volume (A 0 ∩ A 1)).toReal =
    (volume (A 0)).toReal+(volume (A 1)).toReal at hab
  simp only [Fin.sum_univ_two,coveredArea]
  change gapArea K f p = (volume K).toReal-((volume (A 0)).toReal+(volume (A 1)).toReal)+
    (volume (A 0 ∩ A 1)).toReal
  linarith only [hab,hd]

theorem gap_le_pair {K : Set Point} (hK : IsCompact K)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2) (hcross : cross (f 0) (f 1) ≠ 0) :
    gapArea K f p ≤ (volume K).toReal-∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairArea f p := by
  rw [gap_identity hK f p]
  apply add_le_add le_rfl
  exact ENNReal.toReal_mono (PlanarPairArea.compact_pair _ _ hcross _ _ _ _).measure_ne_top
    (measure_mono fun _ hx => ⟨hx.1.2,hx.2.2⟩)

theorem gap_eq_pair {K : Set Point} (hK : IsCompact K)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hcontain : plank (f 0) (p.1 0) (p.2 0) ∩ plank (f 1) (p.1 1) (p.2 1) ⊆ K) :
    gapArea K f p = (volume K).toReal-∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairArea f p := by
  rw [gap_identity hK f p]
  have he : (K ∩ plank (f 0) (p.1 0) (p.2 0)) ∩ (K ∩ plank (f 1) (p.1 1) (p.2 1)) =
      plank (f 0) (p.1 0) (p.2 0) ∩ plank (f 1) (p.1 1) (p.2 1) := by
    ext x
    exact ⟨fun hx => ⟨hx.1.2,hx.2.2⟩,
      fun hx => ⟨⟨hcontain hx,hx.1⟩,⟨hcontain hx,hx.2⟩⟩⟩
  rw [he]
  rfl

theorem individual_equality_canonical {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hcross : cross (f 0) (f 1) ≠ 0)
    (c r : Fin 2 → ℝ) (hcc : ∀ i, c i ∈ Icc 0 1)
    (hr : ∀ i, 0 < r i) (hR : (∑ i, r i) < 1)
    (hcontain : plank (f 0) ((path c r 0).1 0) ((path c r 0).2 0) ∩
      plank (f 1) ((path c r 0).1 1) ((path c r 0).2 1) ⊆ K)
    (heq : gapArea K f (path c r 0) = (1-∑ i, r i)^2*(volume K).toReal) :
    ∀ i, (volume (K \ plank (f i) ((path c r 0).1 i) ((path c r 0).2 i))).toReal =
      (1-r i)^2*(volume K).toReal := by
  classical
  let D (i) : UnitSectionDensity K (f i) := Classical.choice
    (exists_unitSectionDensity hK hc hne hV (f i) (hnorm i) (hunit i))
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; norm_num
  let P := pairCoefficient (f 0) (f 1) hcross*r 0*r 1
  have ho (t : ℝ) (ht : -1 < t) (i : Fin 2) :
      (path c r t).1 i ≤ (path c r t).2 i := by
    apply sub_nonneg.mp
    rw [path_width]
    exact mul_nonneg (by linarith only [ht]) (hr i).le
  have hscale (t : ℝ) (ht : -1 < t) : pairArea f (path c r t) = (1+t)^2*P := by
    unfold pairArea
    simp only [plank]
    rw [area_pair (f 0) (f 1) hcross _ _ _ _ (ho t ht 0) (ho t ht 1)]
    simp only [path_width]
    dsimp only [P]
    ring
  have hbudget (t : ℝ) : budget K f (path c r t) = (1+t)*(∑ i, r i) := by
    simp only [budget,hunit,div_one,path_width,Finset.mul_sum]
  have hz : PlanarWindowEulerRigidity.margin K f c r P 0 = 0 := by
    have he := gap_eq_pair hK f (path c r 0) hcontain
    rw [he,hscale 0 (by norm_num)] at heq
    change (volume K).toReal-(∑ i, coveredArea K (f i) ((1-r i)*c i+0*(-r i*c i))
      (c i+(1-c i)*r i+0*(r i*(1-c i))))+(1+0)^2*P-
      (volume K).toReal*(1-(1+0)*(∑ i, r i))^2 = 0
    simp only [add_zero,one_mul] at heq ⊢
    rw [mul_comm (volume K).toReal ((1-∑ i, r i)^2)]
    exact sub_eq_zero.mpr heq
  have hmin : IsLocalMin (PlanarWindowEulerRigidity.margin K f c r P) 0 := by
    have ht : ∀ᶠ t : ℝ in 𝓝 0, -1 < t := Ioi_mem_nhds (by norm_num)
    have hb : ∀ᶠ t : ℝ in 𝓝 0, (1+t)*(∑ i, r i) < 1 :=
      (show ContinuousAt (fun t : ℝ => (1+t)*(∑ i, r i)) 0 by fun_prop).eventually_lt_const
        (by simpa only [add_zero,one_mul] using hR)
    filter_upwards [ht,hb] with t ht hb
    rw [hz]
    change 0 ≤ (volume K).toReal-(∑ i, coveredArea K (f i) ((path c r t).1 i) ((path c r t).2 i))+
      (1+t)^2*P-(volume K).toReal*(1-(1+t)*(∑ i, r i))^2
    apply sub_nonneg.mpr
    have hl := PlanarTwoPlankCells.sharpBound_two K hK hc hne f
      (path c r t).1 (path c r t).2 (ho t ht) hW
    change (max 0 (1-budget K f (path c r t)))^2*(volume K).toReal ≤ gapArea K f (path c r t) at hl
    rw [hbudget,max_eq_right (sub_nonneg.mpr hb.le)] at hl
    have hu := gap_le_pair hK f (path c r t) hcross
    rw [hscale t ht] at hu
    apply le_trans (b := gapArea K f (path c r t)) ?_ hu
    rw [mul_comm (volume K).toReal]
    exact hl
  intro i
  have hr1 (j) : r j < 1 :=
    (Finset.single_le_sum (fun k _ => (hr k).le) (Finset.mem_univ j)).trans_lt hR
  have hbalance := PlanarUnitEulerRigidity.balance_eq_of_local_min f D c r hcc hr hr1 P hmin hz i
  simpa only [path,zero_mul,add_zero] using
    PlanarUnitWindowRigidity.gap_eq_of_balance_eq hK (D i) (hcc i) (hr i).le (hr1 i) hbalance

/-- The already-proved two-window bound supplies no-waste directly. -/
theorem no_waste {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1) (he : Equality K f p) (i : Fin 2) :
    0 ≤ p.1 i ∧ p.2 i ≤ 1 := by
  have ht := budget_clip_eq PlanarTwoPlankCells.sharpBound_two hK hc hne hV f p hW hnorm
    (fun j => (ho j).le) hR he
  have hle (j : Fin 2) : (clip (p.2 j)-clip (p.1 j))/rangeWidth K (f j) ≤
      (p.2 j-p.1 j)/rangeWidth K (f j) :=
    (div_le_div_iff_of_pos_right (hW j)).mpr (clip_sub_le (ho j).le)
  have h := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp ht i (Finset.mem_univ i)
  exact (clip_length_eq_iff (ho i)).mp ((div_left_inj' (hW i).ne').mp h)

theorem individual_equality {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hcross : cross (f 0) (f 1) ≠ 0)
    (p : Endpoints 2) (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1)
    (hcontain : plank (f 0) (p.1 0) (p.2 0) ∩ plank (f 1) (p.1 1) (p.2 1) ⊆ K)
    (heq : Equality K f p) : ∀ i, (volume (K \ plank (f i) (p.1 i) (p.2 i))).toReal =
      (1-(p.2 i-p.1 i)/rangeWidth K (f i))^2*(volume K).toReal := by
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; norm_num
  have he := no_waste hK hc hne hV f p hW hnorm ho hR heq
  let r (i) := p.2 i-p.1 i
  have hr (i) : 0 < r i := sub_pos.mpr (ho i)
  have hsum : (∑ i, r i) = budget K f p := by simp only [budget,hunit,div_one,r]
  have hr1 (i) : r i < 1 :=
    (Finset.single_le_sum (fun j _ => (hr j).le) (Finset.mem_univ i)).trans_lt (hsum ▸ hR)
  let c (i) := p.1 i/(1-r i)
  have hcanonical (i) := FiniteDimensionalNormalization.canonical_window
    (he i).1 (he i).2 (hr1 i)
  have hcc (i) : c i ∈ Icc (0 : ℝ) 1 := (hcanonical i).1
  have hp : path c r 0 = p := by
    apply Prod.ext <;> funext i
    · change (1-r i)*c i+0*(-r i*c i) = p.1 i
      simpa only [zero_mul,add_zero] using (hcanonical i).2.1
    · change c i+(1-c i)*r i+0*(r i*(1-c i)) = p.2 i
      simpa only [zero_mul,add_zero] using (hcanonical i).2.2
  have heq' : gapArea K f (path c r 0) = (1-∑ i, r i)^2*(volume K).toReal := by
    rw [hp,hsum]
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at heq
    rwa [max_eq_right (sub_pos.mpr hR).le] at heq
  have hi := individual_equality_canonical hK hc hne hV f hnorm hunit hcross c r hcc hr
    (by rwa [hsum]) (by simpa only [hp] using hcontain) heq'
  intro i
  simpa only [hp,hunit,div_one,r] using hi i


theorem original_individual_equality {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hcross : cross (f 0) (f 1) ≠ 0) (hR : budget K f p < 1)
    (hcontain : plank (f 0) (p.1 0) (p.2 0) ∩ plank (f 1) (p.1 1) (p.2 1) ⊆ K)
    (heq : Equality K f p) : ∀ i, (volume (K \ plank (f i) (p.1 i) (p.2 i))).toReal =
      (1-(p.2 i-p.1 i)/rangeWidth K (f i))^2*(volume K).toReal := by
  classical
  choose g a hg hnorm hunit using fun i => exists_unit_form hK hne (f i) (hW i)
  let q : Endpoints 2 := (fun i => (p.1 i-a i)/rangeWidth K (f i),
    fun i => (p.2 i-a i)/rangeWidth K (f i))
  have hqo (i) : q.1 i < q.2 i :=
    (div_lt_div_iff_of_pos_right (hW i)).mpr (sub_lt_sub_right (ho i) _)
  have hb (i) : plank (g i) (q.1 i) (q.2 i) = plank (f i) (p.1 i) (p.2 i) := by
    ext x
    simp only [plank,mem_ofPred_eq,hg]
    dsimp only [q]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  have hbudget : budget K g q = budget K f p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hunit]
    dsimp only [q]
    ring
  have hgap : gapArea K g q = gapArea K f p := by
    change (volume (K \ ⋃ i, plank (g i) (q.1 i) (q.2 i))).toReal =
      (volume (K \ ⋃ i, plank (f i) (p.1 i) (p.2 i))).toReal
    simp only [hb]
  have hgcross : cross (g 0) (g 1) ≠ 0 := by
    rw [cross_scaled_pair (f 0) (g 0) (f 1) (g 1) _ _
      (linear_eq_of_formula _ _ _ _ (hg 0)) (linear_eq_of_formula _ _ _ _ (hg 1))]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hW 0).ne') (inv_ne_zero (hW 1).ne')) hcross
  have hct : plank (g 0) (q.1 0) (q.2 0) ∩ plank (g 1) (q.1 1) (q.2 1) ⊆ K := by
    rwa [hb,hb]
  have hge : Equality K g q := by
    change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal
    rwa [hgap,hbudget]
  have hi := individual_equality hK hc hne hV g hnorm hunit
    hgcross q hqo (by rwa [hbudget]) hct hge
  intro i
  have hwi : (q.2 i-q.1 i)/rangeWidth K (g i) = (p.2 i-p.1 i)/rangeWidth K (f i) := by
    rw [hunit]
    dsimp only [q]
    ring
  simpa only [hb,hwi] using hi i

/-- Both actual directions are diagonal whenever the full pair overlap
is contained in the genuine quadrilateral. Endpoints and affine scales are arbitrary. -/
theorem directions_of_contained_pair (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i) (hcross : cross (f 0) (f 1) ≠ 0)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcontain : plank (f 0) (p.1 0) (p.2 0) ∩ plank (f 1) (p.1 1) (p.2 1) ⊆
      CrossedQuadrilateralFormDirections.body S)
    (he : Equality (CrossedQuadrilateralFormDirections.body S) f p) :
    ∀ i, (CrossedQuadrilateralFormDirections.normal (f i)).1 = 0 ∨
      (CrossedQuadrilateralFormDirections.normal (f i)).2 = 0 := by
  have hi := original_individual_equality (compact_body S) (convex_body S) (body_nonempty S)
    (area_body_pos S) f p hW ho hcross hR hcontain he
  intro i
  have hRi : (p.2 i-p.1 i)/rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i) < 1 :=
    (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 2))) =>
      div_nonneg (sub_pos.mpr (ho j)).le (hW j).le) (Finset.mem_univ i)).trans_lt hR
  exact CrossedQuadrilateralFormDirections.one_window_direction S (f i) (p.1 i) (p.2 i)
    (ho i) (hW i) hRi (hi i)

/-- Four weak exterior corners suffice; no positive cell-area assumption,
transversality premise or initial pair-containment premise remains. -/
theorem directions_of_four_corners (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcorners : ∀ b c : Bool, ∃ x ∈ CrossedQuadrilateralFormDirections.body S,
      (if b then p.2 0 ≤ f 0 x else f 0 x ≤ p.1 0) ∧
      (if c then p.2 1 ≤ f 1 x else f 1 x ≤ p.1 1))
    (he : Equality (CrossedQuadrilateralFormDirections.body S) f p) :
    ∀ i, (CrossedQuadrilateralFormDirections.normal (f i)).1 = 0 ∨
      (CrossedQuadrilateralFormDirections.normal (f i)).2 = 0 := by
  have hcross := PlanarSevenNonemptyCells.cross_ne_zero_of_corners _ (f 0) (f 1)
    (linear_ne_zero_of_rangeWidth_pos (body_nonempty S) (f 0) (hW 0)) _ _ _ _
    (ho 0) (ho 1) hcorners
  exact directions_of_contained_pair S f p hW ho hcross hR
    (PlanarPairContainment.pair_subset_of_corners (compact_body S).isClosed (convex_body S)
      (f 0) (f 1) hcross _ _ _ _ hcorners) he

/-- A formulation using all four actual closed exterior cells, including
cells which are only a segment or singleton. -/
theorem directions_of_four_cells (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcell : ∀ s, (signCell (CrossedQuadrilateralFormDirections.body S) f p.1 p.2 s).Nonempty)
    (he : Equality (CrossedQuadrilateralFormDirections.body S) f p) :
    ∀ i, (CrossedQuadrilateralFormDirections.normal (f i)).1 = 0 ∨
      (CrossedQuadrilateralFormDirections.normal (f i)).2 = 0 := by
  apply directions_of_four_corners S f p hW ho hR _ he
  intro b c
  cases b <;> cases c
  · obtain ⟨x,hx⟩ := hcell ∅
    exact ⟨x,hx.1,by simpa using hx.2 0,by simpa using hx.2 1⟩
  · obtain ⟨x,hx⟩ := hcell {1}
    exact ⟨x,hx.1,by simpa using hx.2 0,by simpa using hx.2 1⟩
  · obtain ⟨x,hx⟩ := hcell {0}
    exact ⟨x,hx.1,by simpa using hx.2 0,by simpa using hx.2 1⟩
  · obtain ⟨x,hx⟩ := hcell Finset.univ
    exact ⟨x,hx.1,by simpa using hx.2 0,by simpa using hx.2 1⟩

end Quant.CrossedQuadrilateralTwoWindows

/-- info: 'Quant.CrossedQuadrilateralTwoWindows.original_individual_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralTwoWindows.original_individual_equality
