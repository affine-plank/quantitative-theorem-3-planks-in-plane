/- Strictness for contained overlaps with concurrent canonical anchors.
Positive triple overlap is allowed. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralContainedOriginal
public import Plank.Proofs.Quant.PlanarConcurrentScaling

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralConcurrent
open Plank
open Set MeasureTheory Filter Topology PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarSevenCellArea PlanarSevenCellEquality PlanarPairArea PlanarDirectionDerivatives
open PlanarBodySectionDensity PlanarUnitSectionDensity PlanarOverlapCorrection PlanarConcurrentScaling
open PlanarNormalization PlanarTransverseNormalization PlanarEqualityReductions
open CrossedQuadrilateralContainedOriginal
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Pair containment and concurrency force actual individual tightness.
The proof does not assume a null triple overlap or persistent containment. -/
theorem individual_equality_canonical {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (c r : Fin 3 → ℝ) (hcc : ∀ i, c i ∈ Icc 0 1)
    (hr : ∀ i, 0 < r i) (hR : (∑ i, r i) < 1)
    (hcontain : ∀ i j, i ≠ j →
      plank (f i) ((path c r 0).1 i) ((path c r 0).2 i) ∩
        plank (f j) ((path c r 0).1 j) ((path c r 0).2 j) ⊆ K)
    (z : Point) (hanchor : ∀ i, f i z = c i)
    (heq : gapArea K f (path c r 0) = (1-∑ i, r i)^2*(volume K).toReal) :
    ∀ i, (volume (K \ plank (f i) ((path c r 0).1 i) ((path c r 0).2 i))).toReal =
      (1-r i)^2*(volume K).toReal := by
  classical
  let D (i) : UnitSectionDensity K (f i) := Classical.choice
    (exists_unitSectionDensity hK hc hne hV (f i) (hnorm i) (hunit i))
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; norm_num
  let P := correction (windows f (path c r 0))
  have ho (t : ℝ) (ht : -1 < t) (i : Fin 3) :
      (path c r t).1 i ≤ (path c r t).2 i := by
    apply sub_nonneg.mp
    rw [path_width]
    exact mul_nonneg (by linarith only [ht]) (hr i).le
  have hscale (t : ℝ) (ht : -1 < t) :
      correction (windows f (path c r t)) = (1+t)^2*P :=
    correction_scale f z c r hanchor t ht
  have hbudget (t : ℝ) : budget K f (path c r t) = (1+t)*(∑ i, r i) := by
    simp only [budget,hunit,div_one,path_width,Finset.mul_sum]
  have hz : PlanarWindowEulerRigidity.margin K f c r P 0 = 0 := by
    have he := gap_eq_full hK f (path c r 0) hcontain
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
    have hl := PlanarThreePlank.sharpPlanarBound_three K hK hc hne f
      (path c r t).1 (path c r t).2 (ho t ht) hW
    change (max 0 (1-budget K f (path c r t)))^2*(volume K).toReal ≤ gapArea K f (path c r t) at hl
    rw [hbudget,max_eq_right (sub_nonneg.mpr hb.le)] at hl
    have hu := gap_le_full hK f hpairs (path c r t)
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


/-- Normalized forms, arbitrary positive window endpoints. -/
theorem individual_equality {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints 3) (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (hanchor : ∃ z : Point, ∀ i, (1-(p.2 i-p.1 i))*f i z = p.1 i)
    (heq : Equality K f p) : ∀ i, (volume (K \ plank (f i) (p.1 i) (p.2 i))).toReal =
      (1-(p.2 i-p.1 i)/rangeWidth K (f i))^2*(volume K).toReal := by
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; norm_num
  have he := PlanarEqualityReductions.positive_window_no_waste_three hK hc hne hV f p
    hW hnorm (fun i => (ho i).le) hR heq
  let r (i) := p.2 i-p.1 i
  have hr (i) : 0 < r i := sub_pos.mpr (ho i)
  have hsum : (∑ i, r i) = budget K f p := by simp only [budget,hunit,div_one,r]
  have hr1 (i) : r i < 1 :=
    (Finset.single_le_sum (fun j _ => (hr j).le) (Finset.mem_univ i)).trans_lt (hsum ▸ hR)
  let c (i) := p.1 i/(1-r i)
  have hcanonical (i) := FiniteDimensionalNormalization.canonical_window
    (he i (ho i)).1 (he i (ho i)).2 (hr1 i)
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
  obtain ⟨z,hz⟩ := hanchor
  have hcz (i) : f i z = c i := by
    apply (eq_div_iff (sub_pos.mpr (hr1 i)).ne').mpr
    exact (mul_comm (f i z) (1-r i)).trans (hz i)
  have hi := individual_equality_canonical hK hc hne hV f hnorm hunit hpairs c r hcc hr
    (by rwa [hsum]) (by simpa only [hp] using hcontain) z hcz heq'
  intro i
  simpa only [hp,hunit,div_one,r] using hi i


/-- Concurrency written using actual minima and widths. -/
def Concurrent (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) : Prop :=
  ∃ z : Point, ∀ i,
    (rangeWidth K (f i)-(p.2 i-p.1 i))*f i z =
      rangeWidth K (f i)*p.1 i-(p.2 i-p.1 i)*sInf (f i '' K)

theorem minimum_of_unit_form {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (f g : Point →ᵃ[ℝ] ℝ) (a : ℝ) (hW : 0 < rangeWidth K f)
    (hg : ∀ x, g x = (f x-a)/rangeWidth K f)
    (hnorm : ∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1) (hunit : rangeWidth K g = 1) :
    sInf (f '' K) = a := by
  obtain ⟨u,hu,v,hv,hmax,hmin⟩ := Body.exists_realisers hK hne (continuous_form g)
  have hw : rangeWidth K g = g u-g v := Body.width_eq_of_realisers hu hv hmax hmin
  rw [hunit] at hw
  have hgv : g v = 0 := by linarith only [hw,(hnorm u hu).2,(hnorm v hv).1]
  have hvf : f v = a := by
    have h := hg v
    rw [hgv] at h
    have hz := (div_eq_zero_iff).mp h.symm
    exact sub_eq_zero.mp (hz.resolve_right hW.ne')
  have hleast : IsLeast (f '' K) a := by
    refine ⟨⟨v,hv,hvf⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    have hn := (hnorm x hx).1
    rw [hg] at hn
    apply sub_nonneg.mp
    simpa only [zero_mul] using (le_div_iff₀ hW).mp hn
  exact hleast.csInf_eq


/-- Individual equality in the original affine coordinates. -/
theorem original_individual_equality {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (hanchor : Concurrent K f p)
    (heq : Equality K f p) : ∀ i, (volume (K \ plank (f i) (p.1 i) (p.2 i))).toReal =
      (1-(p.2 i-p.1 i)/rangeWidth K (f i))^2*(volume K).toReal := by
  classical
  choose g a hg hnorm hunit using fun i => exists_unit_form hK hne (f i) (hW i)
  let q : Endpoints 3 := (fun i => (p.1 i-a i)/rangeWidth K (f i),
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
  have hgpairs (i j) (hij : i ≠ j) : cross (g i) (g j) ≠ 0 := by
    rw [cross_scaled_pair (f i) (g i) (f j) (g j) _ _
      (linear_eq_of_formula _ _ _ _ (hg i)) (linear_eq_of_formula _ _ _ _ (hg j))]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hW i).ne') (inv_ne_zero (hW j).ne'))
      (hpairs i j hij)
  have hct (i j) (hij : i ≠ j) :
      plank (g i) (q.1 i) (q.2 i) ∩ plank (g j) (q.1 j) (q.2 j) ⊆ K := by
    rw [hb,hb]
    exact hcontain i j hij
  have ha (i) : sInf (f i '' K) = a i :=
    minimum_of_unit_form hK hne (f i) (g i) (a i) (hW i) (hg i) (hnorm i) (hunit i)
  obtain ⟨z,hz⟩ := hanchor
  have hanc : ∃ z : Point, ∀ i, (1-(q.2 i-q.1 i))*g i z = q.1 i := by
    refine ⟨z,fun i => ?_⟩
    have hh := hz i
    rw [ha] at hh
    rw [hg]
    dsimp only [q]
    field_simp [(hW i).ne']
    nlinarith only [hh]
  have hge : Equality K g q := by
    change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal
    rwa [hgap,hbudget]
  have hi := individual_equality hK hc hne hV g hnorm hunit
    hgpairs q hqo (by rwa [hbudget]) hct hanc hge
  intro i
  have hwi : (q.2 i-q.1 i)/rangeWidth K (g i) = (p.2 i-p.1 i)/rangeWidth K (f i) := by
    rw [hunit]
    dsimp only [q]
    ring
  simpa only [hb,hwi] using hi i

/-- No actual equality in this quadrilateral stratum. -/
theorem not_equality (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i) (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩
      plank (f j) (p.1 j) (p.2 j) ⊆ CrossedQuadrilateralFormDirections.body S)
    (hanchor : Concurrent (CrossedQuadrilateralFormDirections.body S) f p) :
    ¬Equality (CrossedQuadrilateralFormDirections.body S) f p := by
  intro he
  have hi := original_individual_equality (compact_body S) (convex_body S) (body_nonempty S)
    (area_body_pos S) f p hW ho hpairs hR hcontain hanchor he
  have hRi (i) : (p.2 i-p.1 i)/rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i) < 1 :=
    (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      div_nonneg (sub_pos.mpr (ho j)).le (hW j).le) (Finset.mem_univ i)).trans_lt hR
  obtain ⟨i,j,hij,hij0⟩ := CrossedQuadrilateralFormDirections.three_tight_have_parallel_pair
    S f p.1 p.2 ho hW hRi hi
  exact hpairs i j hij hij0

theorem strict_gap (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i) (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩
      plank (f j) (p.1 j) (p.2 j) ⊆ CrossedQuadrilateralFormDirections.body S)
    (hanchor : Concurrent (CrossedQuadrilateralFormDirections.body S) f p) :
    (1-budget (CrossedQuadrilateralFormDirections.body S) f p)^2*
      (volume (CrossedQuadrilateralFormDirections.body S)).toReal <
      gapArea (CrossedQuadrilateralFormDirections.body S) f p := by
  have hl := PlanarThreePlank.sharpPlanarBound_three (CrossedQuadrilateralFormDirections.body S)
    (compact_body S) (convex_body S) (body_nonempty S) f p.1 p.2 (fun i => (ho i).le) hW
  change (max 0 (1-budget (CrossedQuadrilateralFormDirections.body S) f p))^2*
      (volume (CrossedQuadrilateralFormDirections.body S)).toReal ≤
      gapArea (CrossedQuadrilateralFormDirections.body S) f p at hl
  rw [max_eq_right (sub_pos.mpr hR).le] at hl
  apply lt_of_le_of_ne hl
  intro he
  apply not_equality S f p hW ho hpairs hR hcontain hanchor
  change gapArea (CrossedQuadrilateralFormDirections.body S) f p =
    (max 0 (1-budget (CrossedQuadrilateralFormDirections.body S) f p))^2*
      (volume (CrossedQuadrilateralFormDirections.body S)).toReal
  rw [max_eq_right (sub_pos.mpr hR).le]
  exact he.symm

/-- Any remaining three-distinct-direction equality either has a clipped
pair overlap, or a positive triple overlap with nonconcurrent canonical anchors.
This is a necessary obstruction list, not a sufficient family catalogue. -/
theorem remaining_obstruction (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i) (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (he : Equality (CrossedQuadrilateralFormDirections.body S) f p) :
    (∃ i j, i ≠ j ∧ ∃ x, x ∈ plank (f i) (p.1 i) (p.2 i) ∩
      plank (f j) (p.1 j) (p.2 j) ∧ x ∉ CrossedQuadrilateralFormDirections.body S) ∨
    (0 < volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∧
      ¬Concurrent (CrossedQuadrilateralFormDirections.body S) f p) := by
  classical
  by_cases hc : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩
      plank (f j) (p.1 j) (p.2 j) ⊆ CrossedQuadrilateralFormDirections.body S
  · right
    refine ⟨?_,fun ha => not_equality S f p hW ho hpairs hR hc ha he⟩
    apply pos_iff_ne_zero.mpr
    intro hz
    exact CrossedQuadrilateralContainedOriginal.not_equality S f p hW ho hpairs hR hc hz he
  · left
    simp only [Set.subset_def] at hc
    push Not at hc
    exact hc

end Quant.CrossedQuadrilateralConcurrent

/-- info: 'Quant.CrossedQuadrilateralConcurrent.strict_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralConcurrent.strict_gap
