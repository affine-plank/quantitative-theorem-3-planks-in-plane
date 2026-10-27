/- Remove an edge-support band from a common-extreme pair on a triangle. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonSupport
public import Plank.Proofs.Quant.CommonMiddleNullWindow

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CommonMiddleSupportReduction
open Set MeasureTheory Proofs.Basic Proofs.Transport CrossedQuadrilateralAttainment
open CommonMiddleAffineTransport CommonMiddleNullWindow CrossedQuadrilateralCommonSupport
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def pulled (T : Triangle) (t : ℝ) (ht : t < 1) (p : Plank) : Plank where
  u := p.u
  u_ne_zero := p.u_ne_zero
  lo := (p.lo-t*dot p.u T.C)/(1-t)
  hi := (p.hi-t*dot p.u T.C)/(1-t)
  lo_le_hi := (div_le_div_iff_of_pos_right (sub_pos.mpr ht)).mpr
    (sub_le_sub_right p.lo_le_hi _)

theorem pulled_common (T : Triangle) (t : ℝ) (ht : t < 1) (p : Plank)
    (hp : CommonExtremes T p) : CommonExtremes T (pulled T t ht p) := hp

theorem pulled_width (T : Triangle) (t : ℝ) (ht : t < 1) (p : Plank) :
    (pulled T t ht p).relWidth T = p.relWidth T/(1-t) := by
  simp only [Plank.relWidth,pulled]
  ring

theorem pulled_slope (T : Triangle) (t : ℝ) (ht : t < 1) (p : Plank) :
    CommonMiddleAffineTransport.slope T (pulled T t ht p) =
      CommonMiddleAffineTransport.slope T p := rfl

theorem pulled_lower (T : Triangle) (t : ℝ) (ht : t < 1) (p : Plank)
    (hp : CommonExtremes T p) :
    lower T (pulled T t ht p) =
      (lower T p-t*CommonMiddleAffineTransport.slope T p)/(1-t) := by
  have hs := (span_pos T p hp).ne'
  simp only [lower,CommonMiddleAffineTransport.slope,pulled,span] at hs ⊢
  field_simp [(sub_pos.mpr ht).ne',hs]
  ring

theorem endpoint_pull {t l b r s w : ℝ} (ht : t < 1)
    (h : (l-t*b)/(1-t) = (1-(r/(1-t)+s/(1-t)))*b+w/(1-t)) :
    l = (1-(r+s))*b+w := by
  field_simp [(sub_pos.mpr ht).ne'] at h
  nlinarith only [h]

/-- Pulling back the support homothety leaves the original pair-stack
identities unchanged. In particular, the pair budget excludes the support band. -/
theorem pair_stack_of_pulled (T : Triangle) (t : ℝ) (ht : t < 1) (p q : Plank)
    (hp : CommonExtremes T p) (hq : CommonExtremes T q)
    (hs : PairOrderedStack T (pulled T t ht p) (pulled T t ht q)) :
    PairOrderedStack T p q := by
  simp only [PairOrderedStack,pulled_slope,pulled_width,pulled_lower T t ht p hp,
    pulled_lower T t ht q hq] at hs
  rcases hs with ⟨hb,hl,hu⟩ | ⟨hb,hl,hu⟩
  · exact Or.inl ⟨hb,by simpa only [add_zero] using
      (endpoint_pull (w := 0) ht (by simpa only [zero_div,add_zero] using hl)),
      endpoint_pull ht hu⟩
  · exact Or.inr ⟨hb,by simpa only [add_zero] using
      (endpoint_pull (w := 0) ht (by simpa only [zero_div,add_zero] using hl)),
      endpoint_pull ht hu⟩

theorem union_two (p : Fin 2 → Plank) :
    (⋃ i, (p i).set) = (p 0).set ∪ (p 1).set := by
  ext z
  simp only [Set.mem_iUnion,Set.mem_union,Fin.exists_fin_two]

/-- Two positive planks have common support vertices A,B. If adding an
inward band based on edge AB is tight, the original pair is an ordered stack. -/
theorem pair_stack_of_equality (T : Triangle) (hK : IsCompact T.set)
    (F : Point →ᵃ[ℝ] ℝ) (hFC : F T.C = 1) (hFA : F T.A = 0)
    (hF : ∀ z ∈ T.set, 0 ≤ F z ∧ F z ≤ 1)
    (p : Fin 2 → Plank) (hc : ∀ i, CommonExtremes T (p i))
    (hw : ∀ i, 0 < (p i).relWidth T) (t : ℝ) (ht : 0 ≤ t)
    (hR : t+((p 0).relWidth T+(p 1).relWidth T) < 1)
    (he : (volume (T.set \ ({z | 0 ≤ F z ∧ F z ≤ t} ∪ ⋃ i, (p i).set))).toReal =
      (1-t-((p 0).relWidth T+(p 1).relWidth T))^2*(volume T.set).toReal) :
    PairOrderedStack T (p 0) (p 1) := by
  have ht1 : t < 1 := by linarith only [hR,hw 0,hw 1]
  have hv : 0 < (volume T.set).toReal := by
    rw [AffineTransport.area_triangle]
    exact mul_pos (abs_pos.mpr (det3_ne_zero T)) (by norm_num)
  let G (i : Fin 2) := direction (p i).u
  have hwidth (i) : rangeWidth T.set (G i) = T.width (p i).u := range_triangle T _ (hc i)
  have ho (i) : (p i).lo < (p i).hi := by
    have hh := hw i
    change 0 < ((p i).hi-(p i).lo)/T.width (p i).u at hh
    exact sub_pos.mp ((div_pos_iff_of_pos_right (width_pos T (p i).u_ne_zero)).mp hh)
  have hsum : (∑ i, ((p i).hi-(p i).lo)/rangeWidth T.set (G i)) =
      (p 0).relWidth T+(p 1).relWidth T := by
    simp only [hwidth,Fin.sum_univ_two,Plank.relWidth]
  obtain ⟨hpull,_⟩ := CrossedQuadrilateralSupportTripleAxes.reduced hK (convex_triangle T) hv
    F G T.C T.A (mem_C T) (mem_A T) hFC hFA hF t (fun i => (p i).lo)
    (fun i => (p i).hi) ht ho (fun i => by rw [hwidth]; exact width_pos T (p i).u_ne_zero)
    (by rwa [hsum]) (by
      rw [hsum]
      change (volume (T.set \ ({z | 0 ≤ F z ∧ F z ≤ t} ∪ ⋃ i, (p i).set))).toReal = _
      exact he)
  simp only [hwidth] at hpull
  let P (i : Fin 2) := pulled T t ht1 (p i)
  change (volume (T.set \ ⋃ i, (P i).set)).toReal =
    (1-∑ i, (P i).relWidth T)^2*(volume T.set).toReal at hpull
  rw [union_two,Fin.sum_univ_two] at hpull
  have hsmall : (P 0).relWidth T+(P 1).relWidth T < 1 := by
    simp only [P,pulled_width,← add_div]
    exact (div_lt_one (sub_pos.mpr ht1)).mpr (by linarith only [hR])
  let n : Plank := ⟨(p 0).u,0,0,(p 0).u_ne_zero,le_rfl⟩
  have hstack := (equality_iff_pairStack T (P 0) (P 1) n (hc 0) (hc 1)
    (by dsimp only [P]; rw [pulled_width]; exact div_pos (hw 0) (sub_pos.mpr ht1))
    (by dsimp only [P]; rw [pulled_width]; exact div_pos (hw 1) (sub_pos.mpr ht1)) rfl hsmall).mp
      (by rw [area_remove_null T (P 0) (P 1) n rfl,null_relWidth T n rfl,add_zero]; exact hpull)
  exact pair_stack_of_pulled T t ht1 (p 0) (p 1) (hc 0) (hc 1) hstack

end Quant.CommonMiddleSupportReduction

/-- info: 'Quant.CommonMiddleSupportReduction.pair_stack_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonMiddleSupportReduction.pair_stack_of_equality
