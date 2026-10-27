/- A transverse third band in a common-support pair: exact half budgets. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonSupport

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCommonPairSplit
open Set MeasureTheory Proofs.Basic Proofs.Transport
open CrossedQuadrilateralAttainment CrossedQuadrilateralDiagonalSplit
open CrossedQuadrilateralCommonSupport
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def transverse (l u : ℝ) (ho : l ≤ u) : Plank where
  u := (0,1)
  u_ne_zero := by norm_num
  lo := l
  hi := u
  lo_le_hi := ho

def cut (j : Bool) (t : ℝ) : ℝ := if j then max t 0 else min t 0

theorem cut_mono (j : Bool) {l u : ℝ} (ho : l ≤ u) : cut j l ≤ cut j u := by
  cases j
  · exact min_le_min_right 0 ho
  · exact max_le_max_right 0 ho

def clipped (j : Bool) (l u : ℝ) (ho : l ≤ u) : Plank :=
  transverse (cut j l) (cut j u) (cut_mono j ho)

def family (p : Fin 2 → Plank) (l u : ℝ) (ho : l ≤ u) : Fin 3 → Plank :=
  ![p 0,p 1,transverse l u ho]

def halfFamily (p : Fin 2 → Plank) (j : Bool) (l u : ℝ) (ho : l ≤ u) : Fin 3 → Plank :=
  ![p 0,p 1,clipped j l u ho]

theorem half_area (S : Shape) (j : Bool) :
    (volume (half S j).set).toReal = (S.a+S.c)*|S.Y j|/2 := by
  rw [AffineTransport.area_triangle]
  have he : det3 (half S j).A (half S j).B (half S j).C = (S.a+S.c)*S.Y j := by
    simp [half,det3]
  rw [he,abs_mul,abs_of_pos (add_pos S.ha S.hc)]
  ring

theorem half_area_pos (S : Shape) (j : Bool) : 0 < (volume (half S j).set).toReal := by
  rw [half_area]
  exact div_pos (mul_pos (add_pos S.ha S.hc) (abs_pos.mpr (S.Y_ne j))) (by norm_num)

theorem half_y_bounds (S : Shape) (j : Bool) {z : Point} (hz : z ∈ (half S j).set) :
    min 0 (S.Y j) ≤ z.2 ∧ z.2 ≤ max 0 (S.Y j) := by
  obtain ⟨α,β,γ,hα,hβ,hγ,hs,rfl⟩ := hz
  have hγ1 : γ ≤ 1 := by linarith only [hα,hβ,hs]
  simp only [half,Prod.snd_add,Prod.smul_mk,smul_eq_mul,mul_zero,zero_add]
  cases j
  · simp only [Shape.Y,Bool.false_eq_true,if_false,min_eq_right (neg_nonpos.mpr S.hd.le),
      max_eq_left (neg_nonpos.mpr S.hd.le)]
    constructor <;> nlinarith [mul_nonneg hγ S.hd.le,mul_nonneg (sub_nonneg.mpr hγ1) S.hd.le]
  · simp only [Shape.Y,if_true,min_eq_left S.hb.le,max_eq_right S.hb.le]
    exact ⟨mul_nonneg hγ S.hb.le,by nlinarith only [hγ1,S.hb]⟩

theorem transverse_range_half (S : Shape) (j : Bool) :
    rangeWidth (half S j).set (direction (0,1)) = |S.Y j| := by
  cases j
  · have h := Plank.Body.width_eq_of_realisers (f := direction (0,1))
      (a := (half S false).A) (b := (half S false).C) (K := (half S false).set)
      (mem_A (half S false)) (mem_C (half S false))
      (fun z hz => by
        simpa [half,Shape.Y,direction,dot,max_eq_left (neg_nonpos.mpr S.hd.le)] using
          (half_y_bounds S false hz).2)
      (fun z hz => by
        simpa [half,Shape.Y,direction,dot,min_eq_right (neg_nonpos.mpr S.hd.le)] using
          (half_y_bounds S false hz).1)
    change rangeWidth (half S false).set (direction (0,1)) =
      dot (0,1) (half S false).A-dot (0,1) (half S false).C at h
    simpa [half,Shape.Y,dot,abs_of_pos S.hd] using h
  · have h := Plank.Body.width_eq_of_realisers (f := direction (0,1))
      (a := (half S true).C) (b := (half S true).A) (K := (half S true).set)
      (mem_C (half S true)) (mem_A (half S true))
      (fun z hz => by
        simpa [half,Shape.Y,direction,dot,max_eq_right S.hb.le] using (half_y_bounds S true hz).2)
      (fun z hz => by
        simpa [half,Shape.Y,direction,dot,min_eq_left S.hb.le] using (half_y_bounds S true hz).1)
    change rangeWidth (half S true).set (direction (0,1)) =
      dot (0,1) (half S true).C-dot (0,1) (half S true).A at h
    simpa [half,Shape.Y,dot,abs_of_pos S.hb] using h

theorem transverse_relativeWidth (S : Shape) (l u : ℝ) (ho : l ≤ u) :
    relativeWidth S (transverse l u ho) = (u-l)/(S.b+S.d) := by
  change (u-l)/rangeWidth S.body (direction (0,1)) = _
  rw [(coordinate_widths S).2]

theorem cut_mem_iff (j : Bool) {y l u : ℝ} (hy : y ≠ 0)
    (hs : if j then 0 ≤ y else y ≤ 0) :
    (cut j l ≤ y ∧ y ≤ cut j u) ↔ (l ≤ y ∧ y ≤ u) := by
  cases j
  · change y ≤ 0 at hs
    have hy' : y < 0 := lt_of_le_of_ne hs hy
    simp only [cut,Bool.false_eq_true,if_false,min_le_iff,le_min_iff]
    constructor
    · rintro ⟨hl,hu⟩
      exact ⟨hl.resolve_right (not_le.mpr hy'),hu.1⟩
    · exact fun h => ⟨Or.inl h.1,h.2,hs⟩
  · change 0 ≤ y at hs
    have hy' : 0 < y := lt_of_le_of_ne hs hy.symm
    simp only [cut,if_true,max_le_iff,le_max_iff]
    constructor
    · rintro ⟨hl,hu⟩
      exact ⟨hl.1,hu.resolve_right (not_le.mpr hy')⟩
    · exact fun h => ⟨⟨h.1,hs⟩,Or.inl h.2⟩

theorem union_three (p : Fin 3 → Plank) :
    (⋃ i, (p i).set) = (p 0).set ∪ ((p 1).set ∪ (p 2).set) := by
  ext z
  simp only [Set.mem_iUnion,Set.mem_union,Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
  rfl

/-- Trimming the transverse band at the splitting diagonal changes a half-gap
only on the shared line, whose actual Lebesgue area is zero. -/
theorem clipped_gap (S : Shape) (p : Fin 2 → Plank) (j : Bool)
    (l u : ℝ) (ho : l ≤ u) :
    volume ((half S j).set \ ⋃ i, (halfFamily p j l u ho i).set) =
      volume ((half S j).set \ ⋃ i, (family p l u ho i).set) := by
  have hn : volume {z : Point | z.2 = 0} = 0 := by
    simpa [dot] using volume_line (by norm_num : ((0,1) : Point) ≠ 0) 0
  apply measure_congr
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hn] with z hz
  apply propext
  change (z ∈ (half S j).set \ ⋃ i, (halfFamily p j l u ho i).set) ↔
    (z ∈ (half S j).set \ ⋃ i, (family p l u ho i).set)
  rw [union_three,union_three]
  simp only [Set.mem_sdiff,Set.mem_union]
  by_cases hmem : z ∈ (half S j).set
  · have hs : if j then 0 ≤ z.2 else z.2 ≤ 0 := by
      have hb := half_y_bounds S j hmem
      cases j
      · simpa [Shape.Y,max_eq_left (neg_nonpos.mpr S.hd.le)] using hb.2
      · simpa [Shape.Y,min_eq_left S.hb.le] using hb.1
    have he := cut_mem_iff j hz hs (l := l) (u := u)
    change (z ∈ (half S j).set ∧ ¬ (z ∈ (p 0).set ∨ z ∈ (p 1).set ∨
      (cut j l ≤ 0*z.1+1*z.2 ∧ 0*z.1+1*z.2 ≤ cut j u))) ↔
      (z ∈ (half S j).set ∧ ¬ (z ∈ (p 0).set ∨ z ∈ (p 1).set ∨
      (l ≤ 0*z.1+1*z.2 ∧ 0*z.1+1*z.2 ≤ u)))
    simp only [zero_mul,one_mul,zero_add,he]
  · simp only [hmem,false_and]

def halfWidth (S : Shape) (j : Bool) (l u : ℝ) : ℝ :=
  (cut j u-cut j l)/|S.Y j|

def pairWidth (S : Shape) (p : Fin 2 → Plank) : ℝ := ∑ i, relativeWidth S (p i)

def budget (S : Shape) (p : Fin 2 → Plank) (l u : ℝ) : ℝ :=
  pairWidth S p+(u-l)/(S.b+S.d)

theorem family_budget (S : Shape) (p : Fin 2 → Plank) (l u : ℝ) (ho : l ≤ u) :
    (∑ i, relativeWidth S (family p l u ho i)) = budget S p l u := by
  simp only [Fin.sum_univ_three,family,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  change relativeWidth S (p 0)+relativeWidth S (p 1)+relativeWidth S (transverse l u ho) = _
  rw [transverse_relativeWidth]
  simp only [budget,pairWidth,Fin.sum_univ_two]

theorem half_budget (S : Shape) (p : Fin 2 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (j : Bool) (l u : ℝ) (ho : l ≤ u) :
    (∑ i, ((halfFamily p j l u ho i).hi-(halfFamily p j l u ho i).lo)/
      rangeWidth (half S j).set (direction (halfFamily p j l u ho i).u)) =
        pairWidth S p+halfWidth S j l u := by
  simp only [Fin.sum_univ_three,halfFamily,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rw [range_triangle _ _ (h 0 j),range_triangle _ _ (h 1 j)]
  change (p 0).relWidth (half S j)+(p 1).relWidth (half S j)+
    (cut j u-cut j l)/rangeWidth (half S j).set (direction (0,1)) = _
  rw [relativeWidth_half S _ (h 0),relativeWidth_half S _ (h 1),transverse_range_half]
  simp only [pairWidth,halfWidth,Fin.sum_univ_two]

theorem half_lower_bound (S : Shape) (p : Fin 2 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (j : Bool) (l u : ℝ) (ho : l ≤ u) :
    (max 0 (1-pairWidth S p-halfWidth S j l u))^2*(volume (half S j).set).toReal ≤
      (volume ((half S j).set \ ⋃ i, (family p l u ho i).set)).toReal := by
  have hw (i : Fin 3) : 0 < rangeWidth (half S j).set (direction (halfFamily p j l u ho i).u) := by
    fin_cases i
    · change 0 < rangeWidth (half S j).set (direction (p 0).u)
      rw [range_triangle _ _ (h 0 j)]
      exact width_pos _ (p 0).u_ne_zero
    · change 0 < rangeWidth (half S j).set (direction (p 1).u)
      rw [range_triangle _ _ (h 1 j)]
      exact width_pos _ (p 1).u_ne_zero
    · change 0 < rangeWidth (half S j).set (direction (0,1))
      rw [transverse_range_half]
      exact abs_pos.mpr (S.Y_ne j)
  have hb := product_lower_bound (compact_half S j) (convex_triangle (half S j))
    ⟨(half S j).A,mem_A (half S j)⟩ (halfFamily p j l u ho) hw
  rw [half_budget S p h j l u ho,clipped_gap] at hb
  simpa only [sub_add_eq_sub_sub] using hb

theorem half_width_mean (S : Shape) (l u : ℝ) :
    (∑ j : Bool, |S.Y j| * halfWidth S j l u) = u-l := by
  have hh (t : ℝ) : min t 0 + max t 0 = t := by simp
  have hc (j : Bool) : |S.Y j| * halfWidth S j l u = cut j u-cut j l := by
    dsimp [halfWidth]
    field_simp [abs_ne_zero.mpr (S.Y_ne j)]
  simp only [hc]
  simp only [Fintype.sum_bool,cut,Bool.false_eq_true,if_false,if_true]
  linarith only [hh l,hh u]

theorem half_deficit_mean (S : Shape) (p : Fin 2 → Plank) (l u : ℝ) :
    (∑ j : Bool, (volume (half S j).set).toReal*(1-pairWidth S p-halfWidth S j l u)) =
      (1-budget S p l u)*(∑ j : Bool, (volume (half S j).set).toReal) := by
  have hw := half_width_mean S l u
  have hs : (∑ j : Bool, |S.Y j|) = S.b+S.d := by
    simp [Shape.Y,abs_of_pos S.hb,abs_of_pos S.hd]
  have hmean : (∑ j : Bool, |S.Y j| * (1-pairWidth S p-halfWidth S j l u)) =
      (1-budget S p l u)*(∑ j : Bool, |S.Y j|) := by
    calc
      _ = (1-pairWidth S p)*(∑ j : Bool, |S.Y j|)-(u-l) := by
        rw [← hw,Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [hs]
        dsimp [budget]
        field_simp [(add_pos S.hb S.hd).ne']
        ring
  calc
    _ = ((S.a+S.c)/2)*(∑ j : Bool, |S.Y j| * (1-pairWidth S p-halfWidth S j l u)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [half_area]
      ring
    _ = ((S.a+S.c)/2)*((1-budget S p l u)*(∑ j : Bool, |S.Y j|)) := by rw [hmean]
    _ = _ := by
      simp only [Finset.mul_sum,half_area]
      apply Finset.sum_congr rfl
      intro j _
      ring

end Quant.CrossedQuadrilateralCommonPairSplit

/-- info: 'Quant.CrossedQuadrilateralCommonPairSplit.half_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCommonPairSplit.half_lower_bound
