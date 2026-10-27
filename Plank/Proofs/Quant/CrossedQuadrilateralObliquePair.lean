/- A vertical band and a band with opposite Y supports: direction necessity. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralObliqueMerge
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonPairCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralObliquePair
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralSectionProfile
open CrossedQuadrilateralSectionGeometry
open CrossedQuadrilateralCommonSupport CrossedQuadrilateralCommonPairSplit
open CrossedQuadrilateralSupport
open scoped BigOperators

def swappedPlank (k lo hi : ℝ) (ho : lo ≤ hi) : Plank where
  u := (1,k)
  u_ne_zero := by simp
  lo := lo
  hi := hi
  lo_le_hi := ho

theorem common (S : Shape) {k : ℝ} (hk : YSupports S k) (lo hi : ℝ) (ho : lo ≤ hi) :
    CommonSupports (transpose S) (swappedPlank k lo hi ho) := by
  have h₁ := (div_le_iff₀ S.hc).mp hk.1
  have h₂ := (le_div_iff₀ S.ha).mp hk.2.1
  have h₃ := (div_le_iff₀ S.ha).mp hk.2.2.1
  have h₄ := (le_div_iff₀ S.hc).mp hk.2.2.2
  intro j
  change dot (1,k) (-S.d,0) ≤ dot (1,k) (0,(transpose S).Y j) ∧
    dot (1,k) (0,(transpose S).Y j) ≤ dot (1,k) (S.b,0)
  cases j <;> simp only [dot,Shape.Y,transpose,Bool.false_eq_true,if_false,if_true,
    one_mul,mul_zero,zero_add,add_zero,mul_neg] <;> constructor <;>
    nlinarith only [h₁,h₂,h₃,h₄]

theorem width (S : Shape) {k : ℝ} (hk : YSupports S k) (lo hi : ℝ) (ho : lo ≤ hi) :
    relativeWidth (transpose S) (swappedPlank k lo hi ho) = (hi-lo)/(S.b+S.d) := by
  rw [relativeWidth,range_body _ _ (common S hk lo hi ho)]
  simp only [CommonMiddleAffineTransport.span,CrossedQuadrilateralDiagonalSplit.half,
    swappedPlank,transpose,dot,one_mul,mul_zero,add_zero,sub_neg_eq_add]

def pair (k lo hi : ℝ) (ho : lo ≤ hi) : Fin 2 → Plank :=
  ![swappedPlank k lo ((lo+hi)/2) (by linarith only [ho]),
    swappedPlank k ((lo+hi)/2) hi (by linarith only [ho])]

theorem pair_common (S : Shape) {k : ℝ} (hk : YSupports S k) (lo hi : ℝ) (ho : lo ≤ hi) :
    ∀ i, CommonSupports (transpose S) (pair k lo hi ho i) := by
  intro i
  fin_cases i <;> apply common S hk

theorem pair_positive (S : Shape) {k lo hi : ℝ} (hk : YSupports S k) (ho : lo < hi) :
    ∀ i, 0 < relativeWidth (transpose S) (pair k lo hi ho.le i) := by
  intro i
  fin_cases i
  · change 0 < relativeWidth (transpose S) (swappedPlank k lo ((lo+hi)/2) _)
    rw [width S hk]
    apply div_pos _ (add_pos S.hb S.hd)
    linarith only [ho]
  · change 0 < relativeWidth (transpose S) (swappedPlank k ((lo+hi)/2) hi _)
    rw [width S hk]
    apply div_pos _ (add_pos S.hb S.hd)
    linarith only [ho]

theorem pair_budget (S : Shape) {k : ℝ} (hk : YSupports S k) (lo hi l u : ℝ) (ho : lo ≤ hi) :
    budget (transpose S) (pair k lo hi ho) l u =
      (u-l)/(S.a+S.c)+(hi-lo)/(S.b+S.d) := by
  simp only [budget,pairWidth,Fin.sum_univ_two,pair,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [width S hk,width S hk]
  dsimp only [transpose]
  ring

theorem pair_union (k lo hi : ℝ) (ho : lo ≤ hi) :
    (pair k lo hi ho 0).set ∪ (pair k lo hi ho 1).set =
      {z : Point | lo ≤ z.1+k*z.2 ∧ z.1+k*z.2 ≤ hi} := by
  ext z
  change ((lo ≤ dot (1,k) z ∧ dot (1,k) z ≤ (lo+hi)/2) ∨
    ((lo+hi)/2 ≤ dot (1,k) z ∧ dot (1,k) z ≤ hi)) ↔ _
  simp only [dot,one_mul,mem_ofPred_eq]
  constructor
  · rintro (h | h) <;> constructor <;> linarith only [h.1,h.2,ho]
  · intro h
    rcases le_total (z.1+k*z.2) ((lo+hi)/2) with hm | hm
    · exact Or.inl ⟨h.1,hm⟩
    · exact Or.inr ⟨hm,h.2⟩

theorem family_image (k lo hi l u : ℝ) (ho : lo ≤ hi) (hu : l ≤ u) :
    (⋃ i, (family (pair k lo hi ho) l u hu i).set) =
      swap '' (UnimodalPlanarMerge.band l u ∪ oblique k lo hi) := by
  rw [union_three]
  change (pair k lo hi ho 0).set ∪ ((pair k lo hi ho 1).set ∪ (transverse l u hu).set) = _
  rw [← Set.union_assoc,pair_union]
  ext z
  change ((lo ≤ z.1+k*z.2 ∧ z.1+k*z.2 ≤ hi) ∨
    (l ≤ dot (0,1) z ∧ dot (0,1) z ≤ u)) ↔ _
  simp only [dot,zero_mul,one_mul,zero_add]
  constructor
  · intro h
    refine ⟨(z.2,z.1),?_,by cases z; rfl⟩
    change (l ≤ z.2 ∧ z.2 ≤ u) ∨ (lo ≤ k*z.2+z.1 ∧ k*z.2+z.1 ≤ hi)
    simpa only [add_comm,or_comm] using h
  · rintro ⟨w,hw,rfl⟩
    change ((lo ≤ w.2+k*w.1 ∧ w.2+k*w.1 ≤ hi) ∨ (l ≤ w.1 ∧ w.1 ≤ u))
    simpa only [UnimodalPlanarMerge.band,oblique,mem_union,mem_ofPred_eq,add_comm,or_comm] using hw

theorem volume_swap (A : Set Point) : volume (swap '' A) = volume A := by
  have hs : swap '' A = Prod.swap ⁻¹' A := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hz
      exact ⟨(z.2,z.1),hz,by cases z; rfl⟩
  rw [hs]
  rw [Measure.volume_eq_prod ℝ ℝ]
  exact Measure.measurePreserving_swap.measure_preimage_emb
    MeasurableEquiv.prodComm.measurableEmbedding A

theorem gap_swap (S : Shape) (A : Set Point) :
    volume ((transpose S).body \ swap '' A) = volume (S.body \ A) := by
  rw [← swap_body,← Set.image_sdiff swap.injective,volume_swap]

theorem lower_bound (S : Shape) {k lo hi l u : ℝ} (hk : YSupports S k)
    (ho : lo ≤ hi) (hu : l ≤ u)
    (hR : (u-l)/(S.a+S.c)+(hi-lo)/(S.b+S.d) < 1) :
    (1-((u-l)/(S.a+S.c)+(hi-lo)/(S.b+S.d)))^2*(volume S.body).toReal ≤
      (volume (S.body \ (UnimodalPlanarMerge.band l u ∪ oblique k lo hi))).toReal := by
  have hh := product_lower_bound (compact_body (transpose S)) (convex_body (transpose S))
    ⟨0,zero_mem (transpose S)⟩ (family (pair k lo hi ho) l u hu)
    (fun i => direction_width_pos (transpose S) (family (pair k lo hi ho) l u hu i).u_ne_zero)
  change (max 0 (1-∑ i, relativeWidth (transpose S) (family (pair k lo hi ho) l u hu i)))^2*
    (volume (transpose S).body).toReal ≤ _ at hh
  rw [family_budget,pair_budget S hk, family_image,gap_swap,
    ← swap_body S,volume_swap,max_eq_right (sub_pos.mpr hR).le] at hh
  exact hh

/-- A single vertical band and a positive Y-supported band can be sharp
only when the latter is horizontal. Splitting it reuses the proved common-pair theorem. -/
theorem direction_of_equality (S : Shape) {k lo hi l u : ℝ} (hk : YSupports S k)
    (ho : lo < hi) (hu : l < u)
    (hR : (u-l)/(S.a+S.c)+(hi-lo)/(S.b+S.d) < 1)
    (he : (volume (S.body \ (UnimodalPlanarMerge.band l u ∪ oblique k lo hi))).toReal =
      (1-((u-l)/(S.a+S.c)+(hi-lo)/(S.b+S.d)))^2*(volume S.body).toReal) : k = 0 := by
  have hb : budget (transpose S) (pair k lo hi ho.le) l u < 1 := by
    rwa [pair_budget S hk]
  have he' : (volume ((transpose S).body \ ⋃ i, (family (pair k lo hi ho.le) l u hu.le i).set)).toReal =
      (1-budget (transpose S) (pair k lo hi ho.le) l u)^2*(volume (transpose S).body).toReal := by
    rw [family_image,gap_swap,pair_budget S hk,← swap_body S,volume_swap]
    exact he
  exact CrossedQuadrilateralCommonPairRigidity.parallel_of_equality (transpose S)
    (pair k lo hi ho.le) (pair_common S hk lo hi ho.le) (pair_positive S hk ho) l u hu hb he' 0

end Quant.CrossedQuadrilateralObliquePair

/-- info: 'Quant.CrossedQuadrilateralObliquePair.direction_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralObliquePair.direction_of_equality
