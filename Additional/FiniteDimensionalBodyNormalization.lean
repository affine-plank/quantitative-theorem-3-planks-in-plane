/- A maximum determinant frame at one interior point normalizes a convex
body in every finite dimension. No plank theorem or vertex bound is used. -/
module

public import Mathlib.Analysis.Convex.Measure
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalBodyNormalization

open Set Metric MeasureTheory
open scoped BigOperators

abbrev Point (n : ℕ) := Fin n → ℝ

variable {n : ℕ}

def frameMatrix (A : Point n) (v : Fin n → Point n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => v j i-A i

def determinant (A : Point n) (v : Fin n → Point n) : ℝ := (frameMatrix A v).det

def frameLinear (A : Point n) (v : Fin n → Point n) : Point n →ₗ[ℝ] Point n :=
  Matrix.toLin' (frameMatrix A v)

theorem det_frameLinear (A : Point n) (v : Fin n → Point n) :
    LinearMap.det (frameLinear A v)=determinant A v := by
  rw [← LinearMap.det_toMatrix']
  simp [frameLinear,determinant]

theorem exists_nondegenerate {K : Set (Point n)} {A : Point n} (hA : A∈interior K) :
    ∃ v : Fin n → Point n, (∀ i,v i∈K) ∧ determinant A v≠0 := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hA)
  let v : Fin n → Point n := fun i => A+Pi.single i (r/2)
  have hv (i) : v i∈K := by
    apply hball
    rw [mem_ball,dist_eq_norm]
    have he : v i-A=Pi.single i (r/2) := by simp [v]
    rw [he]
    apply (pi_norm_lt_iff hr).mpr
    intro j
    by_cases hj : j=i
    · subst j; simp only [Pi.single_eq_same,Real.norm_eq_abs,abs_of_pos (half_pos hr)]; linarith
    · simp [Pi.single_eq_of_ne hj,hr]
  refine ⟨v,hv,?_⟩
  have he : frameMatrix A v=Matrix.diagonal (fun _ : Fin n => r/2) := by
    ext i j
    by_cases h : i=j
    · subst j; simp [frameMatrix,v,Matrix.diagonal]
    · simp [frameMatrix,v,Matrix.diagonal,h]
  rw [determinant,he,Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => (half_pos hr).ne')

/-- Keep one interior point fixed and maximize the absolute frame determinant
over all remaining simplex vertices in the compact body. -/
theorem exists_maximum_frame {K : Set (Point n)} (hK : IsCompact K)
    {A : Point n} (hA : A∈interior K) :
    ∃ v : Fin n → Point n, (∀ i,v i∈K) ∧ determinant A v≠0 ∧
      ∀ w : Fin n → Point n, (∀ i,w i∈K) → |determinant A w|≤|determinant A v| := by
  obtain ⟨v,hv,hn⟩ := exists_nondegenerate hA
  have hc : IsCompact (Set.pi univ (fun _ : Fin n => K)) := isCompact_univ_pi (fun _ => hK)
  have hf : Continuous (fun w : Fin n → Point n => |determinant A w|) := by
    unfold determinant frameMatrix
    exact (show Continuous (fun w : Fin n → Point n =>
      (fun i j => w j i-A i : Matrix (Fin n) (Fin n) ℝ)) by fun_prop).matrix_det.abs
  obtain ⟨w,hw,hm⟩ := hc.exists_isMaxOn
    ⟨v,by simpa only [mem_pi,mem_univ,true_implies] using hv⟩ hf.continuousOn
  have hwK : ∀ i,w i∈K := by simpa only [mem_pi,mem_univ,true_implies] using hw
  refine ⟨w,hwK,?_,?_⟩
  · exact abs_pos.mp ((abs_pos.mpr hn).trans_le (hm (by simpa using hv)))
  · intro z hz
    exact hm (by simpa only [mem_pi,mem_univ,true_implies] using hz)

def frameChart (A : Point n) (v : Fin n → Point n) (h : determinant A v≠0) :
    Point n ≃ᵃ[ℝ] Point n :=
  (LinearMap.equivOfIsUnitDet (show IsUnit (LinearMap.det (frameLinear A v)) by
    rw [det_frameLinear]; exact isUnit_iff_ne_zero.mpr h)).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (Point n) A)

theorem frameChart_apply (A : Point n) (v : Fin n → Point n)
    (h : determinant A v≠0) (x : Point n) :
    frameChart A v h x=A+∑ j,x j • (v j-A) := by
  change A+LinearMap.equivOfIsUnitDet _ x=_
  rw [LinearMap.equivOfIsUnitDet_apply]
  congr 1
  ext i
  simp [frameLinear,Matrix.toLin'_apply,Matrix.mulVec,frameMatrix,dotProduct,mul_comm]

/-- Replacing just the i-th vertex multiplies the frame determinant by its
i-th coordinate. This is the only maximality calculation needed. -/
theorem determinant_update (A : Point n) (v : Fin n → Point n)
    (h : determinant A v≠0) (x : Point n) (i : Fin n) :
    determinant A (Function.update v i (frameChart A v h x))=x i*determinant A v := by
  have he : frameMatrix A (Function.update v i (frameChart A v h x))=
      (frameMatrix A v).updateCol i (fun k => ∑ j,x j*(frameMatrix A v) k j) := by
    ext k j
    by_cases hj : j=i
    · subst j
      simp [frameMatrix,frameChart_apply,Matrix.updateCol]
    · simp [frameMatrix,Matrix.updateCol,hj]
  rw [determinant,he]
  simpa only [smul_eq_mul,determinant] using Matrix.det_updateCol_sum (frameMatrix A v) i x

theorem coordinates_le_one {K : Set (Point n)} {A : Point n} {v : Fin n → Point n}
    (hv : ∀ i,v i∈K) (h : determinant A v≠0)
    (hmax : ∀ w : Fin n → Point n, (∀ i,w i∈K) → |determinant A w|≤|determinant A v|)
    {x : Point n} (hx : frameChart A v h x∈K) (i : Fin n) : |x i|≤1 := by
  have hu : ∀ j,Function.update v i (frameChart A v h x) j∈K := by
    intro j; by_cases hj : j=i
    · subst j; simpa using hx
    · simpa [Function.update_of_ne hj] using hv j
  have hh := hmax _ hu
  rw [determinant_update,abs_mul] at hh
  exact (mul_le_mul_iff_left₀ (abs_pos.mpr h)).mp (by simpa [mul_comm] using hh)

theorem frameChart_mem {K : Set (Point n)} (hK : Convex ℝ K)
    {A : Point n} {v : Fin n → Point n} (hA : A∈K) (hv : ∀ i,v i∈K)
    (h : determinant A v≠0) {x : Point n} (hx : ∀ i,0≤x i) (hs : ∑ i,x i≤1) :
    frameChart A v h x∈K := by
  let w : Fin (n+1) → ℝ := Fin.cons (1-∑ i,x i) x
  let z : Fin (n+1) → Point n := Fin.cons A v
  have hw (i) : 0≤w i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact sub_nonneg.mpr hs
    · exact hx j
  have hsum : ∑ i,w i=1 := by simp [w,Fin.sum_univ_succ]
  have hz (i) : z i∈K := by
    refine Fin.cases hA (fun j => hv j) i
  have hm := hK.sum_mem (t := Finset.univ) (fun i _ => hw i) hsum (fun i _ => hz i)
  convert hm using 1
  rw [frameChart_apply]
  ext k
  simp only [w,z,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,
    Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,
    mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  ring

def innerRadius (n : ℕ) : ℝ := 1/((n : ℝ)+1)^2

theorem innerRadius_pos (n : ℕ) : 0 < innerRadius n := by
  apply one_div_pos.mpr
  exact sq_pos_of_pos (by positivity)

/-- Uniform affine normalization for the sup norm on R^n. The deliberately
simple constants also work in dimension zero. -/
theorem exists_ball_sandwich {K : Set (Point n)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hfull : (interior K).Nonempty) :
    ∃ F : Point n ≃ᵃ[ℝ] Point n,
      closedBall 0 (innerRadius n)⊆F ⁻¹' K ∧ F ⁻¹' K⊆closedBall 0 2 := by
  obtain ⟨A,hA⟩ := hfull
  obtain ⟨v,hv,hn,hm⟩ := exists_maximum_frame hK hA
  let c : ℝ := 1/((n : ℝ)+1)
  let r : ℝ := innerRadius n
  have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hN : 0<(n : ℝ)+1 := by positivity
  have hr : 0<r := innerRadius_pos n
  have hc : 0<c := one_div_pos.mpr hN
  have hc1 : c≤1 := (div_le_one hN).mpr (by linarith only [hn0])
  have hrc : r≤c := by
    exact div_le_div_of_nonneg_left zero_le_one hN (by nlinarith only [hn0])
  have hsum : (n : ℝ)*(c+r)≤1 := by
    have he : 1-(n : ℝ)*(c+r)=r := by
      dsimp only [c,r,innerRadius]
      field_simp
      ring
    linarith only [he,hr]
  let F := (AffineEquiv.constVAdd ℝ (Point n) (fun _ => c)).trans (frameChart A v hn)
  have hF (x : Point n) : F x=frameChart A v hn ((fun _ => c)+x) := rfl
  refine ⟨F,?_,?_⟩
  · intro x hx
    have hh := (pi_norm_le_iff_of_nonneg hr.le).mp (mem_closedBall_zero_iff.mp hx)
    change F x∈K
    rw [hF]
    apply frameChart_mem hconv (interior_subset hA) hv hn
    · intro i
      have hi := (abs_le.mp (show |x i|≤r from hh i)).1
      change 0≤c+x i
      linarith only [hi,hrc]
    · calc
        ∑ i : Fin n, (c+x i) ≤ ∑ _i : Fin n, (c+r) := by
          apply Finset.sum_le_sum
          intro i _
          exact add_le_add le_rfl (abs_le.mp (show |x i|≤r from hh i)).2
        _ = (n : ℝ)*(c+r) := by simp [mul_add]
        _ ≤ 1 := hsum
  · intro x hx
    have hh (i) := coordinates_le_one hv hn hm (show frameChart A v hn ((fun _ => c)+x)∈K from hx) i
    apply mem_closedBall_zero_iff.mpr
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤2)).mpr
    intro i
    have hi := abs_le.mp (hh i)
    change -(1 : ℝ)≤c+x i ∧ c+x i≤1 at hi
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith only [hi.1,hi.2,hc,hc1]

/-- Positive Haar volume supplies full dimension without a separate interior
hypothesis. -/
theorem exists_ball_sandwich_of_volume_pos (μ : Measure (Point n)) [μ.IsAddHaarMeasure]
    {K : Set (Point n)} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0<μ.real K) :
    ∃ F : Point n ≃ᵃ[ℝ] Point n,
      closedBall 0 (innerRadius n)⊆F ⁻¹' K ∧ F ⁻¹' K⊆closedBall 0 2 := by
  apply exists_ball_sandwich hK hconv
  by_contra hn
  have he : interior K=∅ := not_nonempty_iff_eq_empty.mp hn
  have hs : K⊆frontier K := by rw [frontier,he,sdiff_empty]; exact subset_closure
  have hz := measure_mono_null hs (hconv.addHaar_frontier μ)
  simp [Measure.real,hz] at hV

end Plank.FiniteDimensionalBodyNormalization
