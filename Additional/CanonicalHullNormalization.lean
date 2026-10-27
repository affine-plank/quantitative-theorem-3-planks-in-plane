/- A fixed translated simplex and cube for the finite-hull sampler.
The translation puts a uniform inner ball at the origin. -/
module

public import FiniteHullSampling
public import FiniteDimensionalBodyNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.CanonicalHullNormalization

open Set Metric TopologicalSpace
open FiniteDimensionalBodyNormalization (Point innerRadius innerRadius_pos)
open scoped BigOperators

def center (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
def shift (n : ℕ) : Point n ≃ᵃ[ℝ] Point n :=
  AffineEquiv.constVAdd ℝ (Point n) (fun _ => center n)
def vertex (n : ℕ) : Fin (n+1) → Point n :=
  Fin.cons (fun _ => -center n) (fun i => Pi.single i 1 - (fun _ => center n))
def anchor (n : ℕ) : Finset (Point n) := by
  classical
  exact Finset.univ.image (vertex n)
def cube (n : ℕ) : Set (Point n) := shift n ⁻¹' Icc (-1) 1

theorem center_pos (n : ℕ) : 0 < center n := by unfold center; positivity

theorem center_le_one (n : ℕ) : center n ≤ 1 := by
  unfold center
  exact (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    (le_add_of_nonneg_left (Nat.cast_nonneg n))

theorem anchor_nonempty (n : ℕ) : (anchor n).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

theorem vertex_mem_anchor (n : ℕ) (i : Fin (n+1)) : vertex n i ∈ anchor n := by
  classical
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

theorem convex_cube (n : ℕ) : Convex ℝ (cube n) :=
  (convex_Icc (-1 : Point n) 1).affine_preimage (shift n).toAffineMap

theorem anchor_subset_cube (n : ℕ) : (anchor n : Set (Point n)) ⊆ cube n := by
  classical
  intro x hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  change (-1 : Point n) ≤ shift n (vertex n i) ∧ shift n (vertex n i) ≤ 1
  constructor <;> intro j <;> cases i using Fin.cases with
  | zero => norm_num [shift,vertex]
  | succ i =>
    by_cases h : j=i
    · subst j; norm_num [shift,vertex]
    · simp [shift,vertex,Pi.single_eq_of_ne h]

theorem cube_subset_ball (n : ℕ) : cube n ⊆ closedBall (0 : Point n) 2 := by
  intro x hx
  apply mem_closedBall_zero_iff.mpr
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤2)).mpr
  intro i
  have hl := hx.1 i
  have hu := hx.2 i
  change -1 ≤ center n+x i at hl
  change center n+x i ≤ 1 at hu
  rw [Real.norm_eq_abs,abs_le]
  have hc := center_pos n
  have hc1 := center_le_one n
  constructor <;> linarith only [hl,hu,hc,hc1]

theorem ball_subset_anchor_hull (n : ℕ) :
    closedBall (0 : Point n) (innerRadius n) ⊆ convexHull ℝ (anchor n : Set (Point n)) := by
  intro x hx
  let c := center n
  let r := innerRadius n
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hN : 0<(n:ℝ)+1 := by positivity
  have hr : 0<r := innerRadius_pos n
  have hrc : r≤c := by
    exact div_le_div_of_nonneg_left zero_le_one hN (by nlinarith only [hn0])
  have hsum : (n:ℝ)*(c+r)≤1 := by
    have he : 1-(n:ℝ)*(c+r)=r := by
      dsimp only [c,r,center,innerRadius]
      field_simp
      ring
    linarith only [he,hr]
  have hh := (pi_norm_le_iff_of_nonneg hr.le).mp (mem_closedBall_zero_iff.mp hx)
  let y : Point n := fun i => c+x i
  have hy (i) : 0≤y i := by
    have hi := (abs_le.mp (show |x i|≤r from hh i)).1
    dsimp [y]
    linarith only [hi,hrc]
  have hy1 : ∑ i,y i≤1 := by
    calc
      ∑ i,y i ≤ ∑ _i : Fin n,(c+r) := by
        apply Finset.sum_le_sum
        intro i _
        exact add_le_add le_rfl (abs_le.mp (show |x i|≤r from hh i)).2
      _ = (n:ℝ)*(c+r) := by simp [mul_add]
      _ ≤ 1 := hsum
  let w : Fin (n+1) → ℝ := Fin.cons (1-∑ i,y i) y
  have hw (i) : 0≤w i := Fin.cases (sub_nonneg.mpr hy1) hy i
  have hw1 : ∑ i,w i=1 := by simp [w,Fin.sum_univ_succ]
  have hm := (convex_convexHull ℝ (anchor n : Set (Point n))).sum_mem
    (t := Finset.univ) (fun i _ => hw i) hw1
    (fun i _ => subset_convexHull ℝ _ (vertex_mem_anchor n i))
  convert hm using 1
  ext k
  simp [w,vertex,Fin.sum_univ_succ,Pi.single_apply,mul_sub,Finset.sum_sub_distrib,
    ← Finset.sum_mul,y,c]
  ring

theorem shift_vertex (n : ℕ) (i : Fin (n+1)) :
    shift n (vertex n i) =
      (Fin.cons (0 : Point n) (fun j : Fin n => Pi.single j (1:ℝ)) : Fin (n+1) → Point n) i := by
  cases i using Fin.cases <;> ext j <;> simp [shift,vertex]

theorem shift_image_anchor (n : ℕ) :
    shift n '' (anchor n : Set (Point n)) =
      range (Fin.cons (0 : Point n) (fun j : Fin n => Pi.single j (1:ℝ)) :
        Fin (n+1) → Point n) := by
  classical
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i,(shift_vertex n i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨vertex n i,vertex_mem_anchor n i,shift_vertex n i⟩

/-- Translating the sampled hull back gives precisely the standard simplex
vertices and the translated free points, as used by the experiment. -/
theorem shift_image_sampleHull (n k : ℕ) (x : Fin k → Point n) :
    shift n '' (FiniteHullSampling.sampleHull (anchor n) (anchor_nonempty n) x : Set (Point n)) =
      convexHull ℝ (range (Fin.cons (0 : Point n) (fun j : Fin n => Pi.single j (1:ℝ)) :
        Fin (n+1) → Point n) ∪ range (fun i => shift n (x i))) := by
  change (shift n).toAffineMap '' convexHull ℝ ((anchor n : Set (Point n)) ∪ range x) = _
  rw [(shift n).toAffineMap.image_convexHull,Set.image_union]
  change convexHull ℝ (shift n '' (anchor n : Set (Point n)) ∪ shift n '' range x) = _
  rw [shift_image_anchor,← Set.range_comp']

/-- Every full-dimensional compact convex body has an affine copy containing
the same fixed simplex and contained in the same translated cube. -/
theorem exists_affine_anchored {n : ℕ} {K : Set (Point n)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hfull : (interior K).Nonempty) :
    ∃ F : Point n ≃ᵃ[ℝ] Point n,
      ∃ C : FiniteHullSampling.AnchoredBody (anchor n) (cube n),
        (C.1 : Set (Point n)) = F ⁻¹' K := by
  classical
  obtain ⟨a,ha⟩ := hfull
  obtain ⟨v,hv,hn,hm⟩ := FiniteDimensionalBodyNormalization.exists_maximum_frame hK ha
  let F := (shift n).trans (FiniteDimensionalBodyNormalization.frameChart a v hn)
  have hvert (i : Fin (n+1)) : F (vertex n i) ∈ K := by
    change FiniteDimensionalBodyNormalization.frameChart a v hn (shift n (vertex n i)) ∈ K
    rw [shift_vertex]
    cases i using Fin.cases with
    | zero =>
      simpa [FiniteDimensionalBodyNormalization.frameChart_apply] using interior_subset ha
    | succ i =>
      simpa [FiniteDimensionalBodyNormalization.frameChart_apply,Pi.single_apply] using hv i
  have hc : IsCompact (F ⁻¹' K) := by
    rw [show F ⁻¹' K = F.symm '' K by ext x; simp]
    exact hK.image F.symm.toAffineMap.continuous_of_finiteDimensional
  have hanchor : (anchor n : Set (Point n)) ⊆ F ⁻¹' K := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hvert i
  have hout : F ⁻¹' K ⊆ cube n := by
    intro x hx
    have hh (i) := FiniteDimensionalBodyNormalization.coordinates_le_one hv hn hm
      (show FiniteDimensionalBodyNormalization.frameChart a v hn (shift n x) ∈ K from hx) i
    exact ⟨fun i => (abs_le.mp (hh i)).1,fun i => (abs_le.mp (hh i)).2⟩
  refine ⟨F,⟨⟨⟨F ⁻¹' K,hc⟩,⟨vertex n 0,hvert 0⟩⟩,
    hconv.affine_preimage F.toAffineMap,hanchor,hout⟩,rfl⟩

end Plank.CanonicalHullNormalization
