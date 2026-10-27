/- A full-rank family of n+1 affine coordinates summing to one defines a simplex. -/
module
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.SimplicialHalfspaces

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

def lift (b : I → ℝ) (q : I → E →ₗ[ℝ] ℝ) : (ℝ × E) →ₗ[ℝ] (I → ℝ) where
  toFun z i := z.1 * b i + q i z.2
  map_add' z w := by ext i; simp [add_mul]; ring
  map_smul' a z := by ext i; simp [mul_add]; ring

omit [DecidableEq I] [FiniteDimensional ℝ E] in
theorem sum_lift (b : I → ℝ) (q : I → E →ₗ[ℝ] ℝ)
    (hb : ∑ i, b i = 1) (hq : ∀ x, ∑ i, q i x = 0) (z : ℝ × E) :
    ∑ i, lift b q z i = z.1 := by
  simp only [lift,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_add_distrib,
    ← Finset.mul_sum,hb,hq,mul_one,add_zero]

omit [DecidableEq I] [FiniteDimensional ℝ E] in
theorem lift_injective (b : I → ℝ) (q : I → E →ₗ[ℝ] ℝ)
    (hb : ∑ i, b i = 1) (hq : ∀ x, ∑ i, q i x = 0)
    (hker : ∀ x, (∀ i, q i x = 0) → x = 0) : Function.Injective (lift b q) := by
  intro z w hzw
  have hzero : lift b q (z-w) = 0 := by rw [map_sub,hzw,sub_self]
  have hf : (z-w).1 = 0 := by
    rw [← sum_lift b q hb hq (z-w),hzero]
    simp
  have hs : (z-w).2 = 0 := by
    apply hker
    intro i
    have hi := congrFun hzero i
    change (z-w).1*b i+q i (z-w).2 = 0 at hi
    simpa only [hf,zero_mul,zero_add] using hi
  exact sub_eq_zero.mp (Prod.ext hf hs)

/-- Positive halfspaces described by n+1 affine coordinates of total one
are exactly the convex hull of their coordinate vertices. No positivity of
the offsets is required; injectivity and the dimension equation suffice. -/
theorem exists_vertices (b : I → ℝ) (q : I → E →ₗ[ℝ] ℝ)
    (hb : ∑ i, b i = 1) (hq : ∀ x, ∑ i, q i x = 0)
    (hker : ∀ x, (∀ i, q i x = 0) → x = 0)
    (hdim : Fintype.card I = Module.finrank ℝ E + 1) :
    ∃ v : I → E, AffineIndependent ℝ v ∧
      (∀ i k, b k+q k (v i) = if k=i then 1 else 0) ∧
      {x : E | ∀ i, 0 ≤ b i+q i x} = convexHull ℝ (Set.range v) := by
  have hdim' : Module.finrank ℝ (ℝ × E) = Module.finrank ℝ (I → ℝ) := by
    simp [Module.finrank_prod,hdim,Nat.add_comm]
  let e := (lift b q).linearEquivOfInjective (lift_injective b q hb hq hker) hdim'
  let v (i : I) : E := (e.symm (Pi.single i 1)).2
  have hfirst (i : I) : (e.symm (Pi.single i 1)).1 = 1 := by
    rw [← sum_lift b q hb hq (e.symm (Pi.single i 1))]
    change ∑ k, e (e.symm (Pi.single i 1)) k = 1
    simp
  have hv (i k : I) : b k+q k (v i) = if k=i then 1 else 0 := by
    have h := congrFun (e.apply_symm_apply (Pi.single i 1)) k
    change (e.symm (Pi.single i 1)).1*b k+q k (v i) =
      (Pi.single i (1 : ℝ) : I → ℝ) k at h
    simpa [hfirst,Pi.single_apply,eq_comm] using h
  let f : E →ᵃ[ℝ] (I → ℝ) :=
    { toFun := fun x i => b i+q i x
      linear :=
        { toFun := fun x i => q i x
          map_add' := by intros; ext; simp
          map_smul' := by intros; ext; simp }
      map_vadd' := by intros; ext; simp; ring }
  have hai : AffineIndependent ℝ v := by
    apply AffineIndependent.of_comp f
    have hfv : f ∘ v = fun i => Pi.single i (1 : ℝ) := by
      ext i k
      simpa [f,Pi.single_apply,eq_comm] using hv i k
    rw [hfv]
    have hfun : (fun i : I => Pi.single i (1 : ℝ)) = (Pi.basisFun ℝ I) := by
      funext i
      exact (Pi.basisFun_apply ℝ I i).symm
    rw [hfun]
    exact (Pi.basisFun ℝ I).linearIndependent.affineIndependent
  have hsum (x : E) : ∑ i, (b i+q i x) = 1 := by
    rw [Finset.sum_add_distrib,hb,hq,add_zero]
  have hrepr (x : E) : ∑ i, (b i+q i x) • v i = x := by
    have hz : (∑ i, (b i+q i x) • e.symm (Pi.single i 1)) = (1,x) := by
      apply e.injective
      rw [map_sum]
      simp only [map_smul,e.apply_symm_apply]
      ext k
      simp [e,lift,Pi.single_apply,mul_ite]
    have h := congrArg (LinearMap.snd ℝ ℝ E) hz
    simpa only [map_sum,map_smul,LinearMap.snd_apply,v] using h
  have hconv : Convex ℝ {x : E | ∀ i, 0 ≤ b i+q i x} := by
    intro x hx y hy a c ha hc hac i
    have hid : b i+q i (a • x+c • y) = a*(b i+q i x)+c*(b i+q i y) := by
      simp only [map_add,map_smul,smul_eq_mul]
      linear_combination -b i*hac
    rw [hid]
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hc (hy i))
  refine ⟨v,hai,hv,Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact mem_convexHull_of_exists_fintype (fun i => b i+q i x) v hx (hsum x)
      (fun i => Set.mem_range_self i) (hrepr x)
  · apply convexHull_min _ hconv
    rintro _ ⟨i,rfl⟩ k
    rw [hv]
    split_ifs <;> norm_num

end Plank.Convex.SimplicialHalfspaces

/-- info: 'Plank.Convex.SimplicialHalfspaces.exists_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.SimplicialHalfspaces.exists_vertices
