/- A chart-free equality argument for actual windows with quadratic interactions. -/
module

public import Plank.Proofs.Quant.PlanarBalanceRigidity
public import Plank.Proofs.Quant.StationaryInteractionBalance
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarWindowEulerRigidity

open Set MeasureTheory PlanarQuantitative PlanarBodySectionDensity ConcaveDensity
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- The actual area margin on the simultaneous canonical width motion.
`P` is the value of a degree-two interaction term at the original windows. -/
def margin {ι : Type*} [Fintype ι] (K : Set Point) (f : ι → Point →ᵃ[ℝ] ℝ)
    (c r : ι → ℝ) (P t : ℝ) : ℝ :=
  (volume K).toReal-
    ∑ i, coveredArea K (f i) ((1-r i)*c i+t*(-r i*c i))
      (c i+(1-c i)*r i+t*(r i*(1-c i)))+
    (1+t)^2*P-(volume K).toReal*(1-(1+t)*(∑ i, r i))^2

/-- Every individual one-window Euler balance is an equality at a zero
local minimum of the actual margin. No Hessian or area-polynomial chart is
assumed. Existence of the densities and of this minimum remains explicit. -/
theorem balance_eq_of_local_min {ι : Type*} [Fintype ι]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : ι → Point →ᵃ[ℝ] ℝ) (D : ∀ i, BodySectionDensity K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (c r : ι → ℝ) (hc : ∀ i, c i ∈ Icc 0 1)
    (hr0 : ∀ i, 0 < r i) (hr1 : ∀ i, r i < 1) (P : ℝ)
    (hmin : IsLocalMin (margin K f c r P) 0) (hz : margin K f c r P 0 = 0) :
    ∀ i, 2*coveredArea K (f i) ((1-r i)*c i) (c i+(1-c i)*r i) =
      r i*canonicalDensity (D i).density (c i) (r i)+2*r i*(volume K).toReal := by
  let A := (volume K).toReal
  let R := ∑ i, r i
  let C (i) := coveredArea K (f i) ((1-r i)*c i) (c i+(1-c i)*r i)
  let d (i) := canonicalDensity (D i).density (c i) (r i)
  have hder (i) : HasDerivAt
      (fun t => coveredArea K (f i) ((1-r i)*c i+t*(-r i*c i))
        (c i+(1-c i)*r i+t*(r i*(1-c i)))) (r i*d i) 0 := by
    convert! (D i).line_deriv ((1-r i)*c i) (c i+(1-c i)*r i)
      (by nlinarith only [hr0 i]) (-r i*c i) (r i*(1-c i)) using 1
    dsimp [d,canonicalDensity]
    ring
  have hds : HasDerivAt
      (fun t : ℝ => ∑ i, coveredArea K (f i) ((1-r i)*c i+t*(-r i*c i))
        (c i+(1-c i)*r i+t*(r i*(1-c i)))) (∑ i, r i*d i) 0 :=
    HasDerivAt.fun_sum fun i _ => hder i
  have hdp : HasDerivAt (fun t : ℝ => (1+t)^2*P) (2*P) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2).mul_const P using 1
    norm_num
  have hdq : HasDerivAt (fun t : ℝ => A*(1-(1+t)*R)^2) (-2*A*(1-R)*R) 0 := by
    convert! (((((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const R).const_sub 1).pow 2).const_mul A using 1
    norm_num
    ring
  have hd : HasDerivAt (margin K f c r P)
      (-(∑ i, r i*d i)+2*P+2*A*(1-R)*R) 0 := by
    convert! ((hds.const_sub A).add hdp).sub hdq using 1
    ring
  have hstat := hmin.hasDerivAt_eq_zero hd
  have hzero : A-(∑ i, C i)+P-A*(1-R)^2 = 0 := by
    simpa only [margin,zero_mul,add_zero,one_pow,one_mul,C,A,R] using hz
  let J (i) := r i*d i+2*r i*A-2*C i
  have hJ (i) : 0 ≤ J i := sub_nonneg.mpr
    (StationaryInteractionBalance.coveredArea_balance hK hconv hne (f i) (D i)
      (hnorm i) (hunit i) (hc i) (hr0 i).le (hr1 i))
  have hsum : ∑ i, J i = 0 := by
    simp only [J,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
      ← Finset.sum_mul]
    change (∑ i, r i*d i)+2*R*A-2*(∑ i, C i) = 0
    nlinarith only [hstat,hzero]
  intro i
  have hi : J i = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hJ j)).mp hsum i
    (Finset.mem_univ i)
  exact (sub_eq_zero.mp hi).symm

/-- An actual zero minimum with degree-two interactions forces the body
to have at most four vertices. This is conditional on the displayed density
and minimum data, not a claim that every three-plank equality has those data. -/
theorem four_vertices_of_local_min {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (f : ι → Point →ᵃ[ℝ] ℝ) (D : ∀ i, BodySectionDensity K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (c r : ι → ℝ) (hc : ∀ i, c i ∈ Icc 0 1)
    (hr0 : ∀ i, 0 < r i) (hr1 : ∀ i, r i < 1) (P : ℝ)
    (hmin : IsLocalMin (margin K f c r P) 0) (hz : margin K f c r P 0 = 0) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  let i : ι := Classical.choice inferInstance
  exact PlanarBalanceRigidity.four_vertices_of_balance_eq hK hconv hne hV
    (f i) (D i) (hnorm i) (hunit i) (hc i) (hr0 i) (hr1 i)
    (balance_eq_of_local_min hK hconv hne f D hnorm hunit c r hc hr0 hr1 P hmin hz i)

end Plank.PlanarWindowEulerRigidity

/-- info: 'Plank.PlanarWindowEulerRigidity.four_vertices_of_local_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarWindowEulerRigidity.four_vertices_of_local_min
