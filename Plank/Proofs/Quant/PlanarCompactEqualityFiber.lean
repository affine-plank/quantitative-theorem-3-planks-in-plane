/- Compact sets with local lines attain affine extrema at their budget boundary. -/
module

public import Plank.Proofs.Quant.PlanarShiftedDomain
public import Plank.Convex.FiniteExtremeMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCompactEqualityFiber

open Set PlanarQuantitative PlanarParameterDomain
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Choose an extreme affine minimizer. A nontrivial two-sided local line
would contradict extremality, so its budget lies on the boundary.
The compact set itself need not be convex or connected. -/
theorem exists_boundary_minimizer {m : ℕ} {S : Set (Endpoints m)}
    (hS : IsCompact S) (hne : S.Nonempty) (R : Endpoints m → ℝ)
    (hR : ∀ p ∈ S, 0 ≤ R p ∧ R p ≤ 1)
    (hline : ∀ p ∈ S, 0 < R p → R p < 1 →
      ∃ z : Endpoints m, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, |t| < ε → p+t • z ∈ S)
    (L : Endpoints m →ᵃ[ℝ] ℝ) :
    ∃ p ∈ S, (R p = 0 ∨ R p = 1) ∧ ∀ q ∈ S, L p ≤ L q := by
  obtain ⟨p,hp,hmin⟩ := Plank.Convex.ExtremeMinimum.exists_finite_extreme_minimizer
    S hS hne L.linear.toContinuousLinearMap
  refine ⟨p,hp.1,?_,?_⟩
  · by_contra hb
    have hp0 : 0 < R p := lt_of_le_of_ne (hR p hp.1).1
      (fun he => hb (Or.inl he.symm))
    have hp1 : R p < 1 := lt_of_le_of_ne (hR p hp.1).2
      (fun he => hb (Or.inr he))
    obtain ⟨z,hz,ε,hε,hl⟩ := hline p hp.1 hp0 hp1
    exact Plank.Convex.ExtremeMinimum.extreme_no_motion S p hp z hz
      (Metric.eventually_nhds_iff.mpr ⟨ε,hε,fun t ht => hl t
        (by simpa only [dist_zero_right,Real.norm_eq_abs] using ht)⟩)
  · intro q hq
    rw [L.decomp]
    simpa only [Pi.add_apply,LinearMap.coe_toContinuousLinearMap',add_comm]
      using add_le_add_right (hmin hq) (L 0)

/-- Both endpoint budgets occur when the compact set contains one
strictly intermediate configuration and has local lines at every such
configuration. No global choice of one common line is assumed. -/
theorem exists_zero_and_one {m : ℕ} {S : Set (Endpoints m)}
    (hS : IsCompact S) (R : Endpoints m →ₗ[ℝ] ℝ)
    (hR : ∀ p ∈ S, 0 ≤ R p ∧ R p ≤ 1)
    (p : Endpoints m) (hp : p ∈ S) (hp0 : 0 < R p) (hp1 : R p < 1)
    (hline : ∀ q ∈ S, 0 < R q → R q < 1 →
      ∃ z : Endpoints m, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, |t| < ε → q+t • z ∈ S) :
    (∃ q ∈ S, R q = 0) ∧ ∃ r ∈ S, R r = 1 := by
  obtain ⟨q,hq,hqbd,hqmin⟩ := exists_boundary_minimizer hS ⟨p,hp⟩ R hR hline R.toAffineMap
  obtain ⟨r,hr,hrbd,hrmin⟩ := exists_boundary_minimizer hS ⟨p,hp⟩ R hR hline (-R).toAffineMap
  refine ⟨⟨q,hq,?_⟩,r,hr,?_⟩
  · rcases hqbd with h | h
    · exact h
    · have hh : R q ≤ R p := hqmin p hp
      linarith
  · rcases hrbd with h | h
    · have hh : -R r ≤ -R p := hrmin p hp
      linarith
    · exact h

end Plank.PlanarCompactEqualityFiber

/-- info: 'Plank.PlanarCompactEqualityFiber.exists_zero_and_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCompactEqualityFiber.exists_zero_and_one
