/- Finite dual certificates for strict affine-cell spread.

An empty-cell certificate is a nonnegative normalized combination of the
cuts that is nonpositive on every original generator. Otherwise, two
nonnegative combinations of the cuts certify an upper and lower bound for
the objective. This file checks supplied certificates; it does not assert
that certificates exist or trust the program that finds them.
-/
module
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.StrictCellDualCertificate
open scoped BigOperators

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- A normalized nonnegative combination of the cuts separates the hull
from the strictly positive orthant. -/
def HasEmptyCertificate (S : Set E) (f : ι → E →ᵃ[ℝ] ℝ) : Prop :=
  ∃ α : ι → ℝ, (∀ i, 0 ≤ α i) ∧ (∑ i, α i = 1) ∧
    ∀ v ∈ S, ∑ i, α i * f i v ≤ 0

/-- A supplied nonnegative combination of the cuts bounds an affine
objective on the weak cell. Only original generators are checked. -/
def HasUpperCertificate (S : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (g : E →ᵃ[ℝ] ℝ) (U : ℝ) : Prop :=
  ∃ α : ι → ℝ, (∀ i, 0 ≤ α i) ∧
    ∀ v ∈ S, g v + ∑ i, α i * f i v ≤ U

/-- Accept either a certified empty strict cell or two certified bounds
whose difference is at most the requested spread. -/
def HasSpreadCertificate (S : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (g : E →ᵃ[ℝ] ℝ) (w : ℝ) : Prop :=
  HasEmptyCertificate S f ∨ ∃ L U : ℝ, U - L ≤ w ∧
    HasUpperCertificate S f g U ∧ HasUpperCertificate S f (-g) (-L)

/-- Any weighted affine generator inequality extends to the whole hull.
The weights in this transport lemma can have either sign. -/
theorem weighted_le_on_hull (S : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (g : E →ᵃ[ℝ] ℝ) (α : ι → ℝ) (U : ℝ)
    (hrows : ∀ v ∈ S, g v + ∑ i, α i * f i v ≤ U) :
    ∀ x ∈ convexHull ℝ S, g x + ∑ i, α i * f i x ≤ U := by
  let A : E →ᵃ[ℝ] ℝ := g + ∑ i, α i • f i
  have hA (x : E) : A x = g x + ∑ i, α i * f i x := by
    let ev : (E →ᵃ[ℝ] ℝ) →+ ℝ :=
      { toFun := fun a => a x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have he : (∑ i, α i • f i) x = ∑ i, α i * f i x :=
      map_sum ev (fun i => α i • f i) Finset.univ
    simp only [A, AffineMap.coe_add, Pi.add_apply, he]
  have hh : convexHull ℝ S ⊆ A ⁻¹' Set.Iic U := by
    apply convexHull_min ?_ ((convex_Iic U).affine_preimage A)
    intro v hv
    exact (hA v).trans_le (hrows v hv)
  intro x hx
  exact (hA x).symm.trans_le (hh hx)

/-- A supplied upper certificate bounds the entire weak cell, including
boundary points. No topology or finite-generation assumption is needed. -/
theorem upper_bound_of_certificate (S : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (g : E →ᵃ[ℝ] ℝ) (U : ℝ) (hcert : HasUpperCertificate S f g U) :
    ∀ x ∈ convexHull ℝ S, (∀ i, 0 ≤ f i x) → g x ≤ U := by
  obtain ⟨α, hα, hrows⟩ := hcert
  intro x hx hf
  have hsum : 0 ≤ ∑ i, α i * f i x :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (hf i)
  have hb := weighted_le_on_hull S f g α U hrows x hx
  linarith

/-- A supplied normalized separator rules out every strict point. The
strictness of every cut is used only after extending the generator bound. -/
theorem empty_of_certificate (S : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (hcert : HasEmptyCertificate S f) :
    ¬ ∃ x ∈ convexHull ℝ S, ∀ i, 0 < f i x := by
  obtain ⟨α, hα, hsum, hrows⟩ := hcert
  rintro ⟨x, hx, hf⟩
  have hsumpos : 0 < ∑ i, α i := by rw [hsum]; exact zero_lt_one
  obtain ⟨i, -, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hα i)).mp hsumpos
  have hpos : 0 < ∑ i, α i * f i x :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hα j) (hf j).le)
      ⟨i, Finset.mem_univ i, mul_pos hi (hf i)⟩
  have hzero : ∀ v ∈ S, (0 : E →ᵃ[ℝ] ℝ) v + ∑ i, α i * f i v ≤ 0 := by
    simpa using hrows
  have hb := weighted_le_on_hull S f 0 α 0 hzero x hx
  change 0 + (∑ i, α i * f i x) ≤ 0 at hb
  linarith

/-- Supplied dual certificates certify strict spread using inequalities on
the original generators alone. The empty strict cell passes independently
of the size of its weak relaxation. This is a sufficient certificate theorem. -/
theorem strict_spread_of_certificate (S : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (g : E →ᵃ[ℝ] ℝ) (w : ℝ) (hcert : HasSpreadCertificate S f g w) :
    ∀ x ∈ convexHull ℝ S, (∀ i, 0 < f i x) →
      ∀ y ∈ convexHull ℝ S, (∀ i, 0 < f i y) → g x - g y ≤ w := by
  rcases hcert with hempty | ⟨L, U, hwidth, hupper, hlower⟩
  · intro x hx hf
    exact False.elim (empty_of_certificate S f hempty ⟨x, hx, hf⟩)
  · intro x hx hfx y hy hfy
    have hu := upper_bound_of_certificate S f g U hupper x hx (fun i => (hfx i).le)
    have hl := upper_bound_of_certificate S f (-g) (-L) hlower y hy (fun i => (hfy i).le)
    change -g y ≤ -L at hl
    linarith

end Plank.Convex.StrictCellDualCertificate

/-- info: 'Plank.Convex.StrictCellDualCertificate.weighted_le_on_hull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.StrictCellDualCertificate.weighted_le_on_hull

/-- info: 'Plank.Convex.StrictCellDualCertificate.upper_bound_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.StrictCellDualCertificate.upper_bound_of_certificate

/-- info: 'Plank.Convex.StrictCellDualCertificate.empty_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.StrictCellDualCertificate.empty_of_certificate

/-- info: 'Plank.Convex.StrictCellDualCertificate.strict_spread_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.StrictCellDualCertificate.strict_spread_of_certificate
