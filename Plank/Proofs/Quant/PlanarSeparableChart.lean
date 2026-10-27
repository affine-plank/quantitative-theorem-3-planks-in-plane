/- Recover actual density slopes from a separable quadratic area chart. -/
module

public import Plank.Proofs.Quant.PlanarBodySectionDensity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSeparableChart

open Set PlanarQuantitative PlanarPlankCellCharts PlanarPolygonCharts
open PlanarBodySectionDensity QuadraticChartCalculus
open scoped Topology

variable {κ : Type*} [Fintype κ]

/-- Subtracting pair-plank terms leaves a quadratic chart for the body area
minus the individual covered areas. The identity is about actual measures. -/
structure SeparableAreaChart (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ) where
  region : Set (EndpointSpace κ)
  open_region : IsOpen region
  ordered : ∀ e ∈ region, ∀ i, e.1 i < e.2 i
  formula : QuadraticFormula (EndpointSpace κ)
  constant : ℝ
  area_identity : ∀ e ∈ region,
    formula.eval e = constant-∑ i, coveredArea K (f i) (e.1 i) (e.2 i)

theorem hasDerivAt_eval_line (q : QuadraticFormula (EndpointSpace κ))
    (e z : EndpointSpace κ) :
    HasDerivAt (fun t : ℝ => q.eval (e+t • z)) (derivative q e z) 0 := by
  have hp : HasDerivAt (fun t : ℝ => e+t • z) z 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add e
  exact (hasFDerivAt_eval q e).comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)

theorem hasDerivAt_gradient_line (q : QuadraticFormula (EndpointSpace κ))
    (e z w : EndpointSpace κ) :
    HasDerivAt (fun t : ℝ => derivative q (e+t • z) w) (hessian q z w) 0 := by
  have hd := ((hasDerivAt_id (0 : ℝ)).mul_const (hessian q z w)).const_add
    (derivative q e w)
  simp only [one_mul] at hd
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    rw [derivative_add]
    simp)

namespace SeparableAreaChart

variable {K : Set Point} {f : κ → Point →ᵃ[ℝ] ℝ}

/-- The full chart derivative is identified with actual section densities. -/
theorem derivative_eq (ch : SeparableAreaChart K f) (D : ∀ i, BodySectionDensity K (f i))
    (e : EndpointSpace κ) (he : e ∈ ch.region) (z : EndpointSpace κ) :
    derivative ch.formula e z =
      ∑ i, ((D i).density (e.1 i)*z.1 i-(D i).density (e.2 i)*z.2 i) := by
  have hs : HasDerivAt (fun t : ℝ => ∑ i, coveredArea K (f i)
      (e.1 i+t*z.1 i) (e.2 i+t*z.2 i))
      (∑ i, ((D i).density (e.2 i)*z.2 i-(D i).density (e.1 i)*z.1 i)) 0 :=
    HasDerivAt.fun_sum (fun i _ => (D i).line_deriv _ _ (ch.ordered e he i) _ _)
  have hn := hs.const_sub ch.constant
  have hp : HasDerivAt (fun t : ℝ => ch.formula.eval (e+t • z))
      (-(∑ i, ((D i).density (e.2 i)*z.2 i-(D i).density (e.1 i)*z.1 i))) 0 := by
    apply hn.congr_of_eventuallyEq
    have hc : Continuous (fun t : ℝ => e+t • z) := by fun_prop
    have ht : Filter.Tendsto (fun t : ℝ => e+t • z) (nhds 0) (nhds e) := by
      simpa only [zero_smul, add_zero] using hc.tendsto 0
    filter_upwards [ht.eventually (ch.open_region.mem_nhds he)] with t ht
    exact ch.area_identity (e+t • z) ht
  have hh := (hasDerivAt_eval_line ch.formula e z).unique hp
  rw [hh, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SeparableAreaChart

variable [DecidableEq κ]

def lowerDirection (i : κ) : EndpointSpace κ := (Pi.single i 1, 0)
def upperDirection (i : κ) : EndpointSpace κ := (0, Pi.single i 1)

namespace SeparableAreaChart

variable {K : Set Point} {f : κ → Point →ᵃ[ℝ] ℝ}

theorem derivative_lower (ch : SeparableAreaChart K f) (D : ∀ i, BodySectionDensity K (f i))
    (e : EndpointSpace κ) (he : e ∈ ch.region) (i : κ) :
    derivative ch.formula e (lowerDirection i) = (D i).density (e.1 i) := by
  rw [ch.derivative_eq D e he]
  simp [lowerDirection, Pi.single_apply, mul_ite]

theorem derivative_upper (ch : SeparableAreaChart K f) (D : ∀ i, BodySectionDensity K (f i))
    (e : EndpointSpace κ) (he : e ∈ ch.region) (i : κ) :
    derivative ch.formula e (upperDirection i) = -(D i).density (e.2 i) := by
  rw [ch.derivative_eq D e he]
  simp [upperDirection, Pi.single_apply, mul_ite]

/-- On the open chart the density itself is differentiable at every lower
endpoint, with slope the corresponding fixed diagonal Hessian entry. -/
theorem density_deriv_lower (ch : SeparableAreaChart K f) (D : ∀ i, BodySectionDensity K (f i))
    (e : EndpointSpace κ) (he : e ∈ ch.region) (i : κ) :
    HasDerivAt (D i).density
      (hessian ch.formula (lowerDirection i) (lowerDirection i)) (e.1 i) := by
  let z := lowerDirection i
  have hp : HasDerivAt (fun t : ℝ => e+(t-e.1 i) • z) z (e.1 i) := by
    simpa only [one_smul, id_eq] using
      (((hasDerivAt_id (e.1 i)).sub_const (e.1 i)).smul_const z).const_add e
  have hd : HasDerivAt (fun t : ℝ => derivative ch.formula (e+(t-e.1 i) • z) z)
      (hessian ch.formula z z) (e.1 i) := by
    have hh := (hasDerivAt_gradient_line ch.formula e z z).comp_of_eq (e.1 i)
      ((hasDerivAt_id (e.1 i)).sub_const (e.1 i)) (by simp)
    simpa only [Function.comp_def, mul_one, id_eq] using hh
  apply hd.congr_of_eventuallyEq
  have ht : Filter.Tendsto (fun t : ℝ => e+(t-e.1 i) • z) (nhds (e.1 i)) (nhds e) := by
    simpa only [ContinuousAt, sub_self, zero_smul, add_zero] using hp.continuousAt
  filter_upwards [ht.eventually (ch.open_region.mem_nhds he)] with t ht
  have hh := ch.derivative_lower D _ ht i
  simpa [z, lowerDirection] using hh.symm

theorem density_deriv_upper (ch : SeparableAreaChart K f) (D : ∀ i, BodySectionDensity K (f i))
    (e : EndpointSpace κ) (he : e ∈ ch.region) (i : κ) :
    HasDerivAt (D i).density
      (-hessian ch.formula (upperDirection i) (upperDirection i)) (e.2 i) := by
  let z := upperDirection i
  have hp : HasDerivAt (fun t : ℝ => e+(t-e.2 i) • z) z (e.2 i) := by
    simpa only [one_smul, id_eq] using
      (((hasDerivAt_id (e.2 i)).sub_const (e.2 i)).smul_const z).const_add e
  have hd : HasDerivAt (fun t : ℝ => -derivative ch.formula (e+(t-e.2 i) • z) z)
      (-hessian ch.formula z z) (e.2 i) := by
    have hh := ((hasDerivAt_gradient_line ch.formula e z z).comp_of_eq (e.2 i)
      ((hasDerivAt_id (e.2 i)).sub_const (e.2 i)) (by simp)).neg
    simpa only [Function.comp_def, mul_one, id_eq, Pi.neg_def] using hh
  apply hd.congr_of_eventuallyEq
  have ht : Filter.Tendsto (fun t : ℝ => e+(t-e.2 i) • z) (nhds (e.2 i)) (nhds e) := by
    simpa only [ContinuousAt, sub_self, zero_smul, add_zero] using hp.continuousAt
  filter_upwards [ht.eventually (ch.open_region.mem_nhds he)] with t ht
  have hh := ch.derivative_upper D _ ht i
  simpa [z, upperDirection] using (congrArg Neg.neg hh).symm

/-- Every Hessian entry is determined by the two actual section slopes
for each plank; after removing the pair terms there are no mixed terms. -/
theorem hessian_eq (ch : SeparableAreaChart K f) (D : ∀ i, BodySectionDensity K (f i))
    (e : EndpointSpace κ) (he : e ∈ ch.region) (z : EndpointSpace κ) :
    hessian ch.formula z z = ∑ i,
      ((hessian ch.formula (lowerDirection i) (lowerDirection i))*(z.1 i)^2+
      (hessian ch.formula (upperDirection i) (upperDirection i))*(z.2 i)^2) := by
  have hi (i : κ) : HasDerivAt (fun t : ℝ =>
      (D i).density (e.1 i+t*z.1 i)*z.1 i-(D i).density (e.2 i+t*z.2 i)*z.2 i)
      ((hessian ch.formula (lowerDirection i) (lowerDirection i))*(z.1 i)^2+
        (hessian ch.formula (upperDirection i) (upperDirection i))*(z.2 i)^2) 0 := by
    have hl := (ch.density_deriv_lower D e he i).comp_of_eq (0 : ℝ)
      (((hasDerivAt_id (0 : ℝ)).mul_const (z.1 i)).const_add (e.1 i)) (by simp)
    have hu := (ch.density_deriv_upper D e he i).comp_of_eq (0 : ℝ)
      (((hasDerivAt_id (0 : ℝ)).mul_const (z.2 i)).const_add (e.2 i)) (by simp)
    convert! (hl.mul_const (z.1 i)).sub (hu.mul_const (z.2 i)) using 1
    simp
    ring
  have hs := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset κ)) => hi i)
  have hq : HasDerivAt (fun t : ℝ => derivative ch.formula (e+t • z) z)
      (∑ i, ((hessian ch.formula (lowerDirection i) (lowerDirection i))*(z.1 i)^2+
        (hessian ch.formula (upperDirection i) (upperDirection i))*(z.2 i)^2)) 0 := by
    apply hs.congr_of_eventuallyEq
    have hc : Continuous (fun t : ℝ => e+t • z) := by fun_prop
    have ht : Filter.Tendsto (fun t : ℝ => e+t • z) (nhds 0) (nhds e) := by
      simpa only [zero_smul, add_zero] using hc.tendsto 0
    filter_upwards [ht.eventually (ch.open_region.mem_nhds he)] with t ht
    exact ch.derivative_eq D _ ht z
  exact (hasDerivAt_gradient_line ch.formula e z z).unique hq

/-- The first-derivative identities survive at the selected chart limit
because both the actual density and the polynomial gradient are continuous. -/
theorem derivative_lower_at_closure (ch : SeparableAreaChart K f)
    (D : ∀ i, BodySectionDensity K (f i)) (e : EndpointSpace κ)
    (he : e ∈ closure ch.region) (i : κ) :
    derivative ch.formula e (lowerDirection i) = (D i).density (e.1 i) := by
  exact Set.EqOn.closure (fun x hx => ch.derivative_lower D x hx i)
    ((continuous_derivative ch.formula).clm_apply continuous_const)
    ((D i).continuous.comp (by fun_prop)) he

theorem derivative_upper_at_closure (ch : SeparableAreaChart K f)
    (D : ∀ i, BodySectionDensity K (f i)) (e : EndpointSpace κ)
    (he : e ∈ closure ch.region) (i : κ) :
    derivative ch.formula e (upperDirection i) = -(D i).density (e.2 i) := by
  exact Set.EqOn.closure (fun x hx => ch.derivative_upper D x hx i)
    ((continuous_derivative ch.formula).clm_apply continuous_const)
    (((D i).continuous.comp (by fun_prop)).neg) he

/-- Supporting-slope inequalities also persist on the chart closure,
even when the density has a corner at the selected endpoint. -/
theorem supporting_bounds_at_closure (ch : SeparableAreaChart K f)
    (D : ∀ i, BodySectionDensity K (f i))
    (hconc : ∀ i, ConcaveOn ℝ (Icc 0 1) (D i).density)
    (hinside : ∀ e ∈ ch.region, ∀ i, e.1 i ∈ Ioo 0 1 ∧ e.2 i ∈ Ioo 0 1)
    (e : EndpointSpace κ) (he : e ∈ closure ch.region) (i : κ) :
    (hessian ch.formula (lowerDirection i) (lowerDirection i))*e.1 i ≤ (D i).density (e.1 i) ∧
    (hessian ch.formula (upperDirection i) (upperDirection i))*(1-e.2 i) ≤ (D i).density (e.2 i) := by
  have hlo (x) (hx : x ∈ ch.region) :=
    (PlanarSectionConcavity.supporting_slope_bounds (hconc i)
      ((D i).nonnegative 0) ((D i).nonnegative 1) (hinside x hx i).1
      (ch.density_deriv_lower D x hx i)).1
  have hhi (x) (hx : x ∈ ch.region) :
      (hessian ch.formula (upperDirection i) (upperDirection i))*(1-x.2 i) ≤
        (D i).density (x.2 i) := by
    simpa only [neg_neg] using
      (PlanarSectionConcavity.supporting_slope_bounds (hconc i)
        ((D i).nonnegative 0) ((D i).nonnegative 1) (hinside x hx i).2
        (ch.density_deriv_upper D x hx i)).2
  constructor
  · exact le_on_closure hlo (by fun_prop)
      ((D i).continuous.comp (by fun_prop)).continuousOn he
  · exact le_on_closure hhi (by fun_prop)
      ((D i).continuous.comp (by fun_prop)).continuousOn he

end SeparableAreaChart

end Plank.PlanarSeparableChart
