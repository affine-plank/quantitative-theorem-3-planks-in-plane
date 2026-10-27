/- Proportional motion at an actual dimension-power gap minimum in every positive dimension. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalEndpointCells
public import Plank.Proofs.Quant.FiniteDimensionalEndpointMajorants
public import Plank.Measure.LinearBands
public import Plank.Measure.FiniteBandContinuity
public import Plank.Proofs.AffineWidth
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalFewCellScaling

open Set MeasureTheory Filter FiniteDimensionalCellSupportingAffine
  FiniteDimensionalEndpointMajorants FiniteDimensionalCapWindowScaling
open scoped BigOperators Topology Pointwise

variable {n m : ℕ}

def deficit (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (B : ℝ) :
    Endpoints (Fin m) →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ _ B-(budgetLinear K f).toAffineMap

def margin (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (B : ℝ)
    (p : Endpoints (Fin m)) : ℝ := gapVolume K f p-(volume K).toReal*(B-budget K f p)^(n+1)

private theorem affine_eval (f : (Point n) →ᵃ[ℝ] ℝ) (x : (Point n)) :
    f x = f.linear x+f 0 := congrFun f.decomp x

theorem continuous_margin {K : Set (Point n)} (hK : IsCompact K)
    (hne : K.Nonempty) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < Body.width K (f i)) (B : ℝ) : Continuous (margin K f B) := by
  exact (continuous_gapVolume hK hne f hW).sub
    (continuous_const.mul ((continuous_const.sub (by unfold budget; fun_prop)).pow (n+1)))

private theorem endpoint_finrank : Module.finrank ℝ (Endpoints (Fin m)) = 2*m := by
  simp [Endpoints,Module.finrank_prod]
  omega

/-- One linear constraint per nonempty null cell controls every local
zero-gap motion. No bound on the number of cells is needed. -/
theorem exists_zero_gap_constraints {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (C : Finset (Finset (Fin m)))
    (p : Endpoints (Fin m)) (ho : ∀ i, p.1 i < p.2 i)
    (hreg : p ∈ region K f C) (hzero : gapVolume K f p = 0) :
    ∃ L : C → Endpoints (Fin m) →ₗ[ℝ] ℝ,
      (∀ s z, L s z = 0 → ∀ t : ℝ,
        (volume (signCell K f (p+t • z) s)).toReal = 0) ∧
      ∀ z, (∀ s, L s z = 0) →
        ∀ᶠ t : ℝ in 𝓝 0, gapVolume K f (p+t • z) = 0 := by
  classical
  have hf := fun i => Body.linear_ne_zero_of_width_pos hne (f i) (hW i)
  have hz (s : Finset (Fin m)) : (volume (signCell K f p s)).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    have hh := Finset.single_le_sum (fun s _ =>
      (ENNReal.toReal_nonneg : 0 ≤ (volume (signCell K f p s)).toReal))
      (Finset.mem_univ s)
    rwa [← gap_eq_sum hK f hf p (fun i => (ho i).le), hzero] at hh
  choose L hL using (fun s : C => exists_zero_constraint hK hc hne hV f hf s p (hz s))
  refine ⟨L,hL,?_⟩
  intro z hzL
  have ht : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
    have hh : Continuous (fun t : ℝ => p+t • z) := by fun_prop
    simpa only [zero_smul,add_zero] using (hh.continuousAt (x := (0 : ℝ))).tendsto
  have horder : IsOpen {e : Endpoints (Fin m) | ∀ i, e.1 i < e.2 i} := by
    simpa only [ofPred_forall] using isOpen_iInter_of_finite
      (fun i : Fin m => isOpen_lt (by fun_prop) (by fun_prop) :
        ∀ i : Fin m, IsOpen {e : Endpoints (Fin m) | e.1 i < e.2 i})
  filter_upwards [ht.eventually ((isOpen_region hK f C).mem_nhds hreg),
    ht.eventually (horder.mem_nhds ho)] with t hr htorder
  rw [gap_eq_sum hK f hf _ (fun i => (htorder i).le)]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : s ∈ C
  · exact hL ⟨s,hs⟩ z (hzL ⟨s,hs⟩) t
  · rw [hr s hs,measure_empty,ENNReal.toReal_zero]

/-- Fewer than `2*m` nonempty closed cells leave a nonzero local motion
preserving zero gap. No minimum or plank-covering inequality is assumed. -/
theorem exists_zero_gap_motion {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (C : Finset (Finset (Fin m))) (hC : C.card < 2*m)
    (p : Endpoints (Fin m)) (ho : ∀ i, p.1 i < p.2 i)
    (hreg : p ∈ region K f C) (hzero : gapVolume K f p = 0) :
    ∃ z : Endpoints (Fin m), z ≠ 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, gapVolume K f (p+t • z) = 0 := by
  classical
  obtain ⟨L,_,hL⟩ := exists_zero_gap_constraints hK hc hne hV f hW C p ho hreg hzero
  let F : Endpoints (Fin m) →ₗ[ℝ] (C → ℝ) := LinearMap.pi L
  have hker : LinearMap.ker F ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt
    (by simpa only [Module.finrank_pi,Fintype.card_coe,endpoint_finrank] using hC)
  obtain ⟨z,hz,hzne⟩ := (LinearMap.ker F).ne_bot_iff.mp hker
  change F z = 0 at hz
  exact ⟨z,hzne,hL z (fun s => congrFun hz s)⟩

private theorem proportional_direction {E ι : Type*} [AddCommGroup E]
    [Module ℝ E] [Module.Finite ℝ E] [Fintype ι]
    (b : ι → ℝ) (hb : b ≠ 0) (L : ι → E →ₗ[ℝ] ℝ)
    (hcard : Fintype.card ι ≤ Module.finrank ℝ E) :
    ∃ z : E, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ i, L i z = b i*c := by
  classical
  let F := LinearMap.pi L
  by_cases hinj : Function.Injective F
  · have hdim : Module.finrank ℝ E = Module.finrank ℝ (ι → ℝ) :=
      Nat.le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj)
        (by simpa only [Module.finrank_pi] using hcard)
    obtain ⟨z,hz⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj b
    refine ⟨z,?_,1,zero_le_one,fun i => by simpa [F] using congrFun hz i⟩
    intro hzero
    apply hb
    simpa only [hzero,map_zero] using hz.symm
  · have hker : F.ker ≠ ⊥ := fun h => hinj (LinearMap.ker_eq_bot.mp h)
    obtain ⟨z,hz,hzne⟩ := F.ker.ne_bot_iff.mp hker
    change F z = 0 at hz
    exact ⟨z,hzne,0,le_rfl,fun i => by simpa [F] using congrFun hz i⟩

/-- A two-sided affine upper bound at a minimum has zero slope. -/
theorem slope_eq_zero_of_eventually_nonneg (a : ℝ)
    (h : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t*a) : a = 0 := by
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
  obtain ⟨t,ht,hplus,hminus⟩ := (h.and (hneg.eventually h)).exists_gt
  nlinarith only [ht,hplus,hminus]

/-- Few nonempty cells admit proportional upper scaling. No minimum or
stationarity assumption is needed to find this direction. -/
theorem exists_common_upper_cell_scaling {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (C : Finset (Finset (Fin m))) (hC : C.card ≤ 2*m)
    (p : Endpoints (Fin m)) (ho : ∀ i, p.1 i < p.2 i)
    (hreg : p ∈ region K f C) (hpositive : 0 < gapVolume K f p) :
    ∃ z : Endpoints (Fin m), z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∀ᶠ t : ℝ in 𝓝 0,
        (∀ s, (volume (signCell K f (p+t • z) s)).toReal ≤
          (volume (signCell K f p s)).toReal*(1+t*c)^(n+1)) ∧
        gapVolume K f (p+t • z) ≤ gapVolume K f p*(1+t*c)^(n+1) := by
  classical
  have hf (i) := Body.linear_ne_zero_of_width_pos hne (f i) (hW i)
  let A (s : Finset (Fin m)) (e : Endpoints (Fin m)) :=
    (volume (signCell K f e s)).toReal
  let b (s : C) := volumeRoot (signCell K f p s)
  choose L hL using (fun s : C => exists_scaling_constraint hK hc hne hV f hf s p)
  have hbase : (∑ s : C, (b s)^(n+1)) = gapVolume K f p := by
    simp_rw [b,volumeRoot_pow]
    rw [gap_eq_sum hK f hf p (fun i => (ho i).le),
      Finset.sum_coe_sort C (fun s => (volume (signCell K f p s)).toReal)]
    exact Finset.sum_subset (Finset.subset_univ _) (fun s _ hs => by
      rw [hreg s hs,measure_empty,ENNReal.toReal_zero])
  have hb : b ≠ 0 := by
    intro hz
    rw [← hbase,hz] at hpositive
    simp at hpositive
  obtain ⟨z,hzne,c,hc0,hscale⟩ := proportional_direction b hb L
    (by simpa only [Fintype.card_coe,endpoint_finrank] using hC)
  have hline : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
    have hh : Continuous (fun t : ℝ => p+t • z) := by fun_prop
    simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto
  have hupper : ∀ᶠ t : ℝ in 𝓝 0, ∀ s,
      A s (p+t • z) ≤ A s p*(1+t*c)^(n+1) := by
    have hCs : ∀ᶠ t : ℝ in 𝓝 0, ∀ s : C,
        A s (p+t • z) ≤ A s p*(1+t*c)^(n+1) :=
      Filter.eventually_all.mpr (fun s => hL s z c (hscale s))
    filter_upwards [hCs,hline.eventually ((isOpen_region hK f C).mem_nhds hreg)] with t ht hr s
    by_cases hs : s ∈ C
    · exact ht ⟨s,hs⟩
    · change (volume (signCell K f (p+t • z) s)).toReal ≤
        (volume (signCell K f p s)).toReal*(1+t*c)^(n+1)
      rw [hr s hs,hreg s hs,measure_empty,ENNReal.toReal_zero,zero_mul]
  have horder : IsOpen {e : Endpoints (Fin m) | ∀ i, e.1 i < e.2 i} := by
    simpa only [ofPred_forall] using isOpen_iInter_of_finite
      (fun i : Fin m => isOpen_lt (by fun_prop) (by fun_prop) :
        ∀ i : Fin m, IsOpen {e : Endpoints (Fin m) | e.1 i < e.2 i})
  refine ⟨z,hzne,c,hc0,?_⟩
  filter_upwards [hupper,hline.eventually (horder.mem_nhds ho)] with t ht hto
  refine ⟨ht,?_⟩
  rw [gap_eq_sum hK f hf _ (fun i => (hto i).le),
    gap_eq_sum hK f hf p (fun i => (ho i).le),Finset.sum_mul]
  exact Finset.sum_le_sum (fun s _ => ht s)

/-- At an actual zero local minimum of the dimension-power actual-gap margin, at most
`2*m` nonempty closed cells admit a common local upper scaling along a nonzero
endpoint direction. All geometric majorants are supplied internally. -/
theorem exists_common_upper_scaling_at_minimum {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (C : Finset (Finset (Fin m))) (hC : C.card ≤ 2*m)
    (B : ℝ) (p : Endpoints (Fin m)) (ho : ∀ i, p.1 i < p.2 i)
    (hreg : p ∈ region K f C) (hq : 0 < B-budget K f p)
    (hz : margin K f B p = 0) (hmin : IsLocalMin (margin K f B) p) :
    ∃ z : Endpoints (Fin m), z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∀ᶠ t : ℝ in 𝓝 0,
        (B-budget K f (p+t • z) = (B-budget K f p)*(1+t*c)) ∧
        (∀ s, (volume (signCell K f (p+t • z) s)).toReal ≤
          (volume (signCell K f p s)).toReal*(1+t*c)^(n+1)) ∧
        margin K f B (p+t • z) = 0 := by
  have hbase : gapVolume K f p = (volume K).toReal*(B-budget K f p)^(n+1) :=
    sub_eq_zero.mp hz
  have hpositive : 0 < gapVolume K f p := by rw [hbase]; positivity
  obtain ⟨z,hzne,c,hc0,hupper⟩ := exists_common_upper_cell_scaling
    hK hc hne hV f hW C hC p ho hreg hpositive
  let q := B-budget K f p
  have hdef (t : ℝ) : B-budget K f (p+t • z) = q-t*budget K f z := by
    simp only [← budgetLinear_apply,map_add,map_smul,smul_eq_mul]
    dsimp only [q]
    simp only [← budgetLinear_apply]
    ring
  have hline : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
    have hh : Continuous (fun t : ℝ => p+t • z) := by fun_prop
    simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto
  have hfactor : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1+t*c := by
    exact (show Continuous (fun t : ℝ => 1+t*c) by fun_prop).continuousAt.eventually
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1+0*c))
  have hbound : ∀ᶠ t : ℝ in 𝓝 0, B-budget K f (p+t • z) ≤ q*(1+t*c) := by
    filter_upwards [hupper,hline.eventually hmin,hfactor] with t hu hm hf
    have hh : (volume K).toReal*(B-budget K f (p+t • z))^(n+1) ≤
        (volume K).toReal*(q*(1+t*c))^(n+1) := by
      have hm' : (volume K).toReal*(B-budget K f (p+t • z))^(n+1) ≤
          gapVolume K f (p+t • z) := by
        change margin K f B p ≤ margin K f B (p+t • z) at hm
        rw [hz] at hm
        exact sub_nonneg.mp hm
      calc
        _ ≤ gapVolume K f (p+t • z) := hm'
        _ ≤ gapVolume K f p*(1+t*c)^(n+1) := hu.2
        _ = _ := by rw [hbase,mul_pow,mul_assoc]
    exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero n)
      (mul_nonneg hq.le hf.le) ((mul_le_mul_iff_right₀ hV).mp hh)
  have hslope : budget K f z+q*c = 0 := slope_eq_zero_of_eventually_nonneg _
    (hbound.mono fun t ht => by rw [hdef] at ht; nlinarith only [ht])
  have hscale (t : ℝ) : B-budget K f (p+t • z) = q*(1+t*c) := by
    rw [hdef,show budget K f z = -(q*c) by linarith only [hslope]]
    ring
  refine ⟨z,hzne,c,hc0,?_⟩
  filter_upwards [hupper,hline.eventually hmin] with t hu hm
  refine ⟨hscale t,hu.1,le_antisymm ?_ ?_⟩
  · apply sub_nonpos.mpr
    rw [hscale]
    calc
      gapVolume K f (p+t • z) ≤ gapVolume K f p*(1+t*c)^(n+1) := hu.2
      _ = (volume K).toReal*(q*(1+t*c))^(n+1) := by rw [hbase,mul_pow,mul_assoc]
  · rwa [hz] at hm

end Plank.FiniteDimensionalFewCellScaling

#print axioms Plank.FiniteDimensionalFewCellScaling.exists_zero_gap_constraints
#print axioms Plank.FiniteDimensionalFewCellScaling.exists_zero_gap_motion

#print axioms Plank.FiniteDimensionalFewCellScaling.exists_common_upper_scaling_at_minimum

#print axioms Plank.FiniteDimensionalFewCellScaling.exists_common_upper_cell_scaling
