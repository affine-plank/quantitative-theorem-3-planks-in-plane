/- Shared cut geometry and support-witness lemmas.
The original namespaces and theorem statements are retained. -/
module
public import MovingAffineCut
public import GlobalPlankBodyMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank

open Set MeasureTheory Filter PrunedPlankCounterexample GlobalPlankBodyMinimum
open MovingAffineCut
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

namespace GlobalBodyTiltEquilibrium

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A competing body whose indexed widths do not decrease has uncovered
fraction at least that of a global minimum. The bodies need not be nested. -/
theorem ratio_le_of_width_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K C : Set E} (hC : IsCompact C) (hc : Convex ℝ C) (hCV : 0<μ.real C)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i,lo i≤hi i)
    (hW : ∀ i,0<Body.width K (f i)) (hw : ∀ i,Body.width K (f i)≤Body.width C (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B) :
    μ.real (K\covered f lo hi)/μ.real K≤μ.real (C\covered f lo hi)/μ.real C := by
  have hb : budget C f lo hi≤budget K f lo hi := by
    apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr (horder i)) (hW i) (hw i)
  have hm := hglobal C f lo hi hC hc hCV (fun i => (hW i).trans_le (hw i))
    horder (hb.trans hbudget)
  have hp : (B-budget K f lo hi)^d≤(B-budget C f lo hi)^d :=
    pow_le_pow_left₀ (sub_nonneg.mpr hbudget) (sub_le_sub_left hb B) d
  unfold margin at hm
  linarith only [hm,hp]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
theorem compact_cut_continuous {L : Set (ℝ × E)} (hL : IsCompact L)
    (h : E → ℝ) (hh : Continuous h) (b t : ℝ) : IsCompact (cut L h b t) :=
  hL.inter_right (isClosed_le continuous_fst
    (continuous_const.add (continuous_const.mul
      (hh.comp continuous_snd))))

omit [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
theorem compact_cut {L : Set (ℝ × E)} (hL : IsCompact L)
    (h : E →ᵃ[ℝ] ℝ) (b t : ℝ) : IsCompact (cut L h b t) :=
  compact_cut_continuous hL h h.continuous_of_finiteDimensional b t

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
/-- Bending a cut with a convex speed preserves convexity for nonpositive time. -/
theorem convex_cut_of_convex {L : Set (ℝ × E)} (hc : Convex ℝ L)
    (h : E → ℝ) (hh : ConvexOn ℝ univ h) (b : ℝ) {t : ℝ} (ht : t≤0) :
    Convex ℝ (cut L h b t) := by
  intro x hx y hy a c ha hcc hac
  refine ⟨hc hx.1 hy.1 ha hcc hac,?_⟩
  change a*x.1+c*y.1≤b+t*h (a • x.2+c • y.2)
  have hj := hh.2 (mem_univ x.2) (mem_univ y.2) ha hcc hac
  simp only [smul_eq_mul] at hj
  have hm := mul_le_mul_of_nonpos_left hj ht
  have hx' := mul_le_mul_of_nonneg_left hx.2 ha
  have hy' := mul_le_mul_of_nonneg_left hy.2 hcc
  change a*x.1≤a*(b+t*h x.2) at hx'
  change c*y.1≤c*(b+t*h y.2) at hy'
  nlinarith only [hx',hy',hm,congrArg (fun r : ℝ => r*b) hac]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
theorem convex_cut {L : Set (ℝ × E)} (hc : Convex ℝ L)
    (h : E →ᵃ[ℝ] ℝ) (b t : ℝ) : Convex ℝ (cut L h b t) := by
  let F : (ℝ × E) →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ E).toAffineMap-
    t • h.comp (LinearMap.snd ℝ ℝ E).toAffineMap
  have he : cut L h b t=L∩F ⁻¹' Iic b := by
    ext p
    simp [cut,F]
  rw [he]
  exact hc.inter ((convex_Iic b).affine_preimage F)

end GlobalBodyTiltEquilibrium

namespace GlobalBodyCutEquilibrium

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Strictly lower witnesses for both extrema exclude a constant value on
the whole cut hyperplane. This proves the needed noncoincidence internally. -/
theorem nonconstant_on_cut {K : Set (ℝ × E)} (f : (ℝ × E) →ᵃ[ℝ] ℝ)
    {b : ℝ} {y : E} {P Q : ℝ × E} (hy : (b,y)∈K)
    (hW : 0<Body.width K f) (hP : P∈K) (hQ : Q∈K)
    (hmax : ∀ x∈K,f x≤f P) (hmin : ∀ x∈K,f Q≤f x)
    (hPb : P.1<b) (hQb : Q.1<b) (u : ℝ) : ¬∀ z,f (b,z)=u := by
  intro hconst
  have hz (z : E) : f.linear (0,z)=0 := by
    have hh := f.linearMap_vsub (b,z) (b,0)
    change f.linear ((b,z)-(b,0))=f (b,z)-f (b,0) at hh
    simpa only [Prod.mk_sub_mk,sub_self,sub_zero,hconst] using hh
  have he (p : ℝ × E) : f p=p.1*f.linear (1,0)+f 0 := by
    have hp : p=p.1 • ((1,0) : ℝ × E)+(0,p.2) := by ext <;> simp
    calc
      f p=f.linear p+f 0 := congrFun f.decomp p
      _ = p.1*f.linear (1,0)+f 0 := by
        conv_lhs => arg 1; rw [hp,map_add,map_smul,hz]
        simp only [smul_eq_mul,add_zero]
  rcases lt_trichotomy (f.linear (1,0)) 0 with hn | hn | hn
  · have hs := mul_lt_mul_of_neg_left hQb hn
    have hm := hmin (b,y) hy
    rw [he Q,he (b,y)] at hm
    change _≤b*f.linear (1,0)+f 0 at hm
    nlinarith only [hs,hm]
  · rw [Body.width_eq_of_realisers hP hQ hmax hmin,he P,he Q,hn] at hW
    norm_num at hW
  · have hs := mul_lt_mul_of_pos_left hPb hn
    have hm := hmax (b,y) hy
    rw [he (b,y),he P] at hm
    change b*f.linear (1,0)+f 0≤_ at hm
    nlinarith only [hs,hm]

end GlobalBodyCutEquilibrium

end Plank
