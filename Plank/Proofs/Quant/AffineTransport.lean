module
/- Quantitative affine transport of the standard-triangle square bound. -/
public import Plank.Quant

@[expose] public section
noncomputable section

namespace Quant.AffineTransport

open Set MeasureTheory Proofs.Basic Proofs.Transport

/-- Linear part of the existing standard-triangle chart. -/
def chartLinear (T : Triangle) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := x.1 • (T.B-T.A)+x.2 • (T.C-T.A)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' r x := by
    simp [smul_add, smul_smul]

theorem chart_eq_linear_add (T : Triangle) :
    chart T = (fun x => T.A+x) ∘ chartLinear T := by
  funext x
  change T.A+x.1 • (T.B-T.A)+x.2 • (T.C-T.A) =
    T.A+(x.1 • (T.B-T.A)+x.2 • (T.C-T.A))
  exact add_assoc _ _ _

theorem det_chartLinear (T : Triangle) :
    LinearMap.det (chartLinear T) = det3 T.A T.B T.C := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, chartLinear, Module.Basis.finTwoProd, det3]
  ring

/-- The chart covers the entire filled triangle. -/
theorem image_chart_stdTriangle (T : Triangle) :
    chart T '' stdTriangle.set = T.set := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact chart_mem T hx
  · rintro x ⟨α, β, γ, hα, hβ, hγ, hsum, hx⟩
    refine ⟨(β,γ), (stdTriangle_mem_iff _).mpr ⟨hβ,hγ,by linarith only [hα,hsum]⟩, ?_⟩
    have hαeq : α = 1-β-γ := by linarith only [hsum]
    rw [hx, hαeq]
    simp only [chart]
    module

/-- Exact Lebesgue scaling, with the Jacobian computed from the vertices. -/
theorem volume_image_chart (T : Triangle) (s : Set (ℝ × ℝ)) :
    volume (chart T '' s) = ENNReal.ofReal |det3 T.A T.B T.C| * volume s := by
  rw [chart_eq_linear_add, Set.image_comp, Set.image_add_left, measure_preimage_add,
    Measure.addHaar_image_linearMap, det_chartLinear]

theorem area_image_chart (T : Triangle) (s : Set (ℝ × ℝ)) :
    (volume (chart T '' s)).toReal = |det3 T.A T.B T.C| * (volume s).toReal := by
  rw [volume_image_chart, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

theorem volume_triangle (T : Triangle) :
    volume T.set = ENNReal.ofReal |det3 T.A T.B T.C| * ENNReal.ofReal (1/2) := by
  rw [← image_chart_stdTriangle, volume_image_chart, Proofs.Quant.volume_stdTriangle]

theorem area_triangle (T : Triangle) :
    (volume T.set).toReal = |det3 T.A T.B T.C| * (1/2) := by
  rw [volume_triangle, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/2)]

def pullbackConfig (T : Triangle) (p : Fin 3 → Plank) : Config :=
  ⟨fun i => pullbackPlank T (p i)⟩

theorem sumRelW_pullbackConfig (T : Triangle) (p : Fin 3 → Plank) :
    (pullbackConfig T p).sumRelW = ∑ i, (p i).relWidth T := by
  simp only [Config.sumRelW, Config.relW, pullbackConfig, relWidth_pullback]

theorem deficit_pullbackConfig (T : Triangle) (p : Fin 3 → Plank) :
    (pullbackConfig T p).deficit = 1-∑ i, (p i).relWidth T := by
  rw [Config.deficit, sumRelW_pullbackConfig]

/-- Pullback of all bands commutes exactly with the uncovered set. -/
theorem image_uncovered_pullbackConfig (T : Triangle) (p : Fin 3 → Plank) :
    chart T '' (pullbackConfig T p).uncovered = T.set \ ⋃ i, (p i).set := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    refine ⟨chart_mem T hx, ?_⟩
    intro hc
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
    apply hn
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    exact (mem_pullback_iff T (p i) x).mpr hi
  · rintro ⟨hy, hn⟩
    rw [← image_chart_stdTriangle] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hc
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
    apply hn
    apply Set.mem_iUnion.mpr
    exact ⟨i, (mem_pullback_iff T (p i) x).mp hi⟩

theorem gapArea_transport (T : Triangle) (p : Fin 3 → Plank) :
    (volume (T.set \ ⋃ i, (p i).set)).toReal =
      |det3 T.A T.B T.C| * (pullbackConfig T p).gapArea := by
  rw [← image_uncovered_pullbackConfig, area_image_chart]
  rfl

/-- A sharp bound on the pulled-back configuration gives the sharp bound on
the original triangle, with its actual Lebesgue area. -/
theorem sqPos_triangle_of_pullback (T : Triangle) (p : Fin 3 → Plank)
    (hsq : Quant.SqPos (pullbackConfig T p)) :
    (max 0 (1-∑ i, (p i).relWidth T))^2*(volume T.set).toReal ≤
      (volume (T.set \ ⋃ i, (p i).set)).toReal := by
  have hs := mul_le_mul_of_nonneg_left hsq (abs_nonneg (det3 T.A T.B T.C))
  rw [area_triangle, gapArea_transport]
  change |det3 T.A T.B T.C| * ((max 0 (pullbackConfig T p).deficit)^2*(1/2)) ≤
    |det3 T.A T.B T.C| * (pullbackConfig T p).gapArea at hs
  rw [deficit_pullbackConfig] at hs
  nlinarith only [hs]

/-- The full standard-triangle theorem transports to every nondegenerate
triangle and every three planks, without an additional Jacobian premise. -/
theorem sqPos_triangle_of_std (hstd : ∀ C : Config, Quant.SqPos C)
    (T : Triangle) (p : Fin 3 → Plank) :
    (max 0 (1-∑ i, (p i).relWidth T))^2*(volume T.set).toReal ≤
      (volume (T.set \ ⋃ i, (p i).set)).toReal :=
  sqPos_triangle_of_pullback T p (hstd _)


end Quant.AffineTransport
