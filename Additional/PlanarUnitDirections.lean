/- A compact space of all planar directions, with continuously varying
actual support normalization. The sphere uses the ambient norm only to fix scale. -/
module

public import Plank.Proofs.Quant.PlanarNormalization
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarUnitDirections

open Set MeasureTheory PlanarQuantitative PlanarGapCells
open Plank.Convex.DeficientHeightTilt

abbrev Direction := Metric.sphere (0 : Point) 1

def raw (u : Point) : Point →ᵃ[ℝ] ℝ :=
  u 0 • AffineMap.proj 0 + u 1 • AffineMap.proj 1

@[simp] theorem raw_apply (u x : Point) : raw u x=u 0*x 0+u 1*x 1 := by
  simp [raw]

theorem raw_linear_ne_zero (u : Direction) : (raw u).linear≠0 := by
  intro he
  have h0 := congrArg (fun L : Point →ₗ[ℝ] ℝ => L (Pi.single 0 1)) he
  have h1 := congrArg (fun L : Point →ₗ[ℝ] ℝ => L (Pi.single 1 1)) he
  have hz : (u : Point)=0 := by
    funext i
    fin_cases i
    · simpa [raw] using h0
    · simpa [raw] using h1
  have hh := u.property
  simp [hz] at hh

instance directionCompact : CompactSpace Direction := inferInstance

instance directionNonempty : Nonempty Direction :=
  ⟨⟨fun _ => 1, by simp⟩⟩

theorem continuous_raw : Continuous (fun p : Direction × Point => raw p.1 p.2) := by
  simp only [raw_apply]
  have hc (j : Fin 2) : Continuous (fun p : Direction × Point => (p.1 : Point) j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)
  exact ((hc 0).mul ((continuous_apply 0).comp continuous_snd)).add
    ((hc 1).mul ((continuous_apply 1).comp continuous_snd))

/-- Positive body area gives positive width in every nonzero affine direction;
this does not use qualitative plank covering or convexity. -/
theorem rangeWidth_pos {K : Set Point} (hK : IsCompact K)
    (hV : 0<(volume K).toReal) (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear≠0) :
    0<rangeWidth K f := by
  have hne : K.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn] at hV
    simp at hV
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne (continuous_form f)
  have hw : rangeWidth K f=f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
  by_contra! hn
  have hz : volume K=0 := measure_mono_null (by
    intro x hx
    change f x=f b
    have h1 := hmax x hx
    have h2 := hmin x hx
    linarith only [hn,hw,h1,h2]) (measure_level_zero f hf (f b))
  simp [hz] at hV

def lower (K : Set Point) (u : Direction) : ℝ := sInf (raw u '' K)

def normalized (K : Set Point) (u : Direction) : Point →ᵃ[ℝ] ℝ :=
  (rangeWidth K (raw u))⁻¹ • (raw u-AffineMap.const ℝ Point (lower K u))

@[simp] theorem normalized_apply (K : Set Point) (u : Direction) (x : Point) :
    normalized K u x=(raw u x-lower K u)/rangeWidth K (raw u) := by
  simp [normalized,div_eq_mul_inv,mul_comm]

theorem continuous_lower {K : Set Point} (hK : IsCompact K) : Continuous (lower K) :=
  hK.continuous_sInf continuous_raw

theorem continuous_width {K : Set Point} (hK : IsCompact K) :
    Continuous (fun u : Direction => rangeWidth K (raw u)) :=
  (hK.continuous_sSup continuous_raw).sub (hK.continuous_sInf continuous_raw)

theorem continuous_normalized {K : Set Point} (hK : IsCompact K)
    (hV : 0<(volume K).toReal) :
    Continuous (fun p : Direction × Point => normalized K p.1 p.2) := by
  simp only [normalized_apply]
  exact (continuous_raw.sub ((continuous_lower hK).comp continuous_fst)).div
    ((continuous_width hK).comp continuous_fst)
    (fun p => (rangeWidth_pos hK hV (raw p.1) (raw_linear_ne_zero p.1)).ne')

theorem normalized_bounds {K : Set Point} (hK : IsCompact K)
    (hV : 0<(volume K).toReal) (u : Direction) {x : Point} (hx : x∈K) :
    0≤normalized K u x ∧ normalized K u x≤1 := by
  have hw := rangeWidth_pos hK hV (raw u) (raw_linear_ne_zero u)
  have hi := hK.image (continuous_form (raw u))
  have hl := csInf_le hi.bddBelow (mem_image_of_mem (raw u) hx)
  have hh := le_csSup hi.bddAbove (mem_image_of_mem (raw u) hx)
  rw [normalized_apply]
  refine ⟨div_nonneg (sub_nonneg.mpr hl) hw.le, (div_le_one hw).mpr ?_⟩
  exact sub_le_sub_right hh _

theorem normalized_width {K : Set Point} (hK : IsCompact K)
    (hV : 0<(volume K).toReal) (u : Direction) : rangeWidth K (normalized K u)=1 := by
  have hne : K.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn] at hV
    simp at hV
  obtain ⟨a,ha,hmax⟩ := hK.exists_sSup_image_eq hne (continuous_form (raw u)).continuousOn
  obtain ⟨b,hb,hmin⟩ := hK.exists_sInf_image_eq hne (continuous_form (raw u)).continuousOn
  have hw := rangeWidth_pos hK hV (raw u) (raw_linear_ne_zero u)
  have hga : normalized K u a=1 := by
    rw [normalized_apply,←hmax]
    exact div_self hw.ne'
  have hgb : normalized K u b=0 := by
    rw [normalized_apply,←hmin]
    simp [lower]
  have heq : rangeWidth K (normalized K u)=normalized K u a-normalized K u b :=
    Body.width_eq_of_realisers ha hb
      (fun x hx => by rw [hga]; exact (normalized_bounds hK hV u hx).2)
      (fun x hx => by rw [hgb]; exact (normalized_bounds hK hV u hx).1)
  rw [heq,hga,hgb,sub_zero]

end Plank.PlanarUnitDirections

#print axioms Plank.PlanarUnitDirections.continuous_normalized
#print axioms Plank.PlanarUnitDirections.normalized_width
