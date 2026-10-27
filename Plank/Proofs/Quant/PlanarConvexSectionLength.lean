/- Concavity of actual one-dimensional sections of arbitrary planar convex bodies. -/
module

public import Plank.Proofs.Quant.ConvexSections
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Convex.Function

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarConvexSectionLength

open Set MeasureTheory ConvexSections

/-- Actual section length, including empty and singleton sections. -/
def length (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (volume (fiber K t)).toReal

theorem fiber_interval {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) {t : ℝ} (ht : t ∈ Prod.fst '' K) :
    ∃ a b : ℝ, a ≤ b ∧ fiber K t = Icc a b := by
  obtain ⟨p,hp,hpt⟩ := ht
  have hn : (fiber K t).Nonempty := ⟨p.2,by
    change (t,p.2) ∈ K
    rw [← hpt]
    exact hp⟩
  have hs := compact_fiber hK t
  obtain ⟨a,ha,hmin⟩ := hs.exists_isMinOn hn continuous_id.continuousOn
  obtain ⟨b,hb,hmax⟩ := hs.exists_isMaxOn hn continuous_id.continuousOn
  refine ⟨a,b,hmin hb,?_⟩
  apply Subset.antisymm
  · exact fun x hx => ⟨hmin hx,hmax hx⟩
  · exact (convex_fiber hc t).ordConnected.out ha hb

/-- The actual section length is concave on the full support interval.
No polygon, smoothness, or transverse-support-face assumption is needed. -/
theorem concaveOn_length {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) : ConcaveOn ℝ (Prod.fst '' K) (length K) := by
  refine ⟨hc.linear_image (LinearMap.fst ℝ ℝ ℝ),?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨l,u,hlu,hxI⟩ := fiber_interval hK hc hx
  obtain ⟨v,w,hvw,hyI⟩ := fiber_interval hK hc hy
  have hl : (x,l) ∈ K := by
    change l ∈ fiber K x
    rw [hxI]
    exact ⟨le_rfl,hlu⟩
  have hu : (x,u) ∈ K := by
    change u ∈ fiber K x
    rw [hxI]
    exact ⟨hlu,le_rfl⟩
  have hv : (y,v) ∈ K := by
    change v ∈ fiber K y
    rw [hyI]
    exact ⟨le_rfl,hvw⟩
  have hw : (y,w) ∈ K := by
    change w ∈ fiber K y
    rw [hyI]
    exact ⟨hvw,le_rfl⟩
  have hlow : a*l+b*v ∈ fiber K (a*x+b*y) := by
    exact hc hl hv ha hb hab
  have hhigh : a*u+b*w ∈ fiber K (a*x+b*y) := by
    exact hc hu hw ha hb hab
  have hs : Icc (a*l+b*v) (a*u+b*w) ⊆ fiber K (a*x+b*y) :=
    (convex_fiber hc _).ordConnected.out hlow hhigh
  have horder : a*l+b*v ≤ a*u+b*w :=
    add_le_add (mul_le_mul_of_nonneg_left hlu ha) (mul_le_mul_of_nonneg_left hvw hb)
  have hm : (volume (Icc (a*l+b*v) (a*u+b*w))).toReal ≤ length K (a*x+b*y) :=
    ENNReal.toReal_mono (compact_fiber hK (a*x+b*y)).measure_ne_top (measure_mono hs)
  change a*length K x+b*length K y ≤ length K (a*x+b*y)
  have hxL : length K x = u-l := by
    rw [length,hxI]
    exact Real.volume_real_Icc_of_le hlu
  have hyL : length K y = w-v := by
    rw [length,hyI]
    exact Real.volume_real_Icc_of_le hvw
  have hm' : (a*u+b*w)-(a*l+b*v) ≤ length K (a*x+b*y) := by
    exact (Real.volume_real_Icc_of_le horder) ▸ hm
  rw [hxL,hyL]
  linarith only [hm']

end Plank.PlanarConvexSectionLength

/-- info: 'Plank.PlanarConvexSectionLength.concaveOn_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarConvexSectionLength.concaveOn_length
