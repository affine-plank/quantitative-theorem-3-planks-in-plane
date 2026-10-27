/- Ordered-stack classification on arbitrary triangles with common extremes. -/
module

public import Plank.Proofs.Quant.CommonMiddleConverse
public import Plank.Proofs.Quant.AffineTransport

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CommonMiddleAffineTransport

open Set MeasureTheory Proofs.Basic Proofs.Transport
open scoped BigOperators

/-- The oriented plank form has its minimum at A and maximum at B. -/
def CommonExtremes (T : Triangle) (p : Plank) : Prop :=
  dot p.u T.A ≤ dot p.u T.C ∧ dot p.u T.C ≤ dot p.u T.B

def span (T : Triangle) (p : Plank) : ℝ := dot p.u T.B - dot p.u T.A

def slope (T : Triangle) (p : Plank) : ℝ :=
  (dot p.u T.C - dot p.u T.A) / span T p

def lower (T : Triangle) (p : Plank) : ℝ := (p.lo - dot p.u T.A) / span T p

def upper (T : Triangle) (p : Plank) : ℝ := (p.hi - dot p.u T.A) / span T p

theorem width_eq_span (T : Triangle) (p : Plank) (h : CommonExtremes T p) :
    T.width p.u = span T p := by
  simp only [Triangle.width, max_eq_left h.2, max_eq_right (h.1.trans h.2),
    min_eq_right h.2, min_eq_left h.1, span]

theorem span_pos (T : Triangle) (p : Plank) (h : CommonExtremes T p) :
    0 < span T p := by
  rw [← width_eq_span T p h]
  exact width_pos T p.u_ne_zero

theorem slope_mem (T : Triangle) (p : Plank) (h : CommonExtremes T p) :
    0 ≤ slope T p ∧ slope T p ≤ 1 := by
  have hw := span_pos T p h
  exact ⟨div_nonneg (sub_nonneg.mpr h.1) hw.le,
    (div_le_one hw).mpr (sub_le_sub_right h.2 _)⟩

/-- Normalize the actual affine pullback by its positive width. -/
def normalizedPlank (T : Triangle) (p : Plank) (h : CommonExtremes T p) : Plank :=
  ⟨(1, slope T p), lower T p, upper T p,
    by intro hz; have hf := congrArg Prod.fst hz; norm_num at hf,
    div_le_div_of_nonneg_right (sub_le_sub_right p.lo_le_hi _) (span_pos T p h).le⟩

theorem normalizedPlank_set (T : Triangle) (p : Plank) (h : CommonExtremes T p) :
    (normalizedPlank T p h).set = (pullbackPlank T p).set := by
  ext x
  have hw := span_pos T p h
  have hd : dot (normalizedPlank T p h).u x = dot (pullbackPlank T p).u x / span T p := by
    change 1*x.1 + ((dot p.u T.C-dot p.u T.A)/span T p)*x.2 =
      (dot p.u (T.B-T.A)*x.1 + dot p.u (T.C-T.A)*x.2)/span T p
    rw [dot_sub_right, dot_sub_right]
    change 1*x.1 + ((dot p.u T.C-dot p.u T.A)/span T p)*x.2 =
      (span T p*x.1 + (dot p.u T.C-dot p.u T.A)*x.2)/span T p
    field_simp [ne_of_gt hw]
  change (lower T p ≤ dot (normalizedPlank T p h).u x ∧
    dot (normalizedPlank T p h).u x ≤ upper T p) ↔
    (p.lo-dot p.u T.A ≤ dot (pullbackPlank T p).u x ∧
      dot (pullbackPlank T p).u x ≤ p.hi-dot p.u T.A)
  rw [hd]
  exact and_congr (div_le_div_iff_of_pos_right hw) (div_le_div_iff_of_pos_right hw)

theorem normalizedPlank_relWidth (T : Triangle) (p : Plank) (h : CommonExtremes T p) :
    (normalizedPlank T p h).relWidth stdTriangle = p.relWidth T := by
  have hb := slope_mem T p h
  simp only [Plank.relWidth, normalizedPlank, stdTriangle_width_eq,
    max_eq_left hb.2, max_eq_right zero_le_one, min_eq_right hb.2,
    min_eq_left hb.1, sub_zero, div_one, width_eq_span T p h, lower, upper]
  ring

def normalizedConfig (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) : Config :=
  ⟨fun i => normalizedPlank T (p i) (h i)⟩

theorem normalizedConfig_relW (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) (i : Fin 3) :
    (normalizedConfig T p h).relW i = (p i).relWidth T :=
  normalizedPlank_relWidth T (p i) (h i)

theorem normalizedConfig_sumRelW (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) :
    (normalizedConfig T p h).sumRelW = ∑ i, (p i).relWidth T := by
  simp only [Config.sumRelW, normalizedConfig_relW]

theorem normalizedConfig_deficit (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) :
    (normalizedConfig T p h).deficit = 1-∑ i, (p i).relWidth T := by
  rw [Config.deficit, normalizedConfig_sumRelW]

theorem normalizedConfig_uncovered (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) :
    (normalizedConfig T p h).uncovered = (AffineTransport.pullbackConfig T p).uncovered := by
  simp only [Config.uncovered, normalizedConfig, AffineTransport.pullbackConfig,
    normalizedPlank_set]

/-- Exact transport of the actual uncovered set, not merely its width data. -/
theorem image_uncovered (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) :
    chart T '' (normalizedConfig T p h).uncovered = T.set \ ⋃ i, (p i).set := by
  rw [normalizedConfig_uncovered, AffineTransport.image_uncovered_pullbackConfig]

theorem gapArea_transport (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) :
    (volume (T.set \ ⋃ i, (p i).set)).toReal =
      |det3 T.A T.B T.C| * (normalizedConfig T p h).gapArea := by
  rw [← image_uncovered T p h, AffineTransport.area_image_chart]
  rfl

theorem equality_iff_normalized (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) :
    ((volume (T.set \ ⋃ i, (p i).set)).toReal =
      (max 0 (1-∑ i, (p i).relWidth T))^2 * (volume T.set).toReal) ↔
      TriangleEqualityReductions.Equality (normalizedConfig T p h) := by
  rw [gapArea_transport T p h, AffineTransport.area_triangle,
    ← normalizedConfig_deficit T p h]
  have hn : |det3 T.A T.B T.C| ≠ 0 := abs_ne_zero.mpr (det3_ne_zero T)
  change _ ↔ (normalizedConfig T p h).gapArea =
    (max 0 (normalizedConfig T p h).deficit)^2*(1/2)
  rw [show (max 0 (normalizedConfig T p h).deficit)^2*(|det3 T.A T.B T.C| * (1/2)) =
    |det3 T.A T.B T.C| * ((max 0 (normalizedConfig T p h).deficit)^2*(1/2)) by ring]
  exact ⟨mul_left_cancel₀ hn, fun he => congrArg (fun x => |det3 T.A T.B T.C| * x) he⟩

/-- Six endpoint identities in the original triangle's normalized form
coordinates. Repeated slopes and the boundary slopes zero and one are allowed. -/
def OrderedStack (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), slope T (p (σ 0)) ≤ slope T (p (σ 1)) ∧
    slope T (p (σ 1)) ≤ slope T (p (σ 2)) ∧
    lower T (p (σ 0)) = (1-∑ i, (p i).relWidth T)*slope T (p (σ 0)) ∧
    upper T (p (σ 0)) = (1-∑ i, (p i).relWidth T)*slope T (p (σ 0)) + (p (σ 0)).relWidth T ∧
    lower T (p (σ 1)) = (1-∑ i, (p i).relWidth T)*slope T (p (σ 1)) + (p (σ 0)).relWidth T ∧
    upper T (p (σ 1)) = (1-∑ i, (p i).relWidth T)*slope T (p (σ 1)) +
      (p (σ 0)).relWidth T + (p (σ 1)).relWidth T ∧
    lower T (p (σ 2)) = (1-∑ i, (p i).relWidth T)*slope T (p (σ 2)) +
      (p (σ 0)).relWidth T + (p (σ 1)).relWidth T ∧
    upper T (p (σ 2)) = (1-∑ i, (p i).relWidth T)*slope T (p (σ 2)) + ∑ i, (p i).relWidth T

theorem orderedStack_iff_normalized (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) :
    OrderedStack T p ↔ CommonMiddleNecessity.OrderedStack
      (normalizedConfig T p h) (fun i => slope T (p i)) := by
  simp only [OrderedStack, CommonMiddleNecessity.OrderedStack,
    normalizedConfig_deficit, normalizedConfig_relW, normalizedConfig_sumRelW]
  rfl

/-- Matching area for every displayed ordered stack on an arbitrary triangle.
Zero widths are allowed here, at the specified stack endpoints. -/
theorem equality_of_orderedStack (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) (hR1 : (∑ i, (p i).relWidth T) < 1)
    (hs : OrderedStack T p) :
    (volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2 * (volume T.set).toReal := by
  have he := CommonMiddleNecessity.equality_of_orderedStack
    (normalizedConfig T p h) (fun i => slope T (p i))
    (fun i => slope_mem T (p i) (h i)) (fun _ => rfl)
    (by rwa [normalizedConfig_sumRelW]) ((orderedStack_iff_normalized T p h).mp hs)
  simpa only [max_eq_right (sub_nonneg.mpr hR1.le)] using
    (equality_iff_normalized T p h).mpr he

/-- Exhaustive ordered-stack iff for arbitrary nondegenerate triangles in
the common-minimum/common-maximum chart, with three positive relative widths. -/
theorem equality_iff_orderedStack (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, CommonExtremes T (p i)) (hw : ∀ i, 0 < (p i).relWidth T)
    (hR : 0 < ∑ i, (p i).relWidth T) (hR1 : (∑ i, (p i).relWidth T) < 1) :
    ((volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2 * (volume T.set).toReal) ↔ OrderedStack T p := by
  have he := (equality_iff_normalized T p h).trans
    (CommonMiddleNecessity.equality_iff_orderedStack
      (normalizedConfig T p h) (fun i => slope T (p i))
      (fun i => slope_mem T (p i) (h i)) (fun _ => rfl)
      (fun i => by rw [normalizedConfig_relW]; exact hw i)
      (by rwa [normalizedConfig_sumRelW]) (by rwa [normalizedConfig_sumRelW]))
  simpa only [max_eq_right (sub_nonneg.mpr hR1.le)] using
    he.trans (orderedStack_iff_normalized T p h).symm

end Quant.CommonMiddleAffineTransport

/-- info: 'Quant.CommonMiddleAffineTransport.equality_iff_orderedStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonMiddleAffineTransport.equality_iff_orderedStack
