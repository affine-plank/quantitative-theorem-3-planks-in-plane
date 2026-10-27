/- The complete common-minimum catalogue on arbitrary triangles and bands. -/
module
public import Plank.Proofs.Quant.TriangleCommonMinimumCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCommonMinimumAffineCatalogue
open Set MeasureTheory Proofs.Basic Proofs.Transport
open TriangleCommonMinimumCatalogue
open scoped BigOperators

theorem max_pos (p : Plank) (hu : 0 ≤ p.u.1 ∧ 0 ≤ p.u.2) : 0 < max p.u.1 p.u.2 := by
  by_contra hn
  have hm : max p.u.1 p.u.2 ≤ 0 := le_of_not_gt hn
  apply p.u_ne_zero
  exact Prod.ext (le_antisymm ((le_max_left _ _).trans hm) hu.1)
    (le_antisymm ((le_max_right _ _).trans hm) hu.2)

/-- Positive rescaling fixes the whole physical plank, not just its
intersection with the triangle. The scale is the actual directional span. -/
def normalizedPlank (p : Plank) (hu : 0 ≤ p.u.1 ∧ 0 ≤ p.u.2) : Plank :=
  scaleP (max p.u.1 p.u.2)⁻¹ (inv_pos.mpr (max_pos p hu)) p

theorem normalizedPlank_set (p : Plank) (hu : 0 ≤ p.u.1 ∧ 0 ≤ p.u.2) :
    (normalizedPlank p hu).set=p.set := TriangleMixedTransport.scale_set _ _ _

theorem normalizedPlank_width (p : Plank) (hu : 0 ≤ p.u.1 ∧ 0 ≤ p.u.2) :
    (normalizedPlank p hu).relWidth stdTriangle=p.relWidth stdTriangle :=
  TriangleMixedTransport.scale_width _ _ _ _

theorem normalizedPlank_nonneg (p : Plank) (hu : 0 ≤ p.u.1 ∧ 0 ≤ p.u.2) :
    0 ≤ (normalizedPlank p hu).u.1 ∧ 0 ≤ (normalizedPlank p hu).u.2 := by
  exact ⟨mul_nonneg (inv_nonneg.mpr (max_pos p hu).le) hu.1,
    mul_nonneg (inv_nonneg.mpr (max_pos p hu).le) hu.2⟩

theorem normalizedPlank_max (p : Plank) (hu : 0 ≤ p.u.1 ∧ 0 ≤ p.u.2) :
    max (normalizedPlank p hu).u.1 (normalizedPlank p hu).u.2=1 := by
  change max ((max p.u.1 p.u.2)⁻¹*p.u.1) ((max p.u.1 p.u.2)⁻¹*p.u.2)=1
  rw [← mul_max_of_nonneg _ _ (inv_nonneg.mpr (max_pos p hu).le),
    inv_mul_cancel₀ (max_pos p hu).ne']

def normalizedConfig (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2) : Config :=
  ⟨fun i => normalizedPlank (C.plank i) (hu i)⟩

theorem normalizedConfig_width (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2) (i : Fin 3) :
    (normalizedConfig C hu).relW i=C.relW i := normalizedPlank_width (C.plank i) (hu i)

theorem normalizedConfig_deficit (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2) :
    (normalizedConfig C hu).deficit=C.deficit := by
  simp only [Config.deficit,Config.sumRelW,normalizedConfig_width]

theorem normalizedConfig_uncovered (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2) :
    (normalizedConfig C hu).uncovered=C.uncovered := by
  simp only [Config.uncovered,normalizedConfig,normalizedPlank_set]

theorem equality_iff_catalogue (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔ Catalogue (normalizedConfig C hu) := by
  have hn := TriangleCommonMinimumCatalogue.equality_iff_catalogue (normalizedConfig C hu)
    (fun i => normalizedPlank_nonneg (C.plank i) (hu i))
    (fun i => normalizedPlank_max (C.plank i) (hu i))
    (fun i => (normalizedConfig_width C hu i).symm ▸ hw i)
    ((normalizedConfig_deficit C hu).symm ▸ hδ)
  simpa only [TriangleEqualityReductions.Equality,Config.gapArea,
    normalizedConfig_deficit,normalizedConfig_uncovered] using hn

/-- The same vertex A is a (possibly tied) minimum of every oriented
original plank form. No restriction is put on its other two vertex values. -/
def CommonMinimum (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  ∀ i, dot (p i).u T.A ≤ dot (p i).u T.B ∧ dot (p i).u T.A ≤ dot (p i).u T.C

theorem pullback_nonneg (T : Triangle) (p : Fin 3 → Plank) (hu : CommonMinimum T p) :
    ∀ i, 0 ≤ ((AffineTransport.pullbackConfig T p).plank i).u.1 ∧
      0 ≤ ((AffineTransport.pullbackConfig T p).plank i).u.2 := by
  intro i
  change 0 ≤ dot (p i).u (T.B-T.A) ∧ 0 ≤ dot (p i).u (T.C-T.A)
  rw [dot_sub_right,dot_sub_right]
  exact ⟨sub_nonneg.mpr (hu i).1,sub_nonneg.mpr (hu i).2⟩

def triangleConfig (T : Triangle) (p : Fin 3 → Plank) (hu : CommonMinimum T p) : Config :=
  normalizedConfig (AffineTransport.pullbackConfig T p) (pullback_nonneg T p hu)

theorem triangleConfig_set (T : Triangle) (p : Fin 3 → Plank)
    (hu : CommonMinimum T p) (i : Fin 3) :
    ((triangleConfig T p hu).plank i).set=(pullbackPlank T (p i)).set :=
  normalizedPlank_set (pullbackPlank T (p i)) (pullback_nonneg T p hu i)

theorem triangleConfig_width (T : Triangle) (p : Fin 3 → Plank)
    (hu : CommonMinimum T p) (i : Fin 3) :
    (triangleConfig T p hu).relW i=(p i).relWidth T := by
  rw [triangleConfig,normalizedConfig_width]
  exact relWidth_pullback T (p i)

/-- Complete geometric exhaustion for arbitrary triangles, original
normal magnitudes, arbitrary band positions, and every common-minimum
direction pattern, including all tied extrema and repeated directions.
The three widths are positive and their actual sum is subcritical.
The chart and normalization are constructed and preserve entire planks
and individual widths. Cyclic configurations are outside this theorem. -/
theorem triangle_equality_iff_catalogue (T : Triangle) (p : Fin 3 → Plank)
    (hu : CommonMinimum T p) (hw : ∀ i, 0 < (p i).relWidth T)
    (hR : (∑ i, (p i).relWidth T) < 1) :
    ((volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) ↔
      Catalogue (triangleConfig T p hu) := by
  have hδ : 0 < (AffineTransport.pullbackConfig T p).deficit := by
    rw [AffineTransport.deficit_pullbackConfig]
    exact sub_pos.mpr hR
  have he := equality_iff_catalogue (AffineTransport.pullbackConfig T p)
    (pullback_nonneg T p hu) (fun i => by
      change 0 < (pullbackPlank T (p i)).relWidth stdTriangle
      rw [relWidth_pullback]
      exact hw i) hδ
  rw [triangleConfig,← he]
  rw [AffineTransport.gapArea_transport,AffineTransport.area_triangle]
  have hn : |det3 T.A T.B T.C| ≠ 0 := abs_ne_zero.mpr (det3_ne_zero T)
  unfold TriangleEqualityReductions.Equality
  rw [max_eq_right hδ.le,AffineTransport.deficit_pullbackConfig]
  rw [show (1-∑ i, (p i).relWidth T)^2*(|det3 T.A T.B T.C| * (1/2)) =
    |det3 T.A T.B T.C| * ((1-∑ i, (p i).relWidth T)^2*(1/2)) by ring]
  exact ⟨mul_left_cancel₀ hn,fun h => congrArg (fun x => |det3 T.A T.B T.C| * x) h⟩

end Quant.TriangleCommonMinimumAffineCatalogue

/-- info: 'Quant.TriangleCommonMinimumAffineCatalogue.triangle_equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCommonMinimumAffineCatalogue.triangle_equality_iff_catalogue
