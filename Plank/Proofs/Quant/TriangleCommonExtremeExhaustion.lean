/- The common-extreme catalogue exhausts the entire noncyclic triangle sector. -/
module
public import Plank.Proofs.Quant.TriangleOrientationExhaustion

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCommonExtremeExhaustion
open Set MeasureTheory TriangleCommonExtremeCatalogue TriangleOrientationExhaustion
open TriangleCommonMinimumAffineCatalogue
open scoped BigOperators

/-- The four explicit families, in a constructed chart at any shared extreme
vertex, with the original bands independently oriented toward that vertex. -/
def Catalogue (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  ∃ (v : Fin 3) (h : ∀ i, AtExtreme (atVertex T v) (p i)),
    TriangleCommonMinimumCatalogue.Catalogue
      (triangleConfig (atVertex T v) (fun i => oriented (atVertex T v) (p i))
        (oriented_common (atVertex T v) p h))

theorem equality_iff_catalogue (T : Triangle) (p : Fin 3 → Plank)
    (hc : HasCommonExtreme T p) (hw : ∀ i, 0 < (p i).relWidth T)
    (hR : (∑ i, (p i).relWidth T) < 1) :
    ((volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) ↔ Catalogue T p := by
  constructor
  · intro he
    obtain ⟨v,hv⟩ := hc
    exact ⟨v,hv,(vertex_equality_iff_catalogue T p v hv hw hR).mp he⟩
  · rintro ⟨v,hv,hf⟩
    exact (vertex_equality_iff_catalogue T p v hv hw hR).mpr hf

theorem noncyclic_equality_iff_catalogue (T : Triangle) (p : Fin 3 → Plank)
    (hc : ¬ StrictCyclic T p) (hw : ∀ i, 0 < (p i).relWidth T)
    (hR : (∑ i, (p i).relWidth T) < 1) :
    ((volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) ↔ Catalogue T p :=
  equality_iff_catalogue T p ((exhaustive T p).resolve_right hc) hw hR

theorem edge_equality_iff_catalogue (T : Triangle) (p : Fin 3 → Plank) (j : Fin 3)
    (ht : dot (p j).u T.A = dot (p j).u T.B ∨
      dot (p j).u T.A = dot (p j).u T.C ∨ dot (p j).u T.B = dot (p j).u T.C)
    (hw : ∀ i, 0 < (p i).relWidth T) (hR : (∑ i, (p i).relWidth T) < 1) :
    ((volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) ↔ Catalogue T p :=
  equality_iff_catalogue T p (common_extreme_of_tied_edge T p j ht) hw hR

/-- Every remaining positive-width equality case is strictly cyclic.
No classification of that remaining sector is assumed here. -/
theorem catalogue_or_strict_cyclic (T : Triangle) (p : Fin 3 → Plank)
    (hw : ∀ i, 0 < (p i).relWidth T) (hR : (∑ i, (p i).relWidth T) < 1)
    (he : (volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) :
    Catalogue T p ∨ StrictCyclic T p := by
  rcases exhaustive T p with hc | hc
  · exact Or.inl ((equality_iff_catalogue T p hc hw hR).mp he)
  · exact Or.inr hc

end Quant.TriangleCommonExtremeExhaustion

/-- info: 'Quant.TriangleCommonExtremeExhaustion.noncyclic_equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCommonExtremeExhaustion.noncyclic_equality_iff_catalogue

/-- info: 'Quant.TriangleCommonExtremeExhaustion.catalogue_or_strict_cyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCommonExtremeExhaustion.catalogue_or_strict_cyclic
