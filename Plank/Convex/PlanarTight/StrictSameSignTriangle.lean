/- Original same-sign pair contacts force the exact strict triangle family. -/
module
public import Plank.Convex.PlanarTight.PlanarChart
public import Plank.Convex.PlanarTight.SameSignTriangle
public import Plank.Convex.SameSignCapPlanarContacts
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.StrictSameSignTriangle
open StrictCapSetting PlanarChart SameSignCapAlgebra SameSignCapProduct SameSignCapTransfer

theorem of_balanced_supports (C : Setting) (a b : Point3)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hupper : UpperSupports C.K C.hi a) (hlower : LowerSupports C.K C.lo b)
    (hbalanced : slopeProduct a b = 1) :
    ∃ v : Fin 3 → Point3, AffineIndependent ℝ v ∧ C.K = convexHull ℝ (Set.range v) := by
  let K' := projection '' C.K
  let f := forms C.A C.D
  have hg (x : Point3) (hx : x ∈ C.K) (i : Fin 3) : f i (projection x) = x i :=
    congrFun (graph_projection C.A C.D (C.positive 2).ne' x (C.plane x hx)) i
  have hbox : ∀ z ∈ K', ∀ i, 0 ≤ f i z ∧ f i z ≤ 1 := by
    rintro _ ⟨x, hx, rfl⟩ i
    simpa only [hg x hx i] using C.box x hx i
  have hL (i : Fin 3) : ∃ z ∈ K', f i z = 0 := by
    obtain ⟨x, hx, he⟩ := C.min i
    exact ⟨projection x, ⟨x, hx, rfl⟩, (hg x hx i).trans he⟩
  have hU (i : Fin 3) : ∃ z ∈ K', f i z = 1 := by
    obtain ⟨x, hx, he⟩ := C.max i
    exact ⟨projection x, ⟨x, hx, rfl⟩, (hg x hx i).trans he⟩
  have hupper' : ∀ i, ∀ z ∈ K',
      f i z + a i * f (next i) z ≤ C.hi i + a i * C.hi (next i) := by
    rintro i _ ⟨x, hx, rfl⟩
    simpa only [hg x hx i, hg x hx (next i)] using hupper i x hx
  have hlower' : ∀ i, ∀ z ∈ K',
      C.lo i + b i * C.lo (next i) ≤ f i z + b i * f (next i) z := by
    rintro i _ ⟨x, hx, rfl⟩
    simpa only [hg x hx i, hg x hx (next i)] using hlower i x hx
  obtain ⟨v, _, _, hv, hbody⟩ := SameSignTriangle.eq_triangle_of_balanced (by simp)
    K' (Convex.affine_image projection C.convex) f hbox hL hU C.A C.D
    (fun i => (C.positive i).ne') (graph_plane C.A C.D (C.positive 2).ne')
    (graph_injective C.A C.D) C.lo C.hi a b ha hb C.width_pos C.hi_lt C.total
    hupper' hlower' hbalanced
  exact triangle_of_projection C.K C.A C.D (C.positive 2).ne' C.plane v hv hbody

/-- Six pair contacts at the supplied endpoints supply the geometric cycle
gap. Equality then balances the supports and determines the whole body. -/
theorem of_pair_contacts (C : Setting)
    (hcapsU : ∀ i, ¬ ∃ x ∈ C.K, C.hi i < x i ∧ C.hi (next i) < x (next i))
    (hcapsL : ∀ i, ¬ ∃ x ∈ C.K, x i < C.lo i ∧ x (next i) < C.lo (next i))
    (hcontactsL : ∀ i, ∃ x ∈ C.K, x i = C.lo i ∧ x (next i) = C.lo (next i))
    (hcontactsU : ∀ i, ∃ x ∈ C.K, x i = C.hi i ∧ x (next i) = C.hi (next i)) :
    ∃ v : Fin 3 → Point3, AffineIndependent ℝ v ∧ C.K = convexHull ℝ (Set.range v) := by
  choose a ha hupper using fun i => ConvexCellSeparation.exists_upper_support C.K C.convex
    (AffineMap.proj i) (AffineMap.proj (next i)) (C.hi i) (C.hi (next i))
    (C.hi_lt i) (C.hi_lt (next i)) (C.max i) (C.max (next i)) (hcapsU i)
  choose b hb hlower using fun i => ConvexCellSeparation.exists_lower_support C.K C.convex
    (AffineMap.proj i) (AffineMap.proj (next i)) (C.lo i) (C.lo (next i))
    (C.lo_pos i) (C.lo_pos (next i)) (C.min i) (C.min (next i)) (hcapsL i)
  have hlow (i : Fin 3) : ∃ x ∈ C.K, x i < C.lo i := by
    obtain ⟨x, hx, he⟩ := C.min i
    exact ⟨x, hx, he ▸ C.lo_pos i⟩
  have hhigh (i : Fin 3) : ∃ x ∈ C.K, C.hi i < x i := by
    obtain ⟨x, hx, he⟩ := C.max i
    exact ⟨x, hx, he ▸ C.hi_lt i⟩
  have hgap := SameSignCapPlanarContacts.cycleGap_nonneg_of_pair_contacts
    C.K C.lo C.hi a b C.A C.D C.positive C.width_pos C.plane
    hcontactsL hcontactsU hlow hhigh hupper hlower
  have hrows := numeric_rows_of_supports C.K C.box C.min C.max C.lo C.hi a b ha hb hupper hlower
  have hbalanced := SameSignCapTightRigidity.slopeProduct_eq_one_of_tight
    C.lo C.hi a b ha hb hrows C.width_pos hgap C.total
  exact of_balanced_supports C a b ha hb hupper hlower hbalanced

end Plank.Convex.PlanarTight.StrictSameSignTriangle

/-- info: 'Plank.Convex.PlanarTight.StrictSameSignTriangle.of_balanced_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictSameSignTriangle.of_balanced_supports

/-- info: 'Plank.Convex.PlanarTight.StrictSameSignTriangle.of_pair_contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictSameSignTriangle.of_pair_contacts
