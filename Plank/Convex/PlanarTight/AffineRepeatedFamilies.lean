/- Exact original affine families obtained by splitting a two-plank family. -/
module
public import Plank.Convex.PlanarTight.OrientedRangeCoordinates
public import Plank.Convex.PlanarTight.RepeatedDirectionChart
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AffineRepeatedFamilies
open DeficientHeightTilt (rangeWidth)
open OrientedRangeCoordinates (forms lower upper)

abbrev E := Fin 2 → ℝ
abbrev P := Fin 3 → ℝ

/-- Normalize the actual ranges, reorder and independently orient the functions,
then split one window of an explicit triangular or quadrilateral two-plank family.
The first two oriented functions agree. The predicate contains only range contacts,
positive parameters, affine identities, endpoint equations, and body inequalities. -/
def Normal (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : P) : Prop :=
  let W : P := fun i => rangeWidth K (f i)
  ∃ (m : P) (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool),
    (∀ x ∈ K, ∀ i, m i ≤ f i x ∧ f i x ≤ m i + W i) ∧
    (∀ i, ∃ x ∈ K, f i x = m i) ∧ (∀ i, ∃ x ∈ K, f i x = m i + W i) ∧
    (∀ i, lower m W lo hi σ flip i < upper m W lo hi σ flip i) ∧
    forms f m W σ flip 0 = forms f m W σ flip 1 ∧
    TwoDirectionClassification.Normal (RepeatedDirectionChart.chart (forms f m W σ flip) '' K)
      (AffineMap.proj 0) (AffineMap.proj 1)
      (lower m W lo hi σ flip 0) (upper m W lo hi σ flip 0)
      (lower m W lo hi σ flip 1) (upper m W lo hi σ flip 1)
      (lower m W lo hi σ flip 2) (upper m W lo hi σ flip 2)

theorem Normal.tight (K : Set E) (hK : Convex ℝ K) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : P) (hW : ∀ i, 0 < rangeWidth K (f i)) (hn : Normal K f lo hi) :
    (∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1 ∧
      ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i := by
  obtain ⟨m, σ, flip, hb, hL, hU, hw, heq, hn⟩ := hn
  let W : P := fun i => rangeWidth K (f i)
  let g := forms f m W σ flip
  let L := lower m W lo hi σ flip
  let U := upper m W lo hi σ flip
  have hbg := OrientedRangeCoordinates.box K f m W σ flip hW hb
  have hLg := OrientedRangeCoordinates.zero_contacts K f m W σ flip hW hL hU
  have hUg := OrientedRangeCoordinates.unit_contacts K f m W σ flip hW hL hU
  have hbJ := RepeatedDirectionChart.box K g hbg
  have hLJ := RepeatedDirectionChart.zero_contacts K g hLg
  have hUJ := RepeatedDirectionChart.unit_contacts K g hUg
  have ht := TwoDirectionUnclipped.normal_tight (RepeatedDirectionChart.chart g '' K)
    (Convex.affine_image _ hK) hbJ (hLJ 0) (hUJ 0) (hLJ 1) (hUJ 1) L U hw hn
  have ht' := (RepeatedDirectionChart.tight_iff K g heq L U).mp ht
  refine ⟨?_, (OrientedRangeCoordinates.cover_iff K f m W lo hi σ flip hW).mp ht'.2⟩
  exact (OrientedRangeCoordinates.sum_width_eq m W lo hi σ flip).symm.trans ht'.1

/-- The repeated independent direction case has exactly the stated split families.
The inputs retain their original affine widths and endpoints. -/
theorem of_tight (K : Set E) (hK : Convex ℝ K) (hfull : (interior K).Nonempty)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : P) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hw : ∀ i, lo i < hi i) (m : P)
    (hb : ∀ x ∈ K, ∀ i, m i ≤ f i x ∧ f i x ≤ m i + rangeWidth K (f i))
    (hL : ∀ i, ∃ x ∈ K, f i x = m i)
    (hU : ∀ i, ∃ x ∈ K, f i x = m i + rangeWidth K (f i))
    (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool)
    (heq : forms f m (fun i => rangeWidth K (f i)) σ flip 0 =
      forms f m (fun i => rangeWidth K (f i)) σ flip 1)
    (hind : LinearIndependent ℝ
      ![(forms f m (fun i => rangeWidth K (f i)) σ flip 0).linear,
        (forms f m (fun i => rangeWidth K (f i)) σ flip 2).linear])
    (hsum : (∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) : Normal K f lo hi := by
  let W : P := fun i => rangeWidth K (f i)
  let g := forms f m W σ flip
  let L := lower m W lo hi σ flip
  let U := upper m W lo hi σ flip
  have hwg := OrientedRangeCoordinates.positive m W lo hi σ flip hW hw
  have hbg := OrientedRangeCoordinates.box K f m W σ flip hW hb
  have hLg := OrientedRangeCoordinates.zero_contacts K f m W σ flip hW hL hU
  have hUg := OrientedRangeCoordinates.unit_contacts K f m W σ flip hW hL hU
  have hbJ := RepeatedDirectionChart.box K g hbg
  have hLJ := RepeatedDirectionChart.zero_contacts K g hLg
  have hUJ := RepeatedDirectionChart.unit_contacts K g hUg
  refine ⟨m, σ, flip, hb, hL, hU, hwg, heq, ?_⟩
  apply (TwoDirectionUnclipped.tight_iff (RepeatedDirectionChart.chart g '' K)
    (Convex.affine_image _ hK) (RepeatedDirectionChart.interior_nonempty K g hfull hind)
    hbJ (hLJ 0) (hUJ 0) (hLJ 1) (hUJ 1) L U hwg).mp
  apply (RepeatedDirectionChart.tight_iff K g heq L U).mpr
  exact ⟨(OrientedRangeCoordinates.sum_width_eq m W lo hi σ flip).trans hsum,
    (OrientedRangeCoordinates.cover_iff K f m W lo hi σ flip hW).mpr hcover⟩

end Plank.Convex.PlanarTight.AffineRepeatedFamilies

/-- info: 'Plank.Convex.PlanarTight.AffineRepeatedFamilies.Normal.tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AffineRepeatedFamilies.Normal.tight

/-- info: 'Plank.Convex.PlanarTight.AffineRepeatedFamilies.of_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AffineRepeatedFamilies.of_tight
