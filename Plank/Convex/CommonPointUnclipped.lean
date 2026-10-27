/- A deficient whole-set cover by arbitrary ordered coordinate windows
already has all its original endpoints strictly inside the cube. Clipping
cannot create the common point: positive deficit margins force every
clipped endpoint to equal its original value. -/
module
public import Plank.Convex.CommonPointOfDeficit
public import Plank.Convex.AffineSlabNormalization
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.CommonPointUnclipped
open scoped BigOperators
open AffineSlabNormalization

abbrev Point := Fin 3 → ℝ

private theorem clamp_eq_of_interior (t : ℝ) (hpos : 0 < clamp t)
    (hlt : clamp t < 1) : clamp t = t := by
  have ht0 : 0 < t := by
    have hm : 0 < min 1 t := (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
    exact hm.trans_le (min_le_right 1 t)
  have ht1 : t < 1 := by
    by_contra ht
    have hc : clamp t = 1 := by
      rw [clamp, min_eq_left (le_of_not_gt ht), max_eq_right zero_le_one]
    exact (lt_irrefl 1) (hc ▸ hlt)
  exact clamp_self t ⟨ht0.le, ht1.le⟩

/-- A positive width deficit forces the ORIGINAL ordered windows inside
uniform cube margins. No clipping hypothesis is required. -/
theorem window_margins_of_deficit (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (γ : ℝ) (hγ : 0 < γ) (hdef : (∑ j, (hi j - lo j)) ≤ 1 - γ) :
    ∀ j, γ ≤ lo j ∧ hi j ≤ 1 - γ := by
  have horder' (j : Fin 3) : clamp (lo j) ≤ clamp (hi j) := clamp_mono (hordered j)
  have hcover' : ∀ p ∈ K, ∃ j, clamp (lo j) ≤ p j ∧ p j ≤ clamp (hi j) := by
    intro p hp
    obtain ⟨j, hj⟩ := hcover p hp
    exact ⟨j, clamp_interval (lo j) (hi j) (p j) (hbox p hp j) hj⟩
  have hcost : (∑ j, (clamp (hi j) - clamp (lo j))) ≤ ∑ j, (hi j - lo j) :=
    Finset.sum_le_sum (fun j _ => clamp_sub_le (lo j) (hi j) (hordered j))
  have hm := NearCubeVertexCover.window_margins_of_deficit K hconv hbox hmin hmax
    (fun j => clamp (lo j)) (fun j => clamp (hi j)) horder'
    (fun j => clamp_nonneg (lo j)) (fun j => clamp_le_one (hi j))
    hcover' γ (hcost.trans hdef)
  intro j
  have hloPos : 0 < clamp (lo j) := hγ.trans_le (hm j).1
  have hhiLt : clamp (hi j) < 1 := (hm j).2.trans_lt (by linarith only [hγ])
  have hloEq := clamp_eq_of_interior (lo j) hloPos ((horder' j).trans_lt hhiLt)
  have hhiEq := clamp_eq_of_interior (hi j) (hloPos.trans_le (horder' j)) hhiLt
  simpa only [hloEq, hhiEq] using hm j

/-- Every original endpoint lies strictly between zero and one in a
deficient cover. An individual window may still have zero width. -/
theorem windows_strict_of_deficit (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hdef : (∑ j, (hi j - lo j)) < 1) :
    ∀ j, 0 < lo j ∧ hi j < 1 := by
  let γ := 1 - ∑ j, (hi j - lo j)
  have hγ : 0 < γ := sub_pos.mpr hdef
  have hm := window_margins_of_deficit K hconv hbox hmin hmax lo hi hordered
    hcover γ hγ (by dsimp [γ]; linarith)
  intro j
  exact ⟨hγ.trans_le (hm j).1, (hm j).2.trans_lt (by linarith only [hγ])⟩

/-- Arbitrary ordered real windows covering the whole convex body with
total width below one have a common point in `K` inside all ORIGINAL windows.
The actual coordinate ranges are `[0,1]`; compactness is unnecessary. -/
theorem exists_common (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hdef : (∑ j, (hi j - lo j)) < 1) :
    ∃ p ∈ K, ∀ j, lo j ≤ p j ∧ p j ≤ hi j := by
  have hm := windows_strict_of_deficit K hconv hbox hmin hmax lo hi hordered hcover hdef
  exact CommonPointOfDeficit.exists_common K hconv hbox hmin hmax lo hi hordered
    (fun j => (hm j).1.le) (fun j => (hm j).2.le) hcover hdef

/-- A quantitative deficit gives a common point inside all original
windows and with every coordinate in `[γ,1-γ]`. This does not assert
interiority relative to `K` or relative to a window. -/
theorem exists_common_with_margin (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (γ : ℝ) (hγ : 0 < γ) (hdef : (∑ j, (hi j - lo j)) ≤ 1 - γ) :
    ∃ p ∈ K, (∀ j, lo j ≤ p j ∧ p j ≤ hi j) ∧
      ∀ j, γ ≤ p j ∧ p j ≤ 1 - γ := by
  have hm := window_margins_of_deficit K hconv hbox hmin hmax lo hi hordered hcover γ hγ hdef
  obtain ⟨p, hp, hpall⟩ := exists_common K hconv hbox hmin hmax lo hi hordered hcover
    (by linarith only [hdef, hγ])
  exact ⟨p, hp, hpall, fun j =>
    ⟨(hm j).1.trans (hpall j).1, (hpall j).2.trans (hm j).2⟩⟩

end Plank.Convex.CommonPointUnclipped

/-- info: 'Plank.Convex.CommonPointUnclipped.window_margins_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CommonPointUnclipped.window_margins_of_deficit

/-- info: 'Plank.Convex.CommonPointUnclipped.windows_strict_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CommonPointUnclipped.windows_strict_of_deficit

/-- info: 'Plank.Convex.CommonPointUnclipped.exists_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CommonPointUnclipped.exists_common

/-- info: 'Plank.Convex.CommonPointUnclipped.exists_common_with_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CommonPointUnclipped.exists_common_with_margin
