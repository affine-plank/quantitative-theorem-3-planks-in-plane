/- A planar class-A cover has relative width at least one.
A compact hull of the six coordinate witnesses permits an extreme minimum;
six contacts directly supply positive weights for the cycle-gap inequality. -/
module
public import Plank.Convex.SameSignCapMinimumStrict
public import Plank.Convex.PlanarSixContactWidth
public import Plank.Convex.NormalizedCompactHull
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Plank.Convex
open SameSignCapAlgebra
namespace Plank.Convex.SameSignCapPlanarWidth

theorem next_eq (i : Fin 3) : SameSignCapMinimum.next i = next i := by
  fin_cases i <;> rfl

/-- Every strict feasible box admits six positive supporting rows. -/
theorem positive_supports (K : Set Point) (hK : Convex ℝ K)
    (B : SameSignCapMinimum.Walls) (hB : B ∈ SameSignCapMinimum.wallSet K)
    (hstrict : B ∈ SameSignCapMinimum.strictWalls)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1) :
    ∃ a b : Point, (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
      UpperSupports K B.2 a ∧ LowerSupports K B.1 b := by
  have hw := SameSignCapMinimum.cut_witness K B hstrict hL hU
  have hs (j : Bool × Fin 3) := CompactPairSeparation.positive_support K hK
    (SameSignCapMinimum.cut j) (SameSignCapMinimum.cut (SameSignCapMinimum.succ j))
    (SameSignCapMinimum.wall B j) (SameSignCapMinimum.wall B (SameSignCapMinimum.succ j))
    (hw j) (hw (SameSignCapMinimum.succ j)) (SameSignCapMinimum.cap_empty K B hB j)
  choose r hr hs using hs
  refine ⟨(fun i => r (true, i)), (fun i => r (false, i)),
    (fun i => hr (true, i)), (fun i => hr (false, i)), ?_, ?_⟩
  · intro i x hx
    have h := hs (true, i) x hx
    change x i + r (true, i) * x (SameSignCapMinimum.next i) ≤
      B.2 i + r (true, i) * B.2 (SameSignCapMinimum.next i) at h
    simpa only [next_eq] using h
  · intro i x hx
    have h := hs (false, i) x hx
    change -x i + r (false, i) * -x (SameSignCapMinimum.next i) ≤
      -B.1 i + r (false, i) * -B.1 (SameSignCapMinimum.next i) at h
    rw [next_eq] at h
    nlinarith only [h]

/-- Minimize over the closed family allowing all six same-sign caps to be empty. -/
theorem compact_width_bound (K : Set Point) (hcK : IsCompact K) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (c : Point) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, (∑ i, c i * x i) = D)
    (B : SameSignCapMinimum.Walls) (hB : B ∈ SameSignCapMinimum.wallSet K) :
    1 ≤ SameSignCapMinimum.width B := by
  by_contra! hdef
  obtain ⟨C, hC, _, hCB⟩ := SameSignCapMinimum.exists_extreme_minimizer K B hB
  have hdefC := hCB.trans_lt hdef
  have hstrict := SameSignCapMinimumStrict.strictWalls_of_deficit K hK hbox hL hU C hC.1 hdefC
  have hends (i : Fin 3) : (0 < C.1 i ∧ C.1 i < C.2 i) ∧ C.2 i < 1 :=
    Set.mem_iInter.mp hstrict i
  have hpairs := SameSignCapMinimum.upper_lower_contacts_of_extreme K hcK hK C hC hstrict hL hU
  have hpairL : ∀ i, ∃ x ∈ K, x i = C.1 i ∧ x (next i) = C.1 (next i) := by
    intro i
    simpa only [next_eq] using (hpairs i).1
  have hpairU : ∀ i, ∃ x ∈ K, x i = C.2 i ∧ x (next i) = C.2 (next i) := by
    intro i
    simpa only [next_eq] using (hpairs i).2
  obtain ⟨a, b, ha, hb, has, hbs⟩ := positive_supports K hK C hC.1 hstrict hL hU
  have hnext (i : Fin 3) : i + 1 = next i := by fin_cases i <;> rfl
  have hw := PlanarSixContactWidth.width_bound K C.1 C.2 a b c D
    (fun i => (ha i).le) (fun i => (hb i).le) hc (fun i => (hends i).1.2) hplane hL hU
    (by simpa only [hnext] using hpairL) (by simpa only [hnext] using hpairU)
    (by simpa only [UpperSupports, hnext] using has) (by simpa only [LowerSupports, hnext] using hbs)
  rw [SameSignCapMinimum.width_apply] at hdefC
  exact (not_le_of_gt hdefC) hw


/-- Six attained coordinate witnesses reduce an arbitrary convex set to a compact hull. -/
theorem width_bound (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (c : Point) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, (∑ i, c i * x i) = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hsingle : ∀ e, PlanarCapCaseReduction.SingleEmpty K (fun i => AffineMap.proj i) lo hi e) :
    1 ≤ ∑ i, (hi i - lo i) := by
  by_contra! hdef
  have hends := CommonPointUnclipped.windows_strict_of_deficit K hK hbox hL hU lo hi
    horder hcover hdef
  have hcaps := empty_pair_caps_of_single_empty K lo hi hsingle
  obtain ⟨T, hTK, hcT, hvT, hLT, hUT⟩ := NormalizedCompactHull.exists_subset K hK hL hU
  have hB : (lo, hi) ∈ SameSignCapMinimum.wallSet T := by
    refine ⟨⟨⟨(fun i => (hends i).1.le),
      (fun i => (hends i).1.le.trans (horder i))⟩,
      ⟨(fun i => (horder i).trans (hends i).2.le), (fun i => (hends i).2.le)⟩⟩,
      Set.mem_iInter.mpr horder, ?_⟩
    apply Set.mem_iInter.mpr
    intro x
    apply Set.mem_iInter.mpr
    intro hx
    apply Set.mem_iInter.mpr
    intro i
    constructor
    · change x i ≤ hi i ∨ x (SameSignCapMinimum.next i) ≤ hi (SameSignCapMinimum.next i)
      rw [next_eq]
      by_contra! hh
      exact hcaps.2 i ⟨x, hTK hx, hh.1, hh.2⟩
    · change lo i ≤ x i ∨ lo (SameSignCapMinimum.next i) ≤ x (SameSignCapMinimum.next i)
      rw [next_eq]
      by_contra! hh
      exact hcaps.1 i ⟨x, hTK hx, hh.1, hh.2⟩
  have hw := compact_width_bound T hcT hvT
    (fun x hx => hbox x (hTK hx)) hLT hUT c D hc (fun x hx => hplane x (hTK hx))
    (lo, hi) hB
  rw [SameSignCapMinimum.width_apply] at hw
  exact (not_le_of_gt hdef) hw

theorem width_bound_of_pattern (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (c : Point) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, (∑ i, c i * x i) = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hh : PlanarCapPatterns.Holds
      (PlanarCapCaseReduction.SingleEmpty K (fun i => AffineMap.proj i) lo hi)
      (PlanarCapCaseReduction.EdgeEmpty K (fun i => AffineMap.proj i) lo hi) ⟨63, 0⟩) :
    1 ≤ ∑ i, (hi i - lo i) := by
  apply width_bound K hK hbox hL hU c D hc hplane lo hi horder hcover
  intro e
  apply hh.1 e
  fin_cases e <;> decide

end Plank.Convex.SameSignCapPlanarWidth
