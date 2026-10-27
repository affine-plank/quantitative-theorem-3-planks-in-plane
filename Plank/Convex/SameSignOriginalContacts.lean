/- All six contacts at the original strict same-sign equality cover. -/
module
public import Plank.Convex.SameSignFlatAnchorSymmetry
public import Plank.Convex.SameSignCapPlanarWidth
public import Plank.Convex.PlanarTight.BoundaryStrictObstruction
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace Plank.Convex.SameSignOriginalContacts
open SameSignCapMinimum

theorem cover_of_wallSet (K : Set Point) (B : Walls) (hB : B ∈ wallSet K) :
    ∀ x ∈ K, ∃ i, B.1 i ≤ x i ∧ x i ≤ B.2 i := by
  intro x hx
  apply SameSignCapMinimumStrict.cover_of_pair_caps
  intro i
  have h := mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hB.2.2 x) hx) i
  change (x i ≤ B.2 i ∨ x (next i) ≤ B.2 (next i)) ∧
    (B.1 i ≤ x i ∨ B.1 (next i) ≤ x (next i)) at h
  simpa only [SameSignCapPlanarWidth.next_eq] using h

/-- A zero coefficient is impossible before any use of compactness or minimality. -/
theorem numerator_ne_zero (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls) (hsum : width B = 1)
    (r : Bool × Fin 3 → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B)
    (j : Bool × Fin 3) : SameSignLocalMinimum.numerator r j ≠ 0 := by
  intro hn
  obtain ⟨C, hC, hsumC, hwC, hanchor⟩ := SameSignFlatAnchorSymmetry.zero_anchor
    K hK hbox hL hU A D hA hplane B hB hstrict hsum r hr hs j hn
  have he (i : Fin 3) : (0 < B.1 i ∧ B.1 i < B.2 i) ∧ B.2 i < 1 :=
    mem_iInter.mp hstrict i
  exact PlanarTight.BoundaryStrictObstruction.boundary_not_strict
    K hK hbox hL hU A D hA hplane C.1 C.2 hwC (cover_of_wallSet K C hC)
    (by simpa only [width_apply] using hsumC) hanchor B.1 B.2
    (fun i => (he i).1.1) (fun i => (he i).2) (cover_of_wallSet K B hB)

/-- At an original minimum every supporting row has positive objective coefficient. -/
theorem numerator_pos_of_minimum (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls)
    (hmin : IsMinOn width (wallSet K) B) (hsum : width B = 1)
    (r : Bool × Fin 3 → ℝ) (hr : ∀ j, 0 < r j)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B)
    (j : Bool × Fin 3) : 0 < SameSignLocalMinimum.numerator r j := by
  exact lt_of_le_of_ne (SameSignLocalMinimum.numerator_nonneg_of_minimum K B hmin hstrict r hr hs j)
    (Ne.symm (numerator_ne_zero K hK hbox hL hU A D hA hplane B hB hstrict hsum r hr hs j))

/-- Compact equality covers have all six contacts at their supplied endpoints. -/
theorem compact_contacts (K : Set Point) (hcK : IsCompact K) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls) (hsum : width B = 1) :
    ∀ j, ∃ x ∈ K, cut j x = wall B j ∧ cut (succ j) x = wall B (succ j) := by
  have hmin : IsMinOn width (wallSet K) B := by
    intro C hC
    rw [hsum]
    exact SameSignCapPlanarWidth.compact_width_bound K hcK hK hbox hL hU A D hA hplane C hC
  have hw := cut_witness K B hstrict hL hU
  have hsep (j : Bool × Fin 3) := CompactPairSeparation.positive_support K hK
    (cut j) (cut (succ j)) (wall B j) (wall B (succ j))
    (hw j) (hw (succ j)) (cap_empty K B hB j)
  choose r hr hs using hsep
  have hrows : ∀ x ∈ K, ∀ j,
      SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B := by
    intro x hx j
    simpa only [SameSignLocalMinimum.rows_apply, wall_diagonal] using hs j x hx
  intro j
  exact SameSignLocalMinimum.contact_of_numerator_pos K hcK hK B hmin hstrict hL hU r hr hrows j
    (numerator_pos_of_minimum K hK hbox hL hU A D hA hplane B hB hstrict hmin hsum r hr hrows j)

/-- Restriction to a smaller body preserves all six forbidden pair caps. -/
theorem wallSet_subset (K T : Set Point) (hTK : T ⊆ K) (B : Walls) (hB : B ∈ wallSet K) :
    B ∈ wallSet T := by
  refine ⟨hB.1, hB.2.1, mem_iInter.mpr fun x => mem_iInter.mpr fun hx => ?_⟩
  exact mem_iInter.mp (mem_iInter.mp hB.2.2 x) (hTK hx)

/-- Six coordinate witnesses suffice: no compactness hypothesis and no change of endpoints. -/
theorem contacts (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls) (hsum : width B = 1) :
    ∀ j, ∃ x ∈ K, cut j x = wall B j ∧ cut (succ j) x = wall B (succ j) := by
  obtain ⟨T, hTK, hcT, hvT, hLT, hUT⟩ := NormalizedCompactHull.exists_subset K hK hL hU
  have ht := compact_contacts T hcT hvT (fun x hx => hbox x (hTK hx)) hLT hUT
    A D hA (fun x hx => hplane x (hTK hx)) B (wallSet_subset K T hTK B hB) hstrict hsum
  intro j
  obtain ⟨x, hx, h₁, h₂⟩ := ht j
  exact ⟨x, hTK hx, h₁, h₂⟩

/-- Endpoint form of the six original contacts, ready for the planar equality geometry. -/
theorem upper_lower_contacts (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (B : Walls) (hB : B ∈ wallSet K) (hstrict : B ∈ strictWalls) (hsum : width B = 1) :
    ∀ i, (∃ x ∈ K, x i = B.1 i ∧ x (next i) = B.1 (next i)) ∧
      (∃ x ∈ K, x i = B.2 i ∧ x (next i) = B.2 (next i)) := by
  have hp := contacts K hK hbox hL hU A D hA hplane B hB hstrict hsum
  intro i
  constructor
  · obtain ⟨x, hx, h₁, h₂⟩ := hp (false, i)
    exact ⟨x, hx, neg_inj.mp h₁, neg_inj.mp h₂⟩
  · exact hp (true, i)

end Plank.Convex.SameSignOriginalContacts

/-- info: 'Plank.Convex.SameSignOriginalContacts.numerator_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignOriginalContacts.numerator_ne_zero

/-- info: 'Plank.Convex.SameSignOriginalContacts.upper_lower_contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignOriginalContacts.upper_lower_contacts
