/- The explicit zero-width, boundary, and strict triangle families on a positive plane. -/
module
public import Plank.Convex.PlanarTight.StrictCapDispatcher
public import Plank.Convex.PlanarTight.BoundaryFamilySufficiency
public import Plank.Convex.PlanarTight.ZeroWidthClassification
public import Plank.Convex.PlanarTight.NoWaste
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.NormalizedFamilies
open StrictCapSetting StrictTriangleTransport

/-- Each branch specifies the actual body geometry and window parameters.
Zero-width windows may lie outside the directional range. -/
def Normal (K : Set Point) (lo hi : Point) : Prop :=
  ZeroWidthClassification.Normal K lo hi ∨
    BoundaryClassification.Normal K lo hi ∨
    StrictTriangleClassification.Normal K (fun i => AffineMap.proj i) lo hi

/-- Every displayed family gives a tight cover. This implication does not
need a plane relation, compactness, or positive window widths. -/
theorem Normal.tight (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i) (h : Normal K lo hi) :
    (∑ i, (hi i - lo i)) = 1 ∧ ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i := by
  rcases h with h | h | h
  · obtain ⟨σ, hz, hn⟩ := h
    exact (ZeroWidthClassification.tight_iff K hK hbox hL hU lo hi horder
      ⟨σ 0, hz⟩).mpr ⟨σ, hz, hn⟩
  · exact BoundaryClassification.Normal.tight K hbox hL hU lo hi h
  · exact StrictTriangleClassification.Normal.tight K (fun i => AffineMap.proj i) lo hi h

/-- The complete positive-plane classification reduces to the two final
strict representative lemmas. The right-hand side is the explicit family list. -/
theorem tight_iff_of_representatives (hrepA : Triangular ⟨63, 0⟩) (hrepC : Excluded ⟨56, 3⟩)
    (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) ↔
      Normal K lo hi := by
  constructor
  · rintro ⟨hsum, hcover⟩
    by_cases hz : ∃ i, lo i = hi i
    · exact Or.inl ((ZeroWidthClassification.tight_iff K hK hbox hL hU lo hi horder hz).mp
        ⟨hsum, hcover⟩)
    have hwidth (i : Fin 3) : lo i < hi i :=
      lt_of_le_of_ne (horder i) (fun he => hz ⟨i, he⟩)
    have hclip (i : Fin 3) : 0 ≤ lo i ∧ hi i ≤ 1 :=
      positive_window_no_waste K hK hbox hL hU A D hA hplane lo hi horder
        hcover hsum.le i (hwidth i)
    by_cases hboundary : ∃ i, lo i = 0 ∨ hi i = 1
    · exact Or.inr (Or.inl ((BoundaryClassification.tight_iff K hK hbox hL hU A D hA
        hplane lo hi (fun i => (hclip i).1) (fun i => (hclip i).2) hwidth hboundary).mp
        ⟨hsum, hcover⟩))
    have hlo (i : Fin 3) : 0 < lo i := lt_of_le_of_ne (hclip i).1
      (fun he => hboundary ⟨i, Or.inl he.symm⟩)
    have hhi (i : Fin 3) : hi i < 1 := lt_of_le_of_ne (hclip i).2
      (fun he => hboundary ⟨i, Or.inr he⟩)
    exact Or.inr (Or.inr (StrictCapDispatcher.normal hrepA hrepC
      { K := K, convex := hK, box := hbox, min := hL, max := hU, A := A, D := D,
        positive := hA, plane := hplane, lo := lo, hi := hi, lo_pos := hlo, hi_lt := hhi,
        width_pos := hwidth, covered := hcover, total := hsum }))
  · exact Normal.tight K hK hbox hL hU lo hi horder

end Plank.Convex.PlanarTight.NormalizedFamilies

/-- info: 'Plank.Convex.PlanarTight.NormalizedFamilies.Normal.tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.NormalizedFamilies.Normal.tight

/-- info: 'Plank.Convex.PlanarTight.NormalizedFamilies.tight_iff_of_representatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.NormalizedFamilies.tight_iff_of_representatives
