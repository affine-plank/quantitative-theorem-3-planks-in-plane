/- Cyclic mixed caps give an enclosing triangle with unchanged ranges
at positive planar equality. -/
module
public import Plank.Convex.PlanarTight.TriangleEnclosure
public import Plank.Convex.PlanarTight.CommonPoint
public import Plank.Convex.CyclicCapTriangle
public import Plank.Convex.PlanarCapCaseReduction
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.CyclicTriangle
open CyclicCapTriangle

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Three cyclic mixed supports bound an actual nondegenerate triangle
containing the whole body and covered by the original windows. -/
theorem enclosing_triangle (hdim : Module.finrank ℝ E = 2) (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a : Fin 3 → ℝ) (d : ℝ)
    (ha : ∀ i, 0 < a i) (hplane : ∀ x, ∑ i, a i * f i x = d)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hboxlo : ∑ i, a i * lo i ≤ d) (hboxhi : d ≤ ∑ i, a i * hi i)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (hcaps : ∀ i, ¬ ∃ x ∈ K, hi i < f i x ∧ f (next i) x < lo (next i)) :
    ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧ K ⊆ convexHull ℝ (Set.range v) ∧
      ∀ x ∈ convexHull ℝ (Set.range v), ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i := by
  classical
  choose L hLK hL0 using hL
  choose U hUK hU1 using hU
  have hsep (i : Fin 3) : ∃ α : ℝ, 0 < α ∧
      ∀ x ∈ K, α * f i x + (lo (next i) - α * hi i) ≤ f (next i) x :=
    ConvexCellSeparation.exists_slope K hK (f i) (f (next i)) (hi i) (lo (next i))
      (hhi i) (hlo (next i)) (U i) (L (next i)) (hUK i) (hLK (next i))
      (hU1 i) (hL0 (next i)) (hcaps i)
  choose α hα hs using hsep
  let b (i : Fin 3) := lo (next i) - α i * hi i
  let P : Set E := {x | ∀ i, 0 ≤ slack f α b i x}
  have hKP : K ⊆ P := by
    intro x hx i
    have hb := hs i x hx
    change 0 ≤ f (next i) x - α i * f i x - (lo (next i) - α i * hi i)
    linarith only [hb]
  have hLU : L 0 ≠ U 0 := by
    intro h
    have hh := congrArg (f 0) h
    rw [hL0 0, hU1 0] at hh
    norm_num at hh
  obtain ⟨v, hv, hP⟩ := exists_triangle hdim f a α b d ha hα hplane hinj
    (L 0) (U 0) hLU (hKP (hLK 0)) (hKP (hUK 0))
  have hP' : P = convexHull ℝ (Set.range v) := hP
  have hcyc (i : Fin 3) : ¬ ∃ x ∈ P, hi i < f i x ∧ f (next i) x < lo (next i) := by
    rintro ⟨x, hx, hu, hl⟩
    have hb := hx i
    change 0 ≤ f (next i) x - α i * f i x - (lo (next i) - α i * hi i) at hb
    have ht := mul_lt_mul_of_pos_left hu (hα i)
    linarith only [hb, ht, hl]
  have he0 : PlanarCapCaseReduction.EdgeEmpty P f lo hi 0 := by
    simpa [PlanarCapCaseReduction.EdgeEmpty, PlanarCapCaseReduction.EmptyPair,
      PlanarCapCaseReduction.wall, PlanarCapCaseReduction.next, next] using hcyc 0
  have he2 : PlanarCapCaseReduction.EdgeEmpty P f lo hi 2 := by
    simpa [PlanarCapCaseReduction.EdgeEmpty, PlanarCapCaseReduction.EmptyPair,
      PlanarCapCaseReduction.wall, PlanarCapCaseReduction.next, next] using hcyc 2
  have he4 : PlanarCapCaseReduction.EdgeEmpty P f lo hi 4 := by
    simpa [PlanarCapCaseReduction.EdgeEmpty, PlanarCapCaseReduction.EmptyPair,
      PlanarCapCaseReduction.wall, PlanarCapCaseReduction.next, next] using hcyc 1
  have hnodes (i : Fin 6) : PlanarCapCaseReduction.SingleEmpty P f lo hi i ∨
      PlanarCapCaseReduction.EdgeEmpty P f lo hi i ∨
      PlanarCapCaseReduction.EdgeEmpty P f lo hi (PlanarCapPatterns.prev i) := by
    fin_cases i
    · exact Or.inr (Or.inl he0)
    · exact Or.inr (Or.inr he0)
    · exact Or.inr (Or.inl he2)
    · exact Or.inr (Or.inr he2)
    · exact Or.inr (Or.inl he4)
    · exact Or.inr (Or.inr he4)
  have hcover := PlanarCapCaseReduction.covered_of_nodes P f a d ha
    (fun x _ => hplane x) lo hi hboxlo hboxhi hnodes
  refine ⟨v, hv, hP' ▸ hKP, ?_⟩
  simpa only [hP'] using hcover

/-- Under the cyclic cap pattern, a tight body admits a covered enclosing
triangle with all original directional widths unchanged. This reduces the
body shape to a triangle enclosure, rather than a cap-pattern restatement. -/
theorem enclosing_triangle_of_tight (hdim : Module.finrank ℝ E = 2)
    (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a : Fin 3 → ℝ) (d : ℝ)
    (ha : ∀ i, 0 < a i) (hplane : ∀ x, ∑ i, a i * f i x = d)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (lo hi : Fin 3 → ℝ) (hwidth : ∀ i, lo i < hi i)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (hcaps : ∀ i, ¬ ∃ x ∈ K, hi i < f i x ∧ f (next i) x < lo (next i)) :
    ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧ K ⊆ convexHull ℝ (Set.range v) ∧
      (∀ x ∈ convexHull ℝ (Set.range v), ∀ i, 0 ≤ f i x ∧ f i x ≤ 1) ∧
      (∀ x ∈ convexHull ℝ (Set.range v), ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) := by
  let F : E →ᵃ[ℝ] (Fin 3 → ℝ) := AffineMap.pi f
  have hbox' : ∀ x ∈ F '' K, ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
    rintro _ ⟨x, hx, rfl⟩ i
    exact hbox x hx i
  have hL' : ∀ i, ∃ x ∈ F '' K, x i = 0 := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hL i
    exact ⟨F x, ⟨x, hx, rfl⟩, hxi⟩
  have hU' : ∀ i, ∃ x ∈ F '' K, x i = 1 := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hU i
    exact ⟨F x, ⟨x, hx, rfl⟩, hxi⟩
  have hb := CommonPoint.plane_box_bounds (F '' K) (Convex.affine_image F hK)
    hbox' hL' hU' lo hi a d ha (by rintro _ ⟨x, hx, rfl⟩; exact hplane x)
    hwidth hlo hhi (by rintro _ ⟨x, hx, rfl⟩; exact hcover x hx) hsum
  obtain ⟨v, hv, hKv, hcv⟩ := enclosing_triangle hdim K hK f a d ha hplane hinj
    lo hi hlo hhi hb.1 hb.2 hL hU hcaps
  refine ⟨v, hv, hKv, TriangleEnclosure.ranges_of_tight v f lo hi hwidth ?_ ?_ hcv hsum, hcv⟩
  · intro i
    obtain ⟨x, hx, hxi⟩ := hL i
    exact ⟨x, hKv hx, hxi⟩
  · intro i
    obtain ⟨x, hx, hxi⟩ := hU i
    exact ⟨x, hKv hx, hxi⟩

end Plank.Convex.PlanarTight.CyclicTriangle

/-- info: 'Plank.Convex.PlanarTight.CyclicTriangle.enclosing_triangle_of_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CyclicTriangle.enclosing_triangle_of_tight
