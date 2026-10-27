/- Every positive strict equality cover of a triangle belongs to one
explicit two-parameter family, in the original affine coordinates. -/
module
public import Plank.Convex.PlanarTight.StrictTriangleNormalization
public import Plank.Convex.PlanarTight.TriangleStrictCover
public import Plank.Convex.TriangleWindowCover
public import Plank.Proofs.AffineTriangleNormalization
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.StrictTriangleClassification

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Three positive widths of sum one prescribe the windows and the three
vertex values in every direction. Indices are cyclic. -/
def Frame (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi w : Fin 3 → ℝ) : Prop :=
  ∀ i, f i (v i) = w (i + 1) / (1 - w i) ∧
    f i (v (i + 1)) = 0 ∧ f i (v (i + 2)) = 1 ∧
    lo i = w (i + 1) ∧ hi i = 1 - w (i + 2)

/-- The complete strict triangle family: an actual triangle, a permutation
of its three windows, independent reflections, and two free width parameters. -/
def Normal (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ) : Prop :=
  ∃ (v : Fin 3 → E) (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (w : Fin 3 → ℝ),
    AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v) ∧
    (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
    Frame v (OrientedCommonChord.coordinates flip (fun i => f (π i)))
      (OrientedCommonChord.lower flip (fun i => lo (π i)) (fun i => hi (π i)))
      (OrientedCommonChord.upper flip (fun i => lo (π i)) (fun i => hi (π i))) w

private theorem affine_combination (v : Fin 3 → E) (f : E →ᵃ[ℝ] ℝ)
    (l : Fin 3 → ℝ) (hsum : ∑ i, l i = 1) :
    f (Finset.univ.affineCombination ℝ v l) = ∑ j, l j * f (v j) := by
  have h := (Finset.univ : Finset (Fin 3)).map_affineCombination v l hsum f
  rw [Finset.affineCombination_eq_linear_combination Finset.univ (f ∘ v) l hsum] at h
  simpa only [Function.comp_apply, smul_eq_mul] using h

private theorem hull_weights (v : Fin 3 → E) (x : E)
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ l : Fin 3 → ℝ, (∀ j, 0 ≤ l j) ∧ (∑ j, l j) = 1 ∧
      Finset.univ.affineCombination ℝ v l = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, a, ha, hs, rfl⟩ := hx
  let l (i : Fin 3) := if i ∈ s then a i else 0
  have hl (i : Fin 3) : 0 ≤ l i := by
    dsimp [l]
    split_ifs with hi
    · exact ha i hi
    · exact le_rfl
  have hsum : ∑ i, l i = 1 := by simpa [l] using hs
  refine ⟨l, hl, hsum, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination Finset.univ v l hsum,
    Finset.affineCombination_eq_linear_combination s v a hs]
  simp [l, ite_smul]

theorem Frame.cover (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hframe : Frame v f lo hi w) :
    ∀ x ∈ convexHull ℝ (Set.range v), ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i := by
  intro x hx
  obtain ⟨l, hl, hs, rfl⟩ := hull_weights v x hx
  obtain ⟨i, hL, hH⟩ := TriangleWindowCover.width_parameters_cover w l hw hsum hl hs
  have he : f i (Finset.univ.affineCombination ℝ v l) =
      w (i + 1) / (1 - w i) * l i + l (i + 2) := by
    rw [affine_combination v (f i) l hs, SixBoundaries.sum_cyclic _ i]
    rw [(hframe i).1, (hframe i).2.1, (hframe i).2.2.1]
    ring
  refine ⟨i, ?_⟩
  rw [(hframe i).2.2.2.1, (hframe i).2.2.2.2, he]
  exact ⟨hL, hH⟩

theorem Normal.tight (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (hn : Normal K f lo hi) :
    (∑ i, (hi i - lo i)) = 1 ∧ ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i := by
  obtain ⟨v, π, flip, w, _, hbody, hw, hsum, hframe⟩ := hn
  have hwval (i : Fin 3) : hi (π i) - lo (π i) = w i := by
    rw [← OrientedCommonChord.width_eq flip (fun j => lo (π j)) (fun j => hi (π j)) i]
    rw [(hframe i).2.2.2.1, (hframe i).2.2.2.2]
    have ht := (SixBoundaries.sum_cyclic w i).symm.trans hsum
    linarith only [ht]
  refine ⟨?_, ?_⟩
  · rw [← Equiv.sum_comp π (fun i => hi i - lo i)]
    simpa only [hwval] using hsum
  · intro x hx
    obtain ⟨i, hi'⟩ := Frame.cover v _ _ _ w hw hsum hframe x (hbody ▸ hx)
    exact ⟨π i, (OrientedCommonChord.window_iff flip (fun j => f (π j))
      (fun j => lo (π j)) (fun j => hi (π j)) x i).mp hi'⟩

/-- Necessity retains the supplied triangle and the original affine functions;
only the three plank labels and their orientations are normalized. -/
theorem of_tight (K : Set E) (v : Fin 3 → E) (hind : AffineIndependent ℝ v)
    (hbody : K = convexHull ℝ (Set.range v)) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hwidth : ∀ i, lo i < hi i) (hsum : ∑ i, (hi i - lo i) = 1)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    Normal K f lo hi := by
  classical
  have hK : Convex ℝ K := hbody ▸ convex_convexHull ℝ _
  have hv (j : Fin 3) : v j ∈ K := by
    rw [hbody]
    exact subset_convexHull ℝ _ ⟨j, rfl⟩
  let σ (i : Fin 3) := Tuple.sort (fun j => f i (v j))
  have hmono (i : Fin 3) : Monotone ((fun j => f i (v j)) ∘ σ i) :=
    Tuple.monotone_sort (fun j => f i (v j))
  have hzero (i : Fin 3) : f i (v (σ i 0)) = 0 := by
    obtain ⟨⟨p, hp⟩, _⟩ := TriangleStrictCover.extrema_on_vertices K hK v hbody (f i)
      (fun x hx => hbox x hx i) (hL i) (hU i)
    have hm : f i (v (σ i 0)) ≤ f i (v p) := by
      simpa using hmono i (Fin.zero_le ((σ i).symm p))
    exact le_antisymm (by rwa [hp] at hm) (hbox _ (hv _) i).1
  have hone (i : Fin 3) : f i (v (σ i 2)) = 1 := by
    obtain ⟨_, p, hp⟩ := TriangleStrictCover.extrema_on_vertices K hK v hbody (f i)
      (fun x hx => hbox x hx i) (hL i) (hU i)
    have hm : f i (v p) ≤ f i (v (σ i 2)) := by
      simpa using hmono i (Fin.le_last ((σ i).symm p))
    exact le_antisymm (hbox _ (hv _) i).2 (by rwa [hp] at hm)
  let C : Plank.TriangleNormalization.Cover 3 := {
    g := fun i j => f i (v j)
    σ := σ
    lo := lo
    hi := hi
    bounds := fun i j => hbox (v j) (hv j) i
    zero := hzero
    one := hone
    ordered := fun i => (hwidth i).le
    covered := by
      intro l hl hs
      have hx : Finset.univ.affineCombination ℝ v l ∈ K := by
        rw [hbody]
        exact affineCombination_mem_convexHull (fun j _ => hl j) hs
      obtain ⟨i, hi'⟩ := hcover _ hx
      exact ⟨i, by simpa only [affine_combination v (f i) l hs] using hi'⟩ }
  obtain ⟨π, flip, w, hw, hwsum, hp⟩ := StrictTriangleNormalization.parameters C hlo hhi hwidth hsum
  refine ⟨v, π, flip, w, hind, hbody, hw, hwsum, ?_⟩
  have hval (i j : Fin 3) : OrientedCommonChord.coordinates flip (fun k => f (π k)) i (v j) =
      StrictTriangleNormalization.value flip (fun k => C.g (π k)) i j := by
    cases he : flip i <;> simp [OrientedCommonChord.coordinates,
      StrictTriangleNormalization.value, he, C]
  intro i
  simpa only [hval] using hp i

/-- Exhaustive iff for positive strict windows on a normalized triangle. -/
theorem tight_iff (K : Set E) (v : Fin 3 → E) (hind : AffineIndependent ℝ v)
    (hbody : K = convexHull ℝ (Set.range v)) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (lo hi : Fin 3 → ℝ) (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hwidth : ∀ i, lo i < hi i) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) ↔
      Normal K f lo hi :=
  ⟨fun h => of_tight K v hind hbody f hbox hL hU lo hi hlo hhi hwidth h.1 h.2,
    Normal.tight K f lo hi⟩

end Plank.Convex.PlanarTight.StrictTriangleClassification

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleClassification.Frame.cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleClassification.Frame.cover

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleClassification.Normal.tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleClassification.Normal.tight

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleClassification.of_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleClassification.of_tight

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleClassification.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleClassification.tight_iff
