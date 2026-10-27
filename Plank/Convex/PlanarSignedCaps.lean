/- Signed pairs directly connect the cube to the geometric cuts. -/
module
public import Plank.Convex.SignedCube
public import Plank.Convex.PlanarWindows
public import Plank.Convex.PlanarCellHelly
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.PlanarSignedCaps
open Plank.Convex PlanarCoverSpace SignedCubeCover

def firstCut (e : Edge) : Point 3 →L[ℝ] ℝ := cut e.2.1 (e.1 + 1)
def secondCut (e : Edge) : Point 3 →L[ℝ] ℝ := cut e.2.2 (e.1 + 2)
def firstWall (e : Edge) : Walls 3 →L[ℝ] ℝ := wall e.2.1 (e.1 + 1)
def secondWall (e : Edge) : Walls 3 →L[ℝ] ℝ := wall e.2.2 (e.1 + 2)

def PairEmpty (K : Set (Point 3)) (B : Walls 3) (e : Edge) : Prop :=
  ¬ ∃ x ∈ K, firstWall e B < firstCut e x ∧ secondWall e B < secondCut e x
def PairContact (K : Set (Point 3)) (B : Walls 3) (e : Edge) : Prop :=
  ∃ x ∈ K, firstCut e x = firstWall e B ∧ secondCut e x = secondWall e B

def planeRow (c : Point 3) (b : Bool) : Walls 3 →L[ℝ] ℝ := ∑ i, c i • wall b i
def planeLevel (D : ℝ) (b : Bool) : ℝ := if b then D else -D
def Allowed (K : Set (Point 3)) (c : Point 3) (D : ℝ) (B : Walls 3) : Selection → Prop
  | .inl e => PairEmpty K B e
  | .inr b => planeLevel D b ≤ planeRow c b B

def shiftedCut (B : Walls 3) (v : Vertex) (i : Fin 3) : Point 3 →ᵃ[ℝ] ℝ :=
  (cut (v i) i).toLinearMap.toAffineMap - AffineMap.const ℝ _ (wall (v i) i B)
def corner (B : Walls 3) (v : Vertex) (i : Fin 3) : ℝ := if v i then B.2 i else B.1 i
def coefficient (c : Point 3) (v : Vertex) (i : Fin 3) : ℝ := if v i then c i else -c i

@[simp] theorem planeRow_apply (c : Point 3) (b : Bool) (B : Walls 3) :
    planeRow c b B = ∑ i, c i * wall b i B := by simp [planeRow]

theorem shiftedCut_apply (B : Walls 3) (v : Vertex) (i : Fin 3) (x : Point 3) :
    shiftedCut B v i x = cut (v i) i x - wall (v i) i B := rfl

/-- The omitted coordinate leaves exactly the two cuts of its cube edge. -/
theorem pair_cuts (B : Walls 3) (i : Fin 3) (v : Vertex) (x : Point 3) :
    (firstWall (i, v (i + 1), v (i + 2)) B < firstCut (i, v (i + 1), v (i + 2)) x ∧
      secondWall (i, v (i + 1), v (i + 2)) B < secondCut (i, v (i + 1), v (i + 2)) x) ↔
    ∀ j, j ≠ i → 0 < shiftedCut B v j x := by
  fin_cases i <;>
    simp [firstWall, secondWall, firstCut, secondCut, shiftedCut_apply,
      Fin.forall_fin_succ, sub_pos, and_comm]
  exact and_comm

theorem shifted_relation (B : Walls 3) (c : Point 3) (v : Vertex) (x : Point 3) :
    (∑ i, coefficient c v i * shiftedCut B v i x) =
      (∑ i, c i * x i) - ∑ i, c i * corner B v i := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : v i <;> simp [coefficient, corner, shiftedCut_apply, cut, wall, hi] <;> ring

theorem constant_relation (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D) (b : Bool) (x : Point 3) (hx : x ∈ K) :
    (∑ i, c i * cut b i x) = planeLevel D b := by
  cases b <;> simp [cut, planeLevel, mul_neg, Finset.sum_neg_distrib, hplane x hx]

theorem constant_shifted_relation (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D) (B : Walls 3) (b : Bool)
    (x : Point 3) (hx : x ∈ K) :
    (∑ i, c i * shiftedCut B (constant b) i x) = planeLevel D b - planeRow c b B := by
  simp only [shiftedCut_apply, constant, mul_sub, Finset.sum_sub_distrib, planeRow_apply]
  rw [constant_relation K c D hplane b x hx]

theorem covers_of_allowed (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hc : ∀ i, 0 < c i) (hplane : ∀ x ∈ K, ∑ i, c i * x i = D)
    (B : Walls 3) (s : Finset Selection)
    (ha : ∀ e ∈ s, Allowed K c D B e)
    (hs : ∀ v, ∃ e ∈ s, hits e v) : Covers K B := by
  apply (covers_iff_no_escape K B).mpr
  rintro v ⟨x, hx, ht⟩
  obtain ⟨e, he, hev⟩ := hs v
  cases e with
  | inl e =>
    apply ha _ he
    refine ⟨x, hx, ?_, ?_⟩
    · change wall e.2.1 (e.1 + 1) B < cut e.2.1 (e.1 + 1) x
      rw [← hev.1]
      exact ht _
    · change wall e.2.2 (e.1 + 2) B < cut e.2.2 (e.1 + 2) x
      rw [← hev.2]
      exact ht _
  | inr b =>
    change v = constant b at hev
    subst v
    have hlt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun i _ => mul_lt_mul_of_pos_left (ht i) (hc i))
    change (∑ i, c i * wall b i B) < ∑ i, c i * cut b i x at hlt
    rw [constant_relation K c D hplane b x hx, ← planeRow_apply] at hlt
    exact hlt.not_ge (ha _ he)

theorem allowed_of_redundant (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (B : Walls 3) (v : Vertex) (i : Fin 3)
    (he : ¬ ∃ x ∈ K, ∀ j, j ≠ i → 0 < shiftedCut B v j x) :
    ∃ e, Allowed K c D B e ∧ hits e v := by
  refine ⟨edge i v, ?_, edge_hits i v⟩
  rintro ⟨x, hx, hx1, hx2⟩
  exact he ⟨x, hx, (pair_cuts B i v x).mp ⟨hx1, hx2⟩⟩

theorem mixed_signs (v : Vertex) (h : ¬ ∃ b, v = constant b) :
    (∃ i, v i = true) ∧ ∃ i, v i = false := by
  constructor
  · by_contra! ht
    exact h ⟨false, funext (fun i => by cases hi : v i <;> simp_all [constant])⟩
  · by_contra! ht
    exact h ⟨true, funext (fun i => by cases hi : v i <;> simp_all [constant])⟩

/-- Every sign vertex is excluded by an empty pair cap or its constant
plane bound. The sign vector is already the cube vertex. -/
theorem exists_allowed (K : Set (Point 3)) (hK : Convex ℝ K)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D)
    (B : Walls 3) (hcover : Covers K B) (v : Vertex) :
    ∃ e, Allowed K c D B e ∧ hits e v := by
  have he : ¬ ∃ x ∈ K, ∀ i, 0 < shiftedCut B v i x := by
    rintro ⟨x, hx, hf⟩
    exact (covers_iff_no_escape K B).mp hcover v ⟨x, hx, fun i => sub_pos.mp (hf i)⟩
  by_cases hconst : ∃ b, v = constant b
  · obtain ⟨b, rfl⟩ := hconst
    by_cases hbound : planeLevel D b ≤ planeRow c b B
    · exact ⟨.inr b, hbound, rfl⟩
    obtain ⟨i, hi⟩ := PlanarCellGeometry.exists_redundant_cut_of_relation
      K hK (shiftedCut B (constant b)) c (planeLevel D b - planeRow c b B)
      ⟨0, (hc 0).ne'⟩ (constant_shifted_relation K c D hplane B b)
      (PlanarCellGeometry.positive_point_of_positive _ _ hc
        (sub_pos.mpr (lt_of_not_ge hbound))) he
    exact allowed_of_redundant K c D B (constant b) i hi
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := mixed_signs v hconst
  have hrp : ∃ i, 0 < coefficient c v i := ⟨i, by simpa [coefficient, hi] using hc i⟩
  have hrn : ∃ j, coefficient c v j < 0 := ⟨j, by simpa [coefficient, hj] using neg_neg_of_pos (hc j)⟩
  obtain ⟨k, hk⟩ := PlanarCellGeometry.exists_redundant_cut_of_relation K hK
    (shiftedCut B v) (coefficient c v) (D - ∑ i, c i * corner B v i)
    (hrp.imp fun _ hi => hi.ne') (fun x hx => by rw [shifted_relation, hplane x hx])
    (PlanarCellGeometry.positive_point_of_mixed _ _ hrp hrn) he
  exact allowed_of_redundant K c D B v k hk

/-- Only the two edges through the odd coordinate are needed for the plane bound. -/
theorem mixed_plane_strict (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hc : ∀ j, 0 < c j) (hplane : ∀ x ∈ K, ∑ j, c j * x j = D)
    (B : Walls 3) (horder : ∀ j, B.1 j ≤ B.2 j)
    (hw : ∀ b j, ∃ x ∈ K, wall b j B < cut b j x)
    (s : Finset Selection) (hs : ∀ e ∈ s, Allowed K c D B e)
    (v : Vertex) (i : Fin 3) (hodd : ∀ j, j ≠ i → v j ≠ v i)
    (hv : ∀ k, k ≠ i → edge k v ∈ s) :
    planeLevel D (!v i) < planeRow c (!v i) B := by
  obtain ⟨p, hp, hpi⟩ := hw (v i) i
  have hi : cut (!v i) i p < wall (!v i) i B := by
    cases hvi : v i <;> simp [cut, wall, hvi] at hpi ⊢ <;> linarith only [hpi, horder i]
  have hj (j : Fin 3) (hji : j ≠ i) : cut (!v i) j p ≤ wall (!v i) j B := by
    have hsign : v j = !v i := Bool.eq_not_iff.mpr (hodd j hji)
    rw [← hsign]
    by_contra! hpos
    obtain ⟨k, hki, hk⟩ := omitted_pair_ne i j hji.symm
    apply hs (edge k v) (hv k hki)
    refine ⟨p, hp, (pair_cuts B k v p).mpr ?_⟩
    intro l hl
    rcases hk l hl with rfl | rfl
    · exact sub_pos.mpr hpi
    · exact sub_pos.mpr hpos
  have hall (j : Fin 3) : cut (!v i) j p ≤ wall (!v i) j B := by
    by_cases hji : j = i
    · simpa only [hji] using hi.le
    · exact hj j hji
  have hsum := Finset.sum_lt_sum
    (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hall j) (hc j).le)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hc i)⟩
  rw [constant_relation K c D hplane (!v i) p hp, ← planeRow_apply] at hsum
  exact hsum

end Plank.Convex.PlanarSignedCaps
