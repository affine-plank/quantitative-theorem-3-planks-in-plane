/- Six weak exterior cells determine the same-sign empty pair caps directly.
No minimization or count of frozen covering rows is needed. -/
module
public import Plank.Convex.PlanarSignedCaps
public import Plank.Convex.ConvexPairSeparator
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarSixContactCaps
open Set PlanarCoverSpace PlanarSignedCaps SignedCubeCover

def Weak (K : Set (Point 3)) (B : Walls 3) (v : Vertex) : Prop :=
  ∃ x ∈ K, ∀ i, wall (v i) i B ≤ cut (v i) i x

private instance missingNeighbor_decidable (S : Finset Vertex) : Decidable
    (∀ v ∈ S, v ≠ constant false → v ≠ constant true →
      ∃ w, w ∉ S ∧ ∃ i, hits (edge i v) w) := inferInstance

private instance exactlyMixed_decidable (S : Finset Vertex) : Decidable
    (∀ v, v ∈ S ↔ v ≠ constant false ∧ v ≠ constant true) := inferInstance

/-- With at most two missing cube vertices, every retained mixed vertex can
have a missing neighbor only when the missing vertices are the constants. -/
theorem cube_six : ∀ S : Finset Vertex, 6 ≤ S.card →
    ¬ (constant false ∈ S ∧ constant true ∈ S) →
    (∀ v ∈ S, v ≠ constant false → v ≠ constant true →
      ∃ w, w ∉ S ∧ ∃ i, hits (edge i v) w) →
    ∀ v, v ∈ S ↔ v ≠ constant false ∧ v ≠ constant true := by
  decide +kernel

theorem edge_other : ∀ (e : Edge) (v : Vertex), hits (.inl e) v →
    ∃ w, hits (.inl e) w ∧ w ≠ v := by decide +kernel

theorem leaf_edge : ∀ (b : Bool) (i : Fin 3) (e : Edge),
    hits (.inl e) (leaf b i) → e = (i,b,b) ∨
      ∃ w, hits (.inl e) w ∧ w ≠ leaf b i ∧
        w ≠ constant false ∧ w ≠ constant true := by decide +kernel

theorem edge_as_incident : ∀ (e : Edge) (v : Vertex),
    hits (.inl e) v → edge e.1 v = .inl e := by decide +kernel

/-- An empty pair cap cannot have both endpoint cells nonempty: positive
separation pins both coordinates, and the plane pins the third. -/
theorem unique_weak_endpoint (K : Set (Point 3)) (hK : Convex ℝ K)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hp : ∀ x ∈ K, ∑ i, c i*x i = D)
    (B : Walls 3) (ho : ∀ i, B.1 i < B.2 i)
    (hw : ∀ b i, ∃ x ∈ K, wall b i B < cut b i x)
    (e : Edge) (he : PairEmpty K B e)
    (v w : Vertex) (hv : hits (.inl e) v) (hw' : hits (.inl e) w)
    (hve : Weak K B v) (hwe : Weak K B w) : v = w := by
  obtain ⟨i,b,d⟩ := e
  obtain ⟨a,ha,hs⟩ := ConvexCellSeparation.positive_support K hK
    (cut b (i+1)).toLinearMap.toAffineMap (cut d (i+2)).toLinearMap.toAffineMap
    (wall b (i+1) B) (wall d (i+2) B) (hw b (i+1)) (hw d (i+2)) he
  obtain ⟨x,hx,hvx⟩ := hve
  obtain ⟨y,hy,hwy⟩ := hwe
  have pin (z : Point 3) (hz : z ∈ K)
      (hg : wall b (i+1) B ≤ cut b (i+1) z)
      (hh : wall d (i+2) B ≤ cut d (i+2) z) :
      cut b (i+1) z = wall b (i+1) B ∧ cut d (i+2) z = wall d (i+2) B := by
    have H : cut b (i+1) z + a * cut d (i+2) z ≤
        wall b (i+1) B + a * wall d (i+2) B := hs z hz
    constructor
    · linarith only [H, mul_le_mul_of_nonneg_left hh ha.le, hg]
    · apply le_antisymm _ hh
      apply (mul_le_mul_iff_right₀ ha).mp
      linarith only [H,hg]
  have xpin := pin x hx
    (by simpa only [hv.1] using hvx (i+1))
    (by simpa only [hv.2] using hvx (i+2))
  have ypin := pin y hy
    (by simpa only [hw'.1] using hwy (i+1))
    (by simpa only [hw'.2] using hwy (i+2))
  have hj : x (i+1) = y (i+1) := by
    have hh := xpin.1.trans ypin.1.symm
    cases b <;> simpa [cut] using hh
  have hk : x (i+2) = y (i+2) := by
    have hh := xpin.2.trans ypin.2.symm
    cases d <;> simpa [cut] using hh
  have heq : x = y := by
    have hplaneeq := (hp x hx).trans (hp y hy).symm
    simp only [Fin.sum_univ_three] at hplaneeq
    have hi : x i = y i := by
      apply (mul_left_cancel₀ (hc i).ne')
      fin_cases i <;> dsimp at hj hk ⊢
      all_goals
        rw [hj,hk] at hplaneeq
        linarith only [hplaneeq]
    ext j
    fin_cases i <;> fin_cases j <;> first | exact hi | exact hj | exact hk
  subst y
  ext j
  have h₁ := hvx j
  have h₂ := hwy j
  cases hvj : v j <;> cases hwj : w j <;> try rfl
  all_goals
    simp [cut,wall,hvj,hwj] at h₁ h₂
    exfalso
    linarith only [ho j,h₁,h₂]

/-- Any strict cover with six weak exterior cells has all six same-sign
pair caps empty. The cover need not minimize any cost. -/
theorem mixed_cells_and_pairs (K : Set (Point 3)) (hK : Convex ℝ K)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hp : ∀ x ∈ K, ∑ i, c i*x i = D)
    (B : Walls 3) (ho : ∀ i, B.1 i < B.2 i)
    (hw : ∀ b i, ∃ x ∈ K, wall b i B < cut b i x)
    (hcover : Covers K B)
    (S : Finset Vertex) (hS : 6 ≤ S.card)
    (hweak : ∀ v ∈ S, Weak K B v) :
    (∀ v, v ∈ S ↔ v ≠ constant false ∧ v ≠ constant true) ∧
      ∀ b i, PairEmpty K B (i,b,b) := by
  classical
  have hn : ¬ (constant false ∈ S ∧ constant true ∈ S) := by
    rintro ⟨hl,hu⟩
    obtain ⟨x,hx,hxl⟩ := hweak _ hl
    obtain ⟨y,hy,hyu⟩ := hweak _ hu
    have hlt : ∑ i, c i*x i < ∑ i, c i*y i := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro i _
      apply mul_lt_mul_of_pos_left _ (hc i)
      have hl : x i ≤ B.1 i := by simpa [constant,cut,wall] using hxl i
      have hu : B.2 i ≤ y i := by simpa [constant,cut,wall] using hyu i
      exact (hl.trans_lt (ho i)).trans_le hu
    rw [hp x hx,hp y hy] at hlt
    exact lt_irrefl D hlt
  have cert (v : Vertex) (h0 : v ≠ constant false) (h1 : v ≠ constant true) :
      ∃ e : Edge, PairEmpty K B e ∧ hits (.inl e) v := by
    obtain ⟨e,he,hv⟩ := exists_allowed K hK c D hc hp B hcover v
    cases e with
    | inl e => exact ⟨e,he,hv⟩
    | inr b => cases b <;> exact False.elim (by contradiction)
  have mixed := cube_six S hS hn (by
    intro v hv h0 h1
    obtain ⟨e,he,hev⟩ := cert v h0 h1
    obtain ⟨w,hew,hwv⟩ := edge_other e v hev
    refine ⟨w,?_,e.1,?_⟩
    · intro hwS
      exact hwv (unique_weak_endpoint K hK c D hc hp B ho hw e he
        w v hew hev (hweak w hwS) (hweak v hv))
    · rw [edge_as_incident e v hev]
      exact hew)
  refine ⟨mixed, ?_⟩
  intro b i
  have hl : leaf b i ≠ constant false ∧ leaf b i ≠ constant true := by
    fin_cases b <;> fin_cases i <;> decide
  have hv := (mixed (leaf b i)).mpr hl
  obtain ⟨e,he,hev⟩ := cert (leaf b i) hl.1 hl.2
  rcases leaf_edge b i e hev with rfl | ⟨w,hew,hwv,hw0,hw1⟩
  · exact he
  · exact False.elim (hwv (unique_weak_endpoint K hK c D hc hp B ho hw e he
      w (leaf b i) hew hev (hweak w ((mixed w).mpr ⟨hw0,hw1⟩)) (hweak _ hv)))

/-- The same-sign pair exclusions, without retaining the cell classification. -/
theorem same_sign_pairs (K : Set (Point 3)) (hK : Convex ℝ K)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hp : ∀ x ∈ K, ∑ i, c i*x i = D)
    (B : Walls 3) (ho : ∀ i, B.1 i < B.2 i)
    (hw : ∀ b i, ∃ x ∈ K, wall b i B < cut b i x)
    (hcover : Covers K B)
    (S : Finset Vertex) (hS : 6 ≤ S.card)
    (hweak : ∀ v ∈ S, Weak K B v) :
    ∀ b i, PairEmpty K B (i,b,b) :=
  (mixed_cells_and_pairs K hK c D hc hp B ho hw hcover S hS hweak).2

end Plank.Convex.PlanarSixContactCaps

#print axioms Plank.Convex.PlanarSixContactCaps.same_sign_pairs
