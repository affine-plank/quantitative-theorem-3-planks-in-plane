/- The triangle geometry needed for homothetic extension of a
two-plank equality family. -/
module
public import Plank.Convex.PlanarTight.AnchoredTriangleRigidity
public import Plank.Convex.PlanarTight.AnchoredTriangleShape
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.AnchoredCapBody

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A triangle with its apex on the unit face and its opposite edge
on the zero face of X. -/
def Has (K : Set E) (X : E →ᵃ[ℝ] ℝ) (T : E) : Prop :=
  X T = 1 ∧ ∃ A B, X A = 0 ∧ X B = 0 ∧ K = convexHull ℝ {T, A, B}

theorem of_interior (K : Set E) (hK : Convex ℝ K) (X Y Z : E →ᵃ[ℝ] ℝ)
    (H : TwoPlankClassification.Ranges K Y Z)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, Y x = Y y → Z x = Z y → x = y)
    (hX : ∀ z ∈ K, 0 ≤ X z ∧ X z ≤ 1)
    (hface : {z | z ∈ K ∧ X z = 1}.Subsingleton)
    (T : E) (hT : T ∈ K) (hXT : X T = 1)
    (c g r : ℝ) (hc : 0 < c) (hc₁ : c < 1) (hg : 0 < g) (hg₁ : g < 1)
    (hr : 0 < r) (hr₁ : r < 1)
    (hshape : ∀ z ∈ K, c * Y z ≤ Z z ∧ Z z ≤ 1 - (1 - c) * Y z)
    (hcover : ∀ z ∈ K, X z ≤ r ∨
      (r * Y T ≤ Y z ∧ Y z ≤ r * Y T + (1 - r) * g) ∨
      (r * Z T + (1 - r) * (g * c) ≤ Z z ∧
        Z z ≤ r * Z T + (1 - r) * (1 - g + g * c))) : Has K X T := by
  obtain ⟨v, hv, hY₀, hZ₀, hY₁, hZ₁, hY₂, hZ₂, _, hbody⟩ :=
    AnchoredTriangleShape.eq_triangle K hK Y Z H hinj c hc hc₁ hshape
  have hrange : Set.range v = {v 0, v 1, v 2} := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (h | h | h)
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
  rw [hrange] at hbody
  have hwhere := AnchoredTriangleRigidity.maximizer_is_vertex K hK X (v 0) (v 1) (v 2)
    hbody (fun z hz => (hX z hz).2) hface T hT hXT
  have hz := AnchoredTriangleRigidity.other_vertices_zero K hK X Y Z T (v 0) (v 1) (v 2)
    hT (hv 0) (hv 1) (hv 2) hXT (fun z hz => (hX z hz).1) c g r hc hc₁ hg hg₁ hr hr₁
    hY₀ hZ₀ hY₁ hZ₁ hY₂ hZ₂ hwhere hcover
  refine ⟨hXT, ?_⟩
  rcases hz with ⟨he, h₁, h₂⟩ | ⟨he, h₀, h₂⟩ | ⟨he, h₀, h₁⟩
  · exact ⟨v 1, v 2, h₁, h₂, by rwa [he]⟩
  · refine ⟨v 0, v 2, h₀, h₂, ?_⟩
    simpa only [he, Set.insert_comm] using hbody
  · refine ⟨v 0, v 1, h₀, h₁, ?_⟩
    rw [hbody, he]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

end Plank.Convex.PlanarTight.AnchoredCapBody

/-- info: 'Plank.Convex.PlanarTight.AnchoredCapBody.of_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredCapBody.of_interior
