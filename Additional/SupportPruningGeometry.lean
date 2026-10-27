/-
# Pruning a convex body while preserving covered points and selected widths

Retain the covered part and a maximizing and minimizing support point for each
chosen affine form, then take the closure of their convex hull. The result stays
inside the original compact convex body and has the same covered part and widths.
The covered set and the index type are arbitrary. Finite dimension is not needed.
-/
module

public import Plank.Proofs.AffineWidth
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Choose

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Plank.SupportPruningGeometry

open Set

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed convex hull of the covered points and the retained support points. -/
def prune (K U : Set E) (P Q : ι → E) : Set E :=
  closure (convexHull ℝ ((K ∩ U) ∪ range P ∪ range Q))

theorem covered_subset_prune (K U : Set E) (P Q : ι → E) :
    K ∩ U ⊆ prune K U P Q := by
  intro x hx
  exact subset_closure (subset_convexHull ℝ _ (Or.inl (Or.inl hx)))

theorem pointP_mem_prune (K U : Set E) (P Q : ι → E) (i : ι) :
    P i ∈ prune K U P Q := by
  exact subset_closure (subset_convexHull ℝ _ (Or.inl (Or.inr ⟨i, rfl⟩)))

theorem pointQ_mem_prune (K U : Set E) (P Q : ι → E) (i : ι) :
    Q i ∈ prune K U P Q := by
  exact subset_closure (subset_convexHull ℝ _ (Or.inr ⟨i, rfl⟩))

theorem nonempty_prune [Nonempty ι] (K U : Set E) (P Q : ι → E) :
    (prune K U P Q).Nonempty :=
  ⟨P (Classical.arbitrary ι), pointP_mem_prune K U P Q _⟩

theorem convex_prune (K U : Set E) (P Q : ι → E) :
    Convex ℝ (prune K U P Q) :=
  (convex_convexHull ℝ _).closure

theorem prune_subset {K U : Set E} {P Q : ι → E}
    (hK : IsClosed K) (hconv : Convex ℝ K)
    (hP : ∀ i, P i ∈ K) (hQ : ∀ i, Q i ∈ K) :
    prune K U P Q ⊆ K := by
  apply closure_minimal _ hK
  apply convexHull_min _ hconv
  rintro x ((hx | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · exact hx.1
  · exact hP i
  · exact hQ i

theorem isCompact_prune {K U : Set E} {P Q : ι → E}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (hP : ∀ i, P i ∈ K) (hQ : ∀ i, Q i ∈ K) :
    IsCompact (prune K U P Q) :=
  hK.of_isClosed_subset isClosed_closure (prune_subset hK.isClosed hconv hP hQ)

theorem prune_inter {K U : Set E} {P Q : ι → E}
    (hK : IsClosed K) (hconv : Convex ℝ K)
    (hP : ∀ i, P i ∈ K) (hQ : ∀ i, Q i ∈ K) :
    prune K U P Q ∩ U = K ∩ U := by
  apply Subset.antisymm
  · exact inter_subset_inter_left U (prune_subset hK hconv hP hQ)
  · exact fun x hx => ⟨covered_subset_prune K U P Q hx, hx.2⟩

/-- A second pruning with the same support points changes nothing. -/
theorem prune_idempotent {K U : Set E} {P Q : ι → E}
    (hK : IsClosed K) (hconv : Convex ℝ K)
    (hP : ∀ i, P i ∈ K) (hQ : ∀ i, Q i ∈ K) :
    prune (prune K U P Q) U P Q = prune K U P Q := by
  change closure (convexHull ℝ ((prune K U P Q ∩ U) ∪ range P ∪ range Q)) = _
  rw [prune_inter hK hconv hP hQ]
  rfl

theorem width_prune {K U : Set E} {P Q : ι → E}
    (hK : IsClosed K) (hconv : Convex ℝ K)
    (hP : ∀ i, P i ∈ K) (hQ : ∀ i, Q i ∈ K)
    (f : ι → E →ᵃ[ℝ] ℝ)
    (hmax : ∀ i, ∀ x ∈ K, f i x ≤ f i (P i))
    (hmin : ∀ i, ∀ x ∈ K, f i (Q i) ≤ f i x) (i : ι) :
    Body.width (prune K U P Q) (f i) = Body.width K (f i) := by
  have hsub := prune_subset (U := U) hK hconv hP hQ
  rw [Body.width_eq_of_realisers (pointP_mem_prune K U P Q i)
      (pointQ_mem_prune K U P Q i)
      (fun x hx => hmax i x (hsub hx)) (fun x hx => hmin i x (hsub hx)),
    Body.width_eq_of_realisers (hP i) (hQ i) (hmax i) (hmin i)]

/-- Every family of continuous affine forms admits a pruning preserving all its
widths and the covered part. The witnesses are actual support points of `K`.
The fixed-point statement uses these same support points. -/
theorem exists_support_pruning {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (U : Set E)
    (f : ι → E →ᵃ[ℝ] ℝ) (hf : ∀ i, Continuous (f i)) :
    ∃ (C : Set E) (P Q : ι → E),
      C = prune K U P Q ∧
      IsCompact C ∧ Convex ℝ C ∧ C ⊆ K ∧ C ∩ U = K ∩ U ∧
      (∀ i, Body.width C (f i) = Body.width K (f i)) ∧
      prune C U P Q = C ∧
      (∀ i, P i ∈ K) ∧ (∀ i, Q i ∈ K) ∧
      (∀ i, ∀ x ∈ K, f i x ≤ f i (P i)) ∧
      (∀ i, ∀ x ∈ K, f i (Q i) ≤ f i x) := by
  classical
  have hs : ∀ i, ∃ p ∈ K, ∃ q ∈ K,
      (∀ x ∈ K, f i x ≤ f i p) ∧ (∀ x ∈ K, f i q ≤ f i x) :=
    fun i => Body.exists_realisers hK hne (hf i)
  choose P hP Q hQ hmax hmin using hs
  exact ⟨prune K U P Q, P, Q, rfl,
    isCompact_prune hK hconv hP hQ, convex_prune K U P Q,
    prune_subset hK.isClosed hconv hP hQ, prune_inter hK.isClosed hconv hP hQ,
    width_prune hK.isClosed hconv hP hQ f hmax hmin,
    prune_idempotent hK.isClosed hconv hP hQ, hP, hQ, hmax, hmin⟩

end Plank.SupportPruningGeometry

end

#print axioms Plank.SupportPruningGeometry.covered_subset_prune
#print axioms Plank.SupportPruningGeometry.pointP_mem_prune
#print axioms Plank.SupportPruningGeometry.pointQ_mem_prune
#print axioms Plank.SupportPruningGeometry.nonempty_prune
#print axioms Plank.SupportPruningGeometry.convex_prune
#print axioms Plank.SupportPruningGeometry.prune_subset
#print axioms Plank.SupportPruningGeometry.isCompact_prune
#print axioms Plank.SupportPruningGeometry.prune_inter
#print axioms Plank.SupportPruningGeometry.prune_idempotent
#print axioms Plank.SupportPruningGeometry.width_prune
#print axioms Plank.SupportPruningGeometry.exists_support_pruning
