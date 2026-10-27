/- Finite closed convex covers have a common point when every proper
intersection meets the covered convex set. A compact hull of witnesses
and a separating slice give an induction on the covering family.
Compare Klee (1951), On Certain Intersection Properties of Convex Sets, (2.1). -/
module
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Tactic.Linarith
@[expose] public section

set_option autoImplicit false
noncomputable section
open Set

namespace Plank.Convex.FiniteConvexCoverIntersection

variable {E ι : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- A finite closed convex cover of a nonempty convex set has a common
point if each subfamily obtained by omitting one set has a common point
in the covered set. The covered set need not be closed or compact. -/
theorem inter_nonempty (s : Finset ι) (A : ι → Set E) :
    ∀ (K : Set E), K.Nonempty → Convex ℝ K →
    (∀ i ∈ s, Convex ℝ (A i)) → (∀ i ∈ s, IsClosed (A i)) →
    (∀ x ∈ K, ∃ i ∈ s, x ∈ A i) →
    (∀ i ∈ s, ∃ x ∈ K, ∀ j ∈ s, j ≠ i → x ∈ A j) →
    ∃ x ∈ K, ∀ i ∈ s, x ∈ A i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro K hne _ _ _ _ _
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, by simp⟩
  | @insert k s hk ih =>
    intro K hne hK hA hAc hcover hproper
    by_cases hs : s = ∅
    · subst s
      obtain ⟨x, hx⟩ := hne
      obtain ⟨i, hi, hxi⟩ := hcover x hx
      have hik : i = k := by simpa using hi
      subst i
      exact ⟨x, hx, by simpa using hxi⟩
    obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    by_contra hn
    have hw : ∀ i : ↑(insert k s), ∃ x ∈ K,
        ∀ j ∈ insert k s, j ≠ i.val → x ∈ A j := by
      intro i
      exact hproper i.val i.property
    choose p hpK hpA using hw
    let k' : ↑(insert k s) := ⟨k, Finset.mem_insert_self k s⟩
    let T : Set E := convexHull ℝ (Set.range p)
    have hT : Convex ℝ T := convex_convexHull ℝ _
    have hTc : IsCompact T := (Set.finite_range p).isCompact_convexHull ℝ
    have hTK : T ⊆ K := convexHull_min (by rintro x ⟨i, rfl⟩; exact hpK i) hK
    have hpT (i : ↑(insert k s)) : p i ∈ T :=
      subset_convexHull ℝ _ (Set.mem_range_self i)
    let D : Set E := T ∩ ⋂ j ∈ s, A j
    have hD : Convex ℝ D := hT.inter (convex_iInter₂ fun j hj =>
      hA j (Finset.mem_insert_of_mem hj))
    have hDc : IsCompact D := hTc.inter_right (isClosed_iInter fun j =>
      isClosed_iInter fun hj => hAc j (Finset.mem_insert_of_mem hj))
    have hjk (j : ι) (hj : j ∈ s) : j ≠ k := by
      intro he
      subst j
      exact hk hj
    have hpkD : p k' ∈ D := ⟨hpT k', mem_iInter₂.mpr fun j hj =>
      hpA k' j (Finset.mem_insert_of_mem hj) (hjk j hj)⟩
    have hdisj : Disjoint D (A k) := by
      rw [disjoint_left]
      intro x hx hxk
      apply hn
      refine ⟨x, hTK hx.1, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hxk
      · exact mem_iInter₂.mp hx.2 j hj
    obtain ⟨f, u, v, hleft, huv, hright⟩ :=
      geometric_hahn_banach_compact_closed hD hDc
        (hA k (Finset.mem_insert_self k s)) (hAc k (Finset.mem_insert_self k s)) hdisj
    have hpk : f (p k') < u := hleft _ hpkD
    let S : Set E := T ∩ f ⁻¹' {u}
    have hS : Convex ℝ S := hT.inter
      ((convex_singleton u).linear_preimage f.toLinearMap)
    have hScov : ∀ x ∈ S, ∃ i ∈ s, x ∈ A i := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := hcover x (hTK hx.1)
      rcases Finset.mem_insert.mp hi with rfl | hi
      · have he : f x = u := hx.2
        have hh := hright x hxi
        exfalso
        linarith only [he, hh, huv]
      · exact ⟨i, hi, hxi⟩
    have hwS : ∀ i ∈ s, ∃ x ∈ S, ∀ j ∈ s, j ≠ i → x ∈ A j := by
      intro i hi
      let i' : ↑(insert k s) := ⟨i, Finset.mem_insert_of_mem hi⟩
      have hpi : u < f (p i') := huv.trans
        (hright _ (hpA i' k (Finset.mem_insert_self k s) (hjk i hi).symm))
      let B : Set E := T ∩ {x | ∀ j ∈ s, j ≠ i → x ∈ A j}
      have hB : Convex ℝ B := hT.inter (by
        intro x hx y hy a b ha hb hab j hj hji
        exact hA j (Finset.mem_insert_of_mem hj) (hx j hj hji) (hy j hj hji) ha hb hab)
      have hpkB : p k' ∈ B := ⟨hpT k', fun j hj _ =>
        hpA k' j (Finset.mem_insert_of_mem hj) (hjk j hj)⟩
      have hpiB : p i' ∈ B := ⟨hpT i', fun j hj hji =>
        hpA i' j (Finset.mem_insert_of_mem hj) hji⟩
      have hu : u ∈ f '' B := (convex_iff_ordConnected.mp
        (hB.linear_image f.toLinearMap)).out
          ⟨p k', hpkB, rfl⟩ ⟨p i', hpiB, rfl⟩ ⟨hpk.le, hpi.le⟩
      obtain ⟨x, hx, hxu⟩ := hu
      exact ⟨x, ⟨hx.1, hxu⟩, hx.2⟩
    have hSne : S.Nonempty := by
      obtain ⟨x, hx, _⟩ := hwS i₀ hi₀
      exact ⟨x, hx⟩
    obtain ⟨x, hx, hxA⟩ := ih S hSne hS
      (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hAc j (Finset.mem_insert_of_mem hj)) hScov hwS
    have he : f x = u := hx.2
    have hh := hleft x ⟨hx.1, mem_iInter₂.mpr hxA⟩
    linarith only [he, hh]

end Plank.Convex.FiniteConvexCoverIntersection

/-- info: 'Plank.Convex.FiniteConvexCoverIntersection.inter_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.FiniteConvexCoverIntersection.inter_nonempty
