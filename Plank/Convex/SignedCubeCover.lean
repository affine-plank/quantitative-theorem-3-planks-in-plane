/- A cube edge is a coordinate to leave free and two prescribed signs.
The other two selections are the constant-sign vertices. -/
module
public import Plank.Convex.SignedCube
public import Plank.Convex.PrivateIncidence
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Minimal
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace Plank.Convex.SignedCubeCover
open Plank.Convex


def minimalCover (s : Finset Selection) : Prop :=
  (∀ v, ∃ e ∈ s, hits e v) ∧
  ∀ e ∈ s, ∃ v, hits e v ∧ ∀ f ∈ s, hits f v → f = e

def star (s : Finset Selection) (v : Vertex) : Prop := ∀ i, edge i v ∈ s
def degree (s : Finset Selection) (v : Vertex) : ℕ := PrivateIncidence.degree s hits v
def singletons (s : Finset Selection) : ℕ := (s.filter fun e => e.isRight).card
def incidentEdges (v : Vertex) : Finset Selection :=
  Finset.univ.filter fun e => e.isLeft ∧ hits e v

theorem incidentEdges_card : ∀ v, (incidentEdges v).card = 3 := by decide +kernel

theorem singleton_degree (s : Finset Selection) (h : minimalCover s)
    (b : Bool) (he : Sum.inr b ∈ s) : degree s (constant b) = 1 := by
  obtain ⟨v, rfl, hu⟩ := h.2 (.inr b) he
  apply Finset.card_eq_one.mpr
  refine ⟨.inr b, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun hf => hu f hf.1 hf.2, fun hf => hf ▸ ⟨he, rfl⟩⟩

theorem degree_bound (s : Finset Selection) (h : minimalCover s) (v : Vertex) :
    degree s v ≤ 3 ∧ (2 < degree s v → star s v) := by
  by_cases hs : ∃ b, Sum.inr b ∈ s ∧ v = constant b
  · obtain ⟨b, he, rfl⟩ := hs
    rw [singleton_degree s h b he]
    exact ⟨by decide, fun hn => (by omega : False).elim⟩
  · have hsub : s.filter (fun e => hits e v) ⊆ incidentEdges v := by
      intro e he
      obtain ⟨he, hev⟩ := Finset.mem_filter.mp he
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_, hev⟩
      cases e with
      | inl a => rfl
      | inr b => exact (hs ⟨b, he, hev⟩).elim
    have hle : degree s v ≤ 3 := (Finset.card_le_card hsub).trans_eq (incidentEdges_card v)
    refine ⟨hle, fun hgt i => ?_⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [incidentEdges_card]
      change 3 ≤ degree s v
      omega)
    have hin : edge i v ∈ s.filter (fun e => hits e v) := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, edge_hits i v⟩
    exact (Finset.mem_filter.mp hin).1

theorem incidence_count (s : Finset Selection) :
    (∑ v, degree s v) + singletons s = 2 * s.card := by
  have hsize : ∀ e : Selection, (Finset.univ.filter (hits e)).card +
      (if e.isRight then 1 else 0) = 2 := by decide +kernel
  calc
    (∑ v, degree s v) + singletons s =
        ∑ e ∈ s, ((Finset.univ.filter (hits e)).card +
          (if e.isRight then 1 else 0)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact PrivateIncidence.double_count s hits
      · simp only [singletons, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ _e ∈ s, 2 := Finset.sum_congr rfl fun e _ => hsize e
    _ = 2 * s.card := by simp [Nat.mul_comm]

theorem singletons_le_two (s : Finset Selection) : singletons s ≤ 2 := by
  have hsub : s.filter (fun e => e.isRight) ⊆ ({Sum.inr false, Sum.inr true} : Finset Selection) := by
    intro e he
    obtain ⟨_, he⟩ := Finset.mem_filter.mp he
    cases e with
    | inl a => cases he
    | inr b => cases b <;> simp
  simpa [singletons] using Finset.card_le_card hsub

theorem singletons_le_one (s : Finset Selection)
    (h : ¬ (Sum.inr false ∈ s ∧ Sum.inr true ∈ s)) : singletons s ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨he, hse⟩ := Finset.mem_filter.mp he
  obtain ⟨hf, hsf⟩ := Finset.mem_filter.mp hf
  cases e with
  | inl a => cases hse
  | inr b =>
    cases f with
    | inl a => cases hsf
    | inr c => cases b <;> cases c <;> simp_all

theorem edge_distinct : ∀ i v, edge (i + 1) v ≠ edge i v := by decide +kernel

theorem other_endpoint : ∀ (i : Fin 3) (u v w : Vertex),
    hits (edge i v) u → hits (edge i v) w → u ≠ v → w ≠ v → u = w := by decide +kernel

/-- Every leaf of a selected full star is private to its incident edge. -/
theorem star_leaf (s : Finset Selection) (h : minimalCover s) (v : Vertex)
    (hs : star s v) (i : Fin 3) (w : Vertex)
    (hw : hits (edge i v) w) (hne : w ≠ v) :
    ∀ f ∈ s, hits f w → f = edge i v := by
  obtain ⟨u, hu, hunique⟩ := h.2 (edge i v) (hs i)
  have huv : u ≠ v := by
    intro huv
    exact edge_distinct i v (hunique _ (hs (i + 1)) (by
      simpa only [huv] using edge_hits (i + 1) v))
  simpa only [other_endpoint i u v w hu hw huv hne] using hunique


theorem leaf_incidence : ∀ b i,
    hits (edge i (constant b)) (leaf b i) ∧ leaf b i ≠ constant b := by decide +kernel

/-- At distance two from a constant vertex, the other incident edges
meet its private leaves. The constant singleton selections do not occur. -/
theorem opposite_incidence : ∀ b i f, hits f (leaf (!b) i) →
    f = edge i (constant (!b)) ∨
    (hits f (leaf b (i + 1)) ∧ f ≠ edge (i + 1) (constant b)) ∨
    (hits f (leaf b (i + 2)) ∧ f ≠ edge (i + 2) (constant b)) := by
  intro b i f
  fin_cases b <;> fin_cases i <;> fin_cases f <;> decide

theorem constant_stars (s : Finset Selection) (h : minimalCover s)
    (b : Bool) (hs : star s (constant b)) : star s (constant (!b)) := by
  intro i
  obtain ⟨f, hf, hv⟩ := h.1 (leaf (!b) i)
  rcases opposite_incidence b i f hv with rfl | ⟨hv, hne⟩ | ⟨hv, hne⟩
  · exact hf
  · exact (hne (star_leaf s h (constant b) hs (i + 1) (leaf b (i + 1))
      (leaf_incidence _ _).1 (leaf_incidence _ _).2 f hf hv)).elim
  · exact (hne (star_leaf s h (constant b) hs (i + 2) (leaf b (i + 2))
      (leaf_incidence _ _).1 (leaf_incidence _ _).2 f hf hv)).elim

/-- Private vertices give the count; at six, a full star is unavoidable
unless both constant singleton selections occur. -/
theorem cube_count (s : Finset Selection) (h : minimalCover s) :
    s.card ≤ 6 ∧ (s.card = 6 →
      (Sum.inr false ∈ s ∧ Sum.inr true ∈ s) ∨
      (star s (constant false) ∧ star s (constant true)) ∨
      ∃ v, v ≠ constant false ∧ v ≠ constant true ∧ star s v) := by
  have hsum := incidence_count s
  have hthree := PrivateIncidence.bound s hits 3 h.2 (fun v => (degree_bound s h v).1)
  have hsingle := singletons_le_two s
  have hvertices : Fintype.card Vertex = 8 := by decide +kernel
  rw [hvertices] at hthree
  change (∑ v, degree s v) + 3 * s.card ≤ 3 * 8 + s.card at hthree
  refine ⟨by omega, fun hcard => ?_⟩
  by_cases hboth : Sum.inr false ∈ s ∧ Sum.inr true ∈ s
  · exact Or.inl hboth
  have hstar : ∃ v, star s v := by
    by_contra! hn
    have htwo := PrivateIncidence.bound s hits 2 h.2 (fun v =>
      le_of_not_gt (fun hv => hn v ((degree_bound s h v).2 hv)))
    have hs := singletons_le_one s hboth
    rw [hvertices] at htwo
    change (∑ v, degree s v) + 2 * s.card ≤ 2 * 8 + s.card at htwo
    omega
  obtain ⟨v, hv⟩ := hstar
  by_cases h0 : v = constant false
  · subst v
    exact Or.inr (Or.inl ⟨hv, constant_stars s h false hv⟩)
  by_cases h1 : v = constant true
  · subst v
    exact Or.inr (Or.inl ⟨constant_stars s h true hv, hv⟩)
  exact Or.inr (Or.inr ⟨v, h0, h1, hv⟩)

/-- An inclusion-minimal cover has a private vertex for each selection. -/
theorem exists_minimal_cover (allowed : Selection → Prop)
    (h : ∀ v : Vertex, ∃ e, allowed e ∧ hits e v) :
    ∃ s : Finset Selection, (∀ e ∈ s, allowed e) ∧ minimalCover s := by
  classical
  let t := Finset.univ.filter allowed
  obtain ⟨s, hst, hc, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun s : Finset Selection => ∀ v : Vertex, ∃ e ∈ s, hits e v) t (by
      intro v
      obtain ⟨e, he, hev⟩ := h v
      exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩, hev⟩)
  refine ⟨s, fun e he => (Finset.mem_filter.mp (hst he)).2, hc, ?_⟩
  intro e he
  have herase : ¬ ∀ v : Vertex, ∃ f ∈ s.erase e, hits f v :=
    fun hcover => Finset.notMem_erase e s ((hmin hcover (Finset.erase_subset e s)) he)
  push Not at herase
  obtain ⟨v, hv⟩ := herase
  obtain ⟨f, hf, hfv⟩ := hc v
  have hfe : f = e := by
    by_contra hn
    exact hv f (Finset.mem_erase.mpr ⟨hn, hf⟩) hfv
  subst f
  refine ⟨v, hfv, ?_⟩
  intro g hg hgv
  by_contra hn
  exact hv g (Finset.mem_erase.mpr ⟨hn, hg⟩) hgv

theorem mixed_odd (v : Vertex) (h0 : v ≠ constant false) (h7 : v ≠ constant true) :
    ∃ i, ∀ j, j ≠ i → v j ≠ v i := by
  revert v
  decide +kernel

theorem omitted_pair (i j : Fin 3) (hij : i ≠ j) :
    ∃ k, ∀ l, l ≠ k → l = i ∨ l = j := by
  revert i j
  decide +kernel

theorem edge_ne : ∀ (i j : Fin 3) (v : Vertex), i ≠ j → edge i v ≠ edge j v := by
  decide +kernel


theorem opposite_edge_endpoints : ∀ (v : Vertex) (i : Fin 3) (w : Vertex),
    (∀ j, j ≠ i → v j ≠ v i) → hits (edge i v) w →
      w = v ∨ w = constant (!v i) := by
  decide +kernel

/-- Replacing the opposite edge of a mixed star by the constant singleton
still covers the cube. -/
theorem replace_star_cover (s : Finset Selection)
    (hcover : ∀ w, ∃ e ∈ s, hits e w)
    (v : Vertex) (i : Fin 3) (hodd : ∀ j, j ≠ i → v j ≠ v i)
    (hv : star s v) :
    ∀ w, ∃ e ∈ insert (.inr (!v i)) (s.erase (edge i v)), hits e w := by
  classical
  intro w
  obtain ⟨e, he, hew⟩ := hcover w
  by_cases heq : e = edge i v
  · subst e
    rcases opposite_edge_endpoints v i w hodd hew with hw | hw
    · exact ⟨edge (i + 1) v, Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨edge_distinct i v, hv (i + 1)⟩), hw ▸ edge_hits _ _⟩
    · exact ⟨.inr (!v i), Finset.mem_insert_self _ _, hw⟩
  · exact ⟨e, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨heq, he⟩), hew⟩

end Plank.Convex.SignedCubeCover
