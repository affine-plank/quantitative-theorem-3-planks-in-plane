/- A finite family with a private vertex for every member has few incidences.
The estimate applies to minimal covers by arbitrary finite sets. -/
module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace Plank.Convex.PrivateIncidence

variable {E V : Type*} [Fintype V]
  (s : Finset E) (hits : E → V → Prop) [DecidableRel hits]

def degree (v : V) : ℕ := (s.filter fun e => hits e v).card

/-- Count the incidences by vertices or by selected members. -/
theorem double_count : (∑ v, degree s hits v) =
    ∑ e ∈ s, (Finset.univ.filter (hits e)).card := by
  simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- A private vertex has degree one. Choosing one for each selected member
leaves at most `card V - card s` vertices with larger degree. -/
theorem bound (r : ℕ)
    (hp : ∀ e ∈ s, ∃ v, hits e v ∧ ∀ f ∈ s, hits f v → f = e)
    (hd : ∀ v, degree s hits v ≤ r) :
    (∑ v, degree s hits v) + r * s.card ≤ r * Fintype.card V + s.card := by
  classical
  choose p hp hu using fun e : s => hp e e.property
  have hinj : Function.Injective p := by
    intro e f hef
    apply Subtype.ext
    exact (hu f e e.property (by rw [← hef]; exact hp e))
  let L : Finset V := Finset.univ.image p
  have hcard : L.card = s.card := by
    simp [L, Finset.card_image_of_injective _ hinj]
  have hone (v : V) (hv : v ∈ L) : degree s hits v = 1 := by
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.card_eq_one.mpr
    refine ⟨e, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun hf => hu e f hf.1 hf.2
    · rintro rfl
      exact ⟨e.property, hp e⟩
  have hsplit : L.card + Lᶜ.card = Fintype.card V := by
    simp
  have hsum : (∑ v, degree s hits v) ≤ L.card + r * Lᶜ.card := by
    rw [← Finset.sum_add_sum_compl L]
    have hleft : (∑ v ∈ L, degree s hits v) = L.card := by
      simp_rw [Finset.sum_congr rfl (fun v hv => hone v hv)]
      simp
    rw [hleft]
    apply Nat.add_le_add_left
    calc
      (∑ v ∈ Lᶜ, degree s hits v) ≤ ∑ _v ∈ Lᶜ, r := Finset.sum_le_sum fun v _ => hd v
      _ = r * Lᶜ.card := by simp [Nat.mul_comm]
  rw [← hcard, ← hsplit]
  nlinarith only [hsum]

end Plank.Convex.PrivateIncidence
