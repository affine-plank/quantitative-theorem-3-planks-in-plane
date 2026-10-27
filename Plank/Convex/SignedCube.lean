/- Signs and edges of the three-dimensional cube. -/
module
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Pi
@[expose] public section
set_option autoImplicit false
namespace Plank.Convex.SignedCubeCover

abbrev Vertex := Fin 3 → Bool
abbrev Edge := Fin 3 × Bool × Bool
abbrev Selection := Edge ⊕ Bool

def edge (i : Fin 3) (v : Vertex) : Selection := .inl (i, v (i + 1), v (i + 2))
def constant (b : Bool) : Vertex := fun _ => b

def hits : Selection → Vertex → Prop
  | .inl (i, b, c), v => v (i + 1) = b ∧ v (i + 2) = c
  | .inr b, v => v = constant b

instance : DecidableRel hits := fun e v => by cases e <;> dsimp [hits] <;> infer_instance

def leaf (b : Bool) (i : Fin 3) : Vertex := fun j => if j = i then !b else b

theorem edge_hits (i : Fin 3) (v : Vertex) : hits (edge i v) v := ⟨rfl, rfl⟩

theorem omitted_pair_ne : ∀ (i j : Fin 3), i ≠ j →
    ∃ k, k ≠ i ∧ ∀ l, l ≠ k → l = i ∨ l = j := by
  decide +kernel

end Plank.Convex.SignedCubeCover
