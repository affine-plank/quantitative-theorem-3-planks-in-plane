/- Dihedral symmetries of the six escape nodes transport all empty caps at once. -/
module
public import Plank.Convex.PlanarCapCaseReduction
public import Plank.Convex.CubeSymmetry
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarCapSymmetry
open scoped BigOperators
open PlanarCapPatterns PlanarCapCaseReduction
open CubeSymmetry (Point transform lower upper)

def coordinateRotation (r : Fin 6) : Fin 3 := ⟨r.val % 3, Nat.mod_lt _ (by decide)⟩

/-- The node action `i ↦ r ± i` induces the same action modulo three on coordinates. -/
def coordinateOrder (r : Fin 6) (reverse : Bool) : Equiv.Perm (Fin 3) where
  toFun i := if reverse then coordinateRotation r - i else coordinateRotation r + i
  invFun i := if reverse then coordinateRotation r - i else i - coordinateRotation r
  left_inv := by fin_cases r <;> cases reverse <;> decide
  right_inv := by fin_cases r <;> cases reverse <;> decide

/-- Odd rotations exchange upper and lower walls. -/
def reflectCube (r : Fin 6) : Bool := r.val % 2 == 1

def nodeOrder (r : Fin 6) (reverse : Bool) (i : Fin 6) : Fin 6 :=
  if reverse then r - i else r + i

def edgeOrder (r : Fin 6) (reverse : Bool) (i : Fin 6) : Fin 6 :=
  if reverse then nodeOrder r reverse i - 1 else nodeOrder r reverse i

private theorem node_next (r : Fin 6) (reverse : Bool) (i : Fin 6) :
    nodeOrder r reverse (next i) =
      if reverse then PlanarCapPatterns.prev (nodeOrder r reverse i)
      else next (nodeOrder r reverse i) := by
  fin_cases r <;> cases reverse <;> fin_cases i <;> decide

private theorem node_prev (r : Fin 6) (reverse : Bool) (i : Fin 6) :
    nodeOrder r reverse (PlanarCapPatterns.prev i) =
      if reverse then next (nodeOrder r reverse i)
      else PlanarCapPatterns.prev (nodeOrder r reverse i) := by
  fin_cases r <;> cases reverse <;> fin_cases i <;> decide

private theorem edge_eq (r : Fin 6) (reverse : Bool) (i : Fin 6) :
    edgeOrder r reverse i =
      if reverse then PlanarCapPatterns.prev (nodeOrder r reverse i)
      else nodeOrder r reverse i := by
  fin_cases r <;> cases reverse <;> fin_cases i <;> decide

private theorem next_prev (i : Fin 6) : next (PlanarCapPatterns.prev i) = i := by
  fin_cases i <;> rfl

/-- Every transformed wall is the corresponding original wall. -/
theorem wall_transform (lo hi : Point) (r : Fin 6) (reverse : Bool)
    (i : Fin 6) (x : Point) :
    wall (fun i => AffineMap.proj i)
      (lower lo hi (coordinateOrder r reverse) (reflectCube r))
      (upper lo hi (coordinateOrder r reverse) (reflectCube r)) i
      (transform (coordinateOrder r reverse) (reflectCube r) x) =
    wall (fun i => AffineMap.proj i) lo hi (nodeOrder r reverse i) x := by
  fin_cases r <;> cases reverse <;> fin_cases i <;>
    simp [wall, lower, upper, coordinateOrder, coordinateRotation, reflectCube, nodeOrder,
      Fin.neg_def]

/-- The two neighbours of a node are preserved or exchanged. -/
theorem singleEmpty_transform (K : Set Point) (lo hi : Point)
    (r : Fin 6) (reverse : Bool) (i : Fin 6) :
    SingleEmpty (transform (coordinateOrder r reverse) (reflectCube r) '' K)
      (fun i => AffineMap.proj i)
      (lower lo hi (coordinateOrder r reverse) (reflectCube r))
      (upper lo hi (coordinateOrder r reverse) (reflectCube r)) i ↔
    SingleEmpty K (fun i => AffineMap.proj i) lo hi (nodeOrder r reverse i) := by
  simp only [SingleEmpty, EmptyPair, Set.exists_mem_image, wall_transform, node_next, node_prev]
  cases reverse <;> simp [and_comm]

/-- Reversing the cycle also reverses the two endpoints of an edge. -/
theorem edgeEmpty_transform (K : Set Point) (lo hi : Point)
    (r : Fin 6) (reverse : Bool) (i : Fin 6) :
    EdgeEmpty (transform (coordinateOrder r reverse) (reflectCube r) '' K)
      (fun i => AffineMap.proj i)
      (lower lo hi (coordinateOrder r reverse) (reflectCube r))
      (upper lo hi (coordinateOrder r reverse) (reflectCube r)) i ↔
    EdgeEmpty K (fun i => AffineMap.proj i) lo hi (edgeOrder r reverse i) := by
  simp only [EdgeEmpty, EmptyPair, Set.exists_mem_image, wall_transform, node_next, edge_eq]
  cases reverse <;> simp [next_prev, and_comm]

/-- Every cap selected by `q` is carried to a cap selected by `p`. -/
def Pulls (p q : Pattern) (r : Fin 6) (reverse : Bool) : Prop :=
  (∀ i : Fin 6, q.singles.testBit i.val = true →
    p.singles.testBit (nodeOrder r reverse i).val = true) ∧
  (∀ i : Fin 6, q.edges.testBit i.val = true →
    p.edges.testBit (edgeOrder r reverse i).val = true)

instance (p q : Pattern) (r : Fin 6) (reverse : Bool) : Decidable (Pulls p q r reverse) := by
  unfold Pulls
  infer_instance

/-- A finite bit certificate transports the entire family of empty caps. -/
theorem holds_transform (K : Set Point) (lo hi : Point) (p q : Pattern)
    (r : Fin 6) (reverse : Bool) (hp : Pulls p q r reverse)
    (hh : Holds (SingleEmpty K (fun i => AffineMap.proj i) lo hi)
      (EdgeEmpty K (fun i => AffineMap.proj i) lo hi) p) :
    Holds (SingleEmpty (transform (coordinateOrder r reverse) (reflectCube r) '' K)
      (fun i => AffineMap.proj i) (lower lo hi (coordinateOrder r reverse) (reflectCube r))
      (upper lo hi (coordinateOrder r reverse) (reflectCube r)))
      (EdgeEmpty (transform (coordinateOrder r reverse) (reflectCube r) '' K)
      (fun i => AffineMap.proj i) (lower lo hi (coordinateOrder r reverse) (reflectCube r))
      (upper lo hi (coordinateOrder r reverse) (reflectCube r))) q := by
  constructor
  · intro i hbit
    exact (singleEmpty_transform K lo hi r reverse i).mpr (hh.1 _ (hp.1 i hbit))
  · intro i hbit
    exact (edgeEmpty_transform K lo hi r reverse i).mpr (hh.2 _ (hp.2 i hbit))

/-- The width assertion associated with a cap pattern, for every normalized convex cover. -/
def WidthBound (p : Pattern) : Prop :=
  ∀ (K : Set Point), Convex ℝ K →
    (∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1) →
    (∀ i, ∃ x ∈ K, x i = 0) → (∀ i, ∃ x ∈ K, x i = 1) →
    ∀ (lo hi : Point), (∀ i, lo i ≤ hi i) →
    (∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) →
    Holds (SingleEmpty K (fun i => AffineMap.proj i) lo hi)
      (EdgeEmpty K (fun i => AffineMap.proj i) lo hi) p →
    1 ≤ ∑ i, (hi i - lo i)

/-- A representative's width proof applies to every pattern that contains its transported caps. -/
theorem width_bound_of_pulls (p q : Pattern) (r : Fin 6) (reverse : Bool)
    (hp : Pulls p q r reverse) (hq : WidthBound q) : WidthBound p := by
  intro K hK hbox hL hU lo hi horder hcover hh
  let order := coordinateOrder r reverse
  let flip := reflectCube r
  have hw := hq (transform order flip '' K) (CubeSymmetry.convex_image K hK order flip)
    (CubeSymmetry.box K order flip hbox) (CubeSymmetry.zero_contacts K order flip hL hU)
    (CubeSymmetry.unit_contacts K order flip hL hU) (lower lo hi order flip)
    (upper lo hi order flip) (CubeSymmetry.ordered lo hi order flip horder)
    (CubeSymmetry.cover K lo hi order flip hcover) (holds_transform K lo hi p q r reverse hp hh)
  simpa only [CubeSymmetry.width_sum] using hw

/-- The corresponding assertion when the convex set lies on a positive affine plane. -/
def WidthBoundOnPlane (p : Pattern) : Prop :=
  ∀ (K : Set Point), Convex ℝ K →
    (∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1) →
    (∀ i, ∃ x ∈ K, x i = 0) → (∀ i, ∃ x ∈ K, x i = 1) →
    ∀ (A : Point) (D : ℝ), (∀ i, 0 < A i) → (∀ x ∈ K, ∑ i, A i * x i = D) →
    ∀ (lo hi : Point), (∀ i, lo i ≤ hi i) →
    (∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) →
    Holds (SingleEmpty K (fun i => AffineMap.proj i) lo hi)
      (EdgeEmpty K (fun i => AffineMap.proj i) lo hi) p →
    1 ≤ ∑ i, (hi i - lo i)

/-- The same transport preserves positivity of the plane normal. -/
theorem width_bound_on_plane_of_pulls (p q : Pattern) (r : Fin 6) (reverse : Bool)
    (hp : Pulls p q r reverse) (hq : WidthBoundOnPlane q) : WidthBoundOnPlane p := by
  intro K hK hbox hL hU A D hA hplane lo hi horder hcover hh
  let order := coordinateOrder r reverse
  let flip := reflectCube r
  have hw := hq (transform order flip '' K) (CubeSymmetry.convex_image K hK order flip)
    (CubeSymmetry.box K order flip hbox) (CubeSymmetry.zero_contacts K order flip hL hU)
    (CubeSymmetry.unit_contacts K order flip hL hU) (fun i => A (order i))
    (if flip then (∑ i, A i) - D else D) (fun i => hA (order i))
    (CubeSymmetry.transformed_plane K A D hplane order flip)
    (lower lo hi order flip) (upper lo hi order flip) (CubeSymmetry.ordered lo hi order flip horder)
    (CubeSymmetry.cover K lo hi order flip hcover) (holds_transform K lo hi p q r reverse hp hh)
  simpa only [CubeSymmetry.width_sum] using hw

end Plank.Convex.PlanarCapSymmetry

/-- info: 'Plank.Convex.PlanarCapSymmetry.holds_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapSymmetry.holds_transform

/-- info: 'Plank.Convex.PlanarCapSymmetry.width_bound_on_plane_of_pulls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapSymmetry.width_bound_on_plane_of_pulls
