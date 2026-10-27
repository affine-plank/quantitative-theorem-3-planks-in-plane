/- Coordinate permutations and global reflection preserve normalized cube covers. -/
module
public import Plank.Convex.CommonPointUnclipped
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.CubeSymmetry
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

def permute (p : Equiv.Perm (Fin 3)) : Point →ₗ[ℝ] Point where
  toFun x i := x (p i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def transform (p : Equiv.Perm (Fin 3)) : Bool → Point →ᵃ[ℝ] Point
  | false => (permute p).toAffineMap
  | true => AffineMap.const ℝ Point (fun _ : Fin 3 => (1 : ℝ)) - (permute p).toAffineMap

def lower (lo hi : Point) (p : Equiv.Perm (Fin 3)) : Bool → Point
  | false => fun i => lo (p i)
  | true => fun i => 1 - hi (p i)

def upper (lo hi : Point) (p : Equiv.Perm (Fin 3)) : Bool → Point
  | false => fun i => hi (p i)
  | true => fun i => 1 - lo (p i)

@[simp] theorem transform_false_apply (p : Equiv.Perm (Fin 3)) (x : Point) (i : Fin 3) :
    transform p false x i = x (p i) := rfl

@[simp] theorem transform_true_apply (p : Equiv.Perm (Fin 3)) (x : Point) (i : Fin 3) :
    transform p true x i = 1 - x (p i) := rfl

theorem convex_image (K : Set Point) (hK : Convex ℝ K) (p : Equiv.Perm (Fin 3)) (flip : Bool) :
    Convex ℝ (transform p flip '' K) := Convex.affine_image (transform p flip) hK

theorem ordered (lo hi : Point) (p : Equiv.Perm (Fin 3)) (flip : Bool)
    (horder : ∀ i, lo i ≤ hi i) : ∀ i, lower lo hi p flip i ≤ upper lo hi p flip i := by
  intro i
  cases flip
  · exact horder (p i)
  · exact sub_le_sub_left (horder (p i)) 1

theorem strict (lo hi : Point) (p : Equiv.Perm (Fin 3)) (flip : Bool)
    (hm : ∀ i, 0 < lo i ∧ hi i < 1) :
    ∀ i, 0 < lower lo hi p flip i ∧ upper lo hi p flip i < 1 := by
  intro i
  cases flip
  · exact hm (p i)
  · change 0 < 1 - hi (p i) ∧ 1 - lo (p i) < 1
    obtain ⟨hl, hh⟩ := hm (p i)
    constructor <;> linarith

theorem zero_contacts (K : Set Point) (p : Equiv.Perm (Fin 3)) (flip : Bool)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1) :
    ∀ i, ∃ x ∈ transform p flip '' K, x i = 0 := by
  intro i
  cases flip
  · obtain ⟨x, hx, he⟩ := hL (p i)
    exact ⟨transform p false x, ⟨x, hx, rfl⟩, he⟩
  · obtain ⟨x, hx, he⟩ := hU (p i)
    refine ⟨transform p true x, ⟨x, hx, rfl⟩, ?_⟩
    rw [transform_true_apply, he]
    ring

theorem unit_contacts (K : Set Point) (p : Equiv.Perm (Fin 3)) (flip : Bool)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1) :
    ∀ i, ∃ x ∈ transform p flip '' K, x i = 1 := by
  intro i
  cases flip
  · obtain ⟨x, hx, he⟩ := hU (p i)
    exact ⟨transform p false x, ⟨x, hx, rfl⟩, he⟩
  · obtain ⟨x, hx, he⟩ := hL (p i)
    refine ⟨transform p true x, ⟨x, hx, rfl⟩, ?_⟩
    rw [transform_true_apply, he]
    ring

theorem box (K : Set Point) (p : Equiv.Perm (Fin 3)) (flip : Bool)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∀ x ∈ transform p flip '' K, ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  rintro _ ⟨x, hx, rfl⟩ i
  cases flip
  · exact hbox x hx (p i)
  · rw [transform_true_apply]
    obtain ⟨hl, hu⟩ := hbox x hx (p i)
    constructor <;> linarith

theorem cover (K : Set Point) (lo hi : Point) (p : Equiv.Perm (Fin 3)) (flip : Bool)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) :
    ∀ x ∈ transform p flip '' K, ∃ i,
      lower lo hi p flip i ≤ x i ∧ x i ≤ upper lo hi p flip i := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, hl, hu⟩ := hcover x hx
  refine ⟨p.symm j, ?_⟩
  cases flip
  · change lo (p (p.symm j)) ≤ x (p (p.symm j)) ∧ x (p (p.symm j)) ≤ hi (p (p.symm j))
    simpa only [p.apply_symm_apply] using And.intro hl hu
  · change 1 - hi (p (p.symm j)) ≤ 1 - x (p (p.symm j)) ∧
      1 - x (p (p.symm j)) ≤ 1 - lo (p (p.symm j))
    simp only [p.apply_symm_apply]
    exact ⟨sub_le_sub_left hu 1, sub_le_sub_left hl 1⟩

theorem width_sum (lo hi : Point) (p : Equiv.Perm (Fin 3)) (flip : Bool) :
    (∑ i, (upper lo hi p flip i - lower lo hi p flip i)) = ∑ i, (hi i - lo i) := by
  have hs := Equiv.sum_comp p (fun i => hi i - lo i)
  cases flip
  · exact hs
  · change (∑ i, ((1 - lo (p i)) - (1 - hi (p i)))) = ∑ i, (hi i - lo i)
    calc
      _ = ∑ i, (hi (p i) - lo (p i)) := by apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := hs

/-- Relabelling and reflection preserve affine plane equations. -/
theorem transformed_plane (K : Set Point) (A : Point) (D : ℝ)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (p : Equiv.Perm (Fin 3)) (flip : Bool) :
    ∀ x ∈ transform p flip '' K,
      (∑ i, A (p i) * x i) = if flip then (∑ i, A i) - D else D := by
  rintro _ ⟨x, hx, rfl⟩
  cases flip
  · change (∑ i, A (p i) * x (p i)) = D
    rw [Equiv.sum_comp p (fun i => A i * x i)]
    exact hplane x hx
  · change (∑ i, A (p i) * (1 - x (p i))) = (∑ i, A i) - D
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp p A, Equiv.sum_comp p (fun i => A i * x i), hplane x hx]

end Plank.Convex.CubeSymmetry

/-- info: 'Plank.Convex.CubeSymmetry.cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CubeSymmetry.cover
