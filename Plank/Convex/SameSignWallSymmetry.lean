/- Cyclic relabeling and global reflection of same-sign windows and supports. -/
module
public import Plank.Convex.SameSignLocalMinimum
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace Plank.Convex.SameSignWallSymmetry
open SameSignCapMinimum
abbrev Index := SameSignLocalMinimum.Index

def cycle : Fin 3 ≃ Fin 3 :=
  ⟨next, fun i => next (next i), by intro i; fin_cases i <;> rfl,
    by intro i; fin_cases i <;> rfl⟩
def rotation (i : Fin 3) : Fin 3 ≃ Fin 3 := ![Equiv.refl _, cycle, cycle.symm] i
theorem rotation_zero (i : Fin 3) : rotation i 0 = i := by fin_cases i <;> rfl
theorem rotation_next (i j : Fin 3) : rotation i (next j) = next (rotation i j) := by
  fin_cases i <;> fin_cases j <;> rfl

def permute (σ : Fin 3 ≃ Fin 3) : Point →ᵃ[ℝ] Point :=
  AffineMap.pi fun i => AffineMap.proj (σ i)
@[simp] theorem permute_apply (σ : Fin 3 ≃ Fin 3) (x : Point) (i : Fin 3) :
    permute σ x i = x (σ i) := rfl
def walls (σ : Fin 3 ≃ Fin 3) (B : Walls) : Walls := (permute σ B.1, permute σ B.2)
def slopes (σ : Fin 3 ≃ Fin 3) (r : Index → ℝ) : Index → ℝ := fun j => r (j.1, σ j.2)

theorem permute_symm (σ : Fin 3 ≃ Fin 3) (x : Point) : permute σ.symm (permute σ x) = x := by
  funext i
  simp
theorem image_symm (σ : Fin 3 ≃ Fin 3) (K : Set Point) :
    permute σ.symm '' (permute σ '' K) = K := by
  rw [Set.image_image]
  have he : (fun x => permute σ.symm (permute σ x)) = id := funext (permute_symm σ)
  simp only [he, Set.image_id]
theorem walls_symm (σ : Fin 3 ≃ Fin 3) (B : Walls) : walls σ.symm (walls σ B) = B := by
  apply Prod.ext <;> exact permute_symm σ _
theorem width_walls (σ : Fin 3 ≃ Fin 3) (B : Walls) : width (walls σ B) = width B := by
  simp only [width_apply, walls, permute_apply]
  exact Equiv.sum_comp σ (fun i => B.2 i - B.1 i)
theorem symm_next (σ : Fin 3 ≃ Fin 3) (hσ : ∀ i, σ (next i) = next (σ i)) (i : Fin 3) :
    σ.symm (next i) = next (σ.symm i) := by
  apply σ.injective
  rw [σ.apply_symm_apply, hσ, σ.apply_symm_apply]

theorem wallSet_permute (σ : Fin 3 ≃ Fin 3) (hσ : ∀ i, σ (next i) = next (σ i))
    (K : Set Point) (B : Walls) (hB : B ∈ wallSet K) :
    walls σ B ∈ wallSet (permute σ '' K) := by
  refine ⟨⟨⟨fun i => hB.1.1.1 (σ i), fun i => hB.1.1.2 (σ i)⟩,
    ⟨fun i => hB.1.2.1 (σ i), fun i => hB.1.2.2 (σ i)⟩⟩,
    mem_iInter.mpr (fun i => mem_iInter.mp hB.2.1 (σ i)), ?_⟩
  refine mem_iInter.mpr fun y => mem_iInter.mpr ?_
  rintro ⟨x, hx, rfl⟩
  apply mem_iInter.mpr
  intro i
  have h := mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hB.2.2 x) hx) (σ i)
  change (x (σ i) ≤ B.2 (σ i) ∨ x (next (σ i)) ≤ B.2 (next (σ i))) ∧
    (B.1 (σ i) ≤ x (σ i) ∨ B.1 (next (σ i)) ≤ x (next (σ i))) at h
  change (x (σ i) ≤ B.2 (σ i) ∨ x (σ (next i)) ≤ B.2 (σ (next i))) ∧
    (B.1 (σ i) ≤ x (σ i) ∨ B.1 (σ (next i)) ≤ x (σ (next i)))
  simpa only [hσ] using h

theorem strict_permute (σ : Fin 3 ≃ Fin 3) (B : Walls) (hB : B ∈ strictWalls) :
    walls σ B ∈ strictWalls := mem_iInter.mpr fun i => mem_iInter.mp hB (σ i)

theorem rows_permute (σ : Fin 3 ≃ Fin 3) (hσ : ∀ i, σ (next i) = next (σ i))
    (r : Index → ℝ) (j : Index) (B : Walls) :
    SameSignLocalMinimum.rows (slopes σ r) j (walls σ B) =
      SameSignLocalMinimum.rows r (j.1, σ j.2) B := by
  rcases j with ⟨s, i⟩
  cases s <;> simp [SameSignLocalMinimum.rows, walls, slopes, hσ]

theorem numerator_permute (σ : Fin 3 ≃ Fin 3) (hσ : ∀ i, σ (next i) = next (σ i))
    (r : Index → ℝ) (j : Index) :
    SameSignLocalMinimum.numerator (slopes σ r) j =
      SameSignLocalMinimum.numerator r (j.1, σ j.2) := by
  simp only [SameSignLocalMinimum.numerator, slopes, succ, hσ]

theorem supports_permute (σ : Fin 3 ≃ Fin 3) (hσ : ∀ i, σ (next i) = next (σ i))
    (K : Set Point) (B : Walls) (r : Index → ℝ)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B) :
    ∀ y ∈ permute σ '' K, ∀ j,
      SameSignLocalMinimum.rows (slopes σ r) j (y, y) ≤
        SameSignLocalMinimum.rows (slopes σ r) j (walls σ B) := by
  rintro y ⟨x, hx, rfl⟩ j
  change SameSignLocalMinimum.rows (slopes σ r) j (walls σ (x, x)) ≤ _
  simpa only [rows_permute σ hσ] using hs x hx (j.1, σ j.2)

def reflect : Point →ᵃ[ℝ] Point := AffineMap.const ℝ Point 1 - AffineMap.id ℝ Point
@[simp] theorem reflect_apply (x : Point) (i : Fin 3) : reflect x i = 1 - x i := rfl
def reflectedWalls (B : Walls) : Walls := (reflect B.2, reflect B.1)
def reflectedSlopes (r : Index → ℝ) : Index → ℝ := fun j => r (!j.1, j.2)
theorem reflect_reflect (x : Point) : reflect (reflect x) = x := by funext i; simp
theorem image_reflect (K : Set Point) : reflect '' (reflect '' K) = K := by
  rw [Set.image_image]
  have he : (fun x => reflect (reflect x)) = id := funext reflect_reflect
  simp only [he, Set.image_id]
theorem reflectedWalls_twice (B : Walls) : reflectedWalls (reflectedWalls B) = B := by
  apply Prod.ext <;> exact reflect_reflect _
theorem width_reflected (B : Walls) : width (reflectedWalls B) = width B := by
  simp only [width_apply, reflectedWalls, reflect_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem wallSet_reflect (K : Set Point) (B : Walls) (hB : B ∈ wallSet K) :
    reflectedWalls B ∈ wallSet (reflect '' K) := by
  have hb : reflectedWalls B ∈ Icc 0 1 := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro i
      exact sub_nonneg.mpr (hB.1.2.2 i)
    · intro i
      exact sub_nonneg.mpr (hB.1.2.1 i)
    · intro i
      change 1 - B.2 i ≤ 1
      have h : 0 ≤ B.2 i := hB.1.1.2 i
      linarith only [h]
    · intro i
      change 1 - B.1 i ≤ 1
      have h : 0 ≤ B.1 i := hB.1.1.1 i
      linarith only [h]
  have ho (i : Fin 3) : (reflectedWalls B).1 i ≤ (reflectedWalls B).2 i := by
    change 1 - B.2 i ≤ 1 - B.1 i
    exact sub_le_sub_left (show B.1 i ≤ B.2 i from mem_iInter.mp hB.2.1 i) 1
  refine ⟨hb, mem_iInter.mpr ho, ?_⟩
  refine mem_iInter.mpr fun y => mem_iInter.mpr ?_
  rintro ⟨x, hx, rfl⟩
  apply mem_iInter.mpr
  intro i
  have h := mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hB.2.2 x) hx) i
  change (x i ≤ B.2 i ∨ x (next i) ≤ B.2 (next i)) ∧
    (B.1 i ≤ x i ∨ B.1 (next i) ≤ x (next i)) at h
  change (1 - x i ≤ 1 - B.1 i ∨ 1 - x (next i) ≤ 1 - B.1 (next i)) ∧
    (1 - B.2 i ≤ 1 - x i ∨ 1 - B.2 (next i) ≤ 1 - x (next i))
  exact ⟨h.2.imp (fun h => sub_le_sub_left h 1) (fun h => sub_le_sub_left h 1),
    h.1.imp (fun h => sub_le_sub_left h 1) (fun h => sub_le_sub_left h 1)⟩

theorem strict_reflect (B : Walls) (hB : B ∈ strictWalls) : reflectedWalls B ∈ strictWalls := by
  apply mem_iInter.mpr
  intro i
  have h : (0 < B.1 i ∧ B.1 i < B.2 i) ∧ B.2 i < 1 := mem_iInter.mp hB i
  change (0 < 1 - B.2 i ∧ 1 - B.2 i < 1 - B.1 i) ∧ 1 - B.1 i < 1
  exact ⟨⟨sub_pos.mpr h.2, sub_lt_sub_left h.1.2 1⟩, by linarith only [h.1.1]⟩

theorem numerator_reflect (r : Index → ℝ) (j : Index) :
    SameSignLocalMinimum.numerator (reflectedSlopes r) j =
      SameSignLocalMinimum.numerator r (!j.1, j.2) := rfl

theorem supports_reflect (K : Set Point) (B : Walls) (r : Index → ℝ)
    (hs : ∀ x ∈ K, ∀ j, SameSignLocalMinimum.rows r j (x, x) ≤ SameSignLocalMinimum.rows r j B) :
    ∀ y ∈ reflect '' K, ∀ j,
      SameSignLocalMinimum.rows (reflectedSlopes r) j (y, y) ≤
        SameSignLocalMinimum.rows (reflectedSlopes r) j (reflectedWalls B) := by
  rintro y ⟨x, hx, rfl⟩ ⟨s, i⟩
  cases s
  · have h := hs x hx (true, i)
    simp only [SameSignLocalMinimum.rows, row_upper] at h
    change -((1 - x i) + r (true, i) * (1 - x (next i))) ≤
      -((1 - B.2 i) + r (true, i) * (1 - B.2 (next i)))
    nlinarith only [h]
  · have h := hs x hx (false, i)
    simp only [SameSignLocalMinimum.rows, row_lower] at h
    change (1 - x i) + r (false, i) * (1 - x (next i)) ≤
      (1 - B.1 i) + r (false, i) * (1 - B.1 (next i))
    nlinarith only [h]

end Plank.Convex.SameSignWallSymmetry
