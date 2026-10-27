/- Three cyclic supporting halfplanes on a positive plane enclose a triangle.
Positive slack weights give its barycentric coordinates explicitly. -/
module
public import Plank.Convex.SimplicialHalfspaces
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.CyclicCapTriangle
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def next : Fin 3 → Fin 3 := ![1, 2, 0]

def weight (a α : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![α 1 * α 2 * a 0 + α 1 * a 2 + a 1,
    α 2 * α 0 * a 1 + α 2 * a 0 + a 2,
    α 0 * α 1 * a 2 + α 0 * a 1 + a 0]

def slack (f : Fin 3 → E →ᵃ[ℝ] ℝ) (α b : Fin 3 → ℝ) (i : Fin 3) : E →ᵃ[ℝ] ℝ :=
  f (next i) - α i • f i - AffineMap.const ℝ E (b i)

def total (a α b : Fin 3 → ℝ) (d : ℝ) : ℝ :=
  (1 - α 0 * α 1 * α 2) * d - ∑ i, weight a α i * b i

theorem weight_pos (a α : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) (hα : ∀ i, 0 < α i)
    (i : Fin 3) : 0 < weight a α i := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hα0 := hα 0
  have hα1 := hα 1
  have hα2 := hα 2
  fin_cases i <;> dsimp [weight] <;> positivity

theorem weighted_identity (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a α b : Fin 3 → ℝ) (x : E) :
    (∑ i, weight a α i * slack f α b i x) =
      (1 - α 0 * α 1 * α 2) * (∑ i, a i * f i x) - ∑ i, weight a α i * b i := by
  simp [Fin.sum_univ_three, weight, slack, next]
  ring

theorem weighted_constant (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a α b : Fin 3 → ℝ) (d : ℝ)
    (hplane : ∀ x, ∑ i, a i * f i x = d) (x : E) :
    (∑ i, weight a α i * slack f α b i x) = total a α b d := by
  rw [weighted_identity, hplane x]
  rfl

/-- The positive plane relation makes the cyclic slack coordinates injective
whenever the original affine coordinates are injective. -/
theorem slack_injective (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a α b : Fin 3 → ℝ) (d : ℝ)
    (ha : ∀ i, 0 < a i) (hα : ∀ i, 0 < α i)
    (hplane : ∀ x, ∑ i, a i * f i x = d)
    (hinj : Function.Injective (fun x => fun i => f i x)) :
    Function.Injective (fun x => fun i => slack f α b i x) := by
  intro x y hxy
  have h0 : f 1 x - f 1 y = α 0 * (f 0 x - f 0 y) := by
    have h := congrFun hxy 0
    change f 1 x - α 0 * f 0 x - b 0 = f 1 y - α 0 * f 0 y - b 0 at h
    linarith only [h]
  have h1 : f 2 x - f 2 y = α 1 * (f 1 x - f 1 y) := by
    have h := congrFun hxy 1
    change f 2 x - α 1 * f 1 x - b 1 = f 2 y - α 1 * f 1 y - b 1 at h
    linarith only [h]
  have hp : a 0 * (f 0 x - f 0 y) + a 1 * (f 1 x - f 1 y) +
      a 2 * (f 2 x - f 2 y) = 0 := by
    have hx := hplane x
    have hy := hplane y
    simp only [Fin.sum_univ_three] at hx hy
    linear_combination hx - hy
  have hz : weight a α 2 * (f 0 x - f 0 y) = 0 := by
    calc
      _ = a 0 * (f 0 x - f 0 y) + a 1 * (f 1 x - f 1 y) +
          a 2 * (f 2 x - f 2 y) := by rw [h1, h0]; dsimp [weight]; ring
      _ = 0 := hp
  have hz0 : f 0 x - f 0 y = 0 :=
    (mul_eq_zero.mp hz).resolve_left (weight_pos a α ha hα 2).ne'
  have hz1 : f 1 x - f 1 y = 0 := by rw [h0, hz0, mul_zero]
  have hz2 : f 2 x - f 2 y = 0 := by rw [h1, hz1, mul_zero]
  apply hinj
  funext i
  fin_cases i
  · exact sub_eq_zero.mp hz0
  · exact sub_eq_zero.mp hz1
  · exact sub_eq_zero.mp hz2

private theorem slacks_zero_of_total_zero (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (a α b : Fin 3 → ℝ) (d : ℝ) (ha : ∀ i, 0 < a i) (hα : ∀ i, 0 < α i)
    (hplane : ∀ x, ∑ i, a i * f i x = d) (hC : total a α b d = 0)
    (x : E) (hx : ∀ i, 0 ≤ slack f α b i x) : ∀ i, slack f α b i x = 0 := by
  have hs : ∑ i, weight a α i * slack f α b i x = 0 := by
    rw [weighted_constant f a α b d hplane x, hC]
  have hnonneg (i : Fin 3) : 0 ≤ weight a α i * slack f α b i x :=
    mul_nonneg (weight_pos a α ha hα i).le (hx i)
  intro i
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hs i
    (Finset.mem_univ i)
  exact (mul_eq_zero.mp hz).resolve_left (weight_pos a α ha hα i).ne'

/-- Two distinct feasible points make the total slack strictly positive.
No interior point of the original body is required. -/
theorem total_pos (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a α b : Fin 3 → ℝ) (d : ℝ)
    (ha : ∀ i, 0 < a i) (hα : ∀ i, 0 < α i)
    (hplane : ∀ x, ∑ i, a i * f i x = d)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (x y : E) (hxy : x ≠ y)
    (hx : ∀ i, 0 ≤ slack f α b i x) (hy : ∀ i, 0 ≤ slack f α b i y) :
    0 < total a α b d := by
  have hnonneg : 0 ≤ total a α b d := by
    rw [← weighted_constant f a α b d hplane x]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (weight_pos a α ha hα i).le (hx i))
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hC : total a α b d = 0 := hzero.symm
  apply hxy
  apply slack_injective f a α b d ha hα hplane hinj
  funext i
  change slack f α b i x = slack f α b i y
  rw [slacks_zero_of_total_zero f a α b d ha hα hplane hC x hx i,
    slacks_zero_of_total_zero f a α b d ha hα hplane hC y hy i]

private theorem affine_apply (g : E →ᵃ[ℝ] ℝ) (x : E) :
    g x = g 0 + g.linear x := by
  simpa [add_comm] using g.map_vadd (0 : E) x

/-- A positive weighted affine-coordinate system with constant total and
injective coordinate map is an ordinary triangle in dimension two. -/
theorem triangle_of_positive_slacks [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) (t : Fin 3 → E →ᵃ[ℝ] ℝ)
    (w : Fin 3 → ℝ) (C : ℝ) (hw : ∀ i, 0 < w i) (hC : 0 < C)
    (hsum : ∀ x, ∑ i, w i * t i x = C)
    (hinj : Function.Injective (fun x => fun i => t i x)) :
    ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧
      {x : E | ∀ i, 0 ≤ t i x} = convexHull ℝ (Set.range v) := by
  let s (i : Fin 3) : E →ᵃ[ℝ] ℝ := (w i / C) • t i
  have hspos (i : Fin 3) : 0 < w i / C := div_pos (hw i) hC
  have hsum' (x : E) : ∑ i, s i x = 1 := by
    change (∑ i, (w i / C) * t i x) = 1
    simp only [div_eq_mul_inv, mul_right_comm _ C⁻¹, ← Finset.sum_mul, hsum x]
    exact mul_inv_cancel₀ hC.ne'
  have hs_inj : Function.Injective (fun x => fun i => s i x) := by
    intro x y h
    apply hinj
    funext i
    exact mul_left_cancel₀ (hspos i).ne' (congrFun h i)
  have hlin (x : E) : ∑ i, (s i).linear x = 0 := by
    have he : (∑ i, s i x) = (∑ i, s i 0) + ∑ i, (s i).linear x := by
      simp only [Fin.sum_univ_three]
      rw [affine_apply (s 0) x, affine_apply (s 1) x, affine_apply (s 2) x]
      ring
    rw [hsum' x, hsum' 0] at he
    linarith only [he]
  have hker (x : E) (hx : ∀ i, (s i).linear x = 0) : x = 0 := by
    apply hs_inj
    funext i
    change s i x = s i 0
    rw [affine_apply (s i) x, hx i, add_zero]
  obtain ⟨v, hv, _, hset⟩ := SimplicialHalfspaces.exists_vertices
    (fun i => s i 0) (fun i => (s i).linear) (hsum' 0) hlin hker (by simp [hdim])
  refine ⟨v, hv, ?_⟩
  rw [← hset]
  ext x
  change (∀ i, 0 ≤ t i x) ↔ ∀ i, 0 ≤ s i 0 + (s i).linear x
  simp only [← affine_apply]
  constructor
  · intro hx i
    exact mul_nonneg (hspos i).le (hx i)
  · intro hx i
    exact (mul_nonneg_iff_of_pos_left (hspos i)).mp (hx i)

/-- Three cyclic halfplanes in a positive affine plane, if they contain
two distinct points, intersect in a triangle. -/
theorem exists_triangle [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a α b : Fin 3 → ℝ) (d : ℝ)
    (ha : ∀ i, 0 < a i) (hα : ∀ i, 0 < α i)
    (hplane : ∀ x, ∑ i, a i * f i x = d)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (x y : E) (hxy : x ≠ y)
    (hx : ∀ i, 0 ≤ slack f α b i x) (hy : ∀ i, 0 ≤ slack f α b i y) :
    ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧
      {z : E | ∀ i, 0 ≤ slack f α b i z} = convexHull ℝ (Set.range v) := by
  exact triangle_of_positive_slacks hdim (slack f α b) (weight a α) (total a α b d)
    (weight_pos a α ha hα) (total_pos f a α b d ha hα hplane hinj x y hxy hx hy)
    (weighted_constant f a α b d hplane) (slack_injective f a α b d ha hα hplane hinj)

end Plank.Convex.CyclicCapTriangle

/-- info: 'Plank.Convex.CyclicCapTriangle.exists_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.CyclicCapTriangle.exists_triangle
