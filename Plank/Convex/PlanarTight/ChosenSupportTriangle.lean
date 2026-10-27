/- The same-sign equality case from six fixed extrema and one arbitrary
point. Chosen support slopes suffice; no original pair contacts are needed. -/
module
public import Plank.Convex.PlanarChosenSupports
public import Plank.Convex.PlanarTight.ChosenSupportEquality
public import Plank.Convex.PlanarTight.TriangleSupportShape
public import Plank.Convex.PlanarTight.PlanarCoordinateIndependence
public import Plank.Convex.ConvexPairSupport
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.ChosenSupportTriangle
open PlanarSlopeGap (Triple)

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Positive same-sign supports at total width one force the whole planar
body to be the triangle of three fixed coordinate maxima. Only the six
coordinate contacts and one arbitrary point enter the slope selection. -/
theorem eq_triangle_of_supports (hdim : Module.finrank ℝ E = 2)
    (K : Set E) (hK : Convex ℝ K) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (A : Triple) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x, ∑ i, A i * f i x = D)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (lo hi a₀ b₀ : Triple) (ha₀ : ∀ i, 0 < a₀ i) (hb₀ : ∀ i, 0 < b₀ i)
    (hwidth : ∀ i, lo i < hi i) (hhi : ∀ i, hi i < 1)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (hupper : ∀ i, ∀ x ∈ K, f i x + a₀ i * f (i + 1) x ≤ hi i + a₀ i * hi (i + 1))
    (hlower : ∀ i, ∀ x ∈ K, lo i + b₀ i * lo (i + 1) ≤ f i x + b₀ i * f (i + 1) x) :
    ∃ v : Fin 3 → E, (∀ i, v i ∈ K) ∧ (∀ i, f i (v i) = 1) ∧
      AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v) := by
  choose p hp hzero using hL
  choose v hv hdiag using hU
  have hn (i : Fin 3) : (i + 1) + 1 = i + 2 := by fin_cases i <;> rfl
  have hp' (i : Fin 3) : (i + 2) + 1 = i := by fin_cases i <;> rfl
  have hpp (i : Fin 3) : (i + 2) + 2 = i + 1 := by fin_cases i <;> rfl
  have hbound (i : Fin 3) : hi i + a₀ i * hi (i + 1) < 1 + a₀ i :=
    add_lt_add (hhi i) (by simpa only [mul_one] using
      mul_lt_mul_of_pos_left (hhi _) (ha₀ i))
  have hnext (i : Fin 3) : f i (v (i + 1)) < 1 := by
    have h := hupper i (v (i + 1)) (hv _)
    rw [hdiag, mul_one] at h
    linarith only [h, hbound i]
  have hprev (i : Fin 3) : f i (v (i + 2)) < 1 := by
    have h := hupper (i + 2) (v (i + 2)) (hv _)
    have hh := hbound (i + 2)
    rw [hp', hdiag] at h
    rw [hp'] at hh
    nlinarith only [h, hh, ha₀ (i + 2)]
  have hind : AffineIndependent ℝ v := by
    apply TriangleSupportShape.independent_of_strict_maxima v f hdiag
    intro i j hji
    have hcases : j = i ∨ j = i + 1 ∨ j = i + 2 := by
      fin_cases i <;> fin_cases j <;> simp
    rcases hcases with rfl | rfl | rfl
    · exact False.elim (hji rfl)
    · exact hnext i
    · exact hprev i
  refine ⟨v, hv, hdiag, hind, Set.Subset.antisymm ?_
    (convexHull_min (by rintro _ ⟨i, rfl⟩; exact hv i) hK)⟩
  intro z hz
  let Z : (Fin 3 × Bool) ⊕ Unit → E := fun u =>
    match u with
    | Sum.inl (i, false) => p i
    | Sum.inl (i, true) => v i
    | Sum.inr _ => z
  have hZ (u : (Fin 3 × Bool) ⊕ Unit) : Z u ∈ K := by
    rcases u with ⟨i, b⟩ | u
    · cases b
      · exact hp i
      · exact hv i
    · exact hz
  let Y : Fin 3 → E →ᵃ[ℝ] ℝ := fun i => A i • f i
  let L : Triple := fun i => A i * lo i
  let H : Triple := fun i => A i * hi i
  have hY (i : Fin 3) (x : E) : Y i x = A i * f i x := rfl
  have transform (x d : Triple) (i : Fin 3) :
      A i * x i + (A i * d i / A (i + 1)) * (A (i + 1) * x (i + 1)) =
        A i * (x i + d i * x (i + 1)) := by
    field_simp [(hA (i + 1)).ne']
  obtain ⟨a, b, ha, hb, hu, hl, hab, hba⟩ :=
    PlanarChosenSupports.choose_six_supports (fun u i => Y i (Z u)) L H
      (fun i => A i * a₀ i / A (i + 1)) (fun i => A i * b₀ i / A (i + 1)) D
      (fun i => mul_le_mul_of_nonneg_left (hwidth i).le (hA i).le)
      (fun u => hplane (Z u))
      (fun i => div_pos (mul_pos (hA i) (ha₀ i)) (hA (i + 1)))
      (fun i => div_pos (mul_pos (hA i) (hb₀ i)) (hA (i + 1)))
      (fun i u => by
        simp only [hY, H]
        rw [transform (fun j => f j (Z u)), transform hi]
        exact mul_le_mul_of_nonneg_left (hupper i _ (hZ u)) (hA i).le)
      (fun i u => by
        simp only [hY, L]
        rw [transform lo, transform (fun j => f j (Z u))]
        exact mul_le_mul_of_nonneg_left (hlower i _ (hZ u)) (hA i).le)
  have hgap : 0 ≤ PlanarSlopeGap.gap a b := by
    apply PlanarSlopeGap.gap_nonneg a b (fun _ => 1)
      (fun i => (ha i).le) (fun i => (hb i).le) (fun _ => zero_lt_one)
    · intro i; nlinarith only [hab i]
    · intro i; nlinarith only [hba i]
  have hw (i : Fin 3) : L i < H i := mul_lt_mul_of_pos_left (hwidth i) (hA i)
  have hratio : ∑ i, (H i - L i) / A i = 1 := by
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [H, L]
    rw [← mul_sub, mul_div_cancel_left₀ _ (hA i).ne']
  have hzero' (i : Fin 3) : ∃ u ∈ (Set.univ : Set ((Fin 3 × Bool) ⊕ Unit)),
      Y i (Z u) = 0 :=
    ⟨Sum.inl (i, false), Set.mem_univ _, by simp [Z, hY, hzero]⟩
  have hmax' (i : Fin 3) : ∃ u ∈ (Set.univ : Set ((Fin 3 × Bool) ⊕ Unit)),
      Y i (Z u) = A i :=
    ⟨Sum.inl (i, true), Set.mem_univ _, by simp [Z, hY, hdiag]⟩
  have he := ChosenSupportEquality.opposite_eq Set.univ (fun i u => Y i (Z u))
    L H a b A ha hb hw hA hzero' hmax'
    (fun i u _ => hu i u) (fun i u _ => hl i u) hgap hratio
  have hc (i : Fin 3) := ChosenSupportEquality.upper_contacts Set.univ
    (fun j u => Y j (Z u)) L H a b A ha hb (fun j u _ => hu j u) (fun j u _ => hl j u)
    (fun j => (he j).2) i (Sum.inl (i, true)) (Set.mem_univ _)
    (by simp [Z, hY, hdiag])
  let g : Fin 3 → E →ᵃ[ℝ] ℝ := fun i =>
    AffineMap.const ℝ E (H (i + 1) + a (i + 1) * H (i + 2)) -
      (Y (i + 1) + a (i + 1) • Y (i + 2))
  have hg (i : Fin 3) (x : E) : g i x =
      H (i + 1) + a (i + 1) * H (i + 2) -
        (Y (i + 1) x + a (i + 1) * Y (i + 2) x) := rfl
  let C : Set E := convexHull ℝ (Set.range Z)
  have hvC (i : Fin 3) : v i ∈ C :=
    subset_convexHull ℝ (Set.range Z) ⟨Sum.inl (i, true), rfl⟩
  have hside : ∀ x ∈ C, ∀ i, 0 ≤ g i x := by
    intro x hx i
    apply (convexHull_min (t := (g i) ⁻¹' Set.Ici 0) ?_
      ((convex_Ici (0 : ℝ)).affine_preimage (g i))) hx
    rintro _ ⟨u, rfl⟩
    change 0 ≤ g i (Z u)
    rw [hg]
    exact sub_nonneg.mpr (by simpa only [hn] using hu (i + 1) u)
  have hoff : ∀ i j, j ≠ i → g i (v j) = 0 := by
    intro i j hji
    rw [hg]
    apply sub_eq_zero.mpr
    have hcases : j = i ∨ j = i + 1 ∨ j = i + 2 := by
      fin_cases i <;> fin_cases j <;> simp
    rcases hcases with rfl | rfl | rfl
    · exact False.elim (hji rfl)
    · simpa only [Z, hn] using (hc (i + 1)).1.symm
    · simpa only [Z, hpp] using (hc (i + 2)).2.symm
  have hinjY : Function.Injective (fun x => fun i => Y i x) := by
    intro x y hxy
    apply hinj
    funext i
    exact mul_left_cancel₀ (hA i).ne' (congrFun hxy i)
  have hnonzero : ∀ i, ∃ x, g i x ≠ 0 := by
    intro i
    obtain ⟨x, hx⟩ := PlanarCoordinateIndependence.nonzero_pair_cut hdim Y (fun _ => 1) D
      (fun _ => one_ne_zero) (fun x => by simpa only [one_mul, hY] using hplane x) hinjY
      (i + 1) (a (i + 1)) (H (i + 1) + a (i + 1) * H (i + 2)) (ha _).ne'
    refine ⟨x, ?_⟩
    rw [hg]
    have hnext' : SameSignCapAlgebra.next (i + 1) = i + 2 := by fin_cases i <;> rfl
    simpa only [hnext'] using hx
  have hC := TriangleSupportShape.eq_convexHull_of_supports hdim C (convex_convexHull ℝ _)
    v hvC hind g hside hoff hnonzero
  rw [← hC]
  exact subset_convexHull ℝ (Set.range Z) ⟨Sum.inr (), rfl⟩

/-- The manuscript's same-sign case: six empty pair caps, strictly interior
positive windows, a positive planar chart, and total width one imply triangularity.
The conclusion concerns the original whole convex set and its actual maxima. -/
theorem eq_triangle_of_empty_caps (hdim : Module.finrank ℝ E = 2)
    (K : Set E) (hK : Convex ℝ K) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (A : Triple) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x, ∑ i, A i * f i x = D)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (lo hi : Triple) (hlo : ∀ i, 0 < lo i)
    (hwidth : ∀ i, lo i < hi i) (hhi : ∀ i, hi i < 1)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (hupper : ∀ i, ¬ ∃ x ∈ K, hi i < f i x ∧ hi (i + 1) < f (i + 1) x)
    (hlower : ∀ i, ¬ ∃ x ∈ K, f i x < lo i ∧ f (i + 1) x < lo (i + 1)) :
    ∃ v : Fin 3 → E, (∀ i, v i ∈ K) ∧ (∀ i, f i (v i) = 1) ∧
      AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v) := by
  have hu (i : Fin 3) : ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K,
      f i x + a * f (i + 1) x ≤ hi i + a * hi (i + 1) := by
    apply ConvexCellSeparation.positive_support K hK (f i) (f (i + 1)) (hi i) (hi (i + 1))
    · obtain ⟨x, hx, he⟩ := hU i
      exact ⟨x, hx, he ▸ hhi i⟩
    · obtain ⟨x, hx, he⟩ := hU (i + 1)
      exact ⟨x, hx, he ▸ hhi (i + 1)⟩
    · exact hupper i
  have hl (i : Fin 3) : ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K,
      lo i + b * lo (i + 1) ≤ f i x + b * f (i + 1) x := by
    obtain ⟨b, hb, hsupport⟩ := ConvexCellSeparation.positive_support K hK
      (-f i) (-f (i + 1)) (-lo i) (-lo (i + 1))
      (by obtain ⟨x, hx, he⟩ := hL i; exact ⟨x, hx, by change -lo i < -f i x; rw [he]; linarith only [hlo i]⟩)
      (by obtain ⟨x, hx, he⟩ := hL (i + 1); exact ⟨x, hx, by change -lo (i + 1) < -f (i + 1) x; rw [he]; linarith only [hlo (i + 1)]⟩)
      (by rintro ⟨x, hx, h1, h2⟩; exact hlower i ⟨x, hx, neg_lt_neg_iff.mp h1, neg_lt_neg_iff.mp h2⟩)
    refine ⟨b, hb, fun x hx => ?_⟩
    have h : -f i x + b * -f (i + 1) x ≤ -lo i + b * -lo (i + 1) := hsupport x hx
    nlinarith only [h]
  choose a ha hau using hu
  choose b hb hbl using hl
  exact eq_triangle_of_supports hdim K hK f hL hU A D hA hplane hinj
    lo hi a b ha hb hwidth hhi hsum hau hbl

end Plank.Convex.PlanarTight.ChosenSupportTriangle
