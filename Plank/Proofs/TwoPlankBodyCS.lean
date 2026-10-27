/- The retained Cauchy–Schwarz proof on a compact convex body.
The topology-free scalar and normalized-coordinate development lives in
TwoPlankScalar. This module preserves its historical public import interface
and the original compact-body theorem. The paper's Hunter proof remains in
Proofs/TwoPlankBody.lean. -/
module
public import Plank.Proofs.Body
public import Plank.Proofs.TwoPlankScalar
@[expose] public section
noncomputable section

open Set Finset Plank.Body

namespace Plank.TwoPlankBodyCS

/-- ★★ **Two planks on a convex body** ★★ — a compact convex body `K` in
a real topological vector space, two continuous affine functionals
`f 0, f 1` with windows `[lo i, hi i]` covering `K`: the relative widths
sum to at least `1`.  The realisers of §4 come from compactness, the
coordinates are the functionals normalised by their own realisers, and
the windows are clamped to `[0,1]` — a covered point stays covered
(`clamp01_le_of`) and the clamped window is no wider (`clamp01_sub_le`).
KERNEL. -/
theorem twoplank_affine {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {K : Set E} (hconv : Convex ℝ K) (hcomp : IsCompact K) (hne : K.Nonempty)
    (f : Fin 2 → (E →ᵃ[ℝ] ℝ)) (hf : ∀ i, Continuous (f i)) (lo hi : Fin 2 → ℝ)
    (hle : ∀ i, lo i ≤ hi i) (hpos : ∀ i, 0 < width K (f i))
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    1 ≤ ∑ i : Fin 2, (hi i - lo i) / width K (f i) := by
  classical
  obtain ⟨pR, hpRT, pL, hpLT, hmax0, hmin0⟩ := exists_realisers hcomp hne (hf 0)
  obtain ⟨qU, hqUT, qD, hqDT, hmax1, hmin1⟩ := exists_realisers hcomp hne (hf 1)
  have hW0 : width K (f 0) = f 0 pR - f 0 pL := width_eq_of_realisers hpRT hpLT hmax0 hmin0
  have hW1 : width K (f 1) = f 1 qU - f 1 qD := width_eq_of_realisers hqUT hqDT hmax1 hmin1
  set W0 : ℝ := f 0 pR - f 0 pL with hW0def
  set W1 : ℝ := f 1 qU - f 1 qD with hW1def
  have hW0pos : 0 < W0 := hW0 ▸ hpos 0
  have hW1pos : 0 < W1 := hW1 ▸ hpos 1
  set X : E → ℝ := fun P => (f 0 P - f 0 pL) / W0 with hXdef
  set Y : E → ℝ := fun P => (f 1 P - f 1 qD) / W1 with hYdef
  -- the coordinates are affine along segments of `K`
  have hseg : ∀ P ∈ K, ∀ Q ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ R ∈ K, X R = X P + t * (X Q - X P) ∧ Y R = Y P + t * (Y Q - Y P) := by
    intro P hP Q hQ t ht0 ht1
    refine ⟨P + t • (Q - P), hconv.add_smul_sub_mem hP hQ ⟨ht0, ht1⟩, ?_, ?_⟩
    · simp only [hXdef, map_add_smul_sub]; ring
    · simp only [hYdef, map_add_smul_sub]; ring
  -- the coordinates land in `[0,1]`, with the extremes attained
  have hX0 : ∀ P ∈ K, 0 ≤ X P := fun P hP =>
    div_nonneg (by linarith [hmin0 P hP]) hW0pos.le
  have hX1 : ∀ P ∈ K, X P ≤ 1 := fun P hP => by
    rw [hXdef, div_le_one hW0pos]; linarith [hmax0 P hP]
  have hY0 : ∀ P ∈ K, 0 ≤ Y P := fun P hP =>
    div_nonneg (by linarith [hmin1 P hP]) hW1pos.le
  have hY1 : ∀ P ∈ K, Y P ≤ 1 := fun P hP => by
    rw [hYdef, div_le_one hW1pos]; linarith [hmax1 P hP]
  have hXpL : X pL = 0 := by simp [hXdef]
  have hXpR : X pR = 1 := by rw [hXdef]; field_simp; exact hW0def.symm
  have hYqD : Y qD = 0 := by simp [hYdef]
  have hYqU : Y qU = 1 := by rw [hYdef]; field_simp; exact hW1def.symm
  -- the normalised (and then trimmed) windows
  set L0 : ℝ := (lo 0 - f 0 pL) / W0 with hL0def
  set H0 : ℝ := (hi 0 - f 0 pL) / W0 with hH0def
  set L1 : ℝ := (lo 1 - f 1 qD) / W1 with hL1def
  set H1 : ℝ := (hi 1 - f 1 qD) / W1 with hH1def
  have hL0H0 : L0 ≤ H0 := by
    rw [hL0def, hH0def, div_le_div_iff_of_pos_right hW0pos]; linarith [hle 0]
  have hL1H1 : L1 ≤ H1 := by
    rw [hL1def, hH1def, div_le_div_iff_of_pos_right hW1pos]; linarith [hle 1]
  -- the covering, in the trimmed windows
  have hcov : ∀ P ∈ K,
      (clamp01 L0 ≤ X P ∧ X P ≤ clamp01 H0) ∨
        (clamp01 L1 ≤ Y P ∧ Y P ≤ clamp01 H1) := by
    intro P hP
    obtain ⟨i, hPS⟩ := hcover P hP
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hPS
    · refine Or.inl ⟨clamp01_le_of (hX0 P hP) ?_, le_clamp01_of (hX1 P hP) ?_⟩
      · rw [hL0def, hXdef, div_le_div_iff_of_pos_right hW0pos]; linarith [hPS.1]
      · rw [hH0def, hXdef, div_le_div_iff_of_pos_right hW0pos]; linarith [hPS.2]
    · refine Or.inr ⟨clamp01_le_of (hY0 P hP) ?_, le_clamp01_of (hY1 P hP) ?_⟩
      · rw [hL1def, hYdef, div_le_div_iff_of_pos_right hW1pos]; linarith [hPS.1]
      · rw [hH1def, hYdef, div_le_div_iff_of_pos_right hW1pos]; linarith [hPS.2]
  -- ★ the normalised statement ★
  have main : 1 ≤ (clamp01 H0 - clamp01 L0) + (clamp01 H1 - clamp01 L1) :=
    twoplank_normalised hseg (clamp01_nonneg _) (clamp01_mono hL0H0)
      (clamp01_le_one _) (clamp01_nonneg _) (clamp01_mono hL1H1)
      (clamp01_le_one _) hcov hpLT hpRT hqDT hqUT hXpL hXpR hYqD hYqU
  -- trimming only shrinks, so the untrimmed relative widths are no smaller
  have e0 : (hi 0 - lo 0) / width K (f 0) = H0 - L0 := by
    rw [hW0, hH0def, hL0def, div_sub_div_same]; ring_nf
  have e1 : (hi 1 - lo 1) / width K (f 1) = H1 - L1 := by
    rw [hW1, hH1def, hL1def, div_sub_div_same]; ring_nf
  rw [Fin.sum_univ_two, e0, e1]
  linarith [clamp01_sub_le hL0H0, clamp01_sub_le hL1H1, main]

end Plank.TwoPlankBodyCS

end
