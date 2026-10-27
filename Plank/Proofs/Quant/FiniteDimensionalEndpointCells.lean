/- Shared endpoint-cell geometry and root volume. The historical declaration
namespaces are retained so existing callers use the same definitions. Supporting
affine majorants and cell-count proofs live in separate modules. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalCapWindowCore
public import Plank.Measure.LinearBandsCore
public import Plank.Measure.FiniteBandContinuity
public import Plank.Proofs.AffineWidthCore
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology Pointwise

namespace Plank.FiniteDimensionalCellSupportingAffine

open FiniteDimensionalCapWindowScaling

variable {d : ℕ}

/-- A body cut by fixed linear half-spaces whose offsets vary. Fixing a sign
pattern for the plank gaps gives precisely a family of this form. -/
def cell {ι : Type*} (K : Set (Point d)) (f : ι → (Point d) →L[ℝ] ℝ)
    (u : ι → ℝ) : Set (Point d) :=
  K ∩ ⋂ i, {x | f i x ≤ u i}

theorem isCompact_cell {ι : Type*} {K : Set (Point d)} (hK : IsCompact K)
    (f : ι → (Point d) →L[ℝ] ℝ) (u : ι → ℝ) : IsCompact (cell K f u) :=
  hK.inter_right (isClosed_iInter fun i => isClosed_le (f i).continuous continuous_const)

theorem convex_cell {ι : Type*} {K : Set (Point d)} (hK : Convex ℝ K)
    (f : ι → (Point d) →L[ℝ] ℝ) (u : ι → ℝ) : Convex ℝ (cell K f u) :=
  hK.inter (convex_iInter fun i => (convex_Iic (u i)).linear_preimage (f i).toLinearMap)

/-- Interpolated points from two cells lie in the cell at the interpolated
offsets. This is an inclusion between the actual subsets of the space. -/
theorem smul_cell_add_subset {ι : Type*} {K : Set (Point d)} (hK : Convex ℝ K)
    (f : ι → (Point d) →L[ℝ] ℝ) (u v : ι → ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • cell K f u + b • cell K f v ⊆ cell K f (a • u + b • v) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨hK hx.1 hy.1 ha hb hab, mem_iInter.mpr fun i => ?_⟩
  change f i (a • x + b • y) ≤ a * u i + b * v i
  rw [map_add, map_smul, map_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (mem_iInter.mp hx.2 i) ha)
    (mul_le_mul_of_nonneg_left (mem_iInter.mp hy.2 i) hb)

/-- The parameters for which the actual cut-out cell is nonempty form a
convex set. No positivity of an individual cell volume is assumed. -/
theorem convex_feasible {ι : Type*} {K : Set (Point d)} (hK : Convex ℝ K)
    (f : ι → (Point d) →L[ℝ] ℝ) :
    Convex ℝ {u | (cell K f u).Nonempty} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨x, hx⟩ := hu
  obtain ⟨y, hy⟩ := hv
  exact ⟨a • x + b • y, smul_cell_add_subset hK f u v a b ha hb hab
    (add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy))⟩

/-- The dimension-root of actual convex cells is concave on the feasible
offset domain. Brunn--Minkowski and the geometric inclusion are discharged
inside the proof. Degenerate nonempty cells are allowed. -/
theorem concaveOn_volumeRoot_cell {ι : Type*} {K : Set (Point d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : ι → (Point d) →L[ℝ] ℝ) :
    ConcaveOn ℝ {u | (cell K f u).Nonempty}
      (fun u => volumeRoot (cell K f u)) := by
  refine ⟨convex_feasible hconv f, ?_⟩
  intro u hu v hv a b ha hb hab
  exact (volumeRoot_smul_add (isCompact_cell hK f u) (isCompact_cell hK f v)
    hu hv a b ha hb).trans
      (volumeRoot_mono (isCompact_cell hK f _) (smul_cell_add_subset hconv f u v a b ha hb hab))

variable {κ : Type*}

/-- Compactness of the body makes the feasible offset set closed, although
the offsets themselves are unbounded. -/
theorem isClosed_feasible {K : Set (Point d)} (hK : IsCompact K)
    (f : κ → (Point d) →L[ℝ] ℝ) : IsClosed {u | (cell K f u).Nonempty} := by
  let F : (Point d) → (κ → ℝ) := fun x i => f i x
  have hset : {u | (cell K f u).Nonempty} = F '' K + Ici 0 := by
    ext u
    constructor
    · rintro ⟨x,hxK,hxu⟩
      refine ⟨F x,⟨x,hxK,rfl⟩,u-F x,?_,?_⟩
      · intro i
        exact sub_nonneg.mpr (mem_iInter.mp hxu i)
      · exact add_sub_cancel _ _
    · rintro ⟨_,⟨x,hx,rfl⟩,v,hv,rfl⟩
      refine ⟨x,hx,mem_iInter.mpr fun i => ?_⟩
      change f i x ≤ f i x+v i
      exact le_add_of_nonneg_right (hv i)
  rw [hset]
  exact isClosed_Ici.add_left_of_isCompact (hK.image (continuous_pi fun i => (f i).continuous))

end Plank.FiniteDimensionalCellSupportingAffine

namespace Plank.FiniteDimensionalEndpointMajorants

open FiniteDimensionalCellSupportingAffine FiniteDimensionalCapWindowScaling

variable {n : ℕ}

/-- The actual closed exterior cell. Nonempty null cells remain included. -/
def signCell {κ : Type*} (K : Set (Point n)) (f : κ → (Point n) →ᵃ[ℝ] ℝ)
    (p : Endpoints κ) (s : Finset κ) : Set (Point n) := by
  classical
  exact K ∩ {x | ∀ i, if i ∈ s then p.2 i ≤ f i x else f i x ≤ p.1 i}

def cutForms {κ : Type*} (f : κ → (Point n) →ᵃ[ℝ] ℝ) (s : Finset κ) :
    κ → (Point n) →L[ℝ] ℝ := by
  classical
  exact fun i => if i ∈ s then -(f i).linear.toContinuousLinearMap
    else (f i).linear.toContinuousLinearMap

def cutOffsets {κ : Type*} (f : κ → (Point n) →ᵃ[ℝ] ℝ) (p : Endpoints κ)
    (s : Finset κ) : κ → ℝ := by
  classical
  exact fun i => if i ∈ s then f i 0-p.2 i else p.1 i-f i 0

def cutLinear {κ : Type*} (s : Finset κ) : Endpoints κ →ₗ[ℝ] (κ → ℝ) := by
  classical
  exact {
    toFun := fun z i => if i ∈ s then -z.2 i else z.1 i
    map_add' := by
      intro x y
      ext i
      by_cases hi : i ∈ s <;> simp [hi,add_comm]
    map_smul' := by
      intro a x
      ext i
      by_cases hi : i ∈ s <;> simp [hi]
  }

theorem signCell_eq_cell {κ : Type*} (K : Set (Point n)) (f : κ → (Point n) →ᵃ[ℝ] ℝ)
    (p : Endpoints κ) (s : Finset κ) :
    signCell K f p s = cell K (cutForms f s) (cutOffsets f p s) := by
  classical
  ext x
  simp only [signCell, cell, mem_inter_iff, mem_ofPred_eq, mem_iInter]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  have he : f i x = (f i).linear x+f i 0 := congrFun (f i).decomp x
  by_cases hi : i ∈ s
  · simp only [hi, ite_eq_left, cutForms, cutOffsets, neg_apply,
      LinearMap.coe_toContinuousLinearMap']
    constructor <;> intro h <;> linarith
  · simp only [hi, ite_false, cutForms, cutOffsets, LinearMap.coe_toContinuousLinearMap']
    constructor <;> intro h <;> linarith

theorem cutOffsets_sub {κ : Type*} (f : κ → (Point n) →ᵃ[ℝ] ℝ) (s : Finset κ)
    (p e : Endpoints κ) :
    cutOffsets f e s-cutOffsets f p s = cutLinear s (e-p) := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [cutOffsets,cutLinear,hi]

theorem cutOffsets_motion {κ : Type*} (f : κ → (Point n) →ᵃ[ℝ] ℝ) (s : Finset κ)
    (p z : Endpoints κ) (t : ℝ) :
    cutOffsets f (p+t • z) s = cutOffsets f p s+t • cutLinear s z := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [cutOffsets,cutLinear,hi]
  all_goals ring

theorem cutForms_ne_zero {κ : Type*} (f : κ → (Point n) →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (s : Finset κ) : ∀ i, cutForms f s i ≠ 0 := by
  classical
  intro i
  have h : (f i).linear.toContinuousLinearMap ≠ 0 := by
    intro he
    exact hf i (congrArg ContinuousLinearMap.toLinearMap he)
  by_cases hi : i ∈ s <;> simpa [cutForms,hi] using h

end Plank.FiniteDimensionalEndpointMajorants

namespace Plank.FiniteDimensionalFewCellScaling

open FiniteDimensionalCellSupportingAffine FiniteDimensionalEndpointMajorants
  FiniteDimensionalCapWindowScaling

variable {n m : ℕ}

def budgetLinear (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) :
    Endpoints (Fin m) →ₗ[ℝ] ℝ :=
  ∑ i, (Body.width K (f i))⁻¹ • ((LinearMap.proj i).comp
    (LinearMap.snd ℝ (Fin m → ℝ) (Fin m → ℝ)-LinearMap.fst ℝ _ _))

@[simp] theorem budgetLinear_apply (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ)
    (p : Endpoints (Fin m)) : budgetLinear K f p = budget K f p := by
  simp [budgetLinear,budget,div_eq_mul_inv,mul_comm]

/-- Actual uncovered volume is continuous on the entire endpoint space. -/
theorem continuous_gapVolume {K : Set (Point n)} (hK : IsCompact K)
    (hne : K.Nonempty) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < Body.width K (f i)) : Continuous (gapVolume K f) :=
  FiniteBandContinuity.continuous_area_uncovered volume hK.measurableSet
    hK.measure_ne_top (fun i => (continuous_form (f i)).measurable)
    (fun i c => measure_level_zero (f i) (Body.linear_ne_zero_of_width_pos hne (f i) (hW i)) c)

theorem isCompact_signCell {κ : Type*} {K : Set (Point n)} (hK : IsCompact K)
    (f : κ → (Point n) →ᵃ[ℝ] ℝ) (p : Endpoints κ) (s : Finset κ) :
    IsCompact (signCell K f p s) := by
  rw [signCell_eq_cell]
  exact isCompact_cell hK _ _

/-- A finite family of closed bands leaves exactly its strict exterior cells. -/
theorem gap_eq_iUnion_strictCells {κ : Type*} [Fintype κ]
    (K : Set (Point n)) (f : κ → (Point n) →ᵃ[ℝ] ℝ)
    (lo hi : κ → ℝ) :
    K \ ⋃ i, LinearBands.closedBand (f i) (lo i) (hi i) =
      ⋃ s : Finset κ, K ∩ LinearBands.strictCell (fun i x => f i x) lo hi s := by
  classical
  ext x
  constructor
  · intro hx
    let s := Finset.univ.filter (fun i => hi i < f i x)
    refine mem_iUnion.mpr ⟨s, hx.1, ?_⟩
    intro i
    by_cases hhi : hi i < f i x
    · simp [s, hhi]
    · have hlo : f i x < lo i := by
        apply lt_of_not_ge
        intro h
        exact hx.2 (mem_iUnion.mpr ⟨i, h, le_of_not_gt hhi⟩)
      simpa [s, hhi] using hlo
  · intro hx
    obtain ⟨s, hK, hs⟩ := mem_iUnion.mp hx
    exact ⟨hK, LinearBands.strictCell_subset_gap _ lo hi s hs⟩

/-- Closing the sides of one cell does not change its volume. This remains true
when some plank widths vanish and when two normals coincide. -/
theorem measure_strict_eq_signCell {κ : Type*} [Countable κ]
    (K : Set (Point n)) (f : κ → (Point n) →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (lo hi : κ → ℝ) (s : Finset κ) :
    volume (K ∩ LinearBands.strictCell (fun i x => f i x) lo hi s) =
      volume (signCell K f (lo,hi) s) := by
  classical
  apply measure_congr
  have hae : ∀ᵐ x ∂volume, ∀ i, f i x ≠ lo i ∧ f i x ≠ hi i := by
    refine ae_all_iff.mpr fun i => ?_
    apply Filter.Eventually.and
    · simpa only [ae_iff, not_not] using measure_level_zero (f i) (hf i) (lo i)
    · simpa only [ae_iff, not_not] using measure_level_zero (f i) (hf i) (hi i)
  filter_upwards [hae] with x hx
  apply propext
  simp only [signCell, LinearBands.strictCell, mem_inter_iff, mem_ofPred_eq]
  apply and_congr_right
  intro _
  refine forall_congr' fun i => ?_
  by_cases hs : i ∈ s <;> simp only [hs, ↓reduceIte]
  · exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (hx i).2.symm⟩
  · exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (hx i).1⟩

/-- The sum of actual closed-cell volumes is exactly the uncovered volume.
Disjointness is proved for the strict cells; null affine levels justify closing
them even for zero-width planks. -/
theorem measure_gap_eq_sum_signCells {κ : Type*} [Fintype κ]
    {K : Set (Point n)} (hK : MeasurableSet K)
    (f : κ → (Point n) →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : κ → ℝ) (hwidth : ∀ i, lo i ≤ hi i) :
    volume (K \ ⋃ i, LinearBands.closedBand (f i) (lo i) (hi i)) =
      ∑ s : Finset κ, volume (signCell K f (lo,hi) s) := by
  classical
  have hdis : Pairwise (fun s t : Finset κ => Disjoint
      (K ∩ LinearBands.strictCell (fun i x => f i x) lo hi s)
      (K ∩ LinearBands.strictCell (fun i x => f i x) lo hi t)) := by
    intro s t hst
    exact (LinearBands.disjoint_strictCells (fun i x => f i x) lo hi hwidth hst).mono
      inter_subset_right inter_subset_right
  rw [gap_eq_iUnion_strictCells, measure_iUnion hdis, tsum_fintype]
  · exact Finset.sum_congr rfl fun s _ => measure_strict_eq_signCell K f hf lo hi s
  · intro s
    exact hK.inter (LinearBands.measurableSet_strictCell _
      (fun i => (continuous_form (f i)).measurable) lo hi s)

theorem gap_eq_sum {K : Set (Point n)} (hK : IsCompact K)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (p : Endpoints (Fin m)) (ho : ∀ i, p.1 i ≤ p.2 i) :
    gapVolume K f p = ∑ s, (volume (signCell K f p s)).toReal := by
  have heq := measure_gap_eq_sum_signCells hK.measurableSet f hf p.1 p.2 ho
  exact (congrArg ENNReal.toReal heq).trans (ENNReal.toReal_sum
    (fun s _ => (isCompact_signCell hK f p s).measure_ne_top))

def region (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ)
    (C : Finset (Finset (Fin m))) : Set (Endpoints (Fin m)) :=
  {e | ∀ s, s ∉ C → signCell K f e s = ∅}

theorem isOpen_region {K : Set (Point n)} (hK : IsCompact K)
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (C : Finset (Finset (Fin m))) :
    IsOpen (region K f C) := by
  have hs (s : Finset (Fin m)) : IsOpen {e : Endpoints (Fin m) | signCell K f e s = ∅} := by
    have hcont : Continuous (fun e : Endpoints (Fin m) => cutOffsets f e s) := by
      classical
      apply continuous_pi
      intro i
      by_cases hi : i ∈ s <;> simp only [cutOffsets,hi,ite_true,ite_false] <;> fun_prop
    have hh : IsClosed {e : Endpoints (Fin m) | (signCell K f e s).Nonempty} := by
      simp_rw [signCell_eq_cell]
      exact (isClosed_feasible hK (cutForms f s)).preimage hcont
    convert hh.isOpen_compl using 1
    ext e
    exact not_nonempty_iff_eq_empty.symm
  change IsOpen {e | ∀ s, s ∉ C → signCell K f e s = ∅}
  simpa only [ofPred_forall] using isOpen_iInter_of_finite (fun s =>
    isOpen_iInter_of_finite (fun _ : s ∉ C => hs s))

end Plank.FiniteDimensionalFewCellScaling

namespace Plank.FiniteDimensionalMinimumCellRank

open FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling

variable {n m : ℕ}

/-- Every nonempty closed exterior cell is counted, including null cells. -/
def nonemptyCells (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ)
    (p : Endpoints (Fin m)) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter (fun s => (signCell K f p s).Nonempty)

/-- The normalized dimension-root of the actual uncovered volume. -/
def gapRoot (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ)
    (p : Endpoints (Fin m)) : ℝ :=
  (gapVolume K f p / (volume K).toReal) ^ (((n+1 : ℕ) : ℝ)⁻¹)

/-- The root quantity minimized while keeping the body and directions fixed. -/
def rootCost (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ)
    (p : Endpoints (Fin m)) : ℝ := gapRoot K f p + budget K f p

/-- The uncovered-volume contribution is nonnegative. -/
theorem budget_le_rootCost (K : Set (Point n))
    (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin m)) :
    budget K f p ≤ rootCost K f p :=
  le_add_of_nonneg_left (Real.rpow_nonneg
    (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) _)

theorem continuous_rootCost {K : Set (Point n)} (hK : IsCompact K)
    (hne : K.Nonempty) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < Body.width K (f i)) : Continuous (rootCost K f) := by
  have hR : Continuous (budget K f) := by unfold budget; fun_prop
  exact ((Real.continuous_rpow_const (by positivity :
      0 ≤ (((n+1 : ℕ) : ℝ)⁻¹))).comp
    ((continuous_gapVolume hK hne f hW).div_const _)).add hR

end Plank.FiniteDimensionalMinimumCellRank

namespace Plank.FiniteDimensionalMinimumContactRank

open FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling FiniteDimensionalMinimumCellRank

variable {n m : ℕ}

theorem rootCost_eq_budget_of_gap_eq_zero {K : Set (Point n)}
    {f : Fin m → (Point n) →ᵃ[ℝ] ℝ} {p : Endpoints (Fin m)}
    (hzero : gapVolume K f p = 0) : rootCost K f p = budget K f p := by
  unfold rootCost gapRoot
  rw [hzero,zero_div,Real.zero_rpow (by positivity :
    (((n+1 : ℕ) : ℝ)⁻¹) ≠ 0),zero_add]

end Plank.FiniteDimensionalMinimumContactRank
