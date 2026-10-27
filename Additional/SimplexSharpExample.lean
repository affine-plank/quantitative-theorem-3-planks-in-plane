/- Actual nonparallel equality covers on a coordinate simplex in every finite
positive dimension. The common-minimum bound supplies one side of equality. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalCommonMinimum
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SimplexSharpExample

open Set MeasureTheory
open scoped Pointwise

variable (ι : Type*) [Fintype ι]

def body : Set (ι → ℝ) := {x | (∀i,0≤x i) ∧ ∑i,x i≤1}

def coordinate (i : ι) : (ι → ℝ) →ᵃ[ℝ] ℝ := (LinearMap.proj i).toAffineMap

omit [Fintype ι] in
@[simp] theorem coordinate_apply (i : ι) (x : ι → ℝ) : coordinate ι i x=x i := rfl

theorem zero_mem : (0 : ι → ℝ)∈body ι := by simp [body]

theorem single_mem [DecidableEq ι] (i : ι) : Pi.single i (1 : ℝ)∈body ι := by
  classical
  constructor
  · intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp

theorem coordinate_le_one {x : ι → ℝ} (hx : x∈body ι) (i : ι) : x i≤1 :=
  (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

theorem compact_body : IsCompact (body ι) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : ι → ℝ) (fun _ => 1))).of_isClosed_subset
  · change IsClosed ({x : ι → ℝ | ∀i,0≤x i} ∩ {x | ∑i,x i≤1})
    apply IsClosed.inter
    · rw [Set.ofPred_forall]
      exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
    · exact isClosed_le (by fun_prop) continuous_const
  · intro x hx
    exact ⟨hx.1,fun i => coordinate_le_one ι hx i⟩

theorem convex_body : Convex ℝ (body ι) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      ←Finset.mul_sum]
    nlinarith only [hab,mul_nonneg ha (sub_nonneg.mpr hx.2),mul_nonneg hb (sub_nonneg.mpr hy.2)]

@[simp] theorem width_coordinate (i : ι) : Body.width (body ι) (coordinate ι i)=1 := by
  classical
  have h := Body.width_eq_of_realisers (f := coordinate ι i)
    (single_mem ι i) (zero_mem ι)
    (fun x hx => by simpa using coordinate_le_one ι hx i)
    (fun x hx => hx.1 i)
  simpa using h

omit [Fintype ι] in
/-- Distinct coordinate planks have nonproportional linear parts. -/
theorem directions_nonproportional {i j : ι} (hij : i≠j) (c : ℝ) :
    (coordinate ι i).linear≠c • (coordinate ι j).linear := by
  classical
  intro he
  have h := LinearMap.congr_fun he (Pi.single i (1 : ℝ))
  simp [coordinate,hij.symm] at h

variable (μ : Measure (ι → ℝ)) [μ.IsAddHaarMeasure]

theorem volume_pos : 0<μ.real (body ι) := by
  let U : Set (ι → ℝ) := {x | (∀i,0<x i) ∧ ∑i,x i<1}
  have hu : IsOpen U := by
    change IsOpen ({x : ι → ℝ | ∀i,0<x i} ∩ {x | ∑i,x i<1})
    apply IsOpen.inter
    · rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
    · exact isOpen_lt (by fun_prop) continuous_const
  have hc : 0<(Fintype.card ι:ℝ)+1 := by positivity
  have hne : U.Nonempty := by
    refine ⟨fun _ => 1/((Fintype.card ι:ℝ)+1),fun _ => one_div_pos.mpr hc,?_⟩
    simpa [div_eq_mul_inv] using
      (div_lt_one hc).mpr (by linarith : (Fintype.card ι:ℝ)<(Fintype.card ι:ℝ)+1)
  have hsub : U⊆body ι := fun x hx => ⟨fun i => (hx.1 i).le,hx.2.le⟩
  exact ENNReal.toReal_pos ((hu.measure_pos μ hne).trans_le (measure_mono hsub)).ne'
    (compact_body ι).measure_ne_top

def contracted (r : ι → ℝ) (s : ℝ) : Set (ι → ℝ) :=
  (fun y => r+s • y) '' body ι

/-- Coordinate lower bounds and one sum bound identify the contracted simplex. -/
theorem mem_contracted (r : ι → ℝ) {s : ℝ} (hs : 0<s) {x : ι → ℝ}
    (hl : ∀i,r i≤x i) (hu : (∑i,x i)≤(∑i,r i)+s) : x∈contracted ι r s := by
  let y : ι → ℝ := fun i => (x i-r i)/s
  have hy : y∈body ι := by
    constructor
    · intro i
      exact div_nonneg (sub_nonneg.mpr (hl i)) hs.le
    · dsimp [y]
      rw [←Finset.sum_div,Finset.sum_sub_distrib]
      apply (div_le_one hs).mpr
      linarith only [hu]
  refine ⟨y,hy,?_⟩
  ext i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,y]
  rw [mul_div_cancel₀ _ hs.ne']
  ring

/-- The actual uncovered set lies in a translated contracted simplex. -/
theorem gap_subset_contracted (r : ι → ℝ) (hR : (∑i,r i)<1) :
    body ι\⋃i,LinearBands.closedBand (coordinate ι i) 0 (r i)⊆
      contracted ι r (1-∑i,r i) := by
  intro x hx
  apply mem_contracted ι r (sub_pos.mpr hR)
  · intro i
    apply le_of_lt
    apply lt_of_not_ge
    intro hi
    exact hx.2 (mem_iUnion.mpr ⟨i,hx.1.1 i,hi⟩)
  · simpa using hx.1.2

theorem contracted_volume (r : ι → ℝ) (s : ℝ) (hs : 0≤s) :
    μ.real (contracted ι r s)=s^Fintype.card ι*μ.real (body ι) := by
  have ht : contracted ι r s=(fun x => x+ -r) ⁻¹' (s • body ι) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change r+s • y+ -r∈s • body ι
      have h : r+s • y+ -r=s • y := by abel
      rw [h]
      exact ⟨y,hy,rfl⟩
    · intro hx
      obtain ⟨y,hy,he⟩ := hx
      refine ⟨y,hy,?_⟩
      change s • y=x+ -r at he
      change r+s • y=x
      rw [he]
      abel
  change (μ (contracted ι r s)).toReal=_
  rw [ht,measure_preimage_add_right,μ.addHaar_smul_of_nonneg hs,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hs _)]
  simp [Measure.real]

/-- Exact measured equality, with actual planks and actual body widths. -/
theorem gap_eq [Nonempty ι] (r : ι → ℝ) (hr : ∀i,0≤r i) (hR : (∑i,r i)<1) :
    μ.real (body ι\⋃i,LinearBands.closedBand (coordinate ι i) 0 (r i))=
      (1-∑i,r i)^Fintype.card ι*μ.real (body ι) := by
  have hc : IsCompact (contracted ι r (1-∑i,r i)) := (compact_body ι).image (by fun_prop)
  have hf : μ (contracted ι r (1-∑i,r i))≠⊤ := hc.measure_ne_top
  have hup := ENNReal.toReal_mono hf
    (measure_mono (gap_subset_contracted ι r hR))
  change μ.real _≤μ.real _ at hup
  rw [contracted_volume ι μ r (1-∑i,r i) (sub_pos.mpr hR).le] at hup
  have hlo := FiniteDimensionalCommonMinimum.uncovered_volume_lower_bound μ
    (compact_body ι) (convex_body ι) (coordinate ι) 0 (zero_mem ι)
    (fun i x hx => hx.1 i) (fun _ => 0) r hr (fun i => by simp)
  apply le_antisymm hup
  simpa [Measure.real,max_eq_right (sub_pos.mpr hR).le] using hlo

end Plank.SimplexSharpExample
