/- First moments distinguish two finite translation partitions of the same core. -/
module
public import Plank.Proofs.Quant.TranslationEquality
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TranslationMomentRigidity
open Set MeasureTheory Function
open scoped BigOperators

theorem translated_first_moment (A : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hfin : volume A ≠ ⊤) (hf : IntegrableOn (fun z : ℝ × ℝ => z.1) A) (v : ℝ × ℝ) :
    (∫ z in (fun z => z+v) ⁻¹' A, z.1) =
      (∫ z in A, z.1)-v.1*(volume A).toReal := by
  have hm := hA.preimage (measurable_add_const v)
  calc
    (∫ z in (fun z => z+v) ⁻¹' A, z.1) =
        ∫ z, A.indicator (fun z => z.1-v.1) (z+v) := by
      rw [← integral_indicator hm]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        by_cases hz : z+v ∈ A <;> simp [Set.indicator,hz,Prod.fst_add])
    _ = ∫ z, A.indicator (fun z => z.1-v.1) z := integral_add_right_eq_self _ v
    _ = ∫ z in A, z.1-v.1 := integral_indicator hA
    _ = (∫ z in A, z.1)-v.1*(volume A).toReal := by
      rw [integral_sub hf (integrableOn_const hfin),setIntegral_const]
      simp only [Measure.real,smul_eq_mul,mul_comm]

/-- First-moment identity for a finite almost-everywhere partition of a core
by inverse translates of fixed actual target pieces. -/
theorem partition_first_moment {ι : Type*} [Fintype ι]
    (core : Set (ℝ × ℝ)) (A : ι → Set (ℝ × ℝ)) (v : ι → ℝ × ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, volume (A i) ≠ ⊤)
    (hf : ∀ i, IntegrableOn (fun z : ℝ × ℝ => z.1) (A i))
    (hcore : IntegrableOn (fun z : ℝ × ℝ => z.1) core)
    (hdis : Pairwise (AEDisjoint volume on fun i => (fun z => z+v i) ⁻¹' A i))
    (hcover : (⋃ i, (fun z => z+v i) ⁻¹' A i) =ᵐ[volume] core) :
    (∫ z in core, z.1) = ∑ i, ((∫ z in A i, z.1)-(v i).1*(volume (A i)).toReal) := by
  calc
    (∫ z in core, z.1) = ∫ z in ⋃ i, (fun z => z+v i) ⁻¹' A i, z.1 :=
      (setIntegral_congr_set hcover).symm
    _ = ∑ i, ∫ z in (fun z => z+v i) ⁻¹' A i, z.1 := by
      rw [integral_iUnion_ae (fun i => (hA i |>.preimage (measurable_add_const _)).nullMeasurableSet)
        hdis (hcore.congr_set_ae hcover),tsum_fintype]
    _ = _ := Finset.sum_congr rfl (fun i _ => translated_first_moment (A i) (hA i) (hfin i) (hf i) (v i))

/-- If a second sharp translation partition moves every target at least as
far horizontally, each piece moved strictly farther has zero actual area. -/
theorem null_of_increased_step {ι : Type*} [Fintype ι]
    (core : Set (ℝ × ℝ)) (A : ι → Set (ℝ × ℝ)) (v w : ι → ℝ × ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, volume (A i) ≠ ⊤)
    (hf : ∀ i, IntegrableOn (fun z : ℝ × ℝ => z.1) (A i))
    (hcore : IntegrableOn (fun z : ℝ × ℝ => z.1) core)
    (hdv : Pairwise (AEDisjoint volume on fun i => (fun z => z+v i) ⁻¹' A i))
    (hcv : (⋃ i, (fun z => z+v i) ⁻¹' A i) =ᵐ[volume] core)
    (hdw : Pairwise (AEDisjoint volume on fun i => (fun z => z+w i) ⁻¹' A i))
    (hcw : (⋃ i, (fun z => z+w i) ⁻¹' A i) =ᵐ[volume] core)
    (hle : ∀ i, (v i).1 ≤ (w i).1) (j : ι) (hlt : (v j).1 < (w j).1) :
    volume (A j)=0 := by
  have hv := partition_first_moment core A v hA hfin hf hcore hdv hcv
  have hw := partition_first_moment core A w hA hfin hf hcore hdw hcw
  have hs : (∑ i, ((w i).1-(v i).1)*(volume (A i)).toReal)=0 := by
    calc
      _ = (∑ i, ((∫ z in A i, z.1)-(v i).1*(volume (A i)).toReal))-
          ∑ i, ((∫ z in A i, z.1)-(w i).1*(volume (A i)).toReal) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := sub_eq_zero.mpr (hv.symm.trans hw)
  have hn (i) : 0 ≤ ((w i).1-(v i).1)*(volume (A i)).toReal :=
    mul_nonneg (sub_nonneg.mpr (hle i)) ENNReal.toReal_nonneg
  have hj := Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ j)
  rw [hs] at hj
  have hz := (mul_eq_zero.mp (le_antisymm hj (hn j))).resolve_left (ne_of_gt (sub_pos.mpr hlt))
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (hfin j)

end Quant.TranslationMomentRigidity

/-- info: 'Quant.TranslationMomentRigidity.null_of_increased_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TranslationMomentRigidity.null_of_increased_step
