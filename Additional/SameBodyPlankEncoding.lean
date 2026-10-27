/- Body-preserving version of FinitePlankNormalization.exists_data_le.
The existing encoding proof already constructs the equality of bodies;
this adapter retains that equality in its conclusion. -/
module

public import FinitePlankNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SameBodyPlankEncoding

open Set Metric MeasureTheory NormalizedPlankBodyMinimum FinitePlankNormalization
open PrunedPlankCounterexample (covered)
open PlanarNormalization (clip clip_bounds monotone_clip clip_sub_le)
open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem exists_data_le {r R : ℝ} (hr : 0<r)
    (K : Body (E := E) r R) (f : ι → E →ᵃ[ℝ] ℝ) (a b : ι → ℝ)
    (horder : ∀ i,a i≤b i) (hW : ∀ i,0<Plank.Body.width (K.1 : Set E) (f i))
    (d : ℕ) {B : ℝ} (hbudget : PrunedPlankCounterexample.budget (K.1 : Set E) f a b≤B) :
    ∃ q : Data (E := E) (ι := ι) r R, q.1=K ∧ q∈domain B ∧
      margin μ d B q≤GlobalPlankBodyMinimum.margin μ (K.1 : Set E) f a b d B := by
  choose g c happly hnorm hunit hg using fun i => exists_unit_form
    K.1.isCompact K.1.nonempty (f i) (hW i)
  let p : Endpoints (ι := ι) :=
    (fun i => (a i-c i)/Plank.Body.width (K.1 : Set E) (f i),
     fun i => (b i-c i)/Plank.Body.width (K.1 : Set E) (f i))
  have ho (i) : p.1 i≤p.2 i :=
    (div_le_div_iff_of_pos_right (hW i)).mpr (sub_le_sub_right (horder i) _)
  have hcost : total p=PrunedPlankCounterexample.budget (K.1 : Set E) f a b := by
    unfold total PrunedPlankCounterexample.budget
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [p]
    ring
  have hset : covered g p.1 p.2=covered f a b := by
    ext x
    simp only [covered,mem_iUnion,mem_ofPred_eq]
    apply exists_congr
    intro i
    rw [happly]
    dsimp only [p]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  let pc : Endpoints (ι := ι) := (fun i => clip (p.1 i),fun i => clip (p.2 i))
  obtain ⟨q,hqK,hqp,hgap⟩ := encode_unit_data μ hr K g hunit hnorm pc
  have hle : total q.2.2≤PrunedPlankCounterexample.budget (K.1 : Set E) f a b := by
    rw [hqp,← hcost]
    exact Finset.sum_le_sum (fun i _ => clip_sub_le (ho i))
  have hgapeq : gap μ q=μ.real ((K.1 : Set E)\covered f a b) := by
    rw [hgap,gap_clip μ (K.1 : Set E) g hg hnorm p,hset]
  refine ⟨q,hqK,⟨mem_univ _,mem_univ _,?_,hle.trans hbudget⟩,?_⟩
  · rw [hqp]
    intro i
    exact ⟨(clip_bounds (p.1 i)).1,monotone_clip (ho i),(clip_bounds (p.2 i)).2⟩
  · have hp := pow_le_pow_left₀ (sub_nonneg.mpr hbudget) (sub_le_sub_left hle B) d
    unfold margin GlobalPlankBodyMinimum.margin
    rw [hgapeq]
    have he : (body q : Set E)=(K.1 : Set E) := by unfold body; rw [hqK]
    rw [he]
    exact sub_le_sub_left hp _


end Plank.SameBodyPlankEncoding
