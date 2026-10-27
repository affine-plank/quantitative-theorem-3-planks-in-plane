/- Physical affine planks become compact normalized parameters without
increasing the quantitative margin. Clipping preserves the actual gap area. -/
module

public import NormalizedPlankBodyMinimum
public import Plank.Proofs.Quant.PlanarNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PhysicalPlankNormalization

open Set Metric MeasureTheory
open NormalizedPlankBodyMinimum
open scoped BigOperators

def directionForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Direction (E := E)) : E →ᵃ[ℝ] ℝ := u.1.toLinearMap.toAffineMap

/-- A unit-range affine observable is the support-normalization of an actual
unit continuous-linear-functional direction. -/
theorem exists_direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (g : E →ᵃ[ℝ] ℝ) (hW : Plank.Body.width K g = 1)
    (hbounds : ∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1) :
    ∃ u : Direction (E := E), ∀ x,
      g x = (directionForm u x-sInf (directionForm u '' K))/Plank.Body.width K (directionForm u) := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Plank.Body.exists_realisers hK hne g.continuous_of_finiteDimensional
  have hw := Plank.Body.width_eq_of_realisers ha hb hmax hmin
  have hga : g a = 1 := by linarith only [hw,hW,(hbounds a ha).2,(hbounds b hb).1]
  have hgb : g b = 0 := by linarith only [hw,hW,(hbounds a ha).2,(hbounds b hb).1]
  let L := g.linear.toContinuousLinearMap
  have hL : L ≠ 0 := by
    intro hz
    have he := congrArg (fun f : E →L[ℝ] ℝ => f (a-b)) hz
    change g.linear (a -ᵥ b)=0 at he
    rw [g.linearMap_vsub a b,hga,hgb] at he
    norm_num at he
  let n : ℝ := ‖L‖
  have hn : 0<n := norm_pos_iff.mpr hL
  let u : Direction (E := E) := ⟨n⁻¹ • L,by
    rw [mem_sphere_zero_iff_norm,norm_smul]
    change |n⁻¹| * n=1
    rw [abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']⟩
  have hu (x : E) : directionForm u x = (g x-g 0)/n := by
    have he := congrFun g.decomp x
    change g x=g.linear x+g 0 at he
    change n⁻¹*g.linear x=(g x-g 0)/n
    rw [he]
    ring
  have hmaxu : ∀ x ∈ K, directionForm u x ≤ directionForm u a := by
    intro x hx; rw [hu,hu]
    exact (div_le_div_iff_of_pos_right hn).mpr (sub_le_sub_right (hmax x hx) _)
  have hminu : ∀ x ∈ K, directionForm u b ≤ directionForm u x := by
    intro x hx; rw [hu,hu]
    exact (div_le_div_iff_of_pos_right hn).mpr (sub_le_sub_right (hmin x hx) _)
  have hlo : sInf (directionForm u '' K)=directionForm u b :=
    (show IsLeast (directionForm u '' K) (directionForm u b) from
      ⟨⟨b,hb,rfl⟩,by rintro _ ⟨x,hx,rfl⟩; exact hminu x hx⟩).csInf_eq
  have hwu : Plank.Body.width K (directionForm u)=1/n := by
    rw [Plank.Body.width_eq_of_realisers ha hb hmaxu hminu,hu,hu,hga,hgb]
    ring
  refine ⟨u,fun x => ?_⟩
  rw [hlo,hwu,hu,hu,hgb]
  field_simp [hn.ne']
  ring

open PlanarQuantitative

/-- Encode unit-range data on a normalized body using the actual compact
parameter domain. This keeps the endpoint vector and actual gap area. -/
theorem encode_unit_data {m : ℕ} {r R : ℝ} (hr : 0<r)
    (K : Body (E := Point) r R) (g : Fin m → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, Plank.Body.width (K.1 : Set Point) (g i)=1)
    (hbounds : ∀ i x, x ∈ (K.1 : Set Point) → 0≤g i x ∧ g i x≤1)
    (p : PlanarParameterDomain.Endpoints m) :
    ∃ q : Data (E := Point) (ι := Fin m) r R,
      q.1=K ∧ q.2.2=p ∧ gap volume q=PlanarParameterDomain.gapArea (K.1 : Set Point) g p := by
  choose u hu using fun i => exists_direction K.1.isCompact K.1.nonempty (g i) (hW i) (hbounds i)
  let q : Data (E := Point) (ι := Fin m) r R := (K,u,p)
  have he (i : Fin m) (x : Point) : g i x=(form q i x-lower q i)/span q i := hu i x
  have hband (i : Fin m) (x : Point) :
      (lo q i ≤ form q i x ∧ form q i x ≤ hi q i) ↔ (p.1 i ≤ g i x ∧ g i x ≤ p.2 i) := by
    rw [he]
    have hw := span_pos volume hr q i
    rw [le_div_iff₀ hw,div_le_iff₀ hw]
    change (lower q i+p.1 i*span q i ≤ form q i x ∧
      form q i x ≤ lower q i+p.2 i*span q i) ↔ _
    constructor <;> rintro ⟨hl,hh⟩ <;> constructor <;> linarith only [hl,hh]
  have hset : (⋃ i, {x | lo q i≤form q i x ∧ form q i x≤hi q i})=
      ⋃ i, {x | p.1 i≤g i x ∧ g i x≤p.2 i} := by
    ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    exact exists_congr (fun i => hband i x)
  refine ⟨q,rfl,rfl,?_⟩
  change volume.real ((K.1 : Set Point) \ ⋃ i, {x | lo q i≤form q i x ∧ form q i x≤hi q i})=
    volume.real ((K.1 : Set Point) \ ⋃ i, {x | p.1 i≤g i x ∧ g i x≤p.2 i})
  rw [hset]

/-- Clamping the actual support-normalized windows gives a representative
with no greater margin at the same fixed budget and natural exponent. -/
theorem exists_data_le {m : ℕ} {r R : ℝ} (hr : 0<r)
    (K : Body (E := Point) r R) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (a b : Fin m → ℝ) (horder : ∀ i, a i≤b i)
    (hW : ∀ i, 0<Plank.Body.width (K.1 : Set Point) (f i))
    (d : ℕ) {B : ℝ} (hbudget : PrunedPlankCounterexample.budget (K.1 : Set Point) f a b≤B) :
    ∃ q : Data (E := Point) (ι := Fin m) r R, q ∈ domain B ∧
      margin volume d B q ≤ GlobalPlankBodyMinimum.margin volume (K.1 : Set Point) f a b d B := by
  obtain ⟨g,p,hunit,hnorm,hordered,hcost,hgap⟩ :=
    PlanarNormalization.normalize_data K.1.isCompact K.1.nonempty f a b horder hW
  have hgW (i) : 0<Plank.Body.width (K.1 : Set Point) (g i) := by
    have hu : Plank.Body.width (K.1 : Set Point) (g i)=1 := hunit i
    rw [hu]; norm_num
  let pc := PlanarNormalization.clipEndpoints p
  obtain ⟨q,hqK,hqp,hqgap⟩ := encode_unit_data hr K g hunit hnorm pc
  have htotal : total q.2.2=PlanarParameterDomain.budget (K.1 : Set Point) g pc := by
    rw [hqp]
    simp only [total,PlanarParameterDomain.budget,hunit,div_one]
  have hle : total q.2.2≤PrunedPlankCounterexample.budget (K.1 : Set Point) f a b := by
    rw [htotal]
    exact (PlanarNormalization.budget_clip_le g hgW p hordered).trans_eq hcost
  have hg : gap volume q=PlanarParameterDomain.gapArea (K.1 : Set Point) f (a,b) := by
    rw [hqgap,PlanarNormalization.gapArea_clip K.1.nonempty g hgW hnorm p,hgap]
  refine ⟨q,⟨mem_univ _,mem_univ _,?_,hle.trans hbudget⟩,?_⟩
  · rw [hqp]
    intro i
    exact ⟨(PlanarNormalization.clip_bounds (p.1 i)).1,
      PlanarNormalization.monotone_clip (hordered i),
      (PlanarNormalization.clip_bounds (p.2 i)).2⟩
  · have hp := pow_le_pow_left₀ (sub_nonneg.mpr hbudget) (sub_le_sub_left hle B) d
    unfold margin GlobalPlankBodyMinimum.margin
    rw [hg]
    have he : (body q : Set Point)=(K.1 : Set Point) := by unfold body; rw [hqK]
    rw [he]
    exact sub_le_sub_left hp _

end Plank.PhysicalPlankNormalization
