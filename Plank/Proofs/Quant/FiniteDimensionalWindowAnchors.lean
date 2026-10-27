/- Elementary homotheties and separate canonical anchors for intersections. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalWindowData
public import ResearchFormalized.Convex.OrthantWitnesses
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalIntersectionCentering
open Set MeasureTheory FiniteDimensionalCapWindowScaling
variable {d : ℕ}

theorem form_homothety (f : Point d →ᵃ[ℝ] ℝ) (z : Point d) (t : ℝ) (x : Point d) :
    f (AffineMap.homothety z t x) = (1-t)*f z+t*f x := by
  rw [AffineMap.homothety_eq_lineMap]
  simpa only [AffineMap.lineMap_apply_ring] using f.apply_lineMap z x t

theorem volume_homothety (A : Set (Point d)) (z : Point d) {t : ℝ} (ht : 0 ≤ t) :
    (volume (AffineMap.homothety z t '' A)).toReal = t^(d+1)*(volume A).toReal := by
  rw [volume.addHaar_image_homothety, ENNReal.toReal_mul]
  simp only [Module.finrank_pi, Fintype.card_fin]
  rw [abs_of_nonneg (pow_nonneg ht _), ENNReal.toReal_ofReal (pow_nonneg ht _)]

end Plank.FiniteDimensionalIntersectionCentering

namespace Plank.FiniteDimensionalPairAnchors
open Set MeasureTheory FiniteDimensionalCapWindowScaling FiniteDimensionalWindowFamily
open FiniteDimensionalIntersectionCentering (form_homothety volume_homothety)
attribute [local instance] Classical.propDecidable
variable {d : ℕ} {ι : Type*}

/-- A single canonical window contracts about any point on its anchor level. -/
theorem mem_window_homothety (f : ι → Point d →ᵃ[ℝ] ℝ) (c r : ι → ℝ)
    (z x : Point d) (i : ι) (hz : f i z = c i) {t : ℝ} (ht : 0 < t) :
    AffineMap.homothety z t x ∈ windows f c (fun j => t*r j) i ↔
      x ∈ windows f c r i := by
  change ((1-t*r i)*c i ≤ f i (AffineMap.homothety z t x) ∧
    f i (AffineMap.homothety z t x) ≤ c i+(1-c i)*(t*r i)) ↔ _
  rw [form_homothety, hz]
  rw [show (1-t*r i)*c i = (1-t)*c i+t*((1-r i)*c i) by ring,
    show c i+(1-c i)*(t*r i) = (1-t)*c i+t*(c i+(1-c i)*r i) by ring]
  simp only [add_le_add_iff_left, mul_le_mul_iff_right₀ ht]
  rfl

/-- A common anchor for just the selected subfamily contracts its intersection
inside the body. Other windows impose no restriction on the anchor. -/
theorem intersection_contraction {K : Set (Point d)} (hconv : Convex ℝ K)
    (f : ι → Point d →ᵃ[ℝ] ℝ) (c r : ι → ℝ) (s : Finset ι)
    {z : Point d} (hz : z ∈ K) (hanchor : ∀ i ∈ s, f i z = c i)
    {t : ℝ} (ht : t ∈ Ioc 0 1) :
    AffineMap.homothety z t '' (K ∩ ⋂ i ∈ s, windows f c (fun j => r j/t) i) ⊆
      K ∩ ⋂ i ∈ s, windows f c r i := by
  rintro _ ⟨x, ⟨hxK, hx⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [AffineMap.homothety_eq_lineMap]
    exact hconv.lineMap_mem hz hxK ⟨ht.1.le, ht.2⟩
  · simp only [mem_iInter] at hx ⊢
    intro i hi
    have h := (mem_window_homothety f c (fun j => r j/t) z x i
      (hanchor i hi) ht.1).mpr (hx i hi)
    simpa only [mul_div_cancel₀ _ ht.1.ne'] using h

/-- The clipped intersection scales in every positive dimension. It need not
be bounded before clipping, and the selected directions may be parallel. -/
theorem volume_intersection_contraction {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : ι → Point d →ᵃ[ℝ] ℝ) (c r : ι → ℝ) (s : Finset ι)
    {z : Point d} (hz : z ∈ K) (hanchor : ∀ i ∈ s, f i z = c i)
    {t : ℝ} (ht : t ∈ Ioc 0 1) :
    t^(d+1)*volume.real (K ∩ ⋂ i ∈ s, windows f c (fun j => r j/t) i) ≤
      volume.real (K ∩ ⋂ i ∈ s, windows f c r i) := by
  have h := measureReal_mono (μ := volume)
    (intersection_contraction hconv f c r s hz hanchor ht)
    (measure_ne_top_of_subset inter_subset_left hK.measure_ne_top)
  simpa only [measureReal_def, volume_homothety _ z ht.1.le] using h

/-- Four exterior corner witnesses give every prescribed pair of values in
the two windows. Neither injectivity nor a dimension hypothesis is needed. -/
theorem exists_pair_anchor_of_corners {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} (hconv : Convex ℝ K) (f g : E →ᵃ[ℝ] ℝ)
    {lo hi lo' hi' u v : ℝ} (hu : u ∈ Icc lo hi) (hv : v ∈ Icc lo' hi')
    (hcorners : ∀ b c : Bool, ∃ x ∈ K,
      (if b then hi ≤ f x else f x ≤ lo) ∧ (if c then hi' ≤ g x else g x ≤ lo')) :
    ∃ z ∈ K, f z = u ∧ g z = v := by
  let F : E →ᵃ[ℝ] (Fin 2 → ℝ) := AffineMap.pi ![f, g]
  have hbox := ResearchFormalized.OrthantWitnesses.box_subset
    (hconv.affine_image F) ![lo, lo'] ![hi, hi'] (fun s => by
      obtain ⟨x, hx, hxf, hxg⟩ := hcorners (decide ((0 : Fin 2) ∈ s))
        (decide ((1 : Fin 2) ∈ s))
      refine ⟨F x, ⟨x, hx, rfl⟩, ?_⟩
      intro i
      fin_cases i
      · simpa [F, AffineMap.pi_apply] using hxf
      · simpa [F, AffineMap.pi_apply] using hxg)
  obtain ⟨z, hz, heq⟩ := hbox (show ![u, v] ∈ Icc ![lo, lo'] ![hi, hi'] by
    simp [mem_Icc, Pi.le_def, Fin.forall_fin_two, hu.1, hu.2, hv.1, hv.2])
  exact ⟨z, hz, congrFun heq 0, congrFun heq 1⟩

/-- A normalized window's canonical centre lies in that window. -/
theorem canonical_centre_mem {lo hi : ℝ} (hlo : 0 ≤ lo) (ho : lo ≤ hi)
    (hhi : hi ≤ 1) (hw : hi-lo < 1) : lo/(1-(hi-lo)) ∈ Icc lo hi := by
  obtain ⟨hc, hl, hh⟩ := FiniteDimensionalNormalization.canonical_window hlo hhi hw
  constructor
  · nlinarith only [hl, mul_nonneg hc.1 (sub_nonneg.mpr ho)]
  · nlinarith only [hh, mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr ho)]

end Plank.FiniteDimensionalPairAnchors
