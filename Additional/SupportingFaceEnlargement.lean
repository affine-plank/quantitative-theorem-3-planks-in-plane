/- Convex-hull enlargements above a compact subset of a supporting face's
interior. These are actual convex competitors, with controlled vertical fibers. -/
module
public import Plank.Proofs.Quant.ConvexSections
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Convex.Join

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SupportingFaceEnlargement

open Set Filter ConvexSections
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def enlargement (K : Set (ℝ × E)) (b : ℝ) (A : Set E) (ε : ℝ) : Set (ℝ × E) :=
  convexHull ℝ (K ∪ Prod.mk (b+ε) '' A)

theorem subset_enlargement (K : Set (ℝ × E)) (b : ℝ) (A : Set E) (ε : ℝ) :
    K ⊆ enlargement K b A ε :=
  subset_union_left.trans (subset_convexHull ℝ _)

theorem convex_enlargement (K : Set (ℝ × E)) (b : ℝ) (A : Set E) (ε : ℝ) :
    Convex ℝ (enlargement K b A ε) := convex_convexHull ℝ _

/-- The hull of the body and a compact convex cap is compact, including
in an infinite-dimensional ambient normed space. -/
theorem compact_enlargement {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    (b : ℝ) {A : Set E} (hA : IsCompact A) (hAc : Convex ℝ A) (ε : ℝ) :
    IsCompact (enlargement K b A ε) := by
  let L : Set (ℝ × E) := Prod.mk (b+ε) '' A
  have hL : IsCompact L := hA.image (continuous_const.prodMk continuous_id)
  have hLc : Convex ℝ L :=
    hAc.affine_image ((AffineMap.const ℝ E (b+ε)).prod (AffineMap.id ℝ E))
  change IsCompact (convexHull ℝ (K∪L))
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simpa [hLc.convexHull_eq] using hL
  rcases L.eq_empty_or_nonempty with he | hLn
  · simpa [he,hc.convexHull_eq] using hK
  rw [hc.convexHull_union hLc hne hLn]
  let g : ((ℝ × E) × (ℝ × E)) × ℝ → ℝ × E :=
    fun p => (1-p.2) • p.1.1+p.2 • p.1.2
  have he : convexJoin ℝ K L=g '' ((K×ˢL)×ˢIcc (0 : ℝ) 1) := by
    ext p
    constructor
    · intro hp
      obtain ⟨x,hx,y,hy,a,c,ha,hc',hac,hp⟩ := mem_convexJoin.mp hp
      refine ⟨((x,y),c),⟨⟨hx,hy⟩,⟨hc',by linarith⟩⟩,?_⟩
      have hec : 1-c=a := by linarith
      simpa [g,hec] using hp
    · rintro ⟨⟨⟨x,y⟩,t⟩,⟨⟨hx,hy⟩,ht⟩,rfl⟩
      exact mem_convexJoin.mpr ⟨x,hx,y,hy,1-t,t,sub_nonneg.mpr ht.2,ht.1,by ring,rfl⟩
  rw [he]
  exact ((hK.prod hL).prod isCompact_Icc).image (by dsimp [g]; fun_prop)

theorem vertical_difference (f : (ℝ × E) →L[ℝ] ℝ) (s t : ℝ) (y : E) :
    f (s,y)-f (t,y)=(s-t)*f (1,0) := by
  have he : ((s,y) : ℝ × E)-(t,y)=(s-t) • ((1,0) : ℝ × E) := by
    ext <;> simp
  simpa only [map_sub,map_smul,smul_eq_mul] using congrArg f he

/-- A supporting functional with positive vertical coefficient has a strict
gap on the interior of a higher horizontal section. -/
theorem support_lt_on_interior_face {K : Set (ℝ × E)}
    (f : (ℝ × E) →L[ℝ] ℝ) {z : ℝ × E} (hside : ∀ p∈K,f p≤f z)
    (hf : 0<f (1,0)) {b : ℝ} (hzb : z.1<b) {y : E}
    (hy : y∈interior (fiber K b)) : f (b,y)<f z := by
  have hle := hside (b,y) (show y∈fiber K b from interior_subset hy)
  by_contra hn
  have heq : f (b,y)=f z := le_antisymm hle (not_lt.mp hn)
  have he : ∀ᶠ u : ℝ in 𝓝 0,y+u • (z.2-y)∈fiber K b := by
    have ht : Tendsto (fun u : ℝ => y+u • (z.2-y)) (𝓝 0) (𝓝 y) := by
      simpa using (show Continuous (fun u : ℝ => y+u • (z.2-y)) from by fun_prop).tendsto 0
    exact ht.eventually_mem (mem_interior_iff_mem_nhds.mp hy)
  obtain ⟨u,hu,hw⟩ := he.exists_gt
  have hwle := hside (b,y+u • (z.2-y)) hw
  have hp : ((b,y+u • (z.2-y)) : ℝ × E)=(b,y)+u • ((b,z.2)-(b,y)) := by
    ext <;> simp
  have hv := vertical_difference f b z.1 z.2
  rw [Prod.mk.eta] at hv
  have hstrict : f (b,z.2)>f z := by nlinarith [mul_pos (sub_pos.mpr hzb) hf]
  rw [hp,map_add,map_smul,map_sub,smul_eq_mul,heq] at hwle
  nlinarith [mul_pos hu (sub_pos.mpr hstrict)]

omit [NormedSpace ℝ E] in
/-- A point on the top of a vertical fiber is outside the ambient interior. -/
theorem upper_not_interior {K : Set (ℝ × E)} {z : ℝ × E}
    (hu : ∀ t,(t,z.2)∈K → t≤z.1) : z∉interior K := by
  intro hzi
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hzi)
  have hp : (z.1+r/2,z.2)∈K := interior_subset (hball (by
    rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq]
    simp only [add_sub_cancel_left,dist_self,abs_of_pos (half_pos hr)]
    rw [max_eq_left (half_pos hr).le]
    linarith))
  have := hu _ hp
  linarith

/-- Above an interior point of the projection, a top point has a supporting
functional with strictly positive vertical coefficient. -/
theorem exists_upper_support {K : Set (ℝ × E)} (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) {z : ℝ × E}
    (hu : ∀ t,(t,z.2)∈K → t≤z.1) (hy : z.2∈interior (Prod.snd '' K)) :
    ∃ f : (ℝ × E) →L[ℝ] ℝ,0<f (1,0) ∧ ∀ p∈K,f p≤f z := by
  obtain ⟨f,hf⟩ := geometric_hahn_banach_open_point hc.interior isOpen_interior
    (upper_not_interior hu)
  have hside : ∀ p∈K,f p≤f z := by
    intro p hp
    apply closure_minimal (fun x hx => (hf x hx).le) (isClosed_le f.continuous continuous_const)
    simpa [hc.closure_interior_eq_closure_of_nonempty_interior hi] using subset_closure hp
  have hproj : Prod.snd '' interior K=interior (Prod.snd '' K) :=
    image_interior_eq (ContinuousLinearMap.snd ℝ ℝ E) isOpenMap_snd hc hi
  obtain ⟨p,hp,hpy⟩ := hproj.symm ▸ hy
  have hplt : f p<f z := hf p hp
  have hple : p.1≤z.1 := hu p.1 (by rw [←hpy]; exact interior_subset hp)
  have hd := vertical_difference f z.1 p.1 z.2
  have hep : (p.1,z.2)=p := Prod.ext rfl hpy.symm
  rw [Prod.mk.eta,hep] at hd
  refine ⟨f,?_,hside⟩
  by_contra hn
  have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hple) (not_lt.mp hn)
  linarith

/-- Compactness makes the strict support gap uniform under a small lift. -/
theorem eventually_enlargement_le {K : Set (ℝ × E)} {A : Set E}
    (hA : IsCompact A) (f : (ℝ × E) →L[ℝ] ℝ) (c b : ℝ)
    (hK : ∀ p∈K,f p≤c) (hstrict : ∀ y∈A,f (b,y)<c) :
    ∀ᶠ ε in 𝓝 (0 : ℝ),∀ p∈enlargement K b A ε,f p≤c := by
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ),∀ y∈A,f (b+ε,y)<c := by
    apply hA.eventually_forall_of_forall_eventually
    intro y hy
    exact (show Continuous (fun z : ℝ × E => f (b+z.1,z.2)) from by fun_prop).continuousAt.eventually
      (Iio_mem_nhds (by simpa using hstrict y hy))
  filter_upwards [hev] with ε hε
  exact convexHull_min (by
    rintro p (hp | ⟨y,hy,rfl⟩)
    · exact hK p hp
    · exact (hε y hy).le) (convex_halfSpace_le ⟨f.map_add,f.map_smul⟩ c)

/-- Every point of the enlargement lies at most ε vertically above K. -/
theorem enlargement_vertical_bound {K : Set (ℝ × E)} (hc : Convex ℝ K)
    {b ε : ℝ} {A : Set E} (hA : A⊆fiber K b) (hε : 0≤ε) :
    ∀ p∈enlargement K b A ε,∃ s∈Icc (0 : ℝ) ε,(p.1-s,p.2)∈K := by
  let S : Set (ℝ × E) := {p | ∃ s∈Icc (0 : ℝ) ε,(p.1-s,p.2)∈K}
  have hSc : Convex ℝ S := by
    rintro p ⟨s,hs,hps⟩ q ⟨t,ht,hqt⟩ a c ha hc' hac
    refine ⟨a*s+c*t,⟨add_nonneg (mul_nonneg ha hs.1) (mul_nonneg hc' ht.1),?_⟩,?_⟩
    · calc a*s+c*t ≤ a*ε+c*ε := add_le_add (mul_le_mul_of_nonneg_left hs.2 ha)
            (mul_le_mul_of_nonneg_left ht.2 hc')
           _ = ε := by rw [←add_mul,hac,one_mul]
    · convert hc hps hqt ha hc' hac using 1
      ext
      · simp; ring
      · rfl
  apply convexHull_min ?_ hSc
  rintro p (hp | ⟨y,hy,rfl⟩)
  · exact ⟨0,⟨le_rfl,hε⟩,by simpa using hp⟩
  · exact ⟨ε,⟨hε,le_rfl⟩,by simpa [fiber] using hA hy⟩

/-- Outside the supporting face, an interior projected fiber is exactly
unchanged by every sufficiently small nonnegative lift of a compact inner cap. -/
theorem eventually_vertical_fiber_eq {K : Set (ℝ × E)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty)
    {b : ℝ} (htop : ∀ p∈K,p.1≤b) {A : Set E} (hA : IsCompact A)
    (hAi : A⊆interior (fiber K b)) {y : E}
    (hy : y∈interior (Prod.snd '' K)) (hyF : y∉fiber K b) :
    ∀ᶠ ε in 𝓝 (0 : ℝ),0≤ε → ∀ t,
      (t,y)∈enlargement K b A ε ↔ (t,y)∈K := by
  have hslice : IsCompact (K∩{p | p.2=y}) :=
    hK.inter_right (isClosed_eq continuous_snd continuous_const)
  obtain ⟨p,hp,hpy⟩ := interior_subset hy
  obtain ⟨z,hz,hmax⟩ := hslice.exists_isMaxOn ⟨p,hp,hpy⟩ continuous_fst.continuousOn
  have hu : ∀ t,(t,z.2)∈K → t≤z.1 := by
    intro t ht
    exact hmax ⟨ht,hz.2⟩
  have hzb : z.1<b := lt_of_le_of_ne (htop z hz.1) (by
    intro he
    apply hyF
    change (b,y)∈K
    have hez : (b,y)=z := Prod.ext he.symm hz.2.symm
    exact hez ▸ hz.1)
  obtain ⟨f,hf,hside⟩ := exists_upper_support hc hi hu (hz.2 ▸ hy)
  have hstrict (a) (ha : a∈A) : f (b,a)<f z :=
    support_lt_on_interior_face f hside hf hzb (hAi ha)
  filter_upwards [eventually_enlargement_le hA f (f z) b hside hstrict] with ε hε
  intro hε0 t
  constructor
  · intro ht
    have hfz : f (t,y)≤f z := hε _ ht
    have hv := vertical_difference f t z.1 y
    have he : (z.1,y)=z := Prod.ext rfl hz.2.symm
    rw [he] at hv
    have htz : t≤z.1 := by nlinarith
    obtain ⟨s,hs,hps⟩ := enlargement_vertical_bound hc (hAi.trans interior_subset) hε0 _ ht
    have hc' : Convex ℝ {r : ℝ | (r,y)∈K} :=
      hc.affine_preimage ((AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ y))
    exact hc'.ordConnected.out hps (he.symm ▸ hz.1) ⟨by linarith [hs.1],htz⟩
  · exact fun ht => subset_enlargement K b A ε ht

/-- Every added vertical fiber fits in an interval of length ε. -/
theorem exists_added_interval {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    {b ε : ℝ} {A : Set E} (hA : A⊆fiber K b) (hε : 0≤ε) (y : E) :
    ∃ u : ℝ,{t | (t,y)∈enlargement K b A ε\K}⊆Ioc u (u+ε) := by
  by_cases hy : y∈Prod.snd '' K
  · have hslice : IsCompact (K∩{p | p.2=y}) :=
      hK.inter_right (isClosed_eq continuous_snd continuous_const)
    obtain ⟨p,hp,hpy⟩ := hy
    obtain ⟨z,hz,hmax⟩ := hslice.exists_isMaxOn ⟨p,hp,hpy⟩ continuous_fst.continuousOn
    have hez : (z.1,y)=z := Prod.ext rfl hz.2.symm
    refine ⟨z.1,?_⟩
    rintro t ⟨ht,hnot⟩
    obtain ⟨s,hs,hps⟩ := enlargement_vertical_bound hc hA hε _ ht
    have hlow : t-s≤z.1 := hmax ⟨hps,rfl⟩
    refine ⟨?_,by linarith [hs.2]⟩
    by_contra hn
    have hc' : Convex ℝ {r : ℝ | (r,y)∈K} :=
      hc.affine_preimage ((AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ y))
    exact hnot (hc'.ordConnected.out hps (hez.symm ▸ hz.1) ⟨by linarith [hs.1],not_lt.mp hn⟩)
  · refine ⟨0,?_⟩
    rintro t ⟨ht,_⟩
    obtain ⟨s,_,hps⟩ := enlargement_vertical_bound hc hA hε _ ht
    exact (hy ⟨(t-s,y),hps,rfl⟩).elim

section Measure

open MeasureTheory
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Off the face, almost every fiber is eventually exactly unchanged.
The only discarded projected fibers lie on a Haar-null convex frontier. -/
theorem ae_eventually_vertical_fiber_eq (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty)
    {b : ℝ} (htop : ∀ p∈K,p.1≤b) {A : Set E} (hA : IsCompact A)
    (hAi : A⊆interior (fiber K b)) :
    ∀ᵐ y ∂ν,y∉fiber K b → ∀ᶠ ε in 𝓝 (0 : ℝ),0≤ε → ∀ t,
      (t,y)∈enlargement K b A ε ↔ (t,y)∈K := by
  have hproj : Convex ℝ (Prod.snd '' K) := hc.linear_image (LinearMap.snd ℝ ℝ E)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hproj.addHaar_frontier ν)] with y hy
  intro hyF
  by_cases hymem : y∈Prod.snd '' K
  · exact eventually_vertical_fiber_eq hK hc hi htop hA hAi
      ((mem_interior_iff_notMem_frontier hymem).mpr hy) hyF
  · apply Eventually.of_forall
    intro ε hε t
    apply iff_of_false ?_ (fun ht => hymem ⟨(t,y),ht,rfl⟩)
    intro ht
    obtain ⟨s,_,hps⟩ := enlargement_vertical_bound hc (hAi.trans interior_subset) hε _ ht
    exact hymem ⟨(t-s,y),hps,rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The actual one-dimensional volume of each added fiber is at most ε. -/
theorem volume_added_fiber_le {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    {b ε : ℝ} {A : Set E} (hA : A⊆fiber K b) (hε : 0≤ε) (y : E) :
    volume {t | (t,y)∈enlargement K b A ε\K}≤ENNReal.ofReal ε := by
  obtain ⟨u,hu⟩ := exists_added_interval hK hc hA hε y
  simpa using (measure_mono hu : volume _≤volume (Ioc u (u+ε)))

end Measure

end Plank.SupportingFaceEnlargement
