/- The shape forced by one-plank equality: two cones over a level section.
The affine coordinate is normalized to have range [0,1]. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalOnePlankEquality
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalOnePlankShape

open Set MeasureTheory Topology FiniteDimensionalOnePlankEquality
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalized_ray (f : E →ᵃ[ℝ] ℝ) {b : E} (hb : f b = 0)
    (x : E) (t : ℝ) : f (b+t • (x-b)) = t*f x := by
  have he : b+t • (x-b) = (1-t) • b+t • x := by module
  rw [he]
  simpa only [AffineMap.lineMap_apply_module,AffineMap.lineMap_apply_ring,
    smul_eq_mul,hb,mul_zero,zero_add] using f.apply_lineMap b x t

/-- An exact lower-copy condition forces all lower points onto rays from
the minimum support point to the indicated level section. Compactness rules
out a ray that would keep expanding without reaching that section. -/
theorem lower_copy_forces_cone {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : E →ᵃ[ℝ] ℝ) (b : E) (hb : b ∈ K) (hfb : f b = 0)
    (hmin : ∀ x ∈ K, 0 ≤ f x) {q d : ℝ} (hq : 0 < q) (hq1 : q < 1) (hd : 0 < d)
    (hcopy : ∀ x ∈ K, f x < q*d → x-(1-q) • b ∈ q • K)
    {x : E} (hx : x ∈ K) (hxd : f x ≤ d) :
    x = b ∨ ∃ z ∈ K, f z = d ∧ x ∈ segment ℝ b z := by
  by_cases hxb : x = b
  · exact Or.inl hxb
  right
  have hemb : IsClosedEmbedding (fun t : ℝ => b+t • (x-b)) :=
    (Homeomorph.addLeft b).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left (sub_ne_zero.mpr hxb))
  have hcompact : IsCompact {t : ℝ | b+t • (x-b) ∈ K} := hemb.isCompact_preimage hK
  have h1 : (1 : ℝ) ∈ {t : ℝ | b+t • (x-b) ∈ K} := by simpa using hx
  obtain ⟨m,hm,hmmax⟩ := hcompact.exists_isMaxOn ⟨1,h1⟩ continuous_id.continuousOn
  have hm1 : 1 ≤ m := hmmax h1
  let y := b+m • (x-b)
  have hy : y ∈ K := hm
  have hyf : f y = m*f x := normalized_ray f hfb x m
  have hdmax : d ≤ f y := by
    by_contra h
    have hlt : f y < d := lt_of_not_ge h
    obtain ⟨u,hqu,hu1,huf⟩ : ∃ u : ℝ, q < u ∧ u < 1 ∧ u*f y < q*d := by
      rcases eq_or_lt_of_le (hmin y hy) with hy0 | hyp
      · refine ⟨(q+1)/2,by linarith,by linarith,?_⟩
        rw [← hy0,mul_zero]
        exact mul_pos hq hd
      · have hqr : q < q*d/f y := (lt_div_iff₀ hyp).mpr (mul_lt_mul_of_pos_left hlt hq)
        obtain ⟨u,hqu,hu⟩ := exists_between (lt_min hq1 hqr)
        exact ⟨u,hqu,hu.trans_le (min_le_left _ _),
          (lt_div_iff₀ hyp).mp (hu.trans_le (min_le_right _ _))⟩
    let w := b+u • (y-b)
    have hw : w ∈ K := by
      have he : w = (1-u) • b+u • y := by dsimp [w]; module
      rw [he]
      exact hconv hb hy (sub_nonneg.mpr hu1.le) (hq.trans hqu).le (sub_add_cancel 1 u)
    have hwf : f w < q*d := by rw [normalized_ray f hfb]; exact huf
    obtain ⟨z,hz,hez⟩ := hcopy w hw hwf
    have hzr : b+(u*m/q) • (x-b) = z := by
      apply smul_right_injective E hq.ne'
      change q • (b+(u*m/q) • (x-b)) = q • z
      change q • z = (b+u • ((b+m • (x-b))-b))-(1-q) • b at hez
      rw [hez,smul_add,smul_smul,mul_div_cancel₀ _ hq.ne']
      module
    have hh : u*m/q ≤ m := hmmax (by change b+(u*m/q) • (x-b) ∈ K; rwa [hzr])
    have hgt : m < u*m/q := (lt_div_iff₀ hq).mpr (by nlinarith only [hqu,hm1])
    exact hgt.not_ge hh
  have hypos : 0 < f y := hd.trans_le hdmax
  have hxpos : 0 < f x := by
    have hx0 := hmin x hx
    by_contra hn
    have he : f x = 0 := le_antisymm (le_of_not_gt hn) hx0
    rw [he,mul_zero] at hyf
    exact hypos.ne' hyf
  let z := b+(d/f y) • (y-b)
  have hz : z ∈ K := by
    have he : z = (1-d/f y) • b+(d/f y) • y := by dsimp [z]; module
    rw [he]
    exact hconv hb hy (sub_nonneg.mpr ((div_le_one hypos).mpr hdmax))
      (div_nonneg hd.le hypos.le) (sub_add_cancel 1 _)
  have hfz : f z = d := by rw [normalized_ray f hfb]; exact div_mul_cancel₀ d hypos.ne'
  have hcoef : (f x/d)*(d/f y)*m = 1 := by
    rw [hyf]
    field_simp
  have hrepr : b+(f x/d) • (z-b) = x := by
    dsimp [z,y]
    simp only [add_sub_cancel_left,smul_smul]
    rw [← mul_assoc,hcoef,one_smul,add_sub_cancel]
  have ht : f x/d ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hxpos.le hd.le,(div_le_one hd).mpr hxd⟩
  refine ⟨z,hz,hfz,?_⟩
  rw [segment_eq_image' ℝ]
  exact ⟨f x/d,ht,hrepr⟩

/-- The cone with its apex included, even when its base is empty. -/
def cone (b : E) (S : Set E) : Set E :=
  insert b (⋃ z ∈ S, segment ℝ b z)

def levelSection (K : Set E) (f : E →ᵃ[ℝ] ℝ) (t : ℝ) : Set E :=
  K ∩ {x | f x = t}

def doubleCone (a b : E) (S : Set E) : Set E := cone b S ∪ cone a S

theorem mem_cone_of_segment {b x z : E} {S : Set E}
    (hz : z ∈ S) (hx : x ∈ segment ℝ b z) : x ∈ cone b S :=
  Or.inr (mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨hz,hx⟩⟩)

theorem cone_subset {K S : Set E} (hK : Convex ℝ K) {b : E}
    (hb : b ∈ K) (hS : S ⊆ K) : cone b S ⊆ K := by
  rintro x (he | hx)
  · exact he ▸ hb
  · obtain ⟨z,hzx⟩ := mem_iUnion.mp hx
    obtain ⟨hzS,hxz⟩ := mem_iUnion.mp hzx
    exact hK.segment_subset hb (hS hzS) hxz

theorem cone_range (f : E →ᵃ[ℝ] ℝ) {b : E} (hb : f b = 0)
    {S : Set E} {d : ℝ} (hd : 0 ≤ d) (hS : ∀ z ∈ S, f z = d)
    {x : E} (hx : x ∈ cone b S) : 0 ≤ f x ∧ f x ≤ d := by
  rcases hx with he | hx
  · rw [he,hb]
    exact ⟨le_refl 0,hd⟩
  · obtain ⟨z,hzx⟩ := mem_iUnion.mp hx
    obtain ⟨hzS,hxz⟩ := mem_iUnion.mp hzx
    rw [segment_eq_image' ℝ] at hxz
    obtain ⟨u,hu,rfl⟩ := hxz
    rw [normalized_ray f hb,hS z hzS]
    exact ⟨mul_nonneg hu.1 hd,by nlinarith only [hu.2,hd]⟩

theorem lower_cone_gives_copy {K S : Set E} (hK : Convex ℝ K)
    (f : E →ᵃ[ℝ] ℝ) {b : E} (hb : b ∈ K) (hfb : f b = 0)
    {d q : ℝ} (hd : 0 ≤ d) (hq : 0 < q) (hS : S ⊆ K) (hfS : ∀ z ∈ S, f z = d)
    {x : E} (hx : x ∈ cone b S) (hfx : f x < q*d) :
    x-(1-q) • b ∈ q • K := by
  rcases hx with he | hx
  · rw [he]
    refine ⟨b,hb,?_⟩
    module
  · obtain ⟨z,hzx⟩ := mem_iUnion.mp hx
    obtain ⟨hzS,hxz⟩ := mem_iUnion.mp hzx
    rw [segment_eq_image' ℝ] at hxz
    obtain ⟨u,hu,rfl⟩ := hxz
    rw [normalized_ray f hfb,hfS z hzS] at hfx
    have hdp : 0 < d := by
      by_contra hn
      have he : d = 0 := le_antisymm (le_of_not_gt hn) hd
      simp only [he,mul_zero,lt_self_iff_false] at hfx
    have huq : u < q := (mul_lt_mul_iff_left₀ hdp).mp hfx
    refine ⟨b+(u/q) • (z-b),hK.add_smul_sub_mem hb (hS hzS)
      ⟨div_nonneg hu.1 hq.le,(div_le_one hq).mpr huq.le⟩,?_⟩
    change q • (b+(u/q) • (z-b)) = (b+u • (z-b))-(1-q) • b
    rw [smul_add,smul_smul,mul_div_cancel₀ _ hq.ne']
    module

/-- The self-similarity criterion is exactly a double-cone shape, at the
calibrated level t. In the plane its base is a segment (possibly at an
extreme level), so this describes triangles and quadrilaterals. -/
theorem homothetic_cover_iff_doubleCone {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : E →ᵃ[ℝ] ℝ) (a b : E)
    (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    {q t : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 ≤ t ∧ t ≤ 1) :
    K ⊆ closedHomotheticCover K f (q*t) (q*t+1-q) a b (1-q) ↔
      K = doubleCone a b (levelSection K f t) := by
  let S := levelSection K f t
  let g : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E 1-f
  have hga : g a = 0 := by simp [g,hfa]
  have hgS : ∀ z ∈ S, g z = 1-t := by intro z hz; change 1-f z = 1-t; rw [hz.2]
  have hgf : ∀ x ∈ K, 0 ≤ g x := by intro x hx; change 0 ≤ 1-f x; linarith [(hf x hx).2]
  have hlo : q*t ≤ t := by nlinarith only [ht.1,hq1]
  have hhi : t ≤ q*t+1-q := by nlinarith only [ht.2,hq1]
  constructor
  · intro hcov
    have hl : ∀ x ∈ K, f x < q*t → x-(1-q) • b ∈ q • K := by
      intro x hx hlt
      rcases hcov hx with hp | hp | hp
      · exact (not_lt_of_ge hp.1 hlt).elim
      · simpa only [mem_ofPred_eq,sub_sub_cancel] using hp.1
      · exact (not_lt_of_ge (hlo.trans (hhi.trans hp.2)) hlt).elim
    have hh : ∀ x ∈ K, g x < q*(1-t) → x-(1-q) • a ∈ q • K := by
      intro x hx hgt
      have hgt' : q*t+1-q < f x := by change 1-f x < q*(1-t) at hgt; linarith
      rcases hcov hx with hp | hp | hp
      · exact (not_lt_of_ge hp.2 hgt').elim
      · exact (not_lt_of_ge (hp.2.trans (hlo.trans hhi)) hgt').elim
      · simpa only [mem_ofPred_eq,sub_sub_cancel] using hp.1
    apply Subset.antisymm
    · intro x hx
      rcases le_total (f x) t with hxt | htx
      · apply Or.inl
        rcases eq_or_lt_of_le ht.1 with ht0 | htp
        · apply mem_cone_of_segment (S := S) (z := x)
            ⟨hx,le_antisymm hxt (by simpa only [← ht0] using (hf x hx).1)⟩
          exact right_mem_segment ℝ b x
        · rcases lower_copy_forces_cone hK hconv f b hb hfb (fun y hy => (hf y hy).1)
            hq hq1 htp hl hx hxt with rfl | ⟨z,hz,hfz,hs⟩
          · exact Or.inl rfl
          · exact mem_cone_of_segment (S := S) ⟨hz,hfz⟩ hs
      · apply Or.inr
        rcases eq_or_lt_of_le ht.2 with ht1 | ht1
        · apply mem_cone_of_segment (S := S) (z := x) ⟨hx,le_antisymm (by simpa only [ht1] using (hf x hx).2) htx⟩
          exact right_mem_segment ℝ a x
        · have hgt : g x ≤ 1-t := by change 1-f x ≤ 1-t; linarith only [htx]
          rcases lower_copy_forces_cone hK hconv g a ha hga hgf hq hq1 (sub_pos.mpr ht1)
            hh hx hgt with rfl | ⟨z,hz,hgz,hs⟩
          · exact Or.inl rfl
          · apply mem_cone_of_segment (S := S) ⟨hz,?_⟩ hs
            change 1-f z = 1-t at hgz
            change f z = t
            linarith only [hgz]
    · exact union_subset (cone_subset hconv hb inter_subset_left) (cone_subset hconv ha inter_subset_left)
  · intro he x hx
    by_cases hp : q*t ≤ f x ∧ f x ≤ q*t+1-q
    · exact Or.inl hp
    have hxcone : x ∈ cone b S ∪ cone a S := by rw [he] at hx; exact hx
    rcases hxcone with hxcone | hxcone
    · have hxf := cone_range (S := S) f hfb ht.1 (fun z hz => hz.2) hxcone
      have hlt : f x < q*t := by
        by_contra hn
        exact hp ⟨le_of_not_gt hn,hxf.2.trans hhi⟩
      refine Or.inr (Or.inl ⟨?_,hlt.le⟩)
      simpa only [mem_ofPred_eq,sub_sub_cancel] using
        (lower_cone_gives_copy hconv f hb hfb ht.1 hq inter_subset_left
          (fun z hz => hz.2) hxcone hlt)
    · have hxg := cone_range g hga (sub_nonneg.mpr ht.2) hgS hxcone
      have hlt : q*t+1-q < f x := by
        by_contra hn
        apply hp
        refine ⟨?_,le_of_not_gt hn⟩
        have hxg' := hxg.2
        change 1-f x ≤ 1-t at hxg'
        linarith only [hxg',hlo]
      have hgt : g x < q*(1-t) := by change 1-f x < q*(1-t); linarith only [hlt]
      refine Or.inr (Or.inr ⟨?_,hlt.le⟩)
      simpa only [mem_ofPred_eq,sub_sub_cancel] using
        (lower_cone_gives_copy hconv g ha hga (sub_nonneg.mpr ht.2) hq inter_subset_left
          hgS hxcone hgt)

theorem affine_mix (f : E →ᵃ[ℝ] ℝ) (q : ℝ) (x y : E) :
    f (q • x+(1-q) • y) = q*f x+(1-q)*f y := by
  simpa only [AffineMap.lineMap_apply_module,AffineMap.lineMap_apply_ring,
    smul_eq_mul,add_comm] using f.apply_lineMap y x q

/-- A positive-width equality cover cannot waste either end outside the
support interval. The proof uses actual segments between the support points. -/
theorem position_of_homothetic_cover {K : Set E} (hconv : Convex ℝ K)
    (f : E →ᵃ[ℝ] ℝ) (a b : E) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0) (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    {q lo : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hcov : K ⊆ closedHomotheticCover K f lo (lo+1-q) a b (1-q)) :
    0 ≤ lo ∧ lo ≤ q := by
  have hpoint (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      b+v • (a-b) ∈ K ∧ f (b+v • (a-b)) = v :=
    ⟨hconv.add_smul_sub_mem hb ha hv,by rw [normalized_ray f hfb,hfa,mul_one]⟩
  constructor
  · by_contra hn
    have hlo : lo < 0 := lt_of_not_ge hn
    have hlt : max 0 (lo+1-q) < 1-q := max_lt (by linarith) (by linarith)
    obtain ⟨v,hv0,hv1⟩ := exists_between hlt
    have hvp : 0 < v := (le_max_left _ _).trans_lt hv0
    have hvhi : lo+1-q < v := (le_max_right _ _).trans_lt hv0
    obtain ⟨hx,hfx⟩ := hpoint v ⟨hvp.le,by linarith⟩
    rcases hcov hx with hp | hp | hp
    · have hh := hp.2
      rw [hfx] at hh
      exact hvhi.not_ge hh
    · have hh := hp.2
      change f (b+v • (a-b)) ≤ lo at hh
      rw [hfx] at hh
      linarith only [hh,hlo,hvp]
    · have hcopy : (b+v • (a-b))-(1-q) • a ∈ q • K := by
        simpa only [mem_ofPred_eq,sub_sub_cancel] using hp.1
      obtain ⟨z,hz,hez⟩ := hcopy
      have he : b+v • (a-b) = q • z+(1-q) • a := (sub_eq_iff_eq_add).mp hez.symm
      rw [he,affine_mix,hfa,mul_one] at hfx
      nlinarith only [(hf z hz).1,hfx,hq,hv1]
  · by_contra hn
    have hlo : q < lo := lt_of_not_ge hn
    obtain ⟨v,hvq,hv⟩ := exists_between (lt_min hq1 hlo)
    have hv1 : v < 1 := hv.trans_le (min_le_left _ _)
    have hvlo : v < lo := hv.trans_le (min_le_right _ _)
    obtain ⟨hx,hfx⟩ := hpoint v ⟨(hq.trans hvq).le,hv1.le⟩
    rcases hcov hx with hp | hp | hp
    · have hh := hp.1
      rw [hfx] at hh
      exact hvlo.not_ge hh
    · have hcopy : (b+v • (a-b))-(1-q) • b ∈ q • K := by
        simpa only [mem_ofPred_eq,sub_sub_cancel] using hp.1
      obtain ⟨z,hz,hez⟩ := hcopy
      have he : b+v • (a-b) = q • z+(1-q) • b := (sub_eq_iff_eq_add).mp hez.symm
      rw [he,affine_mix,hfb,mul_zero,add_zero] at hfx
      nlinarith only [(hf z hz).2,hfx,hq,hvq]
    · have hh := hp.2
      change lo+1-q ≤ f (b+v • (a-b)) at hh
      rw [hfx] at hh
      linarith only [hh,hvlo,hq1]

/-- Exhaustive one-plank shape classification in a normalized affine
coordinate. For width r in (0,1), the cut must be [lo,lo+r] inside [0,1]
and the body must be the two cones over its section at lo/(1-r). -/
theorem equality_iff_doubleCone [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (μ K).toReal)
    (f : E →ᵃ[ℝ] ℝ) (a b : E) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0) (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (lo r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (μ (K \ {x | lo ≤ f x ∧ f x ≤ lo+r})).toReal = (1-r)^Module.finrank ℝ E*(μ K).toReal ↔
      0 ≤ lo ∧ lo+r ≤ 1 ∧
      K = doubleCone a b (levelSection K f (lo/(1-r))) := by
  have hW : Body.width K f = 1 := by
    have hh : Body.width K f = f a-f b := Body.width_eq_of_realisers ha hb
      (fun x hx => by simpa only [hfa] using (hf x hx).2)
      (fun x hx => by simpa only [hfb] using (hf x hx).1)
    simpa only [hfa,hfb,sub_zero] using hh
  have hc := equality_iff_homothetic_cover μ hK hconv hV f lo (lo+r)
    (by linarith) (by rw [hW]; norm_num) (by rw [hW]; simpa using hr1) a b ha hb
    (fun x hx => by simpa only [hfa] using (hf x hx).2)
    (fun x hx => by simpa only [hfb] using (hf x hx).1)
  simp only [hW,add_sub_cancel_left,div_one] at hc
  rw [hc]
  have hq : 0 < 1-r := sub_pos.mpr hr1
  have hq1 : 1-r < 1 := by linarith
  have heq : (1-r)*(lo/(1-r)) = lo := mul_div_cancel₀ lo hq.ne'
  constructor
  · intro hcov
    have hp : 0 ≤ lo ∧ lo ≤ 1-r := position_of_homothetic_cover hconv f a b ha hb hfa hfb hf
      hq hq1 (by simpa only [add_sub_assoc,sub_sub_cancel] using hcov)
    have ht : 0 ≤ lo/(1-r) ∧ lo/(1-r) ≤ 1 :=
      ⟨div_nonneg hp.1 hq.le,(div_le_one hq).mpr hp.2⟩
    refine ⟨hp.1,by linarith [hp.2],?_⟩
    apply (homothetic_cover_iff_doubleCone hK hconv f a b ha hb hfa hfb hf hq hq1 ht).mp
    simpa only [heq,sub_sub_cancel,add_sub_assoc] using hcov
  · rintro ⟨hl,hh,he⟩
    have ht : 0 ≤ lo/(1-r) ∧ lo/(1-r) ≤ 1 :=
      ⟨div_nonneg hl hq.le,(div_le_one hq).mpr (by linarith)⟩
    have hc' := (homothetic_cover_iff_doubleCone hK hconv f a b ha hb hfa hfb hf hq hq1 ht).mpr he
    simpa only [heq,sub_sub_cancel,add_sub_assoc] using hc'

/-- Equality for an arbitrary affine coordinate and any chosen support extrema.
There is no polyhedral or section-shape hypothesis: the double cone is the conclusion. -/
theorem equality_iff_doubleCone_of_support [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0 < (μ K).toReal)
    (f : E →ᵃ[ℝ] ℝ) (lo hi : ℝ) (hlohi : lo < hi)
    (hW : 0 < Body.width K f) (hr1 : (hi-lo)/Body.width K f < 1)
    (a b : E) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x) :
    (μ (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
        (1-(hi-lo)/Body.width K f)^Module.finrank ℝ E*(μ K).toReal ↔
      f b ≤ lo ∧ hi ≤ f a ∧
      K = doubleCone a b (levelSection K f (f b+(lo-f b)/(1-(hi-lo)/Body.width K f))) := by
  let W := Body.width K f
  let r := (hi-lo)/W
  let ell := (lo-f b)/W
  let g : E →ᵃ[ℝ] ℝ := W⁻¹ • (f-AffineMap.const ℝ E (f b))
  have hpos : 0 < W := hW
  have hspan : W = f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
  have hg (x : E) : g x = (f x-f b)/W := by simp [g,div_eq_mul_inv,mul_comm]
  have hga : g a = 1 := by rw [hg,← hspan,div_self hW.ne']
  have hgb : g b = 0 := by rw [hg,sub_self,zero_div]
  have hgf : ∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1 := by
    intro x hx
    rw [hg]
    refine ⟨div_nonneg (sub_nonneg.mpr (hmin x hx)) hW.le,?_⟩
    apply (div_le_one hpos).mpr
    rw [hspan]
    linarith only [hmax x hx]
  have hr : 0 < r := div_pos (sub_pos.mpr hlohi) hW
  have hq : 0 < 1-r := sub_pos.mpr hr1
  have he : ell+r = (hi-f b)/W := by dsimp [ell,r]; ring
  have hplank : {x | ell ≤ g x ∧ g x ≤ ell+r} = {x | lo ≤ f x ∧ f x ≤ hi} := by
    ext x
    rw [mem_ofPred_eq,mem_ofPred_eq,he,hg]
    dsimp only [ell]
    simp only [div_le_div_iff_of_pos_right hpos,sub_le_sub_iff_right]
  have hlow : 0 ≤ ell ↔ f b ≤ lo := by
    dsimp only [ell]
    rw [le_div_iff₀ hW,zero_mul]
    exact sub_nonneg
  have hhigh : ell+r ≤ 1 ↔ hi ≤ f a := by
    rw [he,div_le_one hpos,hspan]
    exact sub_le_sub_iff_right (f b)
  have hlevel (x : E) : g x = ell/(1-r) ↔ f x = f b+(lo-f b)/(1-r) := by
    rw [hg,div_eq_iff hW.ne']
    have hc : (ell/(1-r))*W = (lo-f b)/(1-r) := by dsimp [ell]; field_simp [hpos.ne']
    rw [hc]
    constructor <;> intro h <;> linarith only [h]
  have hh := equality_iff_doubleCone μ hK hconv hV g a b ha hb hga hgb hgf ell r hr hr1
  rw [hplank,hlow,hhigh] at hh
  have hs : levelSection K g (ell/(1-r)) =
      levelSection K f (f b+(lo-f b)/(1-r)) := by
    ext x
    simp only [levelSection,mem_inter_iff,mem_ofPred_eq,hlevel]
  rw [hs] at hh
  exact hh

end Plank.FiniteDimensionalOnePlankShape

/-- info: 'Plank.FiniteDimensionalOnePlankShape.lower_copy_forces_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.FiniteDimensionalOnePlankShape.lower_copy_forces_cone
/-- info: 'Plank.FiniteDimensionalOnePlankShape.equality_iff_doubleCone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.FiniteDimensionalOnePlankShape.equality_iff_doubleCone
/-- info: 'Plank.FiniteDimensionalOnePlankShape.equality_iff_doubleCone_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.FiniteDimensionalOnePlankShape.equality_iff_doubleCone_of_support
