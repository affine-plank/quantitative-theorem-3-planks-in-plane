/- A tight positive band cannot waste width or touch a strict extreme vertex. -/
module
public import Plank.Proofs.Quant.TriangleSharp
public import Plank.Proofs.Quant.TriangleEqualityReductions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleEndpointNecessity
open Set MeasureTheory Proofs.Basic Proofs.Transport
open scoped BigOperators

def lowerCut (C : Config) (j : Fin 3) (t : ℝ) (ht : t ≤ (C.plank j).hi) : Config :=
  ⟨Function.update C.plank j
    ⟨(C.plank j).u,t,(C.plank j).hi,(C.plank j).u_ne_zero,ht⟩⟩

theorem lowerCut_deficit (C : Config) (j : Fin 3) (t : ℝ) (ht : t ≤ (C.plank j).hi)
    (hw : stdTriangle.width (C.plank j).u=1) :
    (lowerCut C j t ht).deficit=C.deficit+t-(C.plank j).lo := by
  fin_cases j
  all_goals first
    | change stdTriangle.width (C.plank 0).u=1 at hw
    | change stdTriangle.width (C.plank 1).u=1 at hw
    | change stdTriangle.width (C.plank 2).u=1 at hw
  all_goals
    simp [Config.deficit,Config.sumRelW,Fin.sum_univ_three,Config.relW,
      Plank.relWidth,lowerCut,Function.update_apply,hw]
    ring

theorem gap_finite (C : Config) : volume C.uncovered ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono sdiff_subset)
  rw [Proofs.Quant.volume_stdTriangle]
  exact ENNReal.ofReal_ne_top

theorem lowerCut_gap_subset (C : Config) (j : Fin 3) (t : ℝ) (ht : t ≤ (C.plank j).hi) :
    (lowerCut C j t ht).uncovered ⊆ C.uncovered ∪
      {z | z ∈ stdTriangle.set ∧ dot (C.plank j).u z ≤ t} := by
  intro z hz
  by_cases hzt : dot (C.plank j).u z ≤ t
  · exact Or.inr ⟨hz.1,hzt⟩
  · left
    refine ⟨hz.1,?_⟩
    intro h
    obtain ⟨i,hi⟩ := mem_iUnion.mp h
    apply hz.2
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    by_cases hij : i=j
    · subst i
      simp only [lowerCut,Function.update_self]
      change t ≤ dot (C.plank j).u z ∧ dot (C.plank j).u z ≤ (C.plank j).hi
      exact ⟨(lt_of_not_ge hzt).le,hi.2⟩
    · simpa only [lowerCut,Function.update_of_ne hij] using hi

theorem lowerCut_gap_le (C : Config) (j : Fin 3) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hu : (C.plank j).u=(a,1))
    (t : ℝ) (ht : t ≤ (C.plank j).hi) (ht0 : 0 ≤ t) (hta : t ≤ a) :
    (lowerCut C j t ht).gapArea ≤ C.gapArea+t^2/(2*a) := by
  have hm : volume (lowerCut C j t ht).uncovered ≤ volume C.uncovered+
      volume {z | z ∈ stdTriangle.set ∧ dot (C.plank j).u z ≤ t} :=
    (measure_mono (lowerCut_gap_subset C j t ht)).trans (measure_union_le _ _)
  rw [hu,volume_tent_low ha ha1 ht0 hta] at hm
  have hf : volume C.uncovered+ENNReal.ofReal (t^2/(2*a)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨gap_finite C,ENNReal.ofReal_ne_top⟩
  have hr := ENNReal.toReal_mono hf hm
  rw [ENNReal.toReal_add (gap_finite C) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (by positivity))] at hr
  exact hr

/-- This bound concerns the original positive window; no trimming is
silently performed in the equality statement. -/
theorem lower_nonneg (C : Config) (j : Fin 3) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hu : (C.plank j).u=(a,1))
    (hp : 0 < C.relW j) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C) : 0 ≤ (C.plank j).lo := by
  have hW : stdTriangle.width (C.plank j).u=1 := by rw [hu,width_tent ha ha1]
  have hwidth : C.relW j=(C.plank j).hi-(C.plank j).lo := by
    rw [Config.relW,Plank.relWidth,hW,div_one]
  have horder : (C.plank j).lo < (C.plank j).hi := by
    rw [hwidth] at hp
    exact sub_pos.mp hp
  by_contra hn
  have hl : (C.plank j).lo < 0 := lt_of_not_ge hn
  let t := min (C.plank j).hi 0
  have ht : t ≤ (C.plank j).hi := min_le_left _ _
  have ht0 : t ≤ 0 := min_le_right _ _
  have hlt : (C.plank j).lo < t := lt_min horder hl
  have hg : (lowerCut C j t ht).uncovered=C.uncovered := by
    ext z
    by_cases hz : z ∈ stdTriangle.set
    · have hzn := (Proofs.Quant.stdTriangle_set_eq ▸ hz)
      have hdot : 0 ≤ dot (C.plank j).u z := by
        simp only [hu,dot,one_mul]
        exact add_nonneg (mul_nonneg ha hzn.1) hzn.2.1
      have hi (i : Fin 3) : z ∈ ((lowerCut C j t ht).plank i).set ↔ z ∈ (C.plank i).set := by
        by_cases hij : i=j
        · subst i
          simp only [lowerCut,Function.update_self]
          change (t ≤ dot (C.plank j).u z ∧ dot (C.plank j).u z ≤ (C.plank j).hi) ↔
            ((C.plank j).lo ≤ dot (C.plank j).u z ∧ dot (C.plank j).u z ≤ (C.plank j).hi)
          simp only [ht0.trans hdot,hl.le.trans hdot,true_and]
        · simp only [lowerCut,Function.update_of_ne hij]
      simp only [Config.uncovered,mem_sdiff,mem_iUnion,hi]
    · simp only [Config.uncovered,mem_sdiff,hz,false_and]
  have hb := TriangleSharp.sqPos (lowerCut C j t ht)
  change (max 0 (lowerCut C j t ht).deficit)^2*(1/2) ≤
    (volume (lowerCut C j t ht).uncovered).toReal at hb
  rw [lowerCut_deficit C j t ht hW,hg] at hb
  have hd : 0 ≤ C.deficit+t-(C.plank j).lo := by linarith only [hδ,hlt]
  rw [max_eq_right hd] at hb
  change (C.deficit+t-(C.plank j).lo)^2*(1/2) ≤ C.gapArea at hb
  rw [he,max_eq_right hδ.le] at hb
  nlinarith only [hb,hδ,hlt,sq_nonneg (t-(C.plank j).lo)]

/-- At a strict minimum vertex the newly uncovered cap is quadratic in
the cut. The sharp bound increases to first order, ruling out a zero lower
endpoint. Other plank directions and positions remain arbitrary. -/
theorem lower_pos (C : Config) (j : Fin 3) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hu : (C.plank j).u=(a,1))
    (hp : 0 < C.relW j) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C) : 0 < (C.plank j).lo := by
  have hl := lower_nonneg C j a ha.le ha1 hu hp hδ he
  by_contra hn
  have hz : (C.plank j).lo=0 := le_antisymm (le_of_not_gt hn) hl
  have hW : stdTriangle.width (C.plank j).u=1 := by rw [hu,width_tent ha.le ha1]
  have hh : 0 < (C.plank j).hi := by
    simpa only [Config.relW,Plank.relWidth,hW,div_one,hz,sub_zero] using hp
  let t := min (C.plank j).hi (min a (C.deficit*a))/2
  have hm : 0 < min (C.plank j).hi (min a (C.deficit*a)) := lt_min hh (lt_min ha (mul_pos hδ ha))
  have ht0 : 0 < t := div_pos hm (by norm_num)
  have htmin : t ≤ min (C.plank j).hi (min a (C.deficit*a)) := by
    dsimp only [t]
    linarith only [hm]
  have hth : t ≤ (C.plank j).hi := htmin.trans (min_le_left _ _)
  have hta : t ≤ a := (htmin.trans (min_le_right _ _)).trans (min_le_left _ _)
  have htd : t ≤ C.deficit*a := (htmin.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hg := lowerCut_gap_le C j a ha ha1 hu t hth ht0.le hta
  have hcap : t^2/(2*a) ≤ C.deficit*t/2 := by
    apply (div_le_iff₀ (show 0 < 2*a by positivity)).mpr
    nlinarith only [mul_nonneg ht0.le (sub_nonneg.mpr htd)]
  have hb := TriangleSharp.sqPos (lowerCut C j t hth)
  change (max 0 (lowerCut C j t hth).deficit)^2*(1/2) ≤ (lowerCut C j t hth).gapArea at hb
  rw [lowerCut_deficit C j t hth hW,hz,sub_zero,max_eq_right (add_pos hδ ht0).le] at hb
  rw [he,max_eq_right hδ.le] at hg
  nlinarith only [hb,hg,hcap,sq_nonneg t,mul_pos hδ ht0]

end Quant.TriangleEndpointNecessity

/-- info: 'Quant.TriangleEndpointNecessity.lower_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleEndpointNecessity.lower_pos
