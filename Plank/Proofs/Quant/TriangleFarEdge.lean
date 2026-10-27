/- Exact far-edge constraints in the strict common-minimum chart. -/
module
public import Plank.Proofs.Quant.TriangleSourceBoundary

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleFarEdge
open Set MeasureTheory Function CommonVertex TranslationEquality
open CommonVertexTranslationEquality TriangleTranslationBoundary TriangleSourceBoundary
open scoped BigOperators

theorem closed_interval_of_finite_exceptions {H D : Set ℝ} (hH : IsClosed H)
    (hD : D.Finite) {a b : ℝ} (hab : a < b)
    (h : ∀ t ∈ Ioo a b, t ∉ D → t ∈ H) : Icc a b ⊆ H := by
  have hd₀ : Dense ((Set.univ : Set ℝ) \ D) := dense_univ.sdiff_finite hD
  have hs : (Set.univ : Set ℝ) \ D ⊆ Dᶜ := fun _ hx => hx.2
  have hd : Dense Dᶜ := Dense.mono hs hd₀
  have hi : Ioo a b ⊆ H := by
    intro x hx
    by_contra hn
    obtain ⟨y,hy,hyD⟩ := hd.inter_open_nonempty _ (isOpen_Ioo.inter hH.isOpen_compl)
      ⟨x,hx,hn⟩
    exact hy.2 (h y hy.1 hyD)
  simpa only [closure_Ioo hab.ne] using hH.closure_subset_iff.mpr hi

theorem source_far_univ (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C)
    (s : Finset (Fin 3)) {z : ℝ × ℝ} (hz : z ∈ RowDeletion.triangle C.deficit)
    (hs : z+shift (steps C) s ∈ exteriorCells C s) (hzs : z.1+z.2=C.deficit) :
    s=Finset.univ := by
  classical
  have hsum := (source_faces C hu hδ he s hz hs).2.2 hzs
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hn
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (insert i s))
    (fun j _ _ => relWidth_nonneg (C.plank j))
  rw [Finset.sum_insert hn] at hle
  change C.relW i+∑ j ∈ s, C.relW j ≤ C.sumRelW at hle
  linarith only [hle,hsum,hw i]

/-- If no direction is constant on the far edge, all of that core edge
has the all-high weak assignment. No placement or clipping is assumed. -/
theorem far_upper (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hne : ∀ i, (C.plank i).u.1 ≠ (C.plank i).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C)
    (t : ℝ) (ht : t ∈ Icc 0 C.deficit) (i : Fin 3) :
    (C.plank i).hi ≤ dot (C.plank i).u ((t,C.deficit-t)+shift (steps C) Finset.univ) := by
  classical
  let D : Set ℝ := Set.range (fun k : Finset (Fin 3) × Fin 3 =>
    ((C.plank k.2).lo-(C.plank k.2).u.2*C.deficit-
      dot (C.plank k.2).u (shift (steps C) k.1))/
      ((C.plank k.2).u.1-(C.plank k.2).u.2))
  let H : Set ℝ := {t | (C.plank i).hi ≤
    dot (C.plank i).u ((t,C.deficit-t)+shift (steps C) Finset.univ)}
  have hH : IsClosed H := isClosed_le continuous_const (by unfold dot; fun_prop)
  apply closed_interval_of_finite_exceptions (D := D) hH (Set.finite_range _) hδ ?_ ht
  intro q hq hqD
  have hbad (s : Finset (Fin 3)) (j : Fin 3) :
      dot (C.plank j).u ((q,C.deficit-q)+shift (steps C) s) ≠ (C.plank j).lo := by
    intro hh
    apply hqD
    refine ⟨(s,j),?_⟩
    dsimp only
    apply (div_eq_iff (sub_ne_zero.mpr (hne j))).mpr
    simp only [dot,Prod.fst_add,Prod.snd_add] at hh ⊢
    nlinarith only [hh]
  have hcross (j k : Fin 3) : 0 ≤ dot (C.plank j).u (steps C k) :=
    add_nonneg (mul_nonneg (hu j).1 (steps_nonneg C k).1)
      (mul_nonneg (hu j).2 (steps_nonneg C k).2)
  obtain ⟨s,hh,hl⟩ := exists_side_assignment C.plank (steps C) (steps_self C hu) hcross
    (q,C.deficit-q)
  have hs : (q,C.deficit-q)+shift (steps C) s ∈ exteriorCells C s := by
    rw [exteriorCells,Plank.LinearBands.strictCell]
    intro j
    by_cases hj : j ∈ s
    · simpa only [hj,if_true] using hh j hj
    · simpa only [hj,if_false] using lt_of_le_of_ne (hl j hj) (hbad s j)
  have hz : (q,C.deficit-q) ∈ RowDeletion.triangle C.deficit :=
    ⟨hq.1.le,by linarith only [hq.2],by dsimp; linarith⟩
  have hsall := source_far_univ C hu hw hδ he s hz hs (by dsimp; ring)
  subst s
  exact (hh i (Finset.mem_univ i)).le

/-- A positive vertical escape budget forces a vertical-type plank to
touch the right endpoint of the translated far edge. -/
theorem vertical_upper_contact (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hne : ∀ i, (C.plank i).u.1 ≠ (C.plank i).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C)
    (hy : 0 < (shift (steps C) Finset.univ).2) :
    ∃ i, (C.plank i).u.1 < (C.plank i).u.2 ∧
      (C.plank i).hi = dot (C.plank i).u ((C.deficit,0)+shift (steps C) Finset.univ) := by
  classical
  have hbounds (i) : (C.plank i).hi ≤
      dot (C.plank i).u ((C.deficit,0)+shift (steps C) Finset.univ) := by
    simpa only [sub_self] using far_upper C hu hne hw hδ he C.deficit ⟨hδ.le,le_rfl⟩ i
  have hex : ∃ i, (C.plank i).hi =
      dot (C.plank i).u ((C.deficit,0)+shift (steps C) Finset.univ) := by
    by_contra hn
    push Not at hn
    have hs : (C.deficit,0)+shift (steps C) Finset.univ ∈ exteriorCells C Finset.univ := by
      rw [exteriorCells,Plank.LinearBands.strictCell]
      intro i
      simpa only [Finset.mem_univ,if_true] using lt_of_le_of_ne (hbounds i) (hn i)
    have hz : (C.deficit,0) ∈ RowDeletion.triangle C.deficit := by
      exact ⟨hδ.le,le_rfl,by simp⟩
    have hh := (source_faces C hu hδ he Finset.univ hz hs).2.1 rfl
    linarith only [hh,hy]
  obtain ⟨i,hi⟩ := hex
  refine ⟨i,?_,hi⟩
  have hother := far_upper C hu hne hw hδ he 0 ⟨le_rfl,hδ.le⟩ i
  simp only [sub_zero] at hother
  rw [hi] at hother
  simp only [dot,Prod.fst_add,Prod.snd_add,zero_add] at hother
  have hle : (C.plank i).u.1 ≤ (C.plank i).u.2 := by
    nlinarith only [hother,hδ]
  exact lt_of_le_of_ne hle (hne i)

end Quant.TriangleFarEdge

/-- info: 'Quant.TriangleFarEdge.vertical_upper_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleFarEdge.vertical_upper_contact
