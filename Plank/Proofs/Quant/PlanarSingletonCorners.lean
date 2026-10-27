/- Singleton corner cells exclude every supporting-edge full-cover normal form. -/
module

public import Plank.Proofs.Quant.PlanarCriticalNormalForm

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSingletonCorners

open Set PlanarQuantitative
open Plank.Convex.PlanarTight TwoPlankClassification

def corner (K : Set Point) (X Y : Point →ᵃ[ℝ] ℝ) (l u m v : ℝ)
    (sx sy : Bool) : Set Point :=
  {x | x ∈ K ∧ (if sx then u ≤ X x else X x ≤ l) ∧
    (if sy then v ≤ Y x else Y x ≤ m)}

/-- Every closed corner outside the two windows consists of one point. -/
def SingletonCorners (K : Set Point) (X Y : Point →ᵃ[ℝ] ℝ) (l u m v : ℝ) : Prop :=
  ∀ sx sy, (corner K X Y l u m v sx sy).Nonempty ∧
    (corner K X Y l u m v sx sy).Subsingleton

theorem corner_swap (K : Set Point) (X Y : Point →ᵃ[ℝ] ℝ) (l u m v : ℝ)
    (sx sy : Bool) : corner K Y X m v l u sx sy = corner K X Y l u m v sy sx := by
  ext x
  simp only [corner,mem_ofPred_eq,and_comm]

theorem corner_reflect (K : Set Point) (X Y : Point →ᵃ[ℝ] ℝ) (l u m v : ℝ)
    (sx sy : Bool) :
    corner K (reflect X) Y (1-u) (1-l) m v sx sy = corner K X Y l u m v (!sx) sy := by
  cases sx <;> cases sy <;> ext x <;>
    simp only [corner,mem_ofPred_eq,Bool.false_eq_true,if_false,if_true,
      Bool.not_false,Bool.not_true,reflect_apply,sub_le_sub_iff_left]

theorem SingletonCorners.swap {K : Set Point} {X Y : Point →ᵃ[ℝ] ℝ} {l u m v : ℝ}
    (h : SingletonCorners K X Y l u m v) : SingletonCorners K Y X m v l u := by
  intro sx sy
  simpa only [corner_swap] using h sy sx

theorem SingletonCorners.reflect {K : Set Point} {X Y : Point →ᵃ[ℝ] ℝ} {l u m v : ℝ}
    (h : SingletonCorners K X Y l u m v) :
    SingletonCorners K (reflect X) Y (1-u) (1-l) m v := by
  intro sx sy
  simpa only [corner_reflect] using h (!sx) sy

private theorem lower_not_singleton {K : Set Point} (hK : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (B A : Point) (hB : B ∈ K) (hA : A ∈ K)
    (hXB : X B = 0) (hXA : X A = 0) (hYB : Y B = 0)
    (m : ℝ) (hm : 0 < m) (hmA : m < Y A)
    (hs : {x | x ∈ K ∧ X x ≤ 0 ∧ Y x ≤ m}.Subsingleton) : False := by
  have hYA : 0 < Y A := hm.trans hmA
  let t := m/(2*Y A)
  have ht0 : 0 ≤ t := (div_pos hm (mul_pos (by norm_num) hYA)).le
  have ht1 : t ≤ 1 := by
    apply (div_le_one (mul_pos (by norm_num) hYA)).mpr
    linarith only [hmA,hYA]
  let C := B+t • (A-B)
  have hC : C ∈ K := hK.add_smul_sub_mem hB hA ⟨ht0,ht1⟩
  have hXC : X C = 0 := by simp [C,Body.map_add_smul_sub,hXB,hXA]
  have hYC : Y C = m/2 := by
    simp only [C,Body.map_add_smul_sub,hYB,sub_zero,zero_add]
    dsimp [t]
    field_simp
  have he := hs (show B ∈ {x | x ∈ K ∧ X x ≤ 0 ∧ Y x ≤ m} from
    ⟨hB,by rw [hXB],by rw [hYB]; exact hm.le⟩)
    (show C ∈ {x | x ∈ K ∧ X x ≤ 0 ∧ Y x ≤ m} from
      ⟨hC,by rw [hXC],by rw [hYC]; linarith only [hm]⟩)
  have hh := congrArg Y he
  rw [hYB,hYC] at hh
  linarith only [hh,hm]

private theorem upper_not_singleton {K : Set Point} (hK : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (B A : Point) (hB : B ∈ K) (hA : A ∈ K)
    (hXB : X B = 0) (hXA : X A = 0) (hYB : Y B = 0) (hYA : Y A = 1)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hs : {x | x ∈ K ∧ X x ≤ 0 ∧ v ≤ Y x}.Subsingleton) : False := by
  let t := (v+1)/2
  have ht0 : 0 ≤ t := by dsimp [t]; linarith only [hv0]
  have ht1 : t ≤ 1 := by dsimp [t]; linarith only [hv1]
  let C := B+t • (A-B)
  have hC : C ∈ K := hK.add_smul_sub_mem hB hA ⟨ht0,ht1⟩
  have hXC : X C = 0 := by simp [C,Body.map_add_smul_sub,hXB,hXA]
  have hYC : Y C = t := by simp [C,Body.map_add_smul_sub,hYB,hYA]
  have he := hs (show A ∈ {x | x ∈ K ∧ X x ≤ 0 ∧ v ≤ Y x} from
    ⟨hA,by rw [hXA],by rw [hYA]; exact hv1.le⟩)
    (show C ∈ {x | x ∈ K ∧ X x ≤ 0 ∧ v ≤ Y x} from
      ⟨hC,by rw [hXC],by rw [hYC]; dsimp [t]; linarith only [hv1]⟩)
  have hh := congrArg Y he
  rw [hYA,hYC] at hh
  dsimp [t] at hh
  linarith only [hh,hv1]

/-- The supporting-edge family cannot have all four closed corners
nonempty and singleton. The degenerate apex parameters zero and one are
included; no injectivity or polygon assumption is needed. -/
theorem not_anchored {K : Set Point} (hK : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y) (l u m v : ℝ)
    (hs : SingletonCorners K X Y l u m v) : ¬ Anchored K X Y l u m v := by
  rintro ⟨rfl,hu,hu1,c,hc,hc1,hm,hv,hshape⟩
  by_cases hcp : 0 < c
  · obtain ⟨B,hB,hYB⟩ := H.minY
    have hXB : X B = 0 := by
      have hlow := (hshape B hB).1
      rw [hYB] at hlow
      have hn := (H.box B hB).1.1
      nlinarith only [hlow,hn,hcp]
    obtain ⟨A,hA⟩ := (hs false true).1
    change A ∈ K ∧ X A ≤ 0 ∧ v ≤ Y A at hA
    have hXA : X A = 0 := le_antisymm hA.2.1 (H.box A hA.1).1.1
    have hm0 : 0 < m := by rw [hm]; exact mul_pos hu hcp
    have hmv : m < v := by rw [hv,← hm]; linarith only [hu1]
    exact lower_not_singleton hK X Y B A hB hA.1 hXB hXA hYB m hm0
      (hmv.trans_le hA.2.2) (hs false false).2
  · have hc0 : c = 0 := le_antisymm (le_of_not_gt hcp) hc
    have hm0 : m = 0 := by rw [hm,hc0,mul_zero]
    have hv0 : 0 ≤ v := by rw [hv,hc0,mul_zero,zero_add]; linarith only [hu1]
    have hv1 : v < 1 := by rw [hv,hc0,mul_zero,zero_add]; linarith only [hu]
    obtain ⟨B,hB⟩ := (hs false false).1
    change B ∈ K ∧ X B ≤ 0 ∧ Y B ≤ m at hB
    have hXB : X B = 0 := le_antisymm hB.2.1 (H.box B hB.1).1.1
    have hYB : Y B = 0 := le_antisymm (hB.2.2.trans_eq hm0) (H.box B hB.1).2.1
    obtain ⟨A,hA,hYA⟩ := H.maxY
    have hXA : X A = 0 := by
      have hh := (hshape A hA).2
      rw [hc0,hYA] at hh
      have hn := (H.box A hA).1.1
      linarith only [hh,hn]
    exact upper_not_singleton hK X Y B A hB.1 hA hXB hXA hYB hYA v hv0 hv1
      (hs false true).2

/-- All four supporting-edge alternatives are excluded. A positive
full-cover normal form with singleton corners is the interior quadrilateral
normal form. This is a shape theorem, not an area optimization. -/
theorem interior_of_normal {K : Set Point} (hK : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y) (l u m v : ℝ)
    (hs : SingletonCorners K X Y l u m v) (hn : Normal K X Y l u m v) :
    TwoPlankInterior.Normal K X Y l u m v := by
  rcases hn with hn | hn | hn | hn | hn
  · exact hn
  · exact (not_anchored hK X Y H l u m v hs hn).elim
  · exact (not_anchored hK (reflect X) Y H.reflect (1-u) (1-l) m v hs.reflect hn).elim
  · exact (not_anchored hK Y X H.swap m v l u hs.swap hn).elim
  · exact (not_anchored hK (reflect Y) X H.swap.reflect (1-v) (1-m) l u
      hs.swap.reflect hn).elim

/-- Translate the quantitative sign-cell singleton conclusion into the
four geometric corners used by the full-cover classification. -/
theorem singletonCorners_of_signCells (K : Set Point)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (r : PlanarParameterDomain.Endpoints 2)
    (hs : ∀ s, ∃ y : Point, PlanarGapCells.signCell K f r.1 r.2 s = {y}) :
    SingletonCorners K (f 0) (f 1) (r.1 0) (r.2 0) (r.1 1) (r.2 1) := by
  intro sx sy
  let s : Finset (Fin 2) := (if sx then {0} else ∅) ∪ (if sy then {1} else ∅)
  have he : corner K (f 0) (f 1) (r.1 0) (r.2 0) (r.1 1) (r.2 1) sx sy =
      PlanarGapCells.signCell K f r.1 r.2 s := by
    cases sx <;> cases sy <;> ext x <;>
      simp [corner,PlanarGapCells.signCell,Plank.LinearBands.weakCell,s,
        Fin.forall_fin_two,and_assoc,and_left_comm]
  obtain ⟨y,hy⟩ := hs s
  rw [he,hy]
  exact ⟨singleton_nonempty y,subsingleton_singleton⟩

/-- With both widths positive, a critical full cover whose four cells are
singletons is in the interior quadrilateral family. Every supporting-edge
and zero-width alternative is formally excluded. -/
theorem interior_of_critical_cover {K : Set Point} (hK : Convex ℝ K)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : Ranges K (f 0) (f 1))
    (r : PlanarParameterDomain.Endpoints 2)
    (hR : PlanarParameterDomain.budget K f r = 1)
    (ho : ∀ i, r.1 i < r.2 i)
    (hcover : K ⊆ ⋃ i, {x | r.1 i ≤ f i x ∧ f i x ≤ r.2 i})
    (hs : ∀ s, ∃ y : Point, PlanarGapCells.signCell K f r.1 r.2 s = {y}) :
    TwoPlankInterior.Normal K (f 0) (f 1) (r.1 0) (r.2 0) (r.1 1) (r.2 1) := by
  have hn := PlanarCriticalNormalForm.normal_of_critical_cover hK f H r hR
    (fun i => (ho i).le) hcover
  rcases hn with ⟨_,_,hn⟩ | ⟨hz,_,_⟩ | ⟨hz,_,_⟩
  · exact interior_of_normal hK (f 0) (f 1) H _ _ _ _
      (singletonCorners_of_signCells K f r hs) hn
  · exact (ne_of_lt (ho 0) hz).elim
  · exact (ne_of_lt (ho 1) hz).elim

end Plank.PlanarSingletonCorners

/-- info: 'Plank.PlanarSingletonCorners.interior_of_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSingletonCorners.interior_of_normal
