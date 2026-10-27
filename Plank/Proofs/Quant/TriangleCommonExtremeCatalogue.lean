/- The common-extreme catalogue is independent of the plank orientations. -/
module
public import Plank.Proofs.Quant.TriangleCommonMinimumAffineCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCommonExtremeCatalogue
open Set MeasureTheory Proofs.Basic Proofs.Transport
open TriangleCommonMinimumAffineCatalogue TriangleCommonMinimumCatalogue
open scoped BigOperators

def AtMinimum (T : Triangle) (p : Plank) : Prop :=
  dot p.u T.A ≤ dot p.u T.B ∧ dot p.u T.A ≤ dot p.u T.C

def AtExtreme (T : Triangle) (p : Plank) : Prop :=
  AtMinimum T p ∨ (dot p.u T.B ≤ dot p.u T.A ∧ dot p.u T.C ≤ dot p.u T.A)

def oriented (T : Triangle) (p : Plank) : Plank := by
  classical
  exact if AtMinimum T p then p else flipP p

theorem flip_set (p : Plank) : (flipP p).set=p.set := by
  ext z
  change (-p.hi ≤ dot (-p.u) z ∧ dot (-p.u) z ≤ -p.lo) ↔
    (p.lo ≤ dot p.u z ∧ dot p.u z ≤ p.hi)
  rw [dot_neg_left]
  simp only [neg_le_neg_iff,and_comm]

theorem flip_width (T : Triangle) (p : Plank) : (flipP p).relWidth T=p.relWidth T := by
  change (-p.lo- -p.hi)/T.width (-p.u)=(p.hi-p.lo)/T.width p.u
  rw [width_neg]
  ring

theorem oriented_set (T : Triangle) (p : Plank) : (oriented T p).set=p.set := by
  unfold oriented
  split_ifs
  · rfl
  · exact flip_set p

theorem oriented_width (T : Triangle) (p : Plank) : (oriented T p).relWidth T=p.relWidth T := by
  unfold oriented
  split_ifs
  · rfl
  · exact flip_width T p

theorem oriented_minimum (T : Triangle) (p : Plank) (h : AtExtreme T p) :
    AtMinimum T (oriented T p) := by
  by_cases hm : AtMinimum T p
  · simpa only [oriented,if_pos hm] using hm
  · have hh := h.resolve_left hm
    unfold AtMinimum oriented
    rw [if_neg hm]
    change dot (-p.u) T.A ≤ dot (-p.u) T.B ∧ dot (-p.u) T.A ≤ dot (-p.u) T.C
    simp only [dot_neg_left,neg_le_neg_iff]
    exact hh

theorem oriented_common (T : Triangle) (p : Fin 3 → Plank) (h : ∀ i, AtExtreme T (p i)) :
    CommonMinimum T (fun i => oriented T (p i)) := fun i => oriented_minimum T (p i) (h i)

/-- All bands are unchanged as physical sets; only their data orientation
is chosen so the shared extreme vertex becomes a shared minimum. -/
theorem equality_iff_catalogue (T : Triangle) (p : Fin 3 → Plank)
    (h : ∀ i, AtExtreme T (p i)) (hw : ∀ i, 0 < (p i).relWidth T)
    (hR : (∑ i, (p i).relWidth T) < 1) :
    ((volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) ↔
      Catalogue (triangleConfig T (fun i => oriented T (p i)) (oriented_common T p h)) := by
  have he := triangle_equality_iff_catalogue T (fun i => oriented T (p i))
    (oriented_common T p h) (fun i => by rw [oriented_width]; exact hw i)
    (by simpa only [oriented_width] using hR)
  simpa only [oriented_set,oriented_width] using he

/-- Cycle the vertex labels while retaining the same physical triangle. -/
def rotate (T : Triangle) : Triangle :=
  ⟨T.B,T.C,T.A,by
    have he : ({T.B,T.C,T.A} : Set (ℝ × ℝ))={T.A,T.B,T.C} := by
      ext z
      simp only [mem_insert_iff,mem_singleton_iff]
      tauto
    rw [he]
    exact T.not_collinear⟩

theorem rotate_set (T : Triangle) : (rotate T).set=T.set := by
  ext z
  change (∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a+b+c=1 ∧
    z=a • T.B+b • T.C+c • T.A) ↔
    (∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a+b+c=1 ∧
    z=a • T.A+b • T.B+c • T.C)
  constructor
  · rintro ⟨a,b,c,ha,hb,hc,hs,hz⟩
    exact ⟨c,a,b,hc,ha,hb,by linarith only [hs],by rw [hz]; abel⟩
  · rintro ⟨a,b,c,ha,hb,hc,hs,hz⟩
    exact ⟨b,c,a,hb,hc,ha,by linarith only [hs],by rw [hz]; abel⟩

theorem rotate_width (T : Triangle) (p : Plank) : p.relWidth (rotate T)=p.relWidth T := by
  unfold Plank.relWidth Triangle.width rotate
  congr 2
  · change max (dot p.u T.B) (max (dot p.u T.C) (dot p.u T.A)) =
      max (dot p.u T.A) (max (dot p.u T.B) (dot p.u T.C))
    ac_rfl
  · change min (dot p.u T.B) (min (dot p.u T.C) (dot p.u T.A)) =
      min (dot p.u T.A) (min (dot p.u T.B) (dot p.u T.C))
    ac_rfl

def atVertex (T : Triangle) (v : Fin 3) : Triangle := ![T,rotate T,rotate (rotate T)] v

theorem atVertex_set (T : Triangle) (v : Fin 3) : (atVertex T v).set=T.set := by
  fin_cases v
  · rfl
  · exact rotate_set T
  · exact (rotate_set (rotate T)).trans (rotate_set T)

theorem atVertex_width (T : Triangle) (p : Plank) (v : Fin 3) :
    p.relWidth (atVertex T v)=p.relWidth T := by
  fin_cases v
  · rfl
  · exact rotate_width T p
  · exact (rotate_width (rotate T) p).trans (rotate_width T p)

/-- The common extreme vertex may be any of the three vertices, and
each original band may have either normal orientation. -/
theorem vertex_equality_iff_catalogue (T : Triangle) (p : Fin 3 → Plank) (v : Fin 3)
    (h : ∀ i, AtExtreme (atVertex T v) (p i))
    (hw : ∀ i, 0 < (p i).relWidth T) (hR : (∑ i, (p i).relWidth T) < 1) :
    ((volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) ↔
      Catalogue (triangleConfig (atVertex T v) (fun i => oriented (atVertex T v) (p i))
        (oriented_common (atVertex T v) p h)) := by
  have he := equality_iff_catalogue (atVertex T v) p h
    (fun i => by rw [atVertex_width]; exact hw i) (by simpa only [atVertex_width] using hR)
  simpa only [atVertex_set,atVertex_width] using he

end Quant.TriangleCommonExtremeCatalogue

/-- info: 'Quant.TriangleCommonExtremeCatalogue.vertex_equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCommonExtremeCatalogue.vertex_equality_iff_catalogue
