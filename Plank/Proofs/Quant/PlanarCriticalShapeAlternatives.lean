/- Exact finite-vertex or endpoint-apex alternatives for a critical cover. -/
module

public import Plank.Proofs.Quant.PlanarCriticalAnchoredShape

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCriticalShapeAlternatives

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarShiftedDomain (deficit)
open Plank.Convex.DeficientHeightTilt
open Plank.Convex.PlanarTight TwoPlankClassification PlanarCriticalAnchoredShape

/-- The four directional orientations of the two endpoint-apex
corner-cut families. Every entry consists of endpoint equations and
linear enclosure inequalities. -/
def DegenerateNormal (K : Set Point) (X Y : Point →ᵃ[ℝ] ℝ)
    (l u m v : ℝ) : Prop :=
  DegenerateAnchored K X Y l u m v ∨
  DegenerateAnchored K (reflect X) Y (1-u) (1-l) m v ∨
  DegenerateAnchored K Y X m v l u ∨
  DegenerateAnchored K (reflect Y) X (1-v) (1-m) l u

/-- An exhaustive shape refinement of the positive two-plank full-cover
normal forms. The only possibilities not forced to have at most four
vertices are the explicit endpoint-apex enclosures. -/
theorem normal_alternatives {K : Set Point} (hK : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y) (l u m v : ℝ)
    (hn : Normal K X Y l u m v) :
    (∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) ∨
      DegenerateNormal K X Y l u m v := by
  by_cases hf : ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}
  · exact Or.inl hf
  have hanchored (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y) (l u m v : ℝ)
      (ha : Anchored K X Y l u m v) : DegenerateAnchored K X Y l u m v := by
    rcases anchored_alternatives hK X Y H l u m v ha with ⟨a,b,d,he⟩ | hd
    · exact (hf ⟨a,b,d,d,by simpa using he⟩).elim
    · exact hd
  rcases hn with hn | hn | hn | hn | hn
  · exact (hf (PlanarCriticalQuadrilateral.shape_of_interior hK ![X,Y] H
      l u m v hn)).elim
  · exact Or.inr (Or.inl (hanchored X Y H l u m v hn))
  · exact Or.inr (Or.inr (Or.inl (hanchored (reflect X) Y H.reflect
      (1-u) (1-l) m v hn)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hanchored Y X H.swap m v l u hn))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hanchored (reflect Y) X H.swap.reflect
      (1-v) (1-m) l u hn))))

/-- Apply the exhaustive shape alternatives to an actual full cover with
both critical widths positive and total actual relative width one. -/
theorem critical_cover_alternatives {K : Set Point} (hK : Convex ℝ K)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : Ranges K (f 0) (f 1)) (r : Endpoints 2)
    (hR : budget K f r = 1) (ho : ∀ i, r.1 i < r.2 i)
    (hcover : K ⊆ ⋃ i, {x | r.1 i ≤ f i x ∧ f i x ≤ r.2 i}) :
    (∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) ∨
      DegenerateNormal K (f 0) (f 1) (r.1 0) (r.2 0) (r.1 1) (r.2 1) := by
  have hn := PlanarCriticalNormalForm.normal_of_critical_cover hK f H r hR
    (fun i => (ho i).le) hcover
  rcases hn with ⟨_,_,hn⟩ | ⟨he,_,_⟩ | ⟨he,_,_⟩
  · exact normal_alternatives hK (f 0) (f 1) H _ _ _ _ hn
  · exact (ne_of_lt (ho 0) he).elim
  · exact (ne_of_lt (ho 1) he).elim

/-- Positive windows that vanish together at positive time are strictly
positive everywhere on the backward half-line. -/
theorem strict_backward {m : ℕ} (p z : Endpoints m) (hp : ∀ i, p.1 i < p.2 i)
    (τ : ℝ) (hτ : 0 < τ) (hz : ∀ i, (p+τ • z).1 i = (p+τ • z).2 i)
    (t : ℝ) (ht : t < 0) : ∀ i, (p+t • z).1 i < (p+t • z).2 i := by
  intro i
  have hzi : p.1 i+τ*z.1 i = p.2 i+τ*z.2 i := hz i
  have hdw : z.2 i-z.1 i < 0 := by nlinarith only [hzi,hp i,hτ]
  have hprod := mul_pos_of_neg_of_neg ht hdw
  change p.1 i+t*z.1 i < p.2 i+t*z.2 i
  nlinarith only [hprod,hp i]

/-- No positive-cell-count premise is needed: simultaneous collapse of
an actual quantitative equality yields either a four-vertex body or an
explicit endpoint-apex critical cover, retaining all positive-cell copies.
The displayed line hypotheses are supplied by the equality-line theorem. -/
theorem simultaneous_alternatives {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : Ranges K (f 0) (f 1))
    (p z : Endpoints 2) (c : ℝ) (hp : ∀ i, p.1 i < p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (hu : ∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2)
    (τ : ℝ) (hτ : 0 < τ) (hz : ∀ i, (p+τ • z).1 i = (p+τ • z).2 i) :
    (∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) ∨
      ∃ r : Endpoints 2, budget K f r = 1 ∧
        DegenerateNormal K (f 0) (f 1) (r.1 0) (r.2 0) (r.1 1) (r.2 1) ∧
        ∀ s, 0 < (volume (signCell K f p.1 p.2 s)).toReal →
          ∃ y : Point, signCell K f r.1 r.2 s = {y} ∧
            signCell K f p.1 p.2 s = AffineMap.homothety y (1-budget K f p) ''
              signCell K f (p+τ • z).1 (p+τ • z).2 s := by
  obtain ⟨hW0,hW1⟩ := PlanarCriticalNormalForm.rangeWidth_eq_one (f 0) (f 1) H
  have hW : ∀ i, 0 < rangeWidth K (f i) := by
    intro i
    fin_cases i
    · change 0 < rangeWidth K (f 0)
      rw [hW0]
      exact zero_lt_one
    · change 0 < rangeWidth K (f 1)
      rw [hW1]
      exact zero_lt_one
  obtain ⟨hc,hcrit⟩ := PlanarSimultaneousCollapse.critical_cover_and_copies_at
    hK hconv hne hV f hW p z c (fun i => (hp i).le) hR0 hR1 heq hd hu τ hτ hz
  let r : Endpoints 2 := p+(-(c⁻¹)) • z
  change budget K f r = 1 ∧ (∀ i, r.1 i ≤ r.2 i) ∧
    K ⊆ ⋃ i, {x | r.1 i ≤ f i x ∧ f i x ≤ r.2 i} ∧ _ at hcrit
  have hstrict : ∀ i, r.1 i < r.2 i := strict_backward p z hp τ hτ hz _
    (neg_neg_of_pos (inv_pos.mpr hc))
  rcases critical_cover_alternatives hconv f H r hcrit.1 hstrict hcrit.2.2.1 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨r,hcrit.1,h,hcrit.2.2.2⟩

end Plank.PlanarCriticalShapeAlternatives

/-- info: 'Plank.PlanarCriticalShapeAlternatives.normal_alternatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCriticalShapeAlternatives.normal_alternatives
/-- info: 'Plank.PlanarCriticalShapeAlternatives.simultaneous_alternatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCriticalShapeAlternatives.simultaneous_alternatives
