/- Coincident affine levels force a common direction. For support-normalized
forms the only possibilities are equality and reversal. -/
module

public import PlanarAffineDirections

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.AffineLevelCoincidence

open Set MeasureTheory PlanarQuantitative PlanarGapCells
open Plank.Convex.DeficientHeightTilt

/-- The level-set argument is algebraic and independent of dimension. -/
theorem affine_relation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f g : E →ᵃ[ℝ] ℝ) (hf : f.linear≠0) (a b : ℝ)
    (hlevel : ∀ x, f x=a → g x=b) : ∃ q c : ℝ, ∀ x, g x=q*f x+c := by
  obtain ⟨v,hv⟩ : ∃ v, f.linear v≠0 := by
    by_contra! hn
    apply hf
    apply LinearMap.ext
    intro x
    exact hn x
  have heval (h : E →ᵃ[ℝ] ℝ) (x : E) (t : ℝ) :
      h (x+t • v)=h x+t*h.linear v := by
    calc
      h (x+t • v)=h.linear (x+t • v)+h 0 := congrFun h.decomp _
      _ = h.linear x+h 0+t*h.linear v := by
        rw [map_add,map_smul]
        change h.linear x+t*h.linear v+h 0=_
        ring
      _ = _ := congrArg (fun r : ℝ => r+t*h.linear v)
        (show h.linear x+h 0=h x from (congrFun h.decomp x).symm)
  have hg (x : E) : g x+(a-f x)/f.linear v*g.linear v=b := by
    have h := hlevel (x+((a-f x)/f.linear v) • v) (by
      rw [heval,div_mul_cancel₀ _ hv]
      ring)
    rwa [heval] at h
  refine ⟨g.linear v/f.linear v,g 0-(g.linear v/f.linear v)*f 0,?_⟩
  intro x
  have hx := hg x
  have h0 := hg 0
  field_simp [hv] at hx h0 ⊢
  nlinarith only [hx,h0]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem linear_ne_zero_of_width_pos {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →ᵃ[ℝ] ℝ) (hw : 0<Body.width K f) : f.linear≠0 := by
  intro hz
  obtain ⟨P,hP,Q,hQ,hmax,hmin⟩ := Body.exists_realisers hK hne f.continuous_of_finiteDimensional
  have he := f.linearMap_vsub P Q
  rw [hz,LinearMap.zero_apply] at he
  rw [Body.width_eq_of_realisers hP hQ hmax hmin] at hw
  change 0=f P-f Q at he
  linarith only [he,hw]

/-- Actual unit range and support normalization remove every scale except
orientation. The equality holds everywhere, not only on the body. -/
theorem normalized_relation {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f g : E →ᵃ[ℝ] ℝ) (hf : Body.width K f=1) (hg : Body.width K g=1)
    (hfn : ∀ x∈K, 0≤f x ∧ f x≤1) (hgn : ∀ x∈K, 0≤g x ∧ g x≤1)
    (q c : ℝ) (hrel : ∀ x, g x=q*f x+c) :
    (∀ x, g x=f x) ∨ (∀ x, g x=1-f x) := by
  obtain ⟨P,hP,Q,hQ,hmax,hmin⟩ := Body.exists_realisers hK hne f.continuous_of_finiteDimensional
  have hW : Body.width K f=f P-f Q := Body.width_eq_of_realisers hP hQ hmax hmin
  have hP1 : f P=1 := by linarith only [hf,hW,(hfn P hP).2,(hfn Q hQ).1]
  have hQ0 : f Q=0 := by linarith only [hf,hW,(hfn P hP).2,(hfn Q hQ).1]
  by_cases hq : 0≤q
  · have hgW : Body.width K g=g P-g Q := Body.width_eq_of_realisers hP hQ
      (fun x hx => by rw [hrel,hrel]; exact add_le_add (mul_le_mul_of_nonneg_left (hmax x hx) hq) le_rfl)
      (fun x hx => by rw [hrel,hrel]; exact add_le_add (mul_le_mul_of_nonneg_left (hmin x hx) hq) le_rfl)
    have hq1 : q=1 := by rw [hrel,hrel,hP1,hQ0] at hgW; linarith only [hg,hgW]
    have hc : c=0 := by
      have h1 := (hgn P hP).2
      have h0 := (hgn Q hQ).1
      rw [hrel,hP1,hq1] at h1
      rw [hrel,hQ0,hq1] at h0
      linarith only [h1,h0]
    exact Or.inl (fun x => by rw [hrel,hq1,hc]; ring)
  · have hq' : q≤0 := le_of_lt (lt_of_not_ge hq)
    have hgW : Body.width K g=g Q-g P := Body.width_eq_of_realisers hQ hP
      (fun x hx => by rw [hrel,hrel]; exact add_le_add (mul_le_mul_of_nonpos_left (hmin x hx) hq') le_rfl)
      (fun x hx => by rw [hrel,hrel]; exact add_le_add (mul_le_mul_of_nonpos_left (hmax x hx) hq') le_rfl)
    have hq1 : q= -1 := by rw [hrel,hrel,hP1,hQ0] at hgW; linarith only [hg,hgW]
    have hc : c=1 := by
      have h1 := (hgn Q hQ).2
      have h0 := (hgn P hP).1
      rw [hrel,hQ0,hq1] at h1
      rw [hrel,hP1,hq1] at h0
      linarith only [h1,h0]
    exact Or.inr (fun x => by rw [hrel,hq1,hc]; ring)

/-- Shared boundary hyperplanes of normalized planks imply equal or reversed
functionals. Only inclusion of the first nonempty affine level is needed. -/
theorem normalized_of_level {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f g : E →ᵃ[ℝ] ℝ) (hf : Body.width K f=1) (hg : Body.width K g=1)
    (hfn : ∀ x∈K, 0≤f x ∧ f x≤1) (hgn : ∀ x∈K, 0≤g x ∧ g x≤1)
    (a b : ℝ) (hlevel : ∀ x, f x=a → g x=b) :
    (∀ x, g x=f x) ∨ (∀ x, g x=1-f x) := by
  obtain ⟨q,c,hrel⟩ := affine_relation f g
    (linear_ne_zero_of_width_pos hK hne f (by rw [hf]; norm_num)) a b hlevel
  exact normalized_relation hK hne f g hf hg hfn hgn q c hrel

end Plank.AffineLevelCoincidence

#print axioms Plank.AffineLevelCoincidence.affine_relation
#print axioms Plank.AffineLevelCoincidence.normalized_of_level
