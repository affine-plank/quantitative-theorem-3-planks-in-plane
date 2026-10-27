/- At the retained minimum, six contact cells make arbitrary positive pair
supports sufficient. No finite extremizer hull or nearest-one slopes. -/
module
public import Plank.Proofs.Quant.FiniteDimensionalEndpointCells
public import Plank.Convex.PlanarCornerSupports
public import Plank.Convex.PlanarSixContactCaps

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSixContactMinimum

open Set Filter MeasureTheory FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling FiniteDimensionalMinimumCellRank
  FiniteDimensionalMinimumContactRank
  Convex.PlanarCoverSpace Convex.PlanarSignedCaps Convex.SignedCubeCover
open scoped Topology BigOperators

variable {n m : ℕ}

def coordinateImage (K : Set (FiniteDimensionalCapWindowScaling.Point n))
    (f : Fin m → (FiniteDimensionalCapWindowScaling.Point n) →ᵃ[ℝ] ℝ) :
    Set (Point m) := (fun x i => f i x) '' K

/-- A strict cover with six contact cells suffices. Neither frozen-row
minimality nor a finite-point slope selection is required. -/
theorem width_bound_of_six_contact_cells
    {K : Set (FiniteDimensionalCapWindowScaling.Point n)}
    {f : Fin 3 → (FiniteDimensionalCapWindowScaling.Point n) →ᵃ[ℝ] ℝ}
    (hK : Convex ℝ (coordinateImage K f))
    (hL : ∀ i, ∃ x ∈ coordinateImage K f, x i = 0)
    (hU : ∀ i, ∃ x ∈ coordinateImage K f, x i = 1)
    (c : Point 3) (level : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ coordinateImage K f, ∑ i, c i * x i = level)
    {p : Endpoints (Fin 3)} (hstrict : p ∈ strictWindows)
    (hcover : Covers (coordinateImage K f) p)
    (hcount : 6 ≤ (nonemptyCells K f p).card) :
    1 ≤ ∑ i, (p.2 i-p.1 i) := by
  classical
  have hw : ∀ b i, ∃ x ∈ coordinateImage K f, wall b i p < cut b i x := by
    intro b i
    cases b
    · obtain ⟨x,hx,hi⟩ := hL i
      exact ⟨x,hx,by simpa [cut,wall,hi] using (hstrict i).1⟩
    · obtain ⟨x,hx,hi⟩ := hU i
      exact ⟨x,hx,by simpa [cut,wall,hi] using (hstrict i).2.2⟩
  let sign : Finset (Fin 3) → Vertex := fun s i => decide (i ∈ s)
  have hsign : Function.Injective sign := by
    intro s t h
    ext i
    have h' := congrFun h i
    simpa only [sign,decide_eq_decide] using h'
  let S := (nonemptyCells K f p).image sign
  have hweak : ∀ v ∈ S, Convex.PlanarSixContactCaps.Weak (coordinateImage K f) p v := by
    intro v hv
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
    have hh : (signCell K f p s).Nonempty := by
      simpa only [nonemptyCells,Finset.mem_filter,Finset.mem_univ,true_and] using hs
    obtain ⟨x,hx,hcuts⟩ := hh
    refine ⟨fun j => f j x,⟨x,hx,rfl⟩,?_⟩
    intro i
    have h := hcuts i
    by_cases hi : i ∈ s <;> simpa [sign,hi,cut,wall] using h
  obtain ⟨hmixed,hempty⟩ := Convex.PlanarSixContactCaps.mixed_cells_and_pairs
    (coordinateImage K f) hK c level hc hplane p (fun i => (hstrict i).2.1)
    hw hcover S (by simpa only [S,Finset.card_image_of_injective _ hsign] using hcount) hweak
  let X (b : Bool) (v : coordinateImage K f) (i : Fin 3) := c i * cut b i v.val
  let W (b : Bool) (i : Fin 3) := c i * wall b i p
  have cuts (b : Bool) (i : Fin 3) :
      ∃ a : ℝ, 0 < a ∧ ∀ v : coordinateImage K f,
        X b v i + a * X b v (i+1) ≤ W b i + a * W b (i+1) := by
    have he := hempty b (i+2)
    have he : ¬ ∃ x ∈ coordinateImage K f,
        wall b i p < cut b i x ∧ wall b (i+1) p < cut b (i+1) x := by
      have h₁ : i+2+1 = i := by fin_cases i <;> rfl
      have h₂ : i+2+2 = i+1 := by fin_cases i <;> rfl
      simpa only [PairEmpty,firstWall,secondWall,firstCut,secondCut,
        h₁,h₂] using he
    obtain ⟨a,ha,hs⟩ := Convex.ConvexCellSeparation.positive_support
      (coordinateImage K f) hK
      (c i • (cut b i).toLinearMap.toAffineMap)
      (c (i+1) • (cut b (i+1)).toLinearMap.toAffineMap) (W b i) (W b (i+1))
      (by obtain ⟨x,hx,hh⟩ := hw b i
          exact ⟨x,hx,mul_lt_mul_of_pos_left hh (hc i)⟩)
      (by obtain ⟨x,hx,hh⟩ := hw b (i+1)
          exact ⟨x,hx,mul_lt_mul_of_pos_left hh (hc (i+1))⟩)
      (fun ⟨x,hx,hi,hj⟩ => he ⟨x,hx,(mul_lt_mul_iff_right₀ (hc i)).mp hi,
        (mul_lt_mul_iff_right₀ (hc (i+1))).mp hj⟩)
    exact ⟨a,ha,fun v => hs v.val v.property⟩
  choose a ha supports using cuts
  have contacts (b : Bool) (i : Fin 3) :
      ∃ v, X b v i = W b i ∧ X b v (i+1) = W b (i+1) := by
    have hij : i ≠ i+1 := by fin_cases i <;> decide
    have hleaf : leaf b (i+2) ≠ constant false ∧ leaf b (i+2) ≠ constant true := by
      cases b <;> fin_cases i <;> decide
    obtain ⟨x,hx,hcuts⟩ := hweak _ ((hmixed _).mpr hleaf)
    refine ⟨⟨x,hx⟩,Convex.PlanarSixCellSupports.pair_contact
      (X b) (W b) (a b) (ha b) (supports b) ⟨x,hx⟩ i (i+1) hij ?_ ?_⟩
    · apply mul_le_mul_of_nonneg_left _ (hc i).le
      have h := hcuts i
      fin_cases i <;> simpa [leaf] using h
    · apply mul_le_mul_of_nonneg_left _ (hc (i+1)).le
      have h := hcuts (i+1)
      fin_cases i <;> simpa [leaf] using h
  have h := Convex.PlanarSixCellSupports.width_bound_of_corner_contacts (X true)
    (fun i => c i*p.1 i) (W true) c (a true) (a false) level
    (fun i => mul_lt_mul_of_pos_left (hstrict i).2.1 (hc i)) hc (ha true) (ha false)
    (fun v => hplane v.val v.property)
    (fun i => by obtain ⟨x,hx,hi⟩ := hL i; exact ⟨⟨x,hx⟩,by simp [X,cut,hi]⟩)
    (fun i => by obtain ⟨x,hx,hi⟩ := hU i; exact ⟨⟨x,hx⟩,by simp [X,cut,hi]⟩)
    (supports true)
    (fun i v => by
      simpa [X,W,cut,wall,add_comm] using neg_le_neg (supports false i v))
    (contacts true)
    (by
      intro i
      obtain ⟨v,hi,hj⟩ := contacts false i
      exact ⟨v,by simpa [X,W,cut,wall] using congrArg Neg.neg hi,
        by simpa [X,W,cut,wall] using congrArg Neg.neg hj⟩)
  have hratio (i : Fin 3) : (c i*p.2 i-c i*p.1 i)/c i = p.2 i-p.1 i := by
    rw [← mul_sub,mul_div_cancel_left₀ _ (hc i).ne']
  change 1 ≤ ∑ i, (c i*p.2 i-c i*p.1 i)/c i at h
  simpa only [hratio] using h

end Plank.PlanarSixContactMinimum

#print axioms Plank.PlanarSixContactMinimum.width_bound_of_six_contact_cells
