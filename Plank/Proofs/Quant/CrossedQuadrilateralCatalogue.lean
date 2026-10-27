/- The exhaustive quadrilateral catalogue, including arbitrary null planks. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSingleCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCatalogue
open Plank Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarEqualityReductions
open CrossedQuadrilateralChartSymmetry CrossedQuadrilateralSupportOriginal
open Plank.Convex.DeficientHeightTilt

def pairForms (f : Fin 3 → Point →ᵃ[ℝ] ℝ) : Fin 2 → Point →ᵃ[ℝ] ℝ := fun i => f i.castSucc

def pairEndpoints (p : Endpoints 3) : Endpoints 2 :=
  (fun i => p.1 i.castSucc,fun i => p.2 i.castSucc)

theorem pair_budget (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hn : p.1 2=p.2 2) : budget K (pairForms f) (pairEndpoints p) = budget K f p := by
  simp [budget,pairForms,pairEndpoints,Fin.sum_univ_two,Fin.sum_univ_three,← hn]

theorem pair_gap {K : Set Point} (hne : K.Nonempty)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (hn : p.1 2=p.2 2) :
    gapArea K (pairForms f) (pairEndpoints p) = gapArea K f p := by
  have hu : (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) =
      (⋃ i : Fin 2, {x | p.1 i.castSucc ≤ f i.castSucc x ∧ f i.castSucc x ≤ p.2 i.castSucc}) ∪
      {x | p.1 2 ≤ f 2 x ∧ f 2 x ≤ p.2 2} := by
    ext x
    simp [Fin.exists_fin_succ] <;> tauto
  have hz : volume {x | p.1 2 ≤ f 2 x ∧ f 2 x ≤ p.2 2} = 0 := by
    rw [← hn]
    exact PlanarSingleActivePlank.volume_band_zero hne (f 2) (hW 2) _
  unfold gapArea
  rw [hu,← Set.sdiff_sdiff,measure_sdiff_null hz]
  rfl

theorem pair_equality_iff {K : Set Point} (hne : K.Nonempty)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (hn : p.1 2=p.2 2) :
    Equality K (pairForms f) (pairEndpoints p) ↔ Equality K f p := by
  unfold Equality
  rw [pair_gap hne f p hW hn,pair_budget K f p hn]

def Zero (p : Endpoints 3) : Prop := ∀ i, p.1 i=p.2 i
def One (p : Endpoints 3) : Prop := p.1 0<p.2 0 ∧ p.1 1=p.2 1 ∧ p.1 2=p.2 2
def Two (p : Endpoints 3) : Prop := p.1 0<p.2 0 ∧ p.1 1<p.2 1 ∧ p.1 2=p.2 2
def Positive (p : Endpoints 3) : Prop := ∀ i, p.1 i<p.2 i

theorem activity_split (p : Endpoints 3) (ho : ∀ i, p.1 i ≤ p.2 i) :
    Zero p ∨ (∃ e : Equiv.Perm (Fin 3), One (endpoints e p)) ∨
      (∃ e : Equiv.Perm (Fin 3), Two (endpoints e p)) ∨ Positive p := by
  classical
  have hn (i) (h : ¬p.1 i<p.2 i) : p.1 i=p.2 i := le_antisymm (ho i) (le_of_not_gt h)
  by_cases h0 : p.1 0<p.2 0
  · by_cases h1 : p.1 1<p.2 1
    · by_cases h2 : p.1 2<p.2 2
      · exact Or.inr (Or.inr (Or.inr (by intro i; fin_cases i; exact h0; exact h1; exact h2)))
      · exact Or.inr (Or.inr (Or.inl ⟨Equiv.refl _,h0,h1,hn 2 h2⟩))
    · by_cases h2 : p.1 2<p.2 2
      · right; right; left
        refine ⟨Equiv.swap 1 2,?_⟩
        simpa [Two,endpoints,Equiv.swap_apply_def] using And.intro h0 (And.intro h2 (hn 1 h1))
      · exact Or.inr (Or.inl ⟨Equiv.refl _,h0,hn 1 h1,hn 2 h2⟩)
  · by_cases h1 : p.1 1<p.2 1
    · by_cases h2 : p.1 2<p.2 2
      · right; right; left
        refine ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1),?_⟩
        simpa [Two,endpoints,Equiv.swap_apply_def] using And.intro h1 (And.intro h2 (hn 0 h0))
      · right; left
        refine ⟨Equiv.swap 0 1,?_⟩
        simpa [One,endpoints,Equiv.swap_apply_def] using And.intro h1 (And.intro (hn 0 h0) (hn 2 h2))
    · by_cases h2 : p.1 2<p.2 2
      · right; left
        refine ⟨Equiv.swap 0 2,?_⟩
        simpa [One,endpoints,Equiv.swap_apply_def] using And.intro h2 (And.intro (hn 1 h1) (hn 0 h0))
      · left
        intro i
        fin_cases i; exact hn 0 h0; exact hn 1 h1; exact hn 2 h2

/-- Delete arbitrary null lines. With one positive band it is calibrated;
with two, use the crossed-or-adjacent catalogue; with three, use the complete
triple catalogue. Every presentation preserves original physical bands and widths. -/
def Families (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) : Prop :=
  Zero p ∨
  (∃ e : Equiv.Perm (Fin 3), One (endpoints e p) ∧
    ∃ D : CrossedQuadrilateralSingleCatalogue.Presentation K (f (e 0)) (p.1 (e 0)) (p.2 (e 0)),
      D.calibrated) ∨
  (∃ e : Equiv.Perm (Fin 3), Two (endpoints e p) ∧
    ∃ D : CrossedQuadrilateralTwoPlankFamilies.Presentation K
      (pairForms (fun i => f (e i))) (pairEndpoints (endpoints e p)), D.inFamilies) ∨
  (Positive p ∧ CrossedQuadrilateralTripleCatalogue.Catalogue K f p)

theorem equality_iff_families {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hR : budget K f p < 1) : Equality K f p ↔ Families K f p := by
  have hne : K.Nonempty := by
    obtain ⟨S,T,hb⟩ := CrossedQuadrilateralGenuine.exists_model hG hV
    rw [hb]
    exact (CrossedQuadrilateralContainedOriginal.body_nonempty S).image T
  have hOne (e : Equiv.Perm (Fin 3)) (h : One (endpoints e p)) :
      Equality K f p ↔ ∃ D : CrossedQuadrilateralSingleCatalogue.Presentation K
        (f (e 0)) (p.1 (e 0)) (p.2 (e 0)), D.calibrated := by
    rw [← equality_permute e K f p]
    exact CrossedQuadrilateralSingleCatalogue.equality_iff_family hG hV _ _
      (fun i => hW (e i)) h.1 h.2.1 h.2.2 (by rwa [budget_permute])
  have hTwo (e : Equiv.Perm (Fin 3)) (h : Two (endpoints e p)) :
      Equality K f p ↔ ∃ D : CrossedQuadrilateralTwoPlankFamilies.Presentation K
        (pairForms (fun i => f (e i))) (pairEndpoints (endpoints e p)), D.inFamilies := by
    rw [← equality_permute e K f p,← pair_equality_iff hne _ _ (fun i => hW (e i)) h.2.2]
    apply CrossedQuadrilateralTwoPlankFamilies.equality_iff_families hG hV
    · intro i; exact hW (e i.castSucc)
    · intro i; fin_cases i; exact h.1; exact h.2.1
    · rwa [pair_budget K _ _ h.2.2,budget_permute]
  constructor
  · intro he
    rcases activity_split p ho with hz | ⟨e,h⟩ | ⟨e,h⟩ | hp
    · exact Or.inl hz
    · exact Or.inr (Or.inl ⟨e,h,(hOne e h).mp he⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e,h,(hTwo e h).mp he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hp,
        (CrossedQuadrilateralTripleCatalogue.equality_iff_catalogue hG hV f p hW hp hR).mp he⟩))
  · rintro (hz | ⟨e,h,hD⟩ | ⟨e,h,hD⟩ | ⟨hp,hc⟩)
    · exact equality_of_budget_zero hne f p hW ho ((budget_eq_zero_iff f p hW ho).mpr hz)
    · exact (hOne e h).mpr hD
    · exact (hTwo e h).mpr hD
    · exact CrossedQuadrilateralTripleCatalogue.equality_of_catalogue f p hR hc

/-- At and above budget one equality is precisely an actual cover; below
one the exhaustive calibrated-band catalogue applies, including every null case. -/
theorem all_budgets_iff {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i) :
    Equality K f p ↔
      (1 ≤ budget K f p ∧ K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) ∨
      (budget K f p < 1 ∧ Families K f p) := by
  by_cases hR : budget K f p < 1
  · simp only [hR,not_le.mpr hR,false_and,false_or,true_and]
    exact equality_iff_families hG hV f p hW ho hR
  · simp only [hR,le_of_not_gt hR,false_and,or_false,true_and]
    exact equality_iff_cover_of_one_le (genuine_compact hG) (genuine_convex hG) hV f p (le_of_not_gt hR)

end Quant.CrossedQuadrilateralCatalogue

/-- info: 'Quant.CrossedQuadrilateralCatalogue.all_budgets_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCatalogue.all_budgets_iff
