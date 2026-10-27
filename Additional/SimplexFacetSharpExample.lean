/- Sharp positive-width covers along all faces of a simplex. Orient the last
form as the coordinate sum; all forms then share the minimizing vertex zero. -/
module

public import SimplexSharpExample

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SimplexFacetSharpExample

open Set MeasureTheory SimplexSharpExample

variable (ι : Type*) [Fintype ι]

def form : Option ι → (ι → ℝ) →ᵃ[ℝ] ℝ
  | none => (∑i,(LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).toAffineMap
  | some i => coordinate ι i

@[simp] theorem form_none_apply (x : ι → ℝ) : form ι none x=∑i,x i := by simp [form]
@[simp] theorem form_some_apply (i : ι) (x : ι → ℝ) : form ι (some i) x=x i := rfl
@[simp] theorem form_zero (q : Option ι) : form ι q 0=0 := by cases q <;> simp

@[simp] theorem form_linear_apply (q : Option ι) (x : ι → ℝ) :
    (form ι q).linear x=form ι q x := by
  simpa using (form ι q).linearMap_vsub x 0

theorem range_bounds (q : Option ι) {x : ι → ℝ} (hx : x∈body ι) :
    0≤form ι q x ∧ form ι q x≤1 := by
  cases q with
  | none =>
    simpa only [form_none_apply] using
      (show 0≤∑i,x i ∧ (∑i,x i)≤1 from ⟨Finset.sum_nonneg (fun i _ => hx.1 i),hx.2⟩)
  | some i => exact ⟨hx.1 i,coordinate_le_one ι hx i⟩

@[simp] theorem width_form [Nonempty ι] (q : Option ι) :
    Body.width (body ι) (form ι q)=1 := by
  classical
  cases q with
  | some i => exact width_coordinate ι i
  | none =>
    let j : ι := Classical.arbitrary ι
    have h := Body.width_eq_of_realisers (f := form ι none) (single_mem ι j) (zero_mem ι)
      (fun x hx => by simpa using (range_bounds ι none hx).2)
      (fun x hx => by simpa using (range_bounds ι none hx).1)
    simpa using h

/-- In dimension at least two, all d+1 face directions are nonproportional. -/
theorem directions_nonproportional [Nontrivial ι] {p q : Option ι} (hpq : p≠q) (c : ℝ) :
    (form ι p).linear≠c • (form ι q).linear := by
  classical
  intro he
  cases p with
  | none =>
    cases q with
    | none => exact hpq rfl
    | some j =>
      obtain ⟨i,hij⟩ := exists_ne j
      have h := LinearMap.congr_fun he (Pi.single i (1 : ℝ))
      simp [hij.symm] at h
  | some i =>
    cases q with
    | some j =>
      exact SimplexSharpExample.directions_nonproportional ι
        (fun h => hpq (congrArg some h)) c he
    | none =>
      obtain ⟨j,hji⟩ := exists_ne i
      have h := LinearMap.congr_fun he (Pi.single j (1 : ℝ))
      have hc : c=0 := by simpa [hji.symm] using h.symm
      have h' := LinearMap.congr_fun he (Pi.single i (1 : ℝ))
      simp [hc] at h'

def lo (a : ℝ) (q : Option ι) : ℝ := q.elim (1-a) (fun _ => 0)
def hi (r : ι → ℝ) (q : Option ι) : ℝ := q.elim 1 r

def covered (a : ℝ) (r : ι → ℝ) : Set (ι → ℝ) :=
  ⋃q,LinearBands.closedBand (form ι q) (lo ι a q) (hi ι r q)

omit [Fintype ι] in
theorem windows_ordered {a : ℝ} (ha : 0≤a) {r : ι → ℝ} (hr : ∀i,0≤r i) (q : Option ι) :
    lo ι a q≤hi ι r q := by cases q <;> simp [lo,hi,ha,hr]

omit [Fintype ι] in
theorem windows_positive {a : ℝ} (ha : 0<a) {r : ι → ℝ} (hr : ∀i,0<r i) (q : Option ι) :
    lo ι a q<hi ι r q := by cases q <;> simp [lo,hi,ha,hr]

theorem budget_eq [Nonempty ι] (a : ℝ) (r : ι → ℝ) :
    (∑q,(hi ι r q-lo ι a q)/Body.width (body ι) (form ι q))=a+∑i,r i := by
  simp [lo,hi]
  ring

/-- The original uncovered set fits in a homothetic simplex of ratio 1-R. -/
theorem gap_subset_contracted (a : ℝ) (r : ι → ℝ) (hR : a+(∑i,r i)<1) :
    body ι\covered ι a r⊆contracted ι r (1-(a+∑i,r i)) := by
  intro x hx
  have hu : (∑i,x i)<1-a := by
    apply lt_of_not_ge
    intro h
    apply hx.2 (mem_iUnion.mpr ⟨none,?_⟩)
    simpa [LinearBands.closedBand,lo,hi] using And.intro h hx.1.2
  apply mem_contracted ι r (sub_pos.mpr hR)
  · intro i
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    apply hx.2 (mem_iUnion.mpr ⟨some i,?_⟩)
    exact ⟨hx.1.1 i,h⟩
  · linarith only [hu]

variable (μ : Measure (ι → ℝ)) [μ.IsAddHaarMeasure]

/-- Actual equality for arbitrary nonnegative face widths of total R<1.
All d+1 planks are present; the last one is based at the opposite face. -/
theorem gap_eq [Nonempty ι] (a : ℝ) (r : ι → ℝ)
    (ha : 0≤a) (hr : ∀i,0≤r i) (hR : a+(∑i,r i)<1) :
    μ.real (body ι\covered ι a r)=
      (1-(a+∑i,r i))^Fintype.card ι*μ.real (body ι) := by
  have hc : IsCompact (contracted ι r (1-(a+∑i,r i))) :=
    (compact_body ι).image (by fun_prop)
  have hf : μ (contracted ι r (1-(a+∑i,r i)))≠⊤ := hc.measure_ne_top
  have hup := ENNReal.toReal_mono hf (measure_mono (gap_subset_contracted ι a r hR))
  change μ.real _≤μ.real _ at hup
  rw [contracted_volume ι μ r (1-(a+∑i,r i)) (sub_pos.mpr hR).le] at hup
  have hlo := FiniteDimensionalCommonMinimum.uncovered_volume_lower_bound μ
    (compact_body ι) (convex_body ι) (form ι) 0 (zero_mem ι)
    (fun q x hx => by simpa using (range_bounds ι q hx).1)
    (lo ι a) (hi ι r) (windows_ordered ι ha hr) (fun q => by simp)
  rw [budget_eq] at hlo
  apply le_antisymm hup
  simpa [covered,Measure.real,max_eq_right (sub_pos.mpr hR).le] using hlo

/-- Complete geometric data for the nonparallel equality family. -/
theorem sharp_family [Nontrivial ι] (a : ℝ) (r : ι → ℝ)
    (ha : 0<a) (hr : ∀i,0<r i) (hR : a+(∑i,r i)<1) :
    IsCompact (body ι) ∧ Convex ℝ (body ι) ∧ 0<μ.real (body ι) ∧
    (∀q,lo ι a q<hi ι r q) ∧ (∀q,0<Body.width (body ι) (form ι q)) ∧
    (∀p q,p≠q → ∀c:ℝ,(form ι p).linear≠c • (form ι q).linear) ∧
    (∑q,(hi ι r q-lo ι a q)/Body.width (body ι) (form ι q))=a+∑i,r i ∧
    μ.real (body ι\covered ι a r)=(1-(a+∑i,r i))^Fintype.card ι*μ.real (body ι) := by
  exact ⟨compact_body ι,convex_body ι,volume_pos ι μ,windows_positive ι ha hr,
    fun q => by simp,fun _ _ h c => directions_nonproportional ι h c,
    budget_eq ι a r,gap_eq ι μ a r ha.le (fun i => (hr i).le) hR⟩

/-- Every budget strictly between zero and one is attained with all d+1
plank widths positive; the fixed directions are nonparallel when d≥2. -/
theorem exact_budget_family [Nontrivial ι] {R : ℝ} (hR0 : 0<R) (hR1 : R<1) :
    ∃a : ℝ,∃r : ι → ℝ,(∀q,lo ι a q<hi ι r q) ∧
      (∑q,(hi ι r q-lo ι a q)/Body.width (body ι) (form ι q))=R ∧
      μ.real (body ι\covered ι a r)=(1-R)^Fintype.card ι*μ.real (body ι) := by
  let w := R/((Fintype.card ι:ℝ)+1)
  have hc : 0<(Fintype.card ι:ℝ)+1 := by positivity
  have hw : 0<w := div_pos hR0 hc
  have hs : w+(∑_ : ι,w)=R := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    calc
      w+(Fintype.card ι:ℝ)*w = ((Fintype.card ι:ℝ)+1)*w := by ring
      _ = R := mul_div_cancel₀ _ hc.ne'
  refine ⟨w,fun _ => w,windows_positive ι hw (fun _ => hw),?_,?_⟩
  · rw [budget_eq,hs]
  · have h := gap_eq ι μ w (fun _ => w) hw.le (fun _ => hw.le)
      (by rw [hs]; exact hR1)
    simpa only [hs] using h

end Plank.SimplexFacetSharpExample
