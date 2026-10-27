/- Six coordinate contacts and one finite slope choice prove the planar bound. -/
module
public import Plank.Convex.FinitePairSupports
public import Plank.Convex.ConvexPairSeparator
public import Plank.Convex.PlanarChosenWeights
public import Plank.Convex.PlanarSignedCaps
public import Plank.Convex.PlanarWindowBounds
public import Plank.Convex.SignedCubeCover
public import Plank.Convex.BoundedPolyhedron
public import Mathlib.Analysis.Convex.PathConnected
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.PlanarFrozenMinimum
open Plank.Convex PlanarCoverSpace PlanarCoverMinimum SignedCubeCover PlanarSignedCaps

/-- Frozen rows need preserve coverage only inside the strict-window region.
Closedness of the covering set prevents the deficient sublevel from leaving it. -/
theorem fixed_rows_locally_tight {J : Type*} [Fintype J]
    (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (f : J → Walls 3 →L[ℝ] ℝ) (t : J → ℝ) (B : Walls 3)
    (hB : B ∈ strictWindows) (hdef : width B < 1)
    (hrows : ∀ j, t j ≤ f j B) (hcard : Fintype.card J ≤ 6)
    (hcover : ∀ Y ∈ strictWindows, (∀ j, t j ≤ f j Y) → Covers K Y) :
    ∃ Y ∈ strictWindows, width Y ≤ width B ∧ Fintype.card J = 6 ∧
      ∀ j, t j = f j Y := by
  let S := {Y : Walls 3 | ∀ j, t j ≤ f j Y} ∩ {Y | width Y ≤ width B}
  have hlocal (Y : Walls 3) (hYS : Y ∈ S) (hYC : Y ∈ unitCovers K) : Y ∈ strictWindows := by
    have hpos := widths_positive K hK hbox hL hU Y hYC.1.2 hYC.2 (hYS.2.trans_lt hdef)
    have hends := endpoints_strict K hK hbox hL hU Y hYC.1.2
      (fun i => ⟨hYC.1.1.1.1 i, hYC.1.1.2.2 i⟩) hYC.2 (hYS.2.trans_lt hdef)
    exact fun i => ⟨(hends i).1, hpos i, (hends i).2⟩
  have hconv : Convex ℝ S := by
    convert
      (convex_iInter fun j => (convex_Ici (t j)).linear_preimage (f j).toLinearMap).inter
        ((convex_Iic (width B)).linear_preimage width.toLinearMap) using 1
    ext Y
    simp [S]
  have hBS : B ∈ S := ⟨hrows, le_refl (width B)⟩
  have hkeep : S ⊆ strictWindows := by
    intro Y hYS
    by_contra hn
    obtain ⟨Z, hZS, hZU, hZC⟩ := hconv.isPreconnected strictWindows (unitCovers K)ᶜ
      open_strictWindows (compact_unitCovers K).isClosed.isOpen_compl
      (fun X hXS => by
        by_cases hXC : X ∈ unitCovers K
        · exact Or.inl (hlocal X hXS hXC)
        · exact Or.inr hXC)
      ⟨B, hBS, hB⟩ ⟨Y, hYS, fun hYC => hn (hlocal Y hYS hYC)⟩
    exact hZC (unitCovers_of_strict_cover K Z hZU (hcover Z hZU hZS.1))
  have hb : Bornology.IsBounded S := (compact_unitCovers K).isBounded.subset
    (fun Y hYS => unitCovers_of_strict_cover K Y (hkeep hYS) (hcover Y (hkeep hYS) hYS.1))
  obtain ⟨hc, Y, hy, hcost⟩ := BoundedPolyhedron.bounded_root (fun j => (f j).toLinearMap) t
    width.toLinearMap B hrows hb (by
      simpa [Module.finrank_prod, Module.finrank_pi] using hcard)
  exact ⟨Y, hkeep ⟨fun j => (hy j).le, hcost⟩, hcost,
    by simpa [Module.finrank_prod, Module.finrank_pi] using hc, hy⟩


theorem strict_cut_witnesses (K : Set (Point 3))
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (B : Walls 3) (hB : B ∈ strictWindows) :
    ∀ b i, ∃ x ∈ K, wall b i B < cut b i x := by
  intro b i
  cases b
  · obtain ⟨x, hx, hxi⟩ := hL i
    exact ⟨x, hx, by simpa [cut, wall, hxi] using (hB i).1⟩
  · obtain ⟨x, hx, hxi⟩ := hU i
    exact ⟨x, hx, by simpa [cut, wall, hxi] using (hB i).2.2⟩

def PlaneTight (c : Point 3) (D : ℝ) (Y : Walls 3) : Selection → Prop
  | .inl _ => True
  | .inr b => planeLevel D b = planeRow c b Y

theorem not_both_plane_tight (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (Y : Walls 3) (hY : Y ∈ strictWindows)
    (h0 : PlaneTight c D Y (.inr false)) (h1 : PlaneTight c D Y (.inr true)) : False := by
  have hL : D = ∑ i, c i * Y.1 i := by
    simpa [PlaneTight, planeLevel, planeRow_apply, wall, mul_neg, Finset.sum_neg_distrib] using h0
  have hU : D = ∑ i, c i * Y.2 i := by
    simpa [PlaneTight, planeLevel, planeRow_apply, wall] using h1
  have hlt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun i _ => mul_lt_mul_of_pos_left (hY i).2.1 (hc i))
  exact hlt.ne (hL.symm.trans hU)

/-- Removing the opposite edge of a mixed star preserves geometric coverage
inside the strict-window region, without imposing its replacement plane row. -/
theorem covers_without_opposite (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hc : ∀ j, 0 < c j) (hplane : ∀ x ∈ K, ∑ j, c j * x j = D)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (B : Walls 3) (hB : B ∈ strictWindows)
    (s : Finset Selection) (hcover : ∀ w, ∃ e ∈ s, hits e w)
    (v : Vertex) (i : Fin 3) (hodd : ∀ j, j ≠ i → v j ≠ v i)
    (hv : SignedCubeCover.star s v)
    (hs : ∀ e ∈ s.erase (edge i v), Allowed K c D B e) : Covers K B := by
  have hb := mixed_plane_strict K c D hc hplane B (fun j => (hB j).2.1.le)
    (strict_cut_witnesses K hL hU B hB) (s.erase (edge i v)) hs v i hodd
    (fun k hk => Finset.mem_erase.mpr ⟨edge_ne k i v hk, hv k⟩)
  apply covers_of_allowed K c D hc hplane B (insert (.inr (!v i)) (s.erase (edge i v)))
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hb.le
    · exact hs e he
  · exact replace_star_cover s hcover v i hodd hv

/-- An arbitrary inclusion-minimal cube cover suffices; there is no second
minimization of its edge count. A mixed star would need at most five rows. -/
theorem constant_stars_of_deficit_of_rows (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D)
    (B : Walls 3) (hB : B ∈ unitCovers K) (hdefB : width B < 1)
    (hstrict : B ∈ strictWindows)
    (rows : ∀ e, Allowed K c D B e → ∃ f : Walls 3 →L[ℝ] ℝ, ∃ t : ℝ,
      t ≤ f B ∧ (∀ Y, t ≤ f Y → Allowed K c D Y e) ∧
        (∀ Y, t = f Y → PlaneTight c D Y e)) :
    ∃ s : Finset Selection, (∀ e ∈ s, Allowed K c D B e) ∧
      star s (constant false) ∧ star s (constant true) := by
  classical
  have six (s : Finset Selection) (hs : ∀ e ∈ s, Allowed K c D B e) (hcard : s.card ≤ 6)
      (hcover : ∀ Y ∈ strictWindows, (∀ e ∈ s, Allowed K c D Y e) → Covers K Y) :
      ∃ Y ∈ strictWindows, s.card = 6 ∧ ∀ e ∈ s, PlaneTight c D Y e := by
    have hrows (e : s) := rows e.val (hs _ e.property)
    choose f t ht hpreserve htight using hrows
    obtain ⟨Y, hY, _, hcard', hall⟩ := fixed_rows_locally_tight
      K hK hbox hL hU f t B hstrict hdefB ht (by simpa using hcard)
      (fun Y hY hrows => hcover Y hY
        (fun e he => hpreserve ⟨e, he⟩ Y (hrows ⟨e, he⟩)))
    exact ⟨Y, hY, by simpa using hcard', fun e he => htight ⟨e, he⟩ Y (hall _)⟩
  obtain ⟨s, hs, hminimal⟩ := exists_minimal_cover (Allowed K c D B)
    (exists_allowed K hK c D hc hplane B hB.2)
  have hcard := (cube_count s hminimal).1
  obtain ⟨Y, hY, hsix, hall⟩ := six s hs hcard
    (fun Y _ hY => covers_of_allowed K c D hc hplane Y s hY hminimal.1)
  refine ⟨s, hs, ?_⟩
  rcases (cube_count s hminimal).2 hsix with hboth | hboth | ⟨v, h0, h1, hv⟩
  · exact False.elim (not_both_plane_tight c D hc Y hY
      (hall _ hboth.1) (hall _ hboth.2))
  · exact hboth
  · obtain ⟨i, hi⟩ := mixed_odd v h0 h1
    obtain ⟨_, _, hsize, _⟩ := six (s.erase (edge i v))
      (fun e he => hs e (Finset.mem_of_mem_erase he))
      ((Finset.card_le_card (Finset.erase_subset _ _)).trans hcard)
      (fun Z hZ hrows => covers_without_opposite K c D hc hplane hL hU Z hZ
        s hminimal.1 v i hi hv hrows)
    have herase := Finset.card_erase_add_one (hv i)
    omega


abbrev Hull {ι : Type*} (X : ι → Point 3) := convexHull ℝ (Set.range X)

def excess (c : Point 3) (B : Walls 3) (b : Bool) (i : Fin 3) : Point 3 →ᵃ[ℝ] ℝ :=
  c i • ((cut b i).toLinearMap.toAffineMap - AffineMap.const ℝ _ (wall b i B))

@[simp] theorem excess_apply (c : Point 3) (B : Walls 3) (b : Bool) (i : Fin 3) (x : Point 3) :
    excess c B b i x = c i * (cut b i x - wall b i B) := rfl

theorem choose_edge {ι : Type*} [Fintype ι] (X : ι → Point 3)
    (c : Point 3) (hc : ∀ i, 0 < c i) (B : Walls 3)
    (hw : ∀ b i, ∃ v, wall b i B < cut b i (X v))
    (e : Edge) (he : PairEmpty (Hull X) B e) :
    ∃ a, PlanarChosenSupports.Chosen
      (fun v => excess c B e.2.1 (e.1 + 1) (X v))
      (fun v => excess c B e.2.2 (e.1 + 2) (X v)) a ∧
      ∀ x ∈ Hull X, excess c B e.2.1 (e.1 + 1) x +
        a * excess c B e.2.2 (e.1 + 2) x ≤ 0 := by
  apply FinitePairSupports.chosen_on_hull X
  · obtain ⟨v, hv⟩ := hw e.2.1 (e.1 + 1)
    exact ⟨v, mul_pos (hc _) (sub_pos.mpr hv)⟩
  · obtain ⟨v, hv⟩ := hw e.2.2 (e.1 + 2)
    exact ⟨v, mul_pos (hc _) (sub_pos.mpr hv)⟩
  · rintro ⟨x, hx, h1, h2⟩
    exact he ⟨x, hx, sub_pos.mp (pos_of_mul_pos_right h1 (hc _).le),
      sub_pos.mp (pos_of_mul_pos_right h2 (hc _).le)⟩

/-- Positive pair separators give a supporting row on the original convex set. -/
theorem supporting_row (K : Set (Point 3)) (hK : Convex ℝ K)
    (c : Point 3) (D : ℝ) (B : Walls 3)
    (hw : ∀ b i, ∃ x ∈ K, wall b i B < cut b i x)
    (e : Selection) (he : Allowed K c D B e) :
    ∃ L : Walls 3 →L[ℝ] ℝ, ∃ t : ℝ, t ≤ L B ∧
      (∀ Y, t ≤ L Y → Allowed K c D Y e) ∧
      (∀ Y, t = L Y → PlaneTight c D Y e) := by
  cases e with
  | inr b => exact ⟨planeRow c b, planeLevel D b, he, fun _ h => h, fun _ h => h⟩
  | inl e =>
    let g : Point 3 →ᵃ[ℝ] ℝ :=
      (firstCut e).toLinearMap.toAffineMap - AffineMap.const ℝ _ (firstWall e B)
    let h : Point 3 →ᵃ[ℝ] ℝ :=
      (secondCut e).toLinearMap.toAffineMap - AffineMap.const ℝ _ (secondWall e B)
    obtain ⟨a, ha, hsupport⟩ := ConvexCellSeparation.exists_pos_separator K hK g h
      (by obtain ⟨x, hx, hg⟩ := hw e.2.1 (e.1 + 1)
          exact ⟨x, hx, sub_pos.mpr hg⟩)
      (by obtain ⟨x, hx, hh⟩ := hw e.2.2 (e.1 + 2)
          exact ⟨x, hx, sub_pos.mpr hh⟩)
      (by rintro ⟨x, hx, hg, hh⟩
          exact he ⟨x, hx, sub_pos.mp hg, sub_pos.mp hh⟩)
    let L := firstWall e + a • secondWall e
    refine ⟨L, L B, le_rfl, ?_, fun _ _ => trivial⟩
    intro Y hY ⟨x, hx, h1, h2⟩
    have H := hsupport x hx
    change firstCut e x - firstWall e B + a * (secondCut e x - secondWall e B) ≤ 0 at H
    have h2 := mul_lt_mul_of_pos_left h2 ha
    change firstWall e B + a * secondWall e B ≤ firstWall e Y + a * secondWall e Y at hY
    nlinarith only [H, h1, h2, hY]

/-- Pair rows use the unscaled cuts and need no condition on the plane normal. -/
theorem finite_supporting_row {ι : Type*} [Fintype ι] (X : ι → Point 3)
    (c : Point 3) (D : ℝ) (B : Walls 3)
    (hw : ∀ b i, ∃ v, wall b i B < cut b i (X v))
    (e : Selection) (he : Allowed (Hull X) c D B e) :
    ∃ f : Walls 3 →L[ℝ] ℝ, ∃ t : ℝ, t ≤ f B ∧
      (∀ Y, t ≤ f Y → Allowed (Hull X) c D Y e) ∧
      (∀ Y, t = f Y → PlaneTight c D Y e) :=
  supporting_row (Hull X) (convex_convexHull ℝ _) c D B
    (by intro b i
        obtain ⟨v, hv⟩ := hw b i
        exact ⟨X v, subset_convexHull ℝ _ ⟨v, rfl⟩, hv⟩) e he

/-- The finite support calculation uses points of the original convex set;
the points need not be replaced by their convex hull. -/
theorem constant_stars_bound_on_points {ι : Type*} [Fintype ι]
    (K : Set (Point 3)) (hK : Convex ℝ K) (X : ι → Point 3) (hX : ∀ v, X v ∈ K)
    (hL : ∀ i, ∃ v, X v i = 0) (hU : ∀ i, ∃ v, X v i = 1)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ v, ∑ i, c i * X v i = D)
    (B : Walls 3) (hB : B ∈ strictWindows)
    (hw : ∀ b i, ∃ v, wall b i B < cut b i (X v))
    (s : Finset Selection) (hs : ∀ e ∈ s, Allowed K c D B e)
    (hstars : star s (constant false) ∧ star s (constant true)) : 1 ≤ width B := by
  have cuts (b : Bool) (i : Fin 3) :
      ∃ a, PlanarChosenSupports.Chosen (fun v => excess c B b i (X v))
        (fun v => excess c B b (i + 1) (X v)) a := by
    have H : star s (constant b) := by cases b <;> simp_all only
    have he := hs _ (H (i + 2))
    have he : PairEmpty K B (i + 2, b, b) := by
      simpa only [Allowed, edge, constant] using he
    obtain ⟨a, ha⟩ := FinitePairSupports.chosen_on_points K hK X hX
      (excess c B b ((i + 2) + 1)) (excess c B b ((i + 2) + 2))
      (by obtain ⟨v, hv⟩ := hw b ((i + 2) + 1)
          exact ⟨v, mul_pos (hc _) (sub_pos.mpr hv)⟩)
      (by obtain ⟨v, hv⟩ := hw b ((i + 2) + 2)
          exact ⟨v, mul_pos (hc _) (sub_pos.mpr hv)⟩)
      (by rintro ⟨x, hx, h1, h2⟩
          exact he ⟨x, hx, sub_pos.mp (pos_of_mul_pos_right h1 (hc _).le),
            sub_pos.mp (pos_of_mul_pos_right h2 (hc _).le)⟩)
    refine ⟨a, ?_⟩
    fin_cases i <;> simpa using ha
  choose a ha using cuts true
  choose b hb using cuts false
  have h := PlanarChosenSupports.width_of_chosen (fun v i => c i * X v i)
    (fun i => c i * B.1 i) (fun i => c i * B.2 i) c a b D
    (fun i => mul_le_mul_of_nonneg_left (hB i).2.1.le (hc i).le) hc hplane
    (fun i => (hL i).imp fun v hv => by rw [hv, mul_zero])
    (fun i => (hU i).imp fun v hv => by rw [hv, mul_one])
    (fun i => by simpa [PlanarChosenSupports.Chosen,
      cut, wall, mul_sub] using ha i)
    (fun i => by simpa [PlanarChosenSupports.Chosen,
      cut, wall, neg_add_eq_sub, mul_sub] using hb i)
  have hratio (i : Fin 3) : (c i * B.2 i - c i * B.1 i) / c i = B.2 i - B.1 i := by
    rw [← mul_sub, mul_div_cancel_left₀ _ (hc i).ne']
  simpa only [hratio, width_apply] using h

theorem finite_constant_stars_bound {ι : Type*} [Fintype ι] (X : ι → Point 3)
    (hL : ∀ i, ∃ v, X v i = 0) (hU : ∀ i, ∃ v, X v i = 1)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ v, ∑ i, c i * X v i = D)
    (B : Walls 3) (hB : B ∈ strictWindows)
    (hw : ∀ b i, ∃ v, wall b i B < cut b i (X v))
    (s : Finset Selection) (hs : ∀ e ∈ s, Allowed (Hull X) c D B e)
    (hstars : star s (constant false) ∧ star s (constant true)) : 1 ≤ width B :=
  constant_stars_bound_on_points (Hull X) (convex_convexHull ℝ _) X
    (fun v => subset_convexHull ℝ _ ⟨v, rfl⟩) hL hU c D hc hplane B hB hw s hs hstars

/-- Supporting rows and finite chosen slopes give the width bound. -/
theorem finite_width_bound {ι : Type*} [Fintype ι] (X : ι → Point 3)
    (hbox : ∀ x ∈ Hull X, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ v, X v i = 0) (hU : ∀ i, ∃ v, X v i = 1)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ Hull X, ∑ i, c i * x i = D)
    (lo hi : Point 3) (horder : ∀ i, lo i ≤ hi i)
    (hcover : Covers (Hull X) (lo, hi)) : 1 ≤ ∑ i, (hi i - lo i) := by
  classical
  let K := Hull X
  have hK : Convex ℝ K := convex_convexHull ℝ _
  have hX (v : ι) : X v ∈ K := subset_convexHull ℝ _ ⟨v, rfl⟩
  have hL' (i : Fin 3) : ∃ x ∈ K, x i = 0 := by
    obtain ⟨v, hv⟩ := hL i
    exact ⟨X v, hX v, hv⟩
  have hU' (i : Fin 3) : ∃ x ∈ K, x i = 1 := by
    obtain ⟨v, hv⟩ := hU i
    exact ⟨X v, hX v, hv⟩
  by_contra! hdef
  let B := clipped (lo, hi)
  have hB : B ∈ unitCovers K := clipped_unitCovers K hbox (lo, hi) horder hcover
  have hcost : width B ≤ width (lo, hi) := clipped_width_le (lo, hi) horder
  have hdefB : width B < 1 := hcost.trans_lt (by simpa only [width_apply] using hdef)
  have hpos := widths_positive K hK hbox hL' hU' B hB.1.2 hB.2 hdefB
  have hends := endpoints_strict K hK hbox hL' hU' B hB.1.2
    (fun i => ⟨hB.1.1.1.1 i, hB.1.1.2.2 i⟩) hB.2 hdefB
  have hstrict : B ∈ strictWindows := fun i => ⟨(hends i).1, hpos i, (hends i).2⟩
  have hw (b : Bool) (i : Fin 3) : ∃ v, wall b i B < cut b i (X v) := by
    cases b
    · obtain ⟨v, hv⟩ := hL i
      exact ⟨v, by simpa [wall, cut, hv] using (hstrict i).1⟩
    · obtain ⟨v, hv⟩ := hU i
      exact ⟨v, by simpa [wall, cut, hv] using (hstrict i).2.2⟩
  obtain ⟨s, hs, hstars⟩ := constant_stars_of_deficit_of_rows
    K hK hbox hL' hU' c D hc hplane B hB hdefB hstrict
    (fun e he => finite_supporting_row X c D B hw e he)
  exact hdefB.not_ge (finite_constant_stars_bound X hL hU c D hc
    (fun v => hplane _ (hX v)) B hstrict hw s hs hstars)

/-- Restrict once to the convex hull of six coordinate contacts. -/
theorem width_bound (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D)
    (lo hi : Point 3) (horder : ∀ i, lo i ≤ hi i)
    (hcover : Covers K (lo, hi)) : 1 ≤ ∑ i, (hi i - lo i) := by
  choose x hx hxzero using hL
  choose y hy hymax using hU
  let X : Fin 3 × Bool → Point 3 := fun v => if v.2 then y v.1 else x v.1
  have hX (v : Fin 3 × Bool) : X v ∈ K := by
    rcases v with ⟨i, b⟩
    cases b
    · exact hx i
    · exact hy i
  have hsub : Hull X ⊆ K := convexHull_min (by rintro _ ⟨v, rfl⟩; exact hX v) hK
  exact finite_width_bound X (fun x hx => hbox x (hsub hx))
    (fun i => ⟨(i, false), hxzero i⟩) (fun i => ⟨(i, true), hymax i⟩)
    c D hc (fun x hx => hplane x (hsub hx)) lo hi horder
    (fun x hx => hcover x (hsub hx))

end Plank.Convex.PlanarFrozenMinimum

#print axioms Plank.Convex.PlanarFrozenMinimum.supporting_row
#print axioms Plank.Convex.PlanarFrozenMinimum.constant_stars_bound_on_points
