import Submission.Homology.CompactEuclidean

/-!
# Transport of `LocalGood` to charted spaces (Hatcher 3.27(a), step 5)

Let `M` be a Hausdorff space charted on `EuclideanSpace ℝ (Fin n)`.  For a chart
`φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))` and a compact `A ⊆ φ.source`, the
relative homology `H_k(M, M ∖ A)` is identified with `H_k(ℝⁿ, ℝⁿ ∖ φ(A))` (with `ℝⁿ` lifted to
`EU n := ULift (EuclideanSpace ℝ (Fin n))`, so that everything lives in one universe):

* `chartLift φ : φ.source ≃ₜ ULift.down ⁻¹' φ.target`, the chart as a homeomorphism onto its
  lifted target;
* `excisionCompactIso`: for `A` compact inside an open `U`, excision
  `H_k(U, U ∖ A) ≅ H_k(X, X ∖ A)` (interiors form of excision, `U` and `Aᶜ` open);
* `chartTransportIso φ hA hAφ hB k : Hrel R (TopCat.of M) Aᶜ k ≅ Hrel R (TopCat.of (EU n)) Bᶜ k`
  for `B = chartUp φ '' A`, the composite of two excisions and the homeomorphism invariance
  along `chartLift φ`, natural in the subset (`chartTransportIso_natural`).

Consequences:

* `LocalGood.of_subset_chart_source`: compact subsets of a chart source are locally good;
* `LocalGood.of_isCompact`: arbitrary compact subsets of `M` are locally good (finite cover by
  compact subsets of chart sources and the union step `LocalGood.union`);
* `isZero_Hrel_compl_singleton_manifold`, `HrelComplSingletonManifoldIso`: the local homology
  of a point of `M` is `R` in degree `n` and vanishes in the other degrees;
* `exists_chartBall_isIso_ptRes`: every point `x ∈ M` has a compact neighbourhood `D` (a chart
  ball) such that all point restrictions `H_n(M, M ∖ D) → H_n(M, M ∖ {y})`, `y ∈ D`, are
  isomorphisms.
-/

open CategoryTheory Limits Metric

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-! ### Bookkeeping -/

/-- morphism-level composition of two `HrelMap`s of the identity -/
lemma HrelMap_id_comp_HrelMap_id {X : TopCat.{u}} {A B C : Set X} (h₁ : Set.MapsTo (𝟙 X) A B)
    (h₂ : Set.MapsTo (𝟙 X) B C) (h₃ : Set.MapsTo (𝟙 X) A C) (k : ℕ) :
    HrelMap R (𝟙 X) h₁ k ≫ HrelMap R (𝟙 X) h₂ k = HrelMap R (𝟙 X) h₃ k := by
  rw [← HrelMap_comp R (𝟙 X) (𝟙 X) h₁ h₂ (mapsTo_comp h₁ h₂) k]
  exact HrelMap_eq_of_eq R (Category.id_comp (𝟙 X)) _ k

/-- a commutative square with an isomorphism on the left commutes with the inverse as well -/
lemma iso_inv_comp_eq_comp_inv {𝒞 : Type*} [Category 𝒞] {a b c d : 𝒞} (i : a ≅ b) (i' : c ≅ d)
    {f : a ⟶ c} {g : b ⟶ d} (h : i.hom ≫ g = f ≫ i'.hom) : i.inv ≫ f = g ≫ i'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### Excision for a compact subset of an open set -/

section excisionCompact

variable {X : Type u} [TopologicalSpace X] [T2Space X]

lemma interior_union_interior_compl_eq_univ {U A : Set X} (hU : IsOpen U) (hA : IsCompact A)
    (hAU : A ⊆ U) : interior U ∪ interior Aᶜ = Set.univ := by
  rw [hU.interior_eq, hA.isClosed.isOpen_compl.interior_eq]
  exact Set.eq_univ_of_forall fun x => by
    by_cases hx : x ∈ A
    · exact Or.inl (hAU hx)
    · exact Or.inr hx

/-- **Excision for a compact subset of an open set**: `H_k(U, U ∖ A) ≅ H_k(X, X ∖ A)` for
`A` compact, `U` open, `A ⊆ U`, in a Hausdorff space `X`. -/
def excisionCompactIso {U A : Set X} (hU : IsOpen U) (hA : IsCompact A) (hAU : A ⊆ U) (k : ℕ) :
    Hrel R (TopCat.of U) (Subtype.val ⁻¹' Aᶜ) k ≅ Hrel R (TopCat.of X) Aᶜ k :=
  excisionIso R (X := TopCat.of X) (U := U) (V := Aᶜ)
    (interior_union_interior_compl_eq_univ hU hA hAU) k

lemma excisionCompactIso_hom {U A : Set X} (hU : IsOpen U) (hA : IsCompact A) (hAU : A ⊆ U)
    (k : ℕ) :
    (excisionCompactIso R hU hA hAU k).hom =
      HrelMap R (incl (TopCat.of X) U) (mapsTo_incl (X := TopCat.of X) U Aᶜ) k :=
  rfl

omit [T2Space X] in
lemma mapsTo_id_preimage_val {U A A' : Set X} (h : A' ⊆ A) :
    Set.MapsTo (𝟙 (TopCat.of U)) (Subtype.val ⁻¹' Aᶜ) (Subtype.val ⁻¹' A'ᶜ) :=
  fun _ hx => Set.compl_subset_compl.2 h hx

/-- naturality of `excisionCompactIso` in the compact subset -/
lemma excisionCompactIso_natural {U A A' : Set X} (hU : IsOpen U) (hA : IsCompact A)
    (hAU : A ⊆ U) (hA' : IsCompact A') (hA'U : A' ⊆ U) (h : A' ⊆ A) (k : ℕ) :
    (excisionCompactIso R hU hA hAU k).hom ≫
        HrelMap R (𝟙 (TopCat.of X)) (mapsTo_id_of_subset (Set.compl_subset_compl.2 h)) k =
      HrelMap R (𝟙 (TopCat.of U)) (mapsTo_id_preimage_val h) k ≫
        (excisionCompactIso R hU hA' hA'U k).hom :=
  HrelMap_comp_id R _ _ _ _ _ k

end excisionCompact

/-! ### Charts, lifted to universe `u` -/

section chart

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))

/-- the chart `φ`, followed by the universe lift `EuclideanSpace ℝ (Fin n) → EU n` -/
def chartUp (m : M) : EU.{u} n := ULift.up (φ m)

@[simp]
lemma chartUp_apply (m : M) : chartUp φ m = ULift.up (φ m) := rfl

/-- the chart as a homeomorphism from its source onto its lifted target -/
def chartLift : φ.source ≃ₜ (ULift.down ⁻¹' φ.target : Set (EU.{u} n)) :=
  φ.toHomeomorphSourceTarget.trans
    ((Homeomorph.ulift.{u} (X := EuclideanSpace ℝ (Fin n))).symm.image φ.target |>.trans
      (Homeomorph.setCongr (Set.ext fun x =>
        ⟨fun ⟨_, hy, e⟩ => e ▸ hy, fun h => ⟨x.down, h, rfl⟩⟩)))

@[simp]
lemma chartLift_apply_coe (x : φ.source) : (chartLift φ x : EU.{u} n) = chartUp φ x := rfl

lemma isOpen_liftedTarget : IsOpen (ULift.down ⁻¹' φ.target : Set (EU.{u} n)) :=
  φ.open_target.preimage continuous_uliftDown

lemma chartUp_image_subset {A : Set M} (hAφ : A ⊆ φ.source) :
    chartUp φ '' A ⊆ ULift.down ⁻¹' φ.target := by
  rintro _ ⟨a, ha, rfl⟩
  exact φ.map_source (hAφ ha)

lemma isCompact_chartUp_image {A : Set M} (hA : IsCompact A) (hAφ : A ⊆ φ.source) :
    IsCompact (chartUp φ '' A) :=
  hA.image_of_continuousOn (continuous_uliftUp.comp_continuousOn (φ.continuousOn.mono hAφ))

lemma chartUp_injOn : Set.InjOn (chartUp φ) φ.source :=
  fun _ hx _ hy e => φ.injOn hx hy (ULift.up.inj e)

lemma chartLift_mem_iff {A : Set M} (hAφ : A ⊆ φ.source) {B : Set (EU.{u} n)}
    (hB : chartUp φ '' A = B) (x : φ.source) :
    x ∈ (Subtype.val ⁻¹' Aᶜ : Set φ.source) ↔
      chartLift φ x ∈
        (Subtype.val ⁻¹' Bᶜ : Set (ULift.down ⁻¹' φ.target : Set (EU.{u} n))) := by
  subst hB
  change x.1 ∉ A ↔ chartUp φ x.1 ∉ chartUp φ '' A
  constructor
  · rintro hx ⟨a, ha, e⟩
    exact hx (chartUp_injOn φ (hAφ ha) x.2 e ▸ ha)
  · exact fun h hx => h ⟨x.1, hx, rfl⟩

end chart

/-! ### Transport of relative homology along a chart -/

section transport

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))

/-- **Chart transport.** For a compact `A ⊆ φ.source` and `B = chartUp φ '' A`,
`H_k(M, M ∖ A) ≅ H_k(ℝⁿ, ℝⁿ ∖ B)`. -/
def chartTransportIso {A : Set M} (hA : IsCompact A) (hAφ : A ⊆ φ.source) {B : Set (EU.{u} n)}
    (hB : chartUp φ '' A = B) (k : ℕ) :
    Hrel R (TopCat.of M) Aᶜ k ≅ Hrel R (TopCat.of (EU n)) Bᶜ k :=
  (excisionCompactIso R φ.open_source hA hAφ k).symm ≪≫
    HrelIsoOfHomeomorphIff R (chartLift φ) (chartLift_mem_iff φ hAφ hB) k ≪≫
      excisionCompactIso R (isOpen_liftedTarget φ) (hB ▸ isCompact_chartUp_image φ hA hAφ)
        (hB ▸ chartUp_image_subset φ hAφ) k

/-- naturality of the chart transport in the subset -/
theorem chartTransportIso_natural {A A' : Set M} (hA : IsCompact A) (hAφ : A ⊆ φ.source)
    (hA' : IsCompact A') (hA'φ : A' ⊆ φ.source) {B B' : Set (EU.{u} n)}
    (hB : chartUp φ '' A = B) (hB' : chartUp φ '' A' = B') (h : A' ⊆ A) (h' : B' ⊆ B) (k : ℕ) :
    (chartTransportIso R φ hA hAφ hB k).hom ≫
        HrelMap R (𝟙 (TopCat.of (EU n))) (mapsTo_id_of_subset (Set.compl_subset_compl.2 h')) k =
      HrelMap R (𝟙 (TopCat.of M)) (mapsTo_id_of_subset (Set.compl_subset_compl.2 h)) k ≫
        (chartTransportIso R φ hA' hA'φ hB' k).hom := by
  have e₃ := excisionCompactIso_natural R (isOpen_liftedTarget φ)
    (hB ▸ isCompact_chartUp_image φ hA hAφ) (hB ▸ chartUp_image_subset φ hAφ)
    (hB' ▸ isCompact_chartUp_image φ hA' hA'φ) (hB' ▸ chartUp_image_subset φ hA'φ) h' k
  have e₂ : (HrelIsoOfHomeomorphIff R (chartLift φ) (chartLift_mem_iff φ hAφ hB) k).hom ≫
      HrelMap R (𝟙 (TopCat.of (ULift.down ⁻¹' φ.target : Set (EU.{u} n))))
        (mapsTo_id_preimage_val h') k =
      HrelMap R (𝟙 (TopCat.of φ.source)) (mapsTo_id_preimage_val h) k ≫
        (HrelIsoOfHomeomorphIff R (chartLift φ) (chartLift_mem_iff φ hA'φ hB') k).hom :=
    HrelMap_comp_id R _ _ _ _ _ k
  have e₁ := iso_inv_comp_eq_comp_inv _ _
    (excisionCompactIso_natural R φ.open_source hA hAφ hA' hA'φ h k)
  simp only [chartTransportIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [e₃, ← Category.assoc _ (HrelMap R (𝟙 _) _ k), e₂, Category.assoc,
    ← Category.assoc _ _
      ((HrelIsoOfHomeomorphIff R (chartLift φ) (chartLift_mem_iff φ hA'φ hB') k).hom ≫ _),
    e₁, Category.assoc]

/-- **Chart transport, packaged.** For every compact `A ⊆ φ.source` there is an isomorphism
`H_k(M, M ∖ A) ≅ H_k(ℝⁿ, ℝⁿ ∖ φ(A))`, natural in `A`. -/
theorem exists_HrelTransport :
    ∃ i : ∀ (A : Set M), IsCompact A → A ⊆ φ.source → ∀ k,
        Hrel R (TopCat.of M) Aᶜ k ≅ Hrel R (TopCat.of (EU n)) (chartUp φ '' A)ᶜ k,
      ∀ (A : Set M) (hA : IsCompact A) (hAφ : A ⊆ φ.source) (A' : Set M) (hA' : IsCompact A')
        (hA'φ : A' ⊆ φ.source) (h : A' ⊆ A) (k : ℕ),
        (i A hA hAφ k).hom ≫ HrelMap R (𝟙 (TopCat.of (EU n)))
            (mapsTo_id_of_subset (Set.compl_subset_compl.2 (Set.image_mono h))) k =
          HrelMap R (𝟙 (TopCat.of M)) (mapsTo_id_of_subset (Set.compl_subset_compl.2 h)) k ≫
            (i A' hA' hA'φ k).hom :=
  ⟨fun _ hA hAφ k => chartTransportIso R φ hA hAφ rfl k,
    fun _ hA hAφ _ hA' hA'φ h k =>
      chartTransportIso_natural R φ hA hAφ hA' hA'φ rfl rfl h (Set.image_mono h) k⟩

/-- **Compact subsets of a chart source are locally good.** -/
theorem LocalGood.of_subset_chart_source (hn : 1 ≤ n) {A : Set M} (hA : IsCompact A)
    (hAφ : A ⊆ φ.source) : LocalGood R (TopCat.of M) n A := by
  refine LocalGood.of_iso_map (Y := TopCat.of (EU.{u} n)) (B := chartUp φ '' A) (chartUp φ)
    (fun x hx => ⟨x, hx, rfl⟩) (fun _ ⟨x, hx, e⟩ => ⟨x, hx, e⟩)
    (fun k => chartTransportIso R φ hA hAφ rfl k)
    (fun x hx => (chartTransportIso R φ isCompact_singleton
      (Set.singleton_subset_iff.2 (hAφ hx)) Set.image_singleton n).hom)
    (fun x hx => ?_) (LocalGood.of_isCompact_EU R hn (isCompact_chartUp_image φ hA hAφ))
  exact chartTransportIso_natural R φ hA hAφ isCompact_singleton
    (Set.singleton_subset_iff.2 (hAφ hx)) rfl Set.image_singleton
    (Set.singleton_subset_iff.2 hx) (Set.singleton_subset_iff.2 ⟨x, hx, rfl⟩) n

/-- finite unions of compact subsets of chart sources are locally good -/
theorem LocalGood.of_finset_chart (hn : 1 ≤ n) {ι : Type*} (F : Finset ι) (C : ι → Set M)
    (hC : ∀ a ∈ F, IsCompact (C a) ∧
      ∃ φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), C a ⊆ φ.source) :
    LocalGood R (TopCat.of M) n (⋃ a ∈ F, C a) := by
  classical
  induction F using Finset.induction_on generalizing C with
  | empty => exact (LocalGood.empty _ _).of_eq (by simp)
  | insert a F ha ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨hCa, φ, hφ⟩ := hC a (Finset.mem_insert_self a F)
    refine LocalGood.union hCa.isClosed
      (isClosed_biUnion_finset fun b hb => (hC b (Finset.mem_insert_of_mem hb)).1.isClosed)
      (LocalGood.of_subset_chart_source R φ hn hCa hφ)
      (ih C fun b hb => hC b (Finset.mem_insert_of_mem hb)) ?_
    rw [Set.inter_iUnion₂]
    exact ih (fun b => C a ∩ C b) fun b hb =>
      ⟨hCa.inter_right (hC b (Finset.mem_insert_of_mem hb)).1.isClosed,
        φ, Set.inter_subset_left.trans hφ⟩

end transport

/-! ### `LocalGood` in a charted space -/

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- **Compact subsets of a charted Hausdorff space are locally good** (Hatcher 3.27(a) for
manifolds): for `n ≥ 1` and `A ⊆ M` compact, `H_i(M, M ∖ A) = 0` for `i > n` and a class in
`H_n(M, M ∖ A)` with vanishing point restrictions is zero. -/
theorem LocalGood.of_isCompact (hn : 1 ≤ n) {A : Set M} (hA : IsCompact A) :
    LocalGood R (TopCat.of M) n A := by
  have := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  choose N hN using fun a : M =>
    exists_compact_subset (chartAt (EuclideanSpace ℝ (Fin n)) a).open_source
      (mem_chart_source (EuclideanSpace ℝ (Fin n)) a)
  obtain ⟨F, -, hAF⟩ := hA.elim_nhds_subcover (fun a => interior (N a))
    fun a _ => isOpen_interior.mem_nhds (hN a).2.1
  refine (LocalGood.of_finset_chart R hn F (fun a => A ∩ N a) fun a _ =>
    ⟨hA.inter_right (hN a).1.isClosed, chartAt (EuclideanSpace ℝ (Fin n)) a,
      Set.inter_subset_right.trans (hN a).2.2⟩).of_eq ?_
  ext x
  constructor
  · intro hx
    obtain ⟨a, -, hxa⟩ := Set.mem_iUnion₂.1 hx
    exact hxa.1
  · intro hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hAF hx)
    exact Set.mem_iUnion₂.2 ⟨a, ha, hx, interior_subset hxa⟩

/-! ### The local homology of a point -/

/-- `H_k(M, M ∖ {x}) = 0` for `k ≠ n`, `n ≥ 1` -/
theorem isZero_Hrel_compl_singleton_manifold (hn : 1 ≤ n) (x : M) {k : ℕ} (hk : k ≠ n) :
    IsZero (Hrel R (TopCat.of M) {x}ᶜ k) :=
  (isZero_Hrel_EU_compl_singleton R hn (chartUp (chartAt (EuclideanSpace ℝ (Fin n)) x) x)
    hk).of_iso (chartTransportIso R (chartAt (EuclideanSpace ℝ (Fin n)) x) isCompact_singleton
      (Set.singleton_subset_iff.2 (mem_chart_source _ x)) Set.image_singleton k)

/-- `H_n(M, M ∖ {x}) ≅ R` for `n ≥ 1` -/
def HrelComplSingletonManifoldIso (hn : 1 ≤ n) (x : M) :
    Hrel R (TopCat.of M) {x}ᶜ n ≅ R :=
  chartTransportIso R (chartAt (EuclideanSpace ℝ (Fin n)) x) isCompact_singleton
      (Set.singleton_subset_iff.2 (mem_chart_source _ x)) Set.image_singleton n ≪≫
    HrelEUComplSingletonIso R hn (chartUp (chartAt (EuclideanSpace ℝ (Fin n)) x) x)

/-! ### Chart balls -/

/-- the lift of a closed ball is a closed ball -/
lemma uliftUp_image_closedBall (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ULift.up.{u} '' closedBall c r = closedBall (ULift.up c) r := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [ULift.dist_up_up] using hy
  · intro hz
    exact ⟨z.down, by simpa [ULift.dist_eq] using hz, rfl⟩

/-- **Chart balls.** Every point `x` of `M` has a compact neighbourhood `D` such that all the
point restrictions `H_n(M, M ∖ D) → H_n(M, M ∖ {y})`, `y ∈ D`, are isomorphisms. -/
theorem exists_chartBall_isIso_ptRes (hn : 1 ≤ n) (x : M) :
    ∃ D : Set M, IsCompact D ∧ x ∈ interior D ∧ ∀ y (hy : y ∈ D),
      IsIso (HrelMap R (𝟙 (TopCat.of M)) (compl_mapsTo hy) n :
        Hrel R (TopCat.of M) Dᶜ n ⟶ Hrel R (TopCat.of M) {y}ᶜ n) := by
  set φ := chartAt (EuclideanSpace ℝ (Fin n)) x with hφ
  have hxs : x ∈ φ.source := mem_chart_source _ x
  obtain ⟨r, hr, hKt⟩ :=
    nhds_basis_closedBall.mem_iff.1 (φ.open_target.mem_nhds (φ.map_source hxs))
  have hD : IsCompact (φ.symm '' closedBall (φ x) r) :=
    (isCompact_closedBall _ _).image_of_continuousOn (φ.continuousOn_symm.mono hKt)
  refine ⟨φ.symm '' closedBall (φ x) r, hD, ?_, fun y hy => ?_⟩
  · refine mem_interior.2 ⟨φ.symm '' ball (φ x) r, Set.image_mono ball_subset_closedBall,
      φ.symm.isOpen_image_of_subset_source isOpen_ball
        (φ.symm_source ▸ ball_subset_closedBall.trans hKt),
      ⟨φ x, mem_ball_self hr, φ.left_inv hxs⟩⟩
  · have hDφ : φ.symm '' closedBall (φ x) r ⊆ φ.source :=
      (Set.image_mono hKt).trans φ.symm_image_target_eq_source.subset
    have hB : chartUp φ '' (φ.symm '' closedBall (φ x) r) = closedBall (ULift.up (φ x)) r :=
      calc chartUp φ '' (φ.symm '' closedBall (φ x) r)
          = ULift.up '' (φ '' (φ.symm '' closedBall (φ x) r)) :=
          (Set.image_image ULift.up φ (φ.symm '' closedBall (φ x) r)).symm
        _ = ULift.up '' closedBall (φ x) r :=
          congrArg (ULift.up '' ·) (φ.image_symm_image_of_subset_target hKt)
        _ = closedBall (ULift.up (φ x)) r := uliftUp_image_closedBall _ _
    have hyB : chartUp φ y ∈ closedBall (ULift.up (φ x)) r := hB ▸ ⟨y, hy, rfl⟩
    have hnat := chartTransportIso_natural R φ hD hDφ isCompact_singleton
      (Set.singleton_subset_iff.2 (hDφ hy)) hB Set.image_singleton
      (Set.singleton_subset_iff.2 hy) (Set.singleton_subset_iff.2 hyB) n
    have hiso : IsIso (HrelMap R (𝟙 (TopCat.of (EU n)))
        (mapsTo_id_of_subset (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hyB))) n) :=
      isIso_ptRes_of_convex R hn (convex_closedBall _ _) (isCompact_closedBall _ _) hyB n
    have : HrelMap R (𝟙 (TopCat.of M)) (compl_mapsTo hy) n =
        (chartTransportIso R φ hD hDφ hB n).hom ≫
          HrelMap R (𝟙 (TopCat.of (EU n)))
            (mapsTo_id_of_subset (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hyB))) n ≫
          (chartTransportIso R φ isCompact_singleton (Set.singleton_subset_iff.2 (hDφ hy))
            Set.image_singleton n).inv := by
      rw [← Category.assoc, Iso.eq_comp_inv, hnat]
    rw [this]
    infer_instance

end charted

end PoincareHighDim.SingularPair

end
