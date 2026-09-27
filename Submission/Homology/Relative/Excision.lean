import Submission.Homology.SingularSubcomplex
import Submission.Homology.MayerVietoris.MVShortExact
import Submission.Homology.Subdivision.SmallSimplices
import Submission.Homology.MayerVietoris.MayerVietoris

/-!
# Excision

For a topological space `X` and subsets `U`, `V` whose interiors cover `X`, the inclusion of
pairs `(U, U ∩ V) ⟶ (X, V)` induces isomorphisms in relative singular homology
(`excision`, `excisionIso`).  The two classical forms are deduced from it:

* open covers (`excision_open`): `U`, `V` open with `U ∪ V = X`;
* the closed form (`excision_closed`): for `Z ⊆ A` with `closure Z ⊆ interior A`, the pair
  `(X ∖ Z, A ∖ Z) ⟶ (X, A)` induces isomorphisms in relative homology.

Here the subspace `U ∩ V` of `U` is written as `Subtype.val ⁻¹' V : Set (TopCat.of U)`, so that
the map of pairs is `pairMap (incl X U) _ : pair (TopCat.of U) (Subtype.val ⁻¹' V) ⟶ pair X V`
and the statement is `IsIso (HrelMap R (incl X U) _ n)`.

## Proof

The morphism of pairs factors in `SSetPair` as

`(U, U ∩ V) ≅ (singSub U, singSub (U ∩ V)) ≅ (singSub U, singSub V ⊓ singSub U)
  ⟶ (singSub V ⊔ singSub U, singSub V) ⟶ (X, V)`

(`pairMap_incl_factorisation`).  The first two maps are isomorphisms of pairs
(`restrictPairIso` from `Submission.Homology.SingularSubcomplex` and an equality of
subcomplexes), the third is `excisionPairMap`, which induces isomorphisms in relative homology
because the relative chain complexes are both cokernels of parallel legs of a pushout square
(`Submission.Homology.MayerVietoris.MVShortExact`), and the fourth (`supPairMap`) induces isomorphisms in
relative homology by the five lemma (`HomologicalComplex.HomologySequence.quasiIso_τ₃`) applied
to the short exact sequences of the two pairs: on the subspace it is an isomorphism of
simplicial sets, and on the total space it is the inclusion of the `{U, V}`-small chains,
a quasi-isomorphism by the small simplices theorem (`Submission.Homology.Subdivision.SmallSimplices`).

Everything is universe polymorphic (`TopCat.{u}`, coefficients `R : ModuleCat.{u} ℤ`).
-/

open CategoryTheory Limits HomologicalComplex

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-! ### Quasi-isomorphisms of relative chain complexes -/

section PairQuasiIso

variable {P P' : SSetPair.{u}} (φ : P ⟶ P')

/-- The morphism of short exact sequences `0 → C(P.left) → C(P.right) → C(P) → 0` induced
by a morphism of pairs. -/
def pairShortComplexMap : P.chainComplexShortComplex R ⟶ P'.chainComplexShortComplex R :=
  ShortComplex.homMk (SSet.chainComplexMap φ.left R) (SSet.chainComplexMap φ.right R)
    (SSetPair.chainComplexMap φ R)
    (by
      dsimp only [SSetPair.chainComplexShortComplex]
      rw [← Functor.map_comp, ← Functor.map_comp, MorphismProperty.Arrow.w])
    (chainComplexMap_right_chainComplexπ R φ)

@[simp] lemma pairShortComplexMap_τ₁ :
    (pairShortComplexMap R φ).τ₁ = SSet.chainComplexMap φ.left R := rfl

@[simp] lemma pairShortComplexMap_τ₂ :
    (pairShortComplexMap R φ).τ₂ = SSet.chainComplexMap φ.right R := rfl

@[simp] lemma pairShortComplexMap_τ₃ :
    (pairShortComplexMap R φ).τ₃ = SSetPair.chainComplexMap φ R := rfl

/-- If a morphism of pairs induces quasi-isomorphisms on both members of the pairs, it induces
a quasi-isomorphism of relative chain complexes (five lemma). -/
theorem quasiIso_chainComplexMap_of_quasiIso
    (h₁ : QuasiIso (SSet.chainComplexMap φ.left R))
    (h₂ : QuasiIso (SSet.chainComplexMap φ.right R)) :
    QuasiIso (SSetPair.chainComplexMap φ R) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (pairShortComplexMap R φ)
    (P.shortExact_chainComplexShortComplex R) (P'.shortExact_chainComplexShortComplex R) h₁ h₂

theorem isIso_homologyMap_of_quasiIso
    (h₁ : QuasiIso (SSet.chainComplexMap φ.left R))
    (h₂ : QuasiIso (SSet.chainComplexMap φ.right R)) (n : ℕ) :
    IsIso (SSetPair.homologyMap φ R n) :=
  haveI := quasiIso_chainComplexMap_of_quasiIso R φ h₁ h₂
  (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

/-- An isomorphism of pairs induces isomorphisms in relative homology. -/
instance isIso_homologyMap_of_isIso [IsIso φ] (n : ℕ) : IsIso (SSetPair.homologyMap φ R n) :=
  inferInstanceAs (IsIso ((SSetPair.homologyFunctor.{u} R n).map φ))

end PairQuasiIso

/-! ### The factorisation of the inclusion of pairs `(U, U ∩ V) ⟶ (X, V)` -/

variable {X : TopCat.{u}} (U V : Set X)

lemma mapsTo_incl : Set.MapsTo (incl X U) (Subtype.val ⁻¹' V) V := fun _ hx ↦ hx

lemma singSub_inter_eq_inf_swap : singSub X (U ∩ V) = singSub X V ⊓ singSub X U := by
  rw [singSub_inf, inf_comm]

/-- The isomorphism of pairs
`(singSub U, singSub (U ∩ V)) ≅ (singSub U, singSub V ⊓ singSub U)` coming from the equality
`singSub (U ∩ V) = singSub V ⊓ singSub U`. -/
def infPairIso :
    SSetPair.of (SSet.Subcomplex.homOfLE (singSub_inter_le_left U V)) ≅
      pairInf (singSub X V) (singSub X U) :=
  MorphismProperty.Arrow.isoMk (SSet.Subcomplex.eqToIso (singSub_inter_eq_inf_swap U V))
    (Iso.refl _) (by
      rw [Iso.refl_hom]
      rfl)

@[simp] lemma infPairIso_hom_left :
    (infPairIso U V).hom.left =
      SSet.Subcomplex.homOfLE (singSub_inter_eq_inf_swap U V).le := rfl

@[simp] lemma infPairIso_hom_right : (infPairIso U V).hom.right = 𝟙 _ := rfl

/-- The morphism of pairs `(singSub V ⊔ singSub U, singSub V) ⟶ (X, V)`. -/
def supPairMap : pairSup (singSub X V) (singSub X U) ⟶ pair X V :=
  SSetPair.homMk (singSubIso X V).hom (singSub X V ⊔ singSub X U).ι (by
    show (singSubIso X V).hom ≫ TopCat.toSSet.map (incl X V) =
      SSet.Subcomplex.homOfLE (le_sup_left : singSub X V ≤ singSub X V ⊔ singSub X U) ≫
        (singSub X V ⊔ singSub X U).ι
    rw [singSubIso_hom_map_incl, SSet.Subcomplex.homOfLE_ι])

@[simp] lemma supPairMap_left : (supPairMap U V).left = (singSubIso X V).hom := rfl

@[simp] lemma supPairMap_right : (supPairMap U V).right = (singSub X V ⊔ singSub X U).ι := rfl

/-- the restriction `U ∩ V ⟶ V` of the inclusion `incl X U` -/
abbrev inclRestr : TopCat.of (Subtype.val ⁻¹' V : Set (TopCat.of U)) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨(mapsTo_incl U V).restrict, by fun_prop⟩

lemma pairMap_incl_left :
    (pairMap (incl X U) (mapsTo_incl U V)).left = TopCat.toSSet.map (inclRestr U V) := rfl

lemma pairMap_incl_right :
    (pairMap (incl X U) (mapsTo_incl U V)).right = TopCat.toSSet.map (incl X U) := rfl

lemma restrictPairIso_hom_left :
    (restrictPairIso U V).hom.left = (restrictIso U V).hom := rfl

lemma restrictPairIso_hom_right :
    (restrictPairIso U V).hom.right = (singSubIso X U).inv := rfl

lemma inclRestr_incl : inclRestr U V ≫ incl X V = inclRestrict U V := rfl

lemma factorisation_left :
    TopCat.toSSet.map (inclRestr U V) =
      (restrictIso U V).hom ≫
        SSet.Subcomplex.homOfLE (singSub_inter_eq_inf_swap U V).le ≫
        SSet.Subcomplex.homOfLE (inf_le_left : singSub X V ⊓ singSub X U ≤ singSub X V) ≫
        (singSubIso X V).hom := by
  rw [← cancel_mono (TopCat.toSSet.map (incl X V)), ← Functor.map_comp, inclRestr_incl,
    Category.assoc, Category.assoc, Category.assoc, singSubIso_hom_map_incl,
    SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι, restrictIso_hom_ι]

lemma factorisation_right :
    TopCat.toSSet.map (incl X U) =
      (singSubIso X U).inv ≫ 𝟙 _ ≫
        SSet.Subcomplex.homOfLE (le_sup_right : singSub X U ≤ singSub X V ⊔ singSub X U) ≫
        (singSub X V ⊔ singSub X U).ι := by
  rw [Category.id_comp, SSet.Subcomplex.homOfLE_ι, singSubIso_inv_ι]

/-- The inclusion of pairs `(U, U ∩ V) ⟶ (X, V)` factors through the pairs of subcomplexes. -/
theorem pairMap_incl_factorisation :
    pairMap (incl X U) (mapsTo_incl U V) =
      (restrictPairIso U V).hom ≫ (infPairIso U V).hom ≫
        excisionPairMap (singSub X V) (singSub X U) ≫ supPairMap U V := by
  apply MorphismProperty.Arrow.Hom.ext
  · simp only [MorphismProperty.Comma.comp_hom, Comma.comp_left]
    exact factorisation_left U V
  · simp only [MorphismProperty.Comma.comp_hom, Comma.comp_right]
    exact factorisation_right U V

/-! ### Excision -/

section excision

variable {U V}

lemma iUnion_interior_coverFam_of_union (h : interior U ∪ interior V = Set.univ) :
    ⋃ b, interior (coverFam X U V b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ interior U ∪ interior V := h ▸ Set.mem_univ x
  rw [Set.mem_iUnion]
  rcases hx with hx | hx
  · exact ⟨true, hx⟩
  · exact ⟨false, hx⟩

/-- For a cover by interiors, the inclusion of `singSub U ⊔ singSub V` is a
quasi-isomorphism (small simplices). -/
theorem quasiIso_sup_ι (h : interior U ∪ interior V = Set.univ) :
    QuasiIso (SSet.chainComplexMap (singSub X U ⊔ singSub X V).ι R) := by
  rw [← small_coverFam]
  exact quasiIso_smallChainMap R _ (iUnion_interior_coverFam_of_union h)

theorem quasiIso_supPairMap_left :
    QuasiIso (SSet.chainComplexMap (supPairMap U V).left R) :=
  quasiIso_of_isIso
    (((SSet.chainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj R).map (singSubIso X V).hom)

theorem quasiIso_supPairMap_right (h : interior U ∪ interior V = Set.univ) :
    QuasiIso (SSet.chainComplexMap (supPairMap U V).right R) := by
  rw [supPairMap_right]
  exact quasiIso_sup_ι R (by rwa [Set.union_comm])

theorem isIso_homologyMap_supPairMap (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    IsIso (SSetPair.homologyMap (supPairMap U V) R n) :=
  isIso_homologyMap_of_quasiIso R _ (quasiIso_supPairMap_left R)
    (quasiIso_supPairMap_right R h) n

/-- **Excision** for subsets whose interiors cover `X`: the inclusion of pairs
`(U, U ∩ V) ⟶ (X, V)` induces isomorphisms in relative homology. -/
theorem excision (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    IsIso (HrelMap R (incl X U) (mapsTo_incl U V) n) := by
  have := isIso_homologyMap_supPairMap R h n
  rw [HrelMap, pairMap_incl_factorisation, SSetPair.homologyMap_comp,
    SSetPair.homologyMap_comp, SSetPair.homologyMap_comp]
  infer_instance

/-- **Excision**: `H_n(U, U ∩ V) ≅ H_n(X, V)` when the interiors of `U` and `V` cover `X`. -/
def excisionIso (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    Hrel R (TopCat.of U) (Subtype.val ⁻¹' V) n ≅ Hrel R X V n :=
  @asIso _ _ _ _ _ (excision R h n)

lemma excisionIso_hom (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    (excisionIso R h n).hom = HrelMap R (incl X U) (mapsTo_incl U V) n := rfl

/-- **Excision** for open covers: for `U`, `V` open with `U ∪ V = X`, the inclusion of pairs
`(U, U ∩ V) ⟶ (X, V)` induces isomorphisms in relative homology. -/
theorem excision_open (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HrelMap R (incl X U) (mapsTo_incl U V) n) :=
  excision R (by rwa [hU.interior_eq, hV.interior_eq]) n

/-- `H_n(U, U ∩ V) ≅ H_n(X, V)` for an open cover `{U, V}` of `X`. -/
def excisionOpenIso (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    Hrel R (TopCat.of U) (Subtype.val ⁻¹' V) n ≅ Hrel R X V n :=
  @asIso _ _ _ _ _ (excision_open R hU hV hUV n)

variable (Z A : Set X)

lemma interior_compl_union_interior_of_closure_subset (hZ : closure Z ⊆ interior A) :
    interior Zᶜ ∪ interior A = Set.univ := by
  rw [interior_compl]
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ closure Z
  · exact Or.inr (hZ hx)
  · exact Or.inl hx

/-- **Excision**, closed form: if `closure Z ⊆ interior A`, the inclusion of pairs
`(X ∖ Z, A ∖ Z) ⟶ (X, A)` induces isomorphisms in relative homology. -/
theorem excision_closed (hZ : closure Z ⊆ interior A) (n : ℕ) :
    IsIso (HrelMap R (incl X Zᶜ) (mapsTo_incl Zᶜ A) n) :=
  excision R (interior_compl_union_interior_of_closure_subset Z A hZ) n

/-- `H_n(X ∖ Z, A ∖ Z) ≅ H_n(X, A)` when `closure Z ⊆ interior A`. -/
def excisionClosedIso (hZ : closure Z ⊆ interior A) (n : ℕ) :
    Hrel R (TopCat.of (Zᶜ : Set X)) (Subtype.val ⁻¹' A) n ≅ Hrel R X A n :=
  @asIso _ _ _ _ _ (excision_closed R Z A hZ n)

end excision

end PoincareHighDim.SingularPair
