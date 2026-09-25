import Submission.Homology.SingularSubcomplex
import Submission.Homology.MVShortExact
import Submission.Homology.SmallSimplices

/-!
# The Mayer–Vietoris sequence for an open cover

For a topological space `X` and two open subsets `U`, `V` with `U ∪ V = X`, singular homology
fits into the long exact Mayer–Vietoris sequence

`… ⟶ H_n(U ∩ V) ⟶ H_n(U) ⊞ H_n(V) ⟶ H_n(X) ⟶ H_{n-1}(U ∩ V) ⟶ …`

where the first map is `x ↦ (i_* x, -j_* x)` (`mvOpenLift`), the second is `(a, b) ↦ a + b`
(`mvOpenDesc`) and the connecting morphism is `mvOpenδ`.

The sequence is obtained from the abstract Mayer–Vietoris short exact sequence of the
subcomplexes `singSub X U`, `singSub X V` of the singular simplicial set of `X`
(`Submission.Homology.MVShortExact`), whose terms are identified with the homology of
`U ∩ V`, `U`, `V` and `X` through:

* `singSub X (U ∩ V) = singSub X U ⊓ singSub X V` and the comparison isomorphisms `HIso`
  (`Submission.Homology.SingularSubcomplex`), giving `infIso`;
* the small-simplices theorem (`Submission.Homology.SmallSimplices`, Hatcher 2.21): since the
  interiors of `U` and `V` cover `X`, the inclusion of the subcomplex
  `singSub X U ⊔ singSub X V = small X ![U, V]` induces an isomorphism in homology, giving
  `supIso`.

The three exactness statements are `mayerVietoris_exact₁/₂/₃`; the packaged corollary
`mvOpenδIso` gives `H_{n+1}(X) ≅ H_n(U ∩ V)` when the homology of `U` and `V` vanishes in
degrees `n` and `n + 1` (e.g. for contractible `U`, `V` and `n ≥ 1`).

Everything is universe polymorphic (`TopCat.{u}`, coefficients `R : ModuleCat.{u} ℤ`).
-/

open CategoryTheory Limits HomologicalComplex

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ) (X : TopCat.{u}) (U V : Set X)

/-! ### The cover `{U, V}` as a `Bool`-indexed family -/

/-- The two-element family `true ↦ U`, `false ↦ V`. -/
abbrev coverFam : Bool → Set X := fun b ↦ bif b then U else V

lemma small_coverFam : small X (coverFam X U V) = singSub X U ⊔ singSub X V :=
  small_pair U V

variable {X U V} in
lemma iUnion_interior_coverFam (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    ⋃ b, interior (coverFam X U V b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ U ∪ V := hUV ▸ Set.mem_univ x
  rw [Set.mem_iUnion]
  rcases hx with hx | hx
  · exact ⟨true, by simpa [coverFam, hU.interior_eq] using hx⟩
  · exact ⟨false, by simpa [coverFam, hV.interior_eq] using hx⟩

/-! ### Identification of the terms -/

variable {X U V} in
/-- For an open cover, the inclusion of the subcomplex `singSub X U ⊔ singSub X V` induces an
isomorphism in homology (small simplices, Hatcher 2.21). -/
theorem isIso_homologyMap_sup_ι (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) : IsIso (SSet.homologyMap (singSub X U ⊔ singSub X V).ι R n) := by
  rw [← small_coverFam]
  exact isIso_homologyMap_small R _ (iUnion_interior_coverFam hU hV hUV) n

variable {X U V} in
/-- `H_n(singSub X U ⊔ singSub X V) ≅ H_n(X)` for an open cover. -/
def supIso (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    ((singSub X U ⊔ singSub X V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ≅
      H R X n :=
  @asIso _ _ _ _ _ (isIso_homologyMap_sup_ι R hU hV hUV n)

variable {X U V} in
lemma supIso_hom (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (supIso R hU hV hUV n).hom = SSet.homologyMap (singSub X U ⊔ singSub X V).ι R n := rfl

/-- `H_n(singSub X U ⊓ singSub X V) ≅ H_n(U ∩ V)`. -/
def infIso (n : ℕ) :
    ((singSub X U ⊓ singSub X V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ≅
      H R (TopCat.of (U ∩ V : Set X)) n :=
  (SSet.homologyFunctor.{u} R n).mapIso (SSet.Subcomplex.eqToIso (singSub_inf X U V).symm) ≪≫
    HIso X R (U ∩ V) n

lemma infIso_hom (n : ℕ) :
    (infIso R X U V n).hom =
      SSet.homologyMap (SSet.Subcomplex.homOfLE (singSub_inf X U V).symm.le) R n ≫
        (HIso X R (U ∩ V) n).hom := rfl

/-! ### The maps of the Mayer–Vietoris sequence -/

/-- `H_n(U ∩ V) ⟶ H_n(U) ⊞ H_n(V)`, `x ↦ (i_* x, -j_* x)`. -/
def mvOpenLift (n : ℕ) :
    H R (TopCat.of (U ∩ V : Set X)) n ⟶ H R (TopCat.of U) n ⊞ H R (TopCat.of V) n :=
  biprod.lift (homologyMap ((Cf R).map (inclOfLE (Set.inter_subset_left : U ∩ V ⊆ U))) n)
    (-(homologyMap ((Cf R).map (inclOfLE (Set.inter_subset_right : U ∩ V ⊆ V))) n))

/-- `H_n(U) ⊞ H_n(V) ⟶ H_n(X)`, `(a, b) ↦ a + b`. -/
def mvOpenDesc (n : ℕ) : H R (TopCat.of U) n ⊞ H R (TopCat.of V) n ⟶ H R X n :=
  biprod.desc (inclMap R X U n) (inclMap R X V n)

@[simp]
lemma mvOpenLift_fst (n : ℕ) :
    mvOpenLift R X U V n ≫ biprod.fst =
      homologyMap ((Cf R).map (inclOfLE (Set.inter_subset_left : U ∩ V ⊆ U))) n :=
  biprod.lift_fst _ _

@[simp]
lemma mvOpenLift_snd (n : ℕ) :
    mvOpenLift R X U V n ≫ biprod.snd =
      -homologyMap ((Cf R).map (inclOfLE (Set.inter_subset_right : U ∩ V ⊆ V))) n :=
  biprod.lift_snd _ _

@[simp]
lemma inl_mvOpenDesc (n : ℕ) : biprod.inl ≫ mvOpenDesc R X U V n = inclMap R X U n :=
  biprod.inl_desc _ _

@[simp]
lemma inr_mvOpenDesc (n : ℕ) : biprod.inr ≫ mvOpenDesc R X U V n = inclMap R X V n :=
  biprod.inr_desc _ _

variable {X U V} in
/-- The Mayer–Vietoris connecting morphism `H_{n+1}(X) ⟶ H_n(U ∩ V)`. -/
def mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    H R X (n + 1) ⟶ H R (TopCat.of (U ∩ V : Set X)) n :=
  (supIso R hU hV hUV (n + 1)).inv ≫ mvδ (singSub X U) (singSub X V) R n ≫
    (infIso R X U V n).hom

/-! ### Compatibility with the abstract sequence -/

/-- the isomorphism `H_n(singSub X U) ⊞ H_n(singSub X V) ≅ H_n(U) ⊞ H_n(V)` -/
abbrev biprodHIso (n : ℕ) :
    (((singSub X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ⊞
      ((singSub X V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n) ≅
      (H R (TopCat.of U) n ⊞ H R (TopCat.of V) n) :=
  biprod.mapIso (HIso X R U n) (HIso X R V n)

lemma infIso_hom_mvOpenLift (n : ℕ) :
    (infIso R X U V n).hom ≫ mvOpenLift R X U V n =
      mvLift (singSub X U) (singSub X V) R n ≫ (biprodHIso R X U V n).hom := by
  have h1 : (HIso X R (U ∩ V) n).hom ≫ (mvOpenLift R X U V n ≫ biprod.fst) =
      SSet.homologyMap (SSet.Subcomplex.homOfLE
        (singSub_mono X (Set.inter_subset_left : U ∩ V ⊆ U))) R n ≫ (HIso X R U n).hom := by
    rw [mvOpenLift_fst]
    exact HIso_hom_map_inclOfLE R _ n
  have h2 : (HIso X R (U ∩ V) n).hom ≫ (mvOpenLift R X U V n ≫ biprod.snd) =
      -(SSet.homologyMap (SSet.Subcomplex.homOfLE
        (singSub_mono X (Set.inter_subset_right : U ∩ V ⊆ V))) R n ≫ (HIso X R V n).hom) := by
    rw [mvOpenLift_snd]
    exact (Preadditive.comp_neg _ _).trans (congrArg Neg.neg (HIso_hom_map_inclOfLE R _ n))
  apply biprod.hom_ext
  · rw [Category.assoc, infIso_hom, Category.assoc, h1, biprod.mapIso_hom, Category.assoc,
      biprod.map_fst, reassoc_of% (mvLift_fst (singSub X U) (singSub X V) R n),
      ← Category.assoc, ← SSet.homologyMap_comp]
    rfl
  · rw [Category.assoc, infIso_hom, Category.assoc, h2, biprod.mapIso_hom, Category.assoc,
      biprod.map_snd, reassoc_of% (mvLift_snd (singSub X U) (singSub X V) R n),
      Preadditive.neg_comp, Preadditive.comp_neg, ← Category.assoc, ← SSet.homologyMap_comp]
    rfl

lemma biprodHIso_hom_mvOpenDesc (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (biprodHIso R X U V n).hom ≫ mvOpenDesc R X U V n =
      mvDesc (singSub X U) (singSub X V) R n ≫ (supIso R hU hV hUV n).hom := by
  apply biprod.hom_ext'
  · rw [biprod.mapIso_hom, biprod.inl_map_assoc, inl_mvOpenDesc, HIso_hom_inclMap,
      ← Category.assoc, inl_mvDesc, supIso_hom]
    erw [← SSet.homologyMap_comp]
    rw [SSet.Subcomplex.homOfLE_ι]
  · rw [biprod.mapIso_hom, biprod.inr_map_assoc, inr_mvOpenDesc, HIso_hom_inclMap,
      ← Category.assoc, inr_mvDesc, supIso_hom]
    erw [← SSet.homologyMap_comp]
    rw [SSet.Subcomplex.homOfLE_ι]

variable {X U V} in
lemma supIso_hom_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (supIso R hU hV hUV (n + 1)).hom ≫ mvOpenδ R hU hV hUV n =
      mvδ (singSub X U) (singSub X V) R n ≫ (infIso R X U V n).hom := by
  rw [mvOpenδ, Iso.hom_inv_id_assoc]

/-! ### The Mayer–Vietoris long exact sequence -/

variable {X U V}

@[reassoc (attr := simp)]
lemma mvOpenδ_mvOpenLift (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    mvOpenδ R hU hV hUV n ≫ mvOpenLift R X U V n = 0 := by
  rw [mvOpenδ, Category.assoc, Category.assoc, infIso_hom_mvOpenLift, mvδ_mvLift_assoc,
    zero_comp, comp_zero]

@[reassoc (attr := simp)]
lemma mvOpenLift_mvOpenDesc (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    mvOpenLift R X U V n ≫ mvOpenDesc R X U V n = 0 := by
  rw [← cancel_epi (infIso R X U V n).hom, ← Category.assoc, infIso_hom_mvOpenLift,
    Category.assoc, biprodHIso_hom_mvOpenDesc R X U V hU hV hUV, mvLift_mvDesc_assoc,
    zero_comp, comp_zero]

@[reassoc (attr := simp)]
lemma mvOpenDesc_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    mvOpenDesc R X U V (n + 1) ≫ mvOpenδ R hU hV hUV n = 0 := by
  rw [← cancel_epi (biprodHIso R X U V (n + 1)).hom, ← Category.assoc,
    biprodHIso_hom_mvOpenDesc R X U V hU hV hUV, Category.assoc, supIso_hom_mvOpenδ,
    mvDesc_mvδ_assoc, zero_comp, comp_zero]

/-- **Mayer–Vietoris**, exactness at `H_n(U ∩ V)`:
`H_{n+1}(X) ⟶ H_n(U ∩ V) ⟶ H_n(U) ⊞ H_n(V)` is exact. -/
theorem mayerVietoris_exact₁ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvOpenδ R hU hV hUV n) (mvOpenLift R X U V n)
      (mvOpenδ_mvOpenLift R hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₁' (singSub X U) (singSub X V) R n)
  exact ShortComplex.isoMk (supIso R hU hV hUV (n + 1)) (infIso R X U V n)
    (biprodHIso R X U V n) (supIso_hom_mvOpenδ R hU hV hUV n) (infIso_hom_mvOpenLift R X U V n)

/-- **Mayer–Vietoris**, exactness at `H_n(U) ⊞ H_n(V)`:
`H_n(U ∩ V) ⟶ H_n(U) ⊞ H_n(V) ⟶ H_n(X)` is exact. -/
theorem mayerVietoris_exact₂ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvOpenLift R X U V n) (mvOpenDesc R X U V n)
      (mvOpenLift_mvOpenDesc R hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₂' (singSub X U) (singSub X V) R n)
  exact ShortComplex.isoMk (infIso R X U V n) (biprodHIso R X U V n) (supIso R hU hV hUV n)
    (infIso_hom_mvOpenLift R X U V n) (biprodHIso_hom_mvOpenDesc R X U V hU hV hUV n)

/-- **Mayer–Vietoris**, exactness at `H_{n+1}(X)`:
`H_{n+1}(U) ⊞ H_{n+1}(V) ⟶ H_{n+1}(X) ⟶ H_n(U ∩ V)` is exact. -/
theorem mayerVietoris_exact₃ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvOpenDesc R X U V (n + 1)) (mvOpenδ R hU hV hUV n)
      (mvOpenDesc_mvOpenδ R hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₃' (singSub X U) (singSub X V) R n)
  exact ShortComplex.isoMk (biprodHIso R X U V (n + 1)) (supIso R hU hV hUV (n + 1))
    (infIso R X U V n) (biprodHIso_hom_mvOpenDesc R X U V hU hV hUV (n + 1))
    (supIso_hom_mvOpenδ R hU hV hUV n)

/-! ### Consequences when the homology of `U` and `V` vanishes -/

lemma mvOpenDesc_eq_zero_of_isZero (n : ℕ) (hU' : IsZero (H R (TopCat.of U) n))
    (hV' : IsZero (H R (TopCat.of V) n)) : mvOpenDesc R X U V n = 0 :=
  IsZero.eq_zero_of_src ((biprod_isZero_iff _ _).2 ⟨hU', hV'⟩) _

lemma mvOpenLift_eq_zero_of_isZero (n : ℕ) (hU' : IsZero (H R (TopCat.of U) n))
    (hV' : IsZero (H R (TopCat.of V) n)) : mvOpenLift R X U V n = 0 :=
  IsZero.eq_zero_of_tgt ((biprod_isZero_iff _ _).2 ⟨hU', hV'⟩) _

/-- If `H_{n+1}(U) = H_{n+1}(V) = 0`, the connecting morphism `H_{n+1}(X) ⟶ H_n(U ∩ V)` is
a monomorphism. -/
theorem mono_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : IsZero (H R (TopCat.of U) (n + 1))) (hV' : IsZero (H R (TopCat.of V) (n + 1))) :
    Mono (mvOpenδ R hU hV hUV n) :=
  (mayerVietoris_exact₃ R hU hV hUV n).mono_g (mvOpenDesc_eq_zero_of_isZero R (n + 1) hU' hV')

/-- If `H_n(U) = H_n(V) = 0`, the connecting morphism `H_{n+1}(X) ⟶ H_n(U ∩ V)` is an
epimorphism. -/
theorem epi_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : IsZero (H R (TopCat.of U) n)) (hV' : IsZero (H R (TopCat.of V) n)) :
    Epi (mvOpenδ R hU hV hUV n) :=
  (mayerVietoris_exact₁ R hU hV hUV n).epi_f (mvOpenLift_eq_zero_of_isZero R n hU' hV')

/-- If `H_{n+1}(U) = H_{n+1}(V) = 0`, the connecting morphism `H_{n+1}(X) ⟶ H_n(U ∩ V)` is a
kernel of `H_n(U ∩ V) ⟶ H_n(U) ⊞ H_n(V)` (useful for the `n = 0` case, where the right-hand
term does not vanish). -/
def mvOpenδIsKernel (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : IsZero (H R (TopCat.of U) (n + 1))) (hV' : IsZero (H R (TopCat.of V) (n + 1))) :
    IsLimit (KernelFork.ofι (mvOpenδ R hU hV hUV n) (mvOpenδ_mvOpenLift R hU hV hUV n)) :=
  haveI := mono_mvOpenδ R hU hV hUV n hU' hV'
  (mayerVietoris_exact₁ R hU hV hUV n).fIsKernel

/-- If `H_k(U) = H_k(V) = 0` for `k ∈ {n, n + 1}`, the connecting morphism
`H_{n+1}(X) ⟶ H_n(U ∩ V)` is an isomorphism. -/
theorem isIso_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU₁ : IsZero (H R (TopCat.of U) (n + 1))) (hV₁ : IsZero (H R (TopCat.of V) (n + 1)))
    (hU₀ : IsZero (H R (TopCat.of U) n)) (hV₀ : IsZero (H R (TopCat.of V) n)) :
    IsIso (mvOpenδ R hU hV hUV n) :=
  haveI := mono_mvOpenδ R hU hV hUV n hU₁ hV₁
  haveI := epi_mvOpenδ R hU hV hUV n hU₀ hV₀
  isIso_of_mono_of_epi _

/-- `H_{n+1}(X) ≅ H_n(U ∩ V)` when `H_k(U) = H_k(V) = 0` for `k ∈ {n, n + 1}`. -/
def mvOpenδIso (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU₁ : IsZero (H R (TopCat.of U) (n + 1))) (hV₁ : IsZero (H R (TopCat.of V) (n + 1)))
    (hU₀ : IsZero (H R (TopCat.of U) n)) (hV₀ : IsZero (H R (TopCat.of V) n)) :
    H R X (n + 1) ≅ H R (TopCat.of (U ∩ V : Set X)) n :=
  @asIso _ _ _ _ _ (isIso_mvOpenδ R hU hV hUV n hU₁ hV₁ hU₀ hV₀)

/-- The plan's packaged form: `H_{n+1}(X) ≅ H_n(U ∩ V)` when the homology of `U` and `V`
vanishes in degrees `n` and `n + 1`. -/
def mv_iso_of_isZero (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (h : ∀ k, k = n ∨ k = n + 1 →
      IsZero (H R (TopCat.of U) k) ∧ IsZero (H R (TopCat.of V) k)) :
    H R X (n + 1) ≅ H R (TopCat.of (U ∩ V : Set X)) n :=
  mvOpenδIso R hU hV hUV n (h (n + 1) (Or.inr rfl)).1 (h (n + 1) (Or.inr rfl)).2
    (h n (Or.inl rfl)).1 (h n (Or.inl rfl)).2

/-- For contractible `U`, `V` and `n ≥ 1`: `H_{n+1}(X) ≅ H_n(U ∩ V)`. -/
def mvOpenδIso_of_contractible (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) (hn : n ≠ 0) :
    H R X (n + 1) ≅ H R (TopCat.of (U ∩ V : Set X)) n :=
  mvOpenδIso R hU hV hUV n (isZero_of_contractible R U (n + 1) n.succ_ne_zero)
    (isZero_of_contractible R V (n + 1) n.succ_ne_zero)
    (isZero_of_contractible R U n hn) (isZero_of_contractible R V n hn)

end PoincareHighDim.SingularPair
