import Submission.Homology.SingularPair

/-!
# Naturality, the augmentation and reduced zeroth homology

This module complements `Submission.Homology.SingularPair` with

* functoriality of relative homology (`HrelMap_id`, `HrelMap_comp`) and naturality of the
  three maps of the long exact sequence of a pair (`δ_natural`, `relπ_natural`,
  `inclMap_natural`);
* naturality of the augmentation `ε : H₀(X) → R` (`ε_natural`);
* reduced zeroth homology `Hred₀ R X := kernel (ε R X)` with its functoriality (`Hred₀Map`),
  invariance under homotopy equivalences (`Hred₀Iso`), vanishing for path connected spaces
  (`isZero_Hred₀_of_pathConnected`) and the computation `Hred₀ ≅ R` for a two-point space
  (`Hred₀_two_points`, more generally `Hred₀IsoOfTwoPoints`);
* the pieces of the long exact sequence of a pair with reduced `H₀`
  (`les_red_exact₁/₂/₃`), obtained from general lemmas (`exact_kernelLift₃/₂₃/₁₂`) saying that
  exactness in `ModuleCat ℤ` is inherited by kernels of compatible augmentations.

Convention: maps induced in absolute homology are written `Hmap R f n`, which is
`((singularHomologyFunctor _ n).obj R).map f`; it is definitionally (but not reducibly) equal
to `homologyMap ((Cf R).map f) n` (see `Hmap_eq_homologyMap`).  Statements are phrased with
`Hmap` because `H R X n` only unfolds to `(C R X).homology n` at default transparency, which
makes `rw` fragile on mixed goals; all proofs go through `exact` at that transparency.
-/

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Simplicial

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-! ### Maps in absolute homology -/

/-- the map `H_n(X) → H_n(Y)` induced by `f : X ⟶ Y` -/
abbrev Hmap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) : H R X n ⟶ H R Y n :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj R).map f

lemma Hmap_eq_homologyMap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    Hmap R f n = homologyMap ((Cf R).map f) n := rfl

@[simp]
lemma Hmap_id (X : TopCat.{u}) (n : ℕ) : Hmap R (𝟙 X) n = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

@[reassoc]
lemma Hmap_comp {X Y W : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ W) (n : ℕ) :
    Hmap R (f ≫ g) n = Hmap R f n ≫ Hmap R g n :=
  CategoryTheory.Functor.map_comp _ _ _

lemma inclMap_eq_Hmap (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    inclMap R X A n = Hmap R (incl X A) n := rfl

lemma homologyIso_hom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (homologyIso R e n).hom = Hmap R (TopCat.ofHom e.toFun) n := rfl

instance isIso_Hmap_of_homotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (Hmap R (TopCat.ofHom e.toFun) n) :=
  ⟨(homologyIso R e n).inv, (homologyIso R e n).hom_inv_id, (homologyIso R e n).inv_hom_id⟩

/-! ### Functoriality of relative homology -/

/-- restriction of a map of spaces to subspaces -/
def restr {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B) :
    TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨hf.restrict, by fun_prop⟩

@[simp]
lemma restr_apply {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (a : A) : restr f hf a = ⟨f a, hf a.2⟩ := rfl

lemma restr_comp_incl {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) : restr f hf ≫ incl Y B = incl X A ≫ f := rfl

lemma pairMap_left {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) : (pairMap f hf).left = TopCat.toSSet.map (restr f hf) := rfl

lemma pairMap_right {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) : (pairMap f hf).right = TopCat.toSSet.map f := rfl

lemma restr_id (X : TopCat.{u}) (A : Set X) (hf : Set.MapsTo (𝟙 X) A A) :
    restr (𝟙 X) hf = 𝟙 (TopCat.of A) := by
  ext x
  rfl

lemma restr_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W}
    (f : X ⟶ Y) (g : Y ⟶ W) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hfg : Set.MapsTo (f ≫ g) A D) :
    restr (f ≫ g) hfg = restr f hf ≫ restr g hg := by
  ext x
  rfl

lemma pairMap_id (X : TopCat.{u}) (A : Set X) (hf : Set.MapsTo (𝟙 X) A A) :
    pairMap (𝟙 X) hf = 𝟙 (pair X A) := by
  refine MorphismProperty.Comma.Hom.ext' (CommaMorphism.ext ?_ ?_)
  · change TopCat.toSSet.map (restr (𝟙 X) hf) = 𝟙 _
    rw [restr_id, CategoryTheory.Functor.map_id]
  · rfl

lemma pairMap_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W}
    (f : X ⟶ Y) (g : Y ⟶ W) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hfg : Set.MapsTo (f ≫ g) A D) :
    pairMap (f ≫ g) hfg = pairMap f hf ≫ pairMap g hg := by
  refine MorphismProperty.Comma.Hom.ext' (CommaMorphism.ext ?_ ?_)
  · change TopCat.toSSet.map (restr (f ≫ g) hfg) =
      TopCat.toSSet.map (restr f hf) ≫ TopCat.toSSet.map (restr g hg)
    rw [restr_comp f g hf hg hfg, CategoryTheory.Functor.map_comp]
  · change TopCat.toSSet.map (f ≫ g) = TopCat.toSSet.map f ≫ TopCat.toSSet.map g
    rw [CategoryTheory.Functor.map_comp]

theorem HrelMap_id (X : TopCat.{u}) (A : Set X) (hf : Set.MapsTo (𝟙 X) A A) (n : ℕ) :
    HrelMap R (𝟙 X) hf n = 𝟙 _ := by
  rw [HrelMap, pairMap_id, SSetPair.homologyMap_id]

theorem HrelMap_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W}
    (f : X ⟶ Y) (g : Y ⟶ W) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hfg : Set.MapsTo (f ≫ g) A D) (n : ℕ) :
    HrelMap R (f ≫ g) hfg n = HrelMap R f hf n ≫ HrelMap R g hg n := by
  rw [HrelMap, pairMap_comp f g hf hg hfg, SSetPair.homologyMap_comp]

/-! ### Naturality of the long exact sequence of a pair -/

/-- the morphism of short exact sequences of chain complexes induced by a map of pairs -/
def scMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B) :
    (pair X A).chainComplexShortComplex R ⟶ (pair Y B).chainComplexShortComplex R where
  τ₁ := (Cf R).map (restr f hf)
  τ₂ := (Cf R).map f
  τ₃ := SSetPair.chainComplexMap (pairMap f hf) R
  comm₁₂ := ((SSetPair.chainComplexFunctorLeftToRight _).app R).naturality (pairMap f hf)
  comm₂₃ := ((SSetPair.chainComplexFunctorπ _).app R).naturality (pairMap f hf)

/-- naturality of the connecting morphism `H_{n+1}(X, A) → H_n(A)` -/
theorem δ_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    δ R X A n ≫ Hmap R (restr f hf) n = HrelMap R f hf (n + 1) ≫ δ R Y B n :=
  HomologySequence.δ_naturality (scMap R f hf) _ _ (n + 1) n rfl

theorem δ_natural' {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    δ R X A n ≫ homologyMap ((Cf R).map (restr f hf)) n = HrelMap R f hf (n + 1) ≫ δ R Y B n :=
  δ_natural R f hf n

lemma chainComplexπ_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) :
    ((SSetPair.chainComplexFunctorRight _).obj R).map (pairMap f hf) ≫
      ((SSetPair.chainComplexFunctorπ _).app R).app (pair Y B) =
    ((SSetPair.chainComplexFunctorπ _).app R).app (pair X A) ≫
      ((SSetPair.chainComplexFunctor _).obj R).map (pairMap f hf) :=
  ((SSetPair.chainComplexFunctorπ _).app R).naturality (pairMap f hf)

/-- naturality of the maps `H_n(X) → H_n(X, A)` -/
theorem relπ_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    relπ R X A n ≫ HrelMap R f hf n = Hmap R f n ≫ relπ R Y B n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (chainComplexπ_natural R f hf)
  simp only [homologyMap_comp] at h
  exact h.symm

theorem relπ_natural' {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    relπ R X A n ≫ HrelMap R f hf n = homologyMap ((Cf R).map f) n ≫ relπ R Y B n :=
  relπ_natural R f hf n

/-- naturality of the maps `H_n(A) → H_n(X)` -/
theorem inclMap_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    inclMap R X A n ≫ Hmap R f n = Hmap R (restr f hf) n ≫ inclMap R Y B n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (((SSetPair.chainComplexFunctorLeftToRight _).app R).naturality (pairMap f hf))
  simp only [homologyMap_comp] at h
  exact h.symm

theorem inclMap_natural' {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    inclMap R X A n ≫ homologyMap ((Cf R).map f) n =
      homologyMap ((Cf R).map (restr f hf)) n ≫ inclMap R Y B n :=
  inclMap_natural R f hf n

/-! ### The augmentation -/

/-- the augmentation `H₀(X) → R` -/
abbrev ε (X : TopCat.{u}) : H R X 0 ⟶ R := X.singularHomology₀ε R

@[reassoc]
lemma ι_inv_iCycles (X : SSet.{u}) (x : X _⦋0⦌) :
    X.ιChainComplex x ≫ inv ((X.chainComplex R).iCycles 0) =
      (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
  rw [← cancel_mono ((X.chainComplex R).iCycles 0)]
  simp

/-- naturality of the augmentation of simplicial sets -/
lemma homology₀ε_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  rw [SSet.homologyMap, ← cancel_epi ((X.chainComplex R).homologyπ 0), homologyπ_naturality_assoc,
    ← cancel_epi (inv ((X.chainComplex R).iCycles 0))]
  apply SSet.chainComplex_hom_ext
  intro x
  rw [ι_inv_iCycles_assoc, ι_inv_iCycles_assoc, liftCycles_comp_cyclesMap_assoc]
  simp

/-- naturality of the augmentation -/
@[reassoc (attr := simp)]
theorem ε_natural {X Y : TopCat.{u}} (f : X ⟶ Y) : Hmap R f 0 ≫ ε R Y = ε R X :=
  homology₀ε_natural R (TopCat.toSSet.map f)

theorem ε_natural' {X Y : TopCat.{u}} (f : X ⟶ Y) :
    homologyMap ((Cf R).map f) 0 ≫ Y.singularHomology₀ε R = X.singularHomology₀ε R :=
  ε_natural R f

@[reassoc (attr := simp)]
theorem inclMap_ε (X : TopCat.{u}) (A : Set X) : inclMap R X A 0 ≫ ε R X = ε R (TopCat.of A) :=
  ε_natural R (incl X A)

theorem isIso_ε_of_pathConnected (X : TopCat.{u}) [PathConnectedSpace X] : IsIso (ε R X) :=
  inferInstance

theorem isIso_ε_of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    IsIso (ε R (TopCat.of X)) :=
  inferInstance

/-! ### Reduced zeroth homology -/

/-- reduced zeroth homology, the kernel of the augmentation -/
abbrev Hred₀ (X : TopCat.{u}) : ModuleCat.{u} ℤ := kernel (ε R X)

/-- the inclusion `H̃₀(X) → H₀(X)` -/
abbrev Hred₀ι (X : TopCat.{u}) : Hred₀ R X ⟶ H R X 0 := kernel.ι (ε R X)

instance (X : TopCat.{u}) : Mono (Hred₀ι R X) := inferInstance

@[reassoc (attr := simp)]
lemma Hred₀ι_ε (X : TopCat.{u}) : Hred₀ι R X ≫ ε R X = 0 := kernel.condition _

/-- the map induced on reduced zeroth homology -/
def Hred₀Map {X Y : TopCat.{u}} (f : X ⟶ Y) : Hred₀ R X ⟶ Hred₀ R Y :=
  kernel.lift _ (Hred₀ι R X ≫ Hmap R f 0) (by rw [Category.assoc, ε_natural, kernel.condition])

@[reassoc (attr := simp)]
lemma Hred₀Map_ι {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Hred₀Map R f ≫ Hred₀ι R Y = Hred₀ι R X ≫ Hmap R f 0 :=
  kernel.lift_ι _ _ _

@[simp]
lemma Hred₀Map_id (X : TopCat.{u}) : Hred₀Map R (𝟙 X) = 𝟙 _ := by
  rw [← cancel_mono (Hred₀ι R X), Hred₀Map_ι, Hmap_id, Category.comp_id, Category.id_comp]

@[reassoc]
lemma Hred₀Map_comp {X Y W : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ W) :
    Hred₀Map R (f ≫ g) = Hred₀Map R f ≫ Hred₀Map R g := by
  rw [← cancel_mono (Hred₀ι R W), Hred₀Map_ι, Hmap_comp, Category.assoc, Hred₀Map_ι,
    Hred₀Map_ι_assoc]

lemma mono_Hred₀Map_of_mono {X Y : TopCat.{u}} (f : X ⟶ Y) [Mono (Hmap R f 0)] :
    Mono (Hred₀Map R f) :=
  mono_of_mono_fac (Hred₀Map_ι R f)

/-- a map inducing an isomorphism on `H₀` induces an isomorphism on `H̃₀` -/
def Hred₀MapIso {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso (Hmap R f 0)] : Hred₀ R X ≅ Hred₀ R Y :=
  kernel.mapIso (ε R X) (ε R Y) (asIso (Hmap R f 0)) (Iso.refl R)
    (by rw [Iso.refl_hom, Category.comp_id, asIso_hom, ε_natural])

lemma Hred₀MapIso_hom {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso (Hmap R f 0)] :
    (Hred₀MapIso R f).hom = Hred₀Map R f := rfl

instance isIso_Hred₀Map {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso (Hmap R f 0)] :
    IsIso (Hred₀Map R f) :=
  ⟨(Hred₀MapIso R f).inv, (Hred₀MapIso R f).hom_inv_id, (Hred₀MapIso R f).inv_hom_id⟩

/-- homotopy invariance of reduced zeroth homology -/
def Hred₀Iso {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : Hred₀ R (TopCat.of X) ≅ Hred₀ R (TopCat.of Y) :=
  Hred₀MapIso R (TopCat.ofHom e.toFun)

lemma Hred₀Iso_hom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (Hred₀Iso R e).hom = Hred₀Map R (TopCat.ofHom e.toFun) := rfl

/-- reduced zeroth homology is invariant under homeomorphisms -/
def Hred₀IsoOfHomeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Hred₀ R (TopCat.of X) ≅ Hred₀ R (TopCat.of Y) :=
  Hred₀Iso R e.toHomotopyEquiv

theorem isZero_Hred₀_of_pathConnected (X : TopCat.{u}) [PathConnectedSpace X] :
    IsZero (Hred₀ R X) :=
  (isZero_zero _).of_iso (kernel.ofMono (ε R X))

theorem isZero_Hred₀_of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero (Hred₀ R (TopCat.of X)) :=
  isZero_Hred₀_of_pathConnected R (TopCat.of X)

/-! ### Reduced zeroth homology of a two-point space -/

section two

open scoped Classical

variable {ι : Type u} (a b : ι)

/-- projection onto the `c`-th summand -/
def prj (c : ι) : ∐ (fun _ : ι ↦ R) ⟶ R := Sigma.desc (fun i ↦ if i = c then 𝟙 R else 0)

@[reassoc (attr := simp)]
lemma ι_prj_self (c : ι) : Sigma.ι (fun _ : ι ↦ R) c ≫ prj R c = 𝟙 R := by
  simp [prj]

@[reassoc]
lemma ι_prj_ne {i c : ι} (h : i ≠ c) : Sigma.ι (fun _ : ι ↦ R) i ≫ prj R c = 0 := by
  simp [prj, h]

lemma sub_comp_sigmaDesc_id :
    (Sigma.ι (fun _ : ι ↦ R) a - Sigma.ι (fun _ : ι ↦ R) b) ≫ Sigma.desc (fun _ : ι ↦ 𝟙 R) = 0 := by
  simp [Preadditive.sub_comp]

variable (hab : a ≠ b) (hcov : ∀ i, i = a ∨ i = b)
include hab hcov

lemma prj_total : prj R a ≫ Sigma.ι (fun _ : ι ↦ R) a + prj R b ≫ Sigma.ι (fun _ : ι ↦ R) b =
    𝟙 _ := by
  ext i
  rcases hcov i with rfl | rfl
  · simp [Preadditive.comp_add, ι_prj_ne_assoc R hab]
  · simp [Preadditive.comp_add, ι_prj_ne_assoc R hab.symm]

lemma sigmaDesc_id_eq : Sigma.desc (fun _ : ι ↦ 𝟙 R) = prj R a + prj R b := by
  ext i
  rcases hcov i with rfl | rfl
  · simp [Preadditive.comp_add, ι_prj_ne R hab]
  · simp [Preadditive.comp_add, ι_prj_ne R hab.symm]

/-- `R → R ⊕ R`, `r ↦ (r, -r)` is a kernel of the codiagonal -/
def isLimitKernelForkTwo :
    IsLimit (KernelFork.ofι _ (sub_comp_sigmaDesc_id R a b)) :=
  KernelFork.IsLimit.ofι _ _ (fun g _ ↦ g ≫ prj R a)
    (fun g hg ↦ by
      have h1 : g ≫ prj R a + g ≫ prj R b = 0 := by
        rw [← Preadditive.comp_add, ← sigmaDesc_id_eq R a b hab hcov, hg]
      have h2 : g ≫ prj R b = -(g ≫ prj R a) := by
        rw [eq_neg_iff_add_eq_zero, add_comm, h1]
      calc (g ≫ prj R a) ≫ (Sigma.ι (fun _ : ι ↦ R) a - Sigma.ι (fun _ : ι ↦ R) b)
          = g ≫ prj R a ≫ Sigma.ι (fun _ : ι ↦ R) a + g ≫ prj R b ≫ Sigma.ι (fun _ : ι ↦ R) b := by
            rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc, h2,
              Preadditive.neg_comp, sub_eq_add_neg]
        _ = g := by
            rw [← Preadditive.comp_add, prj_total R a b hab hcov, Category.comp_id])
    (fun g hg m hm ↦ by
      rw [← hm, Category.assoc, Preadditive.sub_comp, ι_prj_self, ι_prj_ne R hab.symm, sub_zero,
        Category.comp_id])

/-- the kernel of the codiagonal `R ⊕ R → R` (indexed by a two-element type) is `R` -/
def kernelSigmaDescTwoIso : kernel (Sigma.desc (fun _ : ι ↦ 𝟙 R)) ≅ R :=
  (kernelIsKernel _).conePointUniqueUpToIso (isLimitKernelForkTwo R a b hab hcov)

end two

/-- `H̃₀(X)` is the kernel of the codiagonal on the free module on the path components -/
def Hred₀IsoKernelSigmaDesc (X : TopCat.{u}) :
    Hred₀ R X ≅ kernel (Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 R)) :=
  kernel.mapIso (ε R X) _ (X.singularHomology₀Iso R) (Iso.refl R)
    (by rw [Iso.refl_hom, Category.comp_id, TopCat.singularHomology₀Iso_sigma_desc_id])

/-- if `X` has exactly two path components, `H̃₀(X) ≅ R` -/
def Hred₀IsoOfTwo (X : TopCat.{u}) (a b : ZerothHomotopy X) (hab : a ≠ b)
    (hcov : ∀ i, i = a ∨ i = b) : Hred₀ R X ≅ R :=
  Hred₀IsoKernelSigmaDesc R X ≪≫ kernelSigmaDescTwoIso R a b hab hcov

lemma _root_.ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace {X : Type u}
    [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    Function.Injective (ZerothHomotopy.mk (X := X)) := by
  intro x y h
  obtain ⟨p⟩ : Joined x y := Quotient.exact h
  exact (isPreconnected_range p.continuous).subsingleton ⟨0, p.source⟩ ⟨1, p.target⟩

/-- for a totally disconnected space, points are path components -/
def _root_.ZerothHomotopy.equivOfTotallyDisconnectedSpace (X : Type u) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : X ≃ ZerothHomotopy X :=
  Equiv.ofBijective ZerothHomotopy.mk
    ⟨ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace, ZerothHomotopy.mk_surjective⟩

/-- the reduced zeroth homology of a totally disconnected two-point space is `R` -/
def Hred₀IsoOfTwoPoints (X : TopCat.{u}) [TotallyDisconnectedSpace X] (x y : X) (hxy : x ≠ y)
    (hcov : ∀ z, z = x ∨ z = y) : Hred₀ R X ≅ R :=
  Hred₀IsoOfTwo R X (.mk x) (.mk y)
    (fun h ↦ hxy (ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace h))
    (fun i ↦ by
      obtain ⟨z, rfl⟩ := ZerothHomotopy.mk_surjective i
      rcases hcov z with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl)

/-- `H̃₀` of the two-point discrete space is `R` -/
def Hred₀_two_points : Hred₀ R (TopCat.of (ULift.{u} (Fin 2))) ≅ R :=
  Hred₀IsoOfTwoPoints R (TopCat.of (ULift.{u} (Fin 2))) ⟨0⟩ ⟨1⟩ (by simp)
    (fun z ↦ by
      rcases z with ⟨z⟩
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl)

/-! ### Exactness and kernels of augmentations -/

section kernelExact

variable {S : ShortComplex (ModuleCat.{u} ℤ)} (hS : S.Exact)

lemma kernelLift_comp_zero₃ {T : ModuleCat.{u} ℤ} (ε₃ : S.X₃ ⟶ T) (h : S.g ≫ ε₃ = 0) :
    S.f ≫ kernel.lift ε₃ S.g h = 0 := by
  rw [← cancel_mono (kernel.ι ε₃), Category.assoc, kernel.lift_ι, S.zero, zero_comp]

include hS in
/-- exactness is inherited when the third term is replaced by the kernel of an augmentation -/
lemma exact_kernelLift₃ {T : ModuleCat.{u} ℤ} (ε₃ : S.X₃ ⟶ T) (h : S.g ≫ ε₃ = 0) :
    (ShortComplex.mk S.f (kernel.lift ε₃ S.g h) (kernelLift_comp_zero₃ ε₃ h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x₂ hx₂
  change kernel.lift ε₃ S.g h x₂ = 0 at hx₂
  apply hS
  have := congrArg (kernel.ι ε₃) hx₂
  rwa [← ModuleCat.comp_apply, kernel.lift_ι, map_zero] at this

section
variable {T₂ T₃ : ModuleCat.{u} ℤ} (ε₂ : S.X₂ ⟶ T₂) (ε₃ : S.X₃ ⟶ T₃) (t : T₂ ⟶ T₃) [Mono t]
  (h : S.g ≫ ε₃ = ε₂ ≫ t)
include h

lemma f_comp_eq_zero_of_mono : S.f ≫ ε₂ = 0 := by
  rw [← cancel_mono t, Category.assoc, ← h, ← Category.assoc, S.zero, zero_comp, zero_comp]

omit [Mono t] in
lemma ι_comp_g_comp_eq_zero : (kernel.ι ε₂ ≫ S.g) ≫ ε₃ = 0 := by
  rw [Category.assoc, h, kernel.condition_assoc, zero_comp]

lemma kernelLift_comp_zero₂₃ :
    kernel.lift ε₂ S.f (f_comp_eq_zero_of_mono ε₂ ε₃ t h) ≫
      kernel.lift ε₃ (kernel.ι ε₂ ≫ S.g) (ι_comp_g_comp_eq_zero ε₂ ε₃ t h) = 0 := by
  rw [← cancel_mono (kernel.ι ε₃), Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, S.zero,
    zero_comp]

include hS in
/-- exactness is inherited by the kernels of compatible augmentations of the second and third
terms, provided the comparison map of the augmentation targets is a monomorphism -/
lemma exact_kernelLift₂₃ :
    (ShortComplex.mk _ _ (kernelLift_comp_zero₂₃ ε₂ ε₃ t h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x₂ hx₂
  change kernel.lift ε₃ (kernel.ι ε₂ ≫ S.g) _ x₂ = 0 at hx₂
  have h1 : S.g (kernel.ι ε₂ x₂) = 0 := by
    have := congrArg (kernel.ι ε₃) hx₂
    rwa [← ModuleCat.comp_apply, kernel.lift_ι, map_zero, ModuleCat.comp_apply] at this
  obtain ⟨x₁, hx₁⟩ := hS _ h1
  refine ⟨x₁, ?_⟩
  apply (ModuleCat.mono_iff_injective (kernel.ι ε₂)).1 inferInstance
  change (kernel.lift ε₂ S.f _ ≫ kernel.ι ε₂) x₁ = kernel.ι ε₂ x₂
  rw [kernel.lift_ι]
  exact hx₁

end

section
variable {T₁ T₂ : ModuleCat.{u} ℤ} (ε₁ : S.X₁ ⟶ T₁) (ε₂ : S.X₂ ⟶ T₂) (t : T₁ ⟶ T₂) [Mono t]
  (h : S.f ≫ ε₂ = ε₁ ≫ t)
include h

omit [Mono t] in
lemma ι_comp_f_comp_eq_zero : (kernel.ι ε₁ ≫ S.f) ≫ ε₂ = 0 := by
  rw [Category.assoc, h, kernel.condition_assoc, zero_comp]

omit [Mono t] in
lemma kernelLift_comp_zero₁₂ :
    kernel.lift ε₂ (kernel.ι ε₁ ≫ S.f) (ι_comp_f_comp_eq_zero ε₁ ε₂ t h) ≫
      (kernel.ι ε₂ ≫ S.g) = 0 := by
  rw [kernel.lift_ι_assoc, Category.assoc, S.zero, comp_zero]

include hS in
/-- exactness is inherited by the kernels of compatible augmentations of the first and second
terms, provided the comparison map of the augmentation targets is a monomorphism -/
lemma exact_kernelLift₁₂ :
    (ShortComplex.mk _ _ (kernelLift_comp_zero₁₂ ε₁ ε₂ t h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x₂ hx₂
  change (kernel.ι ε₂ ≫ S.g) x₂ = 0 at hx₂
  rw [ModuleCat.comp_apply] at hx₂
  obtain ⟨x₁, hx₁⟩ := hS _ hx₂
  have hx₁' : ε₁ x₁ = 0 := by
    apply (ModuleCat.mono_iff_injective t).1 inferInstance
    rw [map_zero]
    calc t (ε₁ x₁) = (S.f ≫ ε₂) x₁ := by rw [h, ModuleCat.comp_apply]
      _ = ε₂ (kernel.ι ε₂ x₂) := by rw [ModuleCat.comp_apply, hx₁]
      _ = (kernel.ι ε₂ ≫ ε₂) x₂ := by rw [ModuleCat.comp_apply]
      _ = 0 := by rw [kernel.condition]; simp
  let y := (ModuleCat.kernelIsoKer ε₁).inv ⟨x₁, LinearMap.mem_ker.2 hx₁'⟩
  have hy : kernel.ι ε₁ y = x₁ := by
    change ((ModuleCat.kernelIsoKer ε₁).inv ≫ kernel.ι ε₁) ⟨x₁, _⟩ = x₁
    rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl
  refine ⟨y, ?_⟩
  apply (ModuleCat.mono_iff_injective (kernel.ι ε₂)).1 inferInstance
  change (kernel.lift ε₂ (kernel.ι ε₁ ≫ S.f) _ ≫ kernel.ι ε₂) y = kernel.ι ε₂ x₂
  rw [kernel.lift_ι, ModuleCat.comp_apply, hy, hx₁]

end

end kernelExact

/-! ### The long exact sequence of a pair with reduced `H₀` -/

variable (X : TopCat.{u}) (A : Set X)

@[reassoc (attr := simp)]
theorem δ_comp_ε : δ R X A 0 ≫ ε R (TopCat.of A) = 0 := by
  have h : δ R X A 0 ≫ inclMap R X A 0 = 0 := (pair X A).homologyδ_comp R 1 0 rfl
  rw [← inclMap_ε, ← Category.assoc, h, zero_comp]

/-- the connecting morphism `H₁(X, A) → H̃₀(A)` -/
def δred : Hrel R X A 1 ⟶ Hred₀ R (TopCat.of A) :=
  kernel.lift _ (δ R X A 0) (δ_comp_ε R X A)

@[reassoc (attr := simp)]
lemma δred_ι : δred R X A ≫ Hred₀ι R (TopCat.of A) = δ R X A 0 :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
lemma δred_comp_Hred₀Map : δred R X A ≫ Hred₀Map R (incl X A) = 0 := by
  rw [← cancel_mono (Hred₀ι R X), Category.assoc, Hred₀Map_ι, δred_ι_assoc, zero_comp]
  exact (pair X A).homologyδ_comp R 1 0 rfl

@[reassoc (attr := simp)]
lemma Hred₀Map_comp_relπ : Hred₀Map R (incl X A) ≫ (Hred₀ι R X ≫ relπ R X A 0) = 0 := by
  rw [Hred₀Map_ι_assoc]
  have h : Hmap R (incl X A) 0 ≫ relπ R X A 0 = 0 := (pair X A).homologyMap_hom_homologyπ R 0
  rw [h, comp_zero]

@[reassoc (attr := simp)]
lemma relπ_comp_δred : relπ R X A 1 ≫ δred R X A = 0 := by
  rw [← cancel_mono (Hred₀ι R (TopCat.of A)), Category.assoc, δred_ι, zero_comp]
  exact (pair X A).comp_homologyδ R 1 0 rfl

/-- `H₁(X, A) → H̃₀(A) → H̃₀(X)` is exact -/
theorem les_red_exact₁ :
    (ShortComplex.mk (δred R X A) (Hred₀Map R (incl X A)) (δred_comp_Hred₀Map R X A)).Exact :=
  exact_kernelLift₂₃ (les_exact₁ R X A 0) (ε R (TopCat.of A)) (ε R X) (𝟙 R)
    (by rw [Category.comp_id]; exact inclMap_ε R X A)

/-- `H̃₀(A) → H̃₀(X) → H₀(X, A)` is exact -/
theorem les_red_exact₂ :
    (ShortComplex.mk (Hred₀Map R (incl X A)) (Hred₀ι R X ≫ relπ R X A 0)
      (Hred₀Map_comp_relπ R X A)).Exact :=
  exact_kernelLift₁₂ (les_exact₂ R X A 0) (ε R (TopCat.of A)) (ε R X) (𝟙 R)
    (by rw [Category.comp_id]; exact inclMap_ε R X A)

/-- `H₁(X) → H₁(X, A) → H̃₀(A)` is exact -/
theorem les_red_exact₃ :
    (ShortComplex.mk (relπ R X A 1) (δred R X A) (relπ_comp_δred R X A)).Exact :=
  exact_kernelLift₃ (les_exact₃ R X A 0) (ε R (TopCat.of A)) (δ_comp_ε R X A)

end PoincareHighDim.SingularPair
