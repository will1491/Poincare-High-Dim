/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib

/-!
# Singular homology of a pair

Integral singular homology of a topological space `X` and of a pair `(X, A)` with `A : Set X`,
built on Mathlib's `singularChainComplexFunctor` and on the relative homology of a pair of
simplicial sets (`SSetPair.homology`): the singular chains of `A` form a subcomplex of those of
`X` through the inclusion, and `Hrel R X A n` is the homology of the cokernel complex.  We
record the long exact sequence of the pair (`les_exact₁/₂/₃`), functoriality (`HrelMap`), and
homotopy invariance (`homologyIso`, `isZero_of_contractible`).

Everything is universe polymorphic (`TopCat.{u}`, coefficients in `ModuleCat.{u} ℤ`, default
coefficient object `Z := ModuleCat.of ℤ (ULift.{u} ℤ)`) because the project's theorems quantify
over `M : Type*`.
-/

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

/-- coefficient ring object -/
abbrev Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)

example : Abelian (ModuleCat.{u} ℤ) := inferInstance
example : HasCoproducts.{u} (ModuleCat.{u} ℤ) := inferInstance
example : CategoryWithHomology (ModuleCat.{u} ℤ) := inferInstance
instance : TopCat.toSSet.{u}.PreservesMonomorphisms := inferInstance

variable (R : ModuleCat.{u} ℤ)

/-- singular chain complex functor with coefficients `R` -/
abbrev Cf : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj R

/-- singular chains -/
abbrev C (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} ℤ) ℕ := (Cf R).obj X

/-- singular homology -/
abbrev H (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} ℤ :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj R).obj X

example (X : TopCat.{u}) (n : ℕ) : H R X n = (C R X).homology n := rfl
example (X : TopCat.{u}) : C R X = (TopCat.toSSet.obj X).chainComplex R := rfl

/-- inclusion of a subspace -/
def incl (X : TopCat.{u}) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance (X : TopCat.{u}) (A : Set X) : Mono (incl X A) :=
  (TopCat.mono_iff_injective _).2 Subtype.val_injective

/-- the singular subcomplex of simplices with image in `A` -/
abbrev singSub (X : TopCat.{u}) (A : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (incl X A))

lemma mem_singSub_iff (X : TopCat.{u}) (A : Set X) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (singSub X A).obj n ↔ Set.range (X.toSSetObjEquiv n σ) ⊆ A := by
  constructor
  · rintro ⟨τ, rfl⟩ _ ⟨x, rfl⟩
    exact ((TopCat.of A).toSSetObjEquiv n τ x).2
  · intro h
    refine ⟨(TopCat.toSSetObjEquiv _ n).symm ⟨fun x => ⟨X.toSSetObjEquiv n σ x, h ⟨x, rfl⟩⟩,
      by fun_prop⟩, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext x
    rfl

/-- the pair of simplicial sets `Sing A ↪ Sing X` -/
def pair (X : TopCat.{u}) (A : Set X) : SSetPair.{u} :=
  SSetPair.of (TopCat.toSSet.map (incl X A))

/-- relative singular homology -/
abbrev Hrel (X : TopCat.{u}) (A : Set X) (n : ℕ) : ModuleCat.{u} ℤ :=
  (pair X A).homology R n

example (X : TopCat.{u}) (A : Set X) (n : ℕ) : (pair X A).right.homology R n = H R X n := rfl
example (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (pair X A).left.homology R n = H R (TopCat.of A) n := rfl

/-- `H_n(A) → H_n(X)` -/
abbrev inclMap (X : TopCat.{u}) (A : Set X) (n : ℕ) : H R (TopCat.of A) n ⟶ H R X n :=
  SSet.homologyMap (pair X A).hom R n

example (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    inclMap R X A n = homologyMap ((Cf R).map (incl X A)) n := rfl

/-- `H_n(X) → H_n(X, A)` -/
abbrev relπ (X : TopCat.{u}) (A : Set X) (n : ℕ) : H R X n ⟶ Hrel R X A n :=
  (pair X A).homologyπ R n

/-- `H_{n+1}(X, A) → H_n(A)` -/
abbrev δ (X : TopCat.{u}) (A : Set X) (n : ℕ) : Hrel R X A (n + 1) ⟶ H R (TopCat.of A) n :=
  (pair X A).homologyδ R (n + 1) n rfl

theorem les_exact₁ (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (δ R X A n) (inclMap R X A n)
      ((pair X A).homologyδ_comp R (n + 1) n rfl :)).Exact :=
  (pair X A).homology_exact₁ R (n + 1) n rfl

theorem les_exact₂ (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (inclMap R X A n) (relπ R X A n)
      ((pair X A).homologyMap_hom_homologyπ R n :)).Exact :=
  (pair X A).homology_exact₂ R n

theorem les_exact₃ (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relπ R X A (n + 1)) (δ R X A n)
      ((pair X A).comp_homologyδ R (n + 1) n rfl :)).Exact :=
  (pair X A).homology_exact₃ R (n + 1) n rfl

/-- maps of pairs -/
def pairMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B) :
    pair X A ⟶ pair Y B :=
  SSetPair.homMk (TopCat.toSSet.map (TopCat.ofHom ⟨hf.restrict, by fun_prop⟩))
    (TopCat.toSSet.map f)
    (by
      show TopCat.toSSet.map _ ≫ TopCat.toSSet.map (incl Y B) =
        TopCat.toSSet.map (incl X A) ≫ TopCat.toSSet.map f
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

abbrev HrelMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (n : ℕ) : Hrel R X A n ⟶ Hrel R Y B n :=
  SSetPair.homologyMap (pairMap f hf) R n

/-- homotopy equivalence ⇒ chain homotopy equivalence -/
def chainHomotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : HomotopyEquiv (C R (TopCat.of X)) (C R (TopCat.of Y)) where
  hom := (Cf R).map (TopCat.ofHom e.toFun)
  inv := (Cf R).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    rw [← Functor.map_comp]
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap (X := TopCat.of X) (Y := TopCat.of X)
      (f := TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (g := 𝟙 _)
      (Classical.choice e.left_inv) R).trans (Homotopy.ofEq (by simp))
  homotopyInvHomId := by
    rw [← Functor.map_comp]
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap (X := TopCat.of Y) (Y := TopCat.of Y)
      (f := TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (g := 𝟙 _)
      (Classical.choice e.right_inv) R).trans (Homotopy.ofEq (by simp))

def homologyIso {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) : H R (TopCat.of X) n ≅ H R (TopCat.of Y) n :=
  haveI : IsIso (homologyMap (chainHomotopyEquiv R e).hom n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  @asIso _ _ _ _ _ this

theorem isZero_of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : IsZero (H R (TopCat.of X) n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  let e' : ContinuousMap.HomotopyEquiv X PUnit.{u + 1} :=
    e.trans (Homeomorph.homeomorphOfUnique Unit PUnit.{u + 1}).toHomotopyEquiv
  have h1 : IsZero (H R (TopCat.of PUnit.{u + 1}) n) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ n R (TopCat.of PUnit.{u + 1}) hn
  have h2 : H R (TopCat.of X) n ≅ H R (TopCat.of PUnit.{u + 1}) n := homologyIso R e' n
  exact h1.of_iso h2

end PoincareHighDim.SingularPair
