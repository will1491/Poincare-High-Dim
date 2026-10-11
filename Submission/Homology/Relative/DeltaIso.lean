/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Homology.Spheres.SphereHomology
import Submission.Homology.Relative.PairVanishing

/-!
# Connecting isomorphisms, degree zero, and homeomorphism invariance of relative homology

Three groups of small results about the singular homology of pairs of
`Submission.Homology.SingularPair`, used throughout the local-homology computations:

* connecting morphisms that are isomorphisms: if `H_{i+2}(X) = H_{i+1}(X) = 0` then
  `δ : H_{i+2}(X, A) → H_{i+1}(A)` is an isomorphism (`isIso_δ_of_isZero`), and if
  `H_1(X) = H̃_0(X) = 0` then `δred : H_1(X, A) → H̃_0(A)` is an isomorphism
  (`isIso_δred_of_isZero`); naturality of `δred` (`δred_natural`);
* degree zero: `H_0(X, A) = 0` as soon as `H_0(A) → H_0(X)` is surjective
  (`isZero_Hrel_zero_of_epi`), which holds when `X` is path connected and `A` nonempty
  (`epi_inclMap_zero_of_pathConnected`);
* bookkeeping for `HrelMap` (`HrelMap_congr`, `HrelMap_eq_of_eq`, `HrelMap_comp_id`,
  `HrelIsoOfEq`) and homeomorphism invariance of relative homology: a homeomorphism
  `f : X ≃ₜ Y` with `f '' A = B` induces `H_k(X, A) ≅ H_k(Y, B)`
  (`HrelIsoOfHomeomorphImage`, `HrelIsoOfHomeomorph`, `HrelIsoOfHomeomorphIff`), naturally in
  the subset (`HrelIsoOfHomeomorphImage_natural`), and
  the nested-subtype identification `HrelIsoOfSubtypeSubtype`.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-! ### Connecting morphisms that are isomorphisms -/

/-- if `H_{i+2}(X) = H_{i+1}(X) = 0` then `δ : H_{i+2}(X, A) → H_{i+1}(A)` is an isomorphism -/
theorem isIso_δ_of_isZero (X : TopCat.{u}) (A : Set X) (i : ℕ)
    (h₁ : IsZero (H R X (i + 2))) (h₂ : IsZero (H R X (i + 1))) :
    IsIso (δ R X A (i + 1)) := by
  have hmono : Mono (δ R X A (i + 1)) :=
    (les_exact₃ R X A (i + 1)).mono_g_iff.2 (h₁.eq_zero_of_src _)
  have hepi : Epi (δ R X A (i + 1)) :=
    (les_exact₁ R X A (i + 1)).epi_f_iff.2 (h₂.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- if `H_1(X) = H̃_0(X) = 0` then `δred : H_1(X, A) → H̃_0(A)` is an isomorphism -/
theorem isIso_δred_of_isZero (X : TopCat.{u}) (A : Set X)
    (h₁ : IsZero (H R X 1)) (h₂ : IsZero (Hred₀ R X)) : IsIso (δred R X A) := by
  have hmono : Mono (δred R X A) :=
    (les_red_exact₃ R X A).mono_g_iff.2 (h₁.eq_zero_of_src _)
  have hepi : Epi (δred R X A) :=
    (les_red_exact₁ R X A).epi_f_iff.2 (h₂.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- the connecting isomorphism `H_{i+2}(X, A) ≅ H_{i+1}(A)` when `H_{i+2}(X) = H_{i+1}(X) = 0` -/
def δIsoOfIsZero (X : TopCat.{u}) (A : Set X) (i : ℕ)
    (h₁ : IsZero (H R X (i + 2))) (h₂ : IsZero (H R X (i + 1))) :
    Hrel R X A (i + 2) ≅ H R (TopCat.of A) (i + 1) :=
  have := isIso_δ_of_isZero R X A i h₁ h₂
  asIso (δ R X A (i + 1))

lemma δIsoOfIsZero_hom (X : TopCat.{u}) (A : Set X) (i : ℕ)
    (h₁ : IsZero (H R X (i + 2))) (h₂ : IsZero (H R X (i + 1))) :
    (δIsoOfIsZero R X A i h₁ h₂).hom = δ R X A (i + 1) := rfl

/-- the reduced connecting isomorphism `H_1(X, A) ≅ H̃_0(A)` when `H_1(X) = H̃_0(X) = 0` -/
def δredIsoOfIsZero (X : TopCat.{u}) (A : Set X)
    (h₁ : IsZero (H R X 1)) (h₂ : IsZero (Hred₀ R X)) :
    Hrel R X A 1 ≅ Hred₀ R (TopCat.of A) :=
  have := isIso_δred_of_isZero R X A h₁ h₂
  asIso (δred R X A)

lemma δredIsoOfIsZero_hom (X : TopCat.{u}) (A : Set X)
    (h₁ : IsZero (H R X 1)) (h₂ : IsZero (Hred₀ R X)) :
    (δredIsoOfIsZero R X A h₁ h₂).hom = δred R X A := rfl

/-- naturality of the reduced connecting morphism `H_1(X, A) → H̃_0(A)` -/
theorem δred_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) :
    δred R X A ≫ Hred₀Map R (restr f hf) = HrelMap R f hf 1 ≫ δred R Y B := by
  rw [← cancel_mono (Hred₀ι R (TopCat.of B)), Category.assoc, Category.assoc, Hred₀Map_ι,
    δred_ι, δred_ι_assoc]
  exact δ_natural R f hf 0

/-! ### Degree zero -/

/-- `H_0(X, A) = 0` when `H_0(A) → H_0(X)` is surjective -/
theorem isZero_Hrel_zero_of_epi (X : TopCat.{u}) (A : Set X) (h : Epi (inclMap R X A 0)) :
    IsZero (Hrel R X A 0) := by
  have hπ : relπ R X A 0 = 0 := (les_exact₂ R X A 0).epi_f_iff.1 h
  have : Epi (relπ R X A 0) := inferInstanceAs (Epi ((pair X A).homologyπ R 0))
  exact IsZero.of_epi_eq_zero _ hπ

/-- `H_0(A) → H_0(X)` is surjective when `X` is path connected and `A` is nonempty -/
theorem epi_inclMap_zero_of_pathConnected (X : TopCat.{u}) (A : Set X) [PathConnectedSpace X]
    [Nonempty A] : Epi (inclMap R X A 0) := by
  have hε : IsIso (ε R X) := isIso_ε_of_pathConnected R X
  have hA : Nonempty (TopCat.of A) := inferInstanceAs (Nonempty A)
  have h : inclMap R X A 0 = ε R (TopCat.of A) ≫ inv (ε R X) := by
    rw [← inclMap_ε, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  have : Epi (ε R (TopCat.of A)) :=
    IsSplitEpi.epi _ (hf := ⟨⟨⟨εSection R (TopCat.of A), εSection_ε R (TopCat.of A)⟩⟩⟩)
  infer_instance

theorem isZero_Hrel_zero_of_pathConnected (X : TopCat.{u}) (A : Set X) [PathConnectedSpace X]
    [Nonempty A] : IsZero (Hrel R X A 0) :=
  isZero_Hrel_zero_of_epi R X A (epi_inclMap_zero_of_pathConnected R X A)

/-! ### Bookkeeping for `HrelMap` -/

/-- the `MapsTo` proof in `HrelMap` is irrelevant -/
lemma HrelMap_congr {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf hf' : Set.MapsTo f A B) (n : ℕ) : HrelMap R f hf n = HrelMap R f hf' n := rfl

lemma HrelMap_eq_of_eq {X Y : TopCat.{u}} {A : Set X} {B : Set Y} {f g : X ⟶ Y} (h : f = g)
    (hf : Set.MapsTo f A B) (n : ℕ) : HrelMap R f hf n = HrelMap R g (h ▸ hf) n := by
  subst h; rfl

lemma mapsTo_id_of_subset {X : TopCat.{u}} {A A' : Set X} (h : A ⊆ A') :
    Set.MapsTo (𝟙 X) A A' := fun x hx => by simpa using h hx

lemma mapsTo_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W} {f : X ⟶ Y}
    {g : Y ⟶ W} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D) : Set.MapsTo (f ≫ g) A D :=
  fun x hx => by simpa using hg (hf hx)

/-- `HrelMap` commutes with enlarging the subsets -/
lemma HrelMap_comp_id {X Y : TopCat.{u}} {A A' : Set X} {B B' : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B') (hA : Set.MapsTo (𝟙 X) A A')
    (hB : Set.MapsTo (𝟙 Y) B B') (n : ℕ) :
    HrelMap R f hf n ≫ HrelMap R (𝟙 Y) hB n = HrelMap R (𝟙 X) hA n ≫ HrelMap R f hf' n := by
  rw [← HrelMap_comp R f (𝟙 Y) hf hB (mapsTo_comp hf hB) n,
    ← HrelMap_comp R (𝟙 X) f hA hf' (mapsTo_comp hA hf') n]
  exact HrelMap_eq_of_eq R (by simp) _ n

/-- transport of relative homology along an equality of subsets -/
def HrelIsoOfEq (X : TopCat.{u}) {A A' : Set X} (h : A = A') (n : ℕ) :
    Hrel R X A n ≅ Hrel R X A' n where
  hom := HrelMap R (𝟙 X) (mapsTo_id_of_subset h.le) n
  inv := HrelMap R (𝟙 X) (mapsTo_id_of_subset h.ge) n
  hom_inv_id := by
    subst h
    rw [HrelMap_id, Category.id_comp]
  inv_hom_id := by
    subst h
    rw [HrelMap_id, Category.id_comp]

/-! ### Homeomorphism invariance of relative homology -/

section homeomorph

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y)

/-- the map of `TopCat` underlying a homeomorphism -/
abbrev homeoHom : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom (f : C(X, Y))

lemma homeoHom_eq_toHomotopyEquiv : homeoHom f = TopCat.ofHom f.toHomotopyEquiv.toFun := rfl

@[simp]
lemma homeoHom_apply (x : X) : homeoHom f x = f x := rfl

lemma homeoHom_comp_symm : homeoHom f ≫ homeoHom f.symm = 𝟙 _ := by
  ext x
  simp

lemma symm_comp_homeoHom : homeoHom f.symm ≫ homeoHom f = 𝟙 _ := by
  ext x
  simp

lemma mapsTo_homeoHom {A : Set X} {B : Set Y} (h : f '' A = B) :
    Set.MapsTo (homeoHom f) A B := by
  subst h
  exact Set.mapsTo_image f A

lemma mapsTo_homeoHom_symm {A : Set X} {B : Set Y} (h : f '' A = B) :
    Set.MapsTo (homeoHom f.symm) B A := by
  subst h
  rintro _ ⟨a, ha, rfl⟩
  simpa using ha

/-- a homeomorphism `f : X ≃ₜ Y` with `f '' A = B` induces `H_k(X, A) ≅ H_k(Y, B)` -/
def HrelIsoOfHomeomorphImage {A : Set X} {B : Set Y} (h : f '' A = B) (k : ℕ) :
    Hrel R (TopCat.of X) A k ≅ Hrel R (TopCat.of Y) B k where
  hom := HrelMap R (homeoHom f) (mapsTo_homeoHom f h) k
  inv := HrelMap R (homeoHom f.symm) (mapsTo_homeoHom_symm f h) k
  hom_inv_id := by
    rw [← HrelMap_comp R _ _ _ _
      (mapsTo_comp (mapsTo_homeoHom f h) (mapsTo_homeoHom_symm f h)) k]
    exact (HrelMap_eq_of_eq R (homeoHom_comp_symm f) _ k).trans (HrelMap_id R _ _ _ k)
  inv_hom_id := by
    rw [← HrelMap_comp R _ _ _ _
      (mapsTo_comp (mapsTo_homeoHom_symm f h) (mapsTo_homeoHom f h)) k]
    exact (HrelMap_eq_of_eq R (symm_comp_homeoHom f) _ k).trans (HrelMap_id R _ _ _ k)

lemma HrelIsoOfHomeomorphImage_hom {A : Set X} {B : Set Y} (h : f '' A = B) (k : ℕ) :
    (HrelIsoOfHomeomorphImage R f h k).hom = HrelMap R (homeoHom f) (mapsTo_homeoHom f h) k :=
  rfl

lemma HrelIsoOfHomeomorphImage_inv {A : Set X} {B : Set Y} (h : f '' A = B) (k : ℕ) :
    (HrelIsoOfHomeomorphImage R f h k).inv =
      HrelMap R (homeoHom f.symm) (mapsTo_homeoHom_symm f h) k :=
  rfl

theorem isIso_HrelMap_homeoHom {A : Set X} {B : Set Y} (h : f '' A = B)
    (hf : Set.MapsTo (homeoHom f) A B) (k : ℕ) : IsIso (HrelMap R (homeoHom f) hf k) :=
  ⟨(HrelIsoOfHomeomorphImage R f h k).inv, (HrelIsoOfHomeomorphImage R f h k).hom_inv_id,
    (HrelIsoOfHomeomorphImage R f h k).inv_hom_id⟩

/-- a homeomorphism `f : X ≃ₜ Y` induces `H_k(X, A) ≅ H_k(Y, f '' A)` -/
def HrelIsoOfHomeomorph (A : Set X) (k : ℕ) :
    Hrel R (TopCat.of X) A k ≅ Hrel R (TopCat.of Y) (f '' A) k :=
  HrelIsoOfHomeomorphImage R f rfl k

lemma HrelIsoOfHomeomorph_hom (A : Set X) (k : ℕ) :
    (HrelIsoOfHomeomorph R f A k).hom = HrelMap R (homeoHom f) (Set.mapsTo_image f A) k :=
  rfl

lemma homeomorph_image_eq_of_mem_iff {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ f x ∈ B) :
    f '' A = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    exact ⟨f.symm y, (h _).2 (by simpa using hy), by simp⟩

/-- a homeomorphism `f : X ≃ₜ Y` with `x ∈ A ↔ f x ∈ B` induces `H_k(X, A) ≅ H_k(Y, B)` -/
def HrelIsoOfHomeomorphIff {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ f x ∈ B) (k : ℕ) :
    Hrel R (TopCat.of X) A k ≅ Hrel R (TopCat.of Y) B k :=
  HrelIsoOfHomeomorphImage R f (homeomorph_image_eq_of_mem_iff f h) k

lemma HrelIsoOfHomeomorphIff_hom {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ f x ∈ B) (k : ℕ) :
    (HrelIsoOfHomeomorphIff R f h k).hom =
      HrelMap R (homeoHom f) (fun x hx => (h x).1 hx) k :=
  rfl

/-- naturality of `HrelIsoOfHomeomorphImage` in the subset -/
lemma HrelIsoOfHomeomorphImage_natural {A A' : Set X} {B B' : Set Y} (h : f '' A = B)
    (h' : f '' A' = B') (hA : Set.MapsTo (𝟙 (TopCat.of X)) A A')
    (hB : Set.MapsTo (𝟙 (TopCat.of Y)) B B') (k : ℕ) :
    (HrelIsoOfHomeomorphImage R f h k).hom ≫ HrelMap R (𝟙 _) hB k =
      HrelMap R (𝟙 _) hA k ≫ (HrelIsoOfHomeomorphImage R f h' k).hom :=
  HrelMap_comp_id R _ _ _ hA hB k

end homeomorph

/-! ### Nested subtypes -/

section nested

variable {X : Type u} [TopologicalSpace X]

lemma homeomorphPreimageVal_image {B B' : Set X} (h : B ⊆ B') (A : Set X) :
    homeomorphPreimageVal h '' (Subtype.val ⁻¹' (Subtype.val ⁻¹' A)) =
      (Subtype.val ⁻¹' A : Set B) := by
  ext ⟨x, hx⟩
  constructor
  · rintro ⟨⟨⟨y, hy⟩, hy'⟩, hyA, hxy⟩
    cases hxy
    exact hyA
  · intro hxA
    exact ⟨⟨⟨x, h hx⟩, hx⟩, hxA, rfl⟩

/-- for `B ⊆ B'`, the pair `(Subtype.val ⁻¹' B, Subtype.val ⁻¹' (Subtype.val ⁻¹' A))` inside
`B'` has the same relative homology as the pair `(B, Subtype.val ⁻¹' A)` -/
def HrelIsoOfSubtypeSubtype {B B' : Set X} (h : B ⊆ B') (A : Set X) (k : ℕ) :
    Hrel R (TopCat.of (Subtype.val ⁻¹' B : Set B')) (Subtype.val ⁻¹' (Subtype.val ⁻¹' A)) k ≅
      Hrel R (TopCat.of B) (Subtype.val ⁻¹' A) k :=
  HrelIsoOfHomeomorphImage R (homeomorphPreimageVal h) (homeomorphPreimageVal_image h A) k

end nested

end PoincareHighDim.SingularPair

end
