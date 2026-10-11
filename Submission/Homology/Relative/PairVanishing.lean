/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Homology.Naturality
import Submission.Morse.Defs

/-!
# Vanishing of the relative homology of a pair

The h-cobordism theorem (Milnor, *Lectures on the h-cobordism theorem*, Theorems 7.8 and 9.1)
takes as hypothesis the vanishing of the relative integral homology `H_*(W, V₀; ℤ)` of the
cobordism relative to its lower end.  We package this hypothesis as

* `RelHomologyVanishes X A` : `H_n(X, A; ℤ) = 0` for every `n`, where `A : Set X` and the
  homology is the singular homology of the pair of `Submission.Homology.SingularPair` with
  the coefficient object `SingularPair.Z` (the integers, lifted to the universe of `X`);

and we prove the one implication needed to keep the earlier, homotopy-theoretic form of the
theorem available:

* `IsHomotopyEquivInclusion.relHomologyVanishes` : if the inclusion `A ↪ B` is a homotopy
  equivalence then `H_*(B, A; ℤ) = 0`, where `A` is regarded as the subset
  `Subtype.val ⁻¹' A` of the subtype `B`.  The proof is the standard long exact sequence
  argument: the inclusion induces isomorphisms in absolute homology, so the maps
  `H_n(B) → H_n(B, A)` and `H_{n+1}(B, A) → H_n(A)` are both zero, and `H_{n+1}(B, A)` sits
  between them in the exact sequence; in degree `0` the map `H_0(B) → H_0(B, A)` is
  surjective and zero.

The converse (Whitehead's theorem, under simple connectivity) is not needed by the project.
-/

open CategoryTheory Limits
open scoped ContinuousMap

noncomputable section

universe u

namespace PoincareHighDim

open SingularPair

/-- `H_n(X, A; ℤ) = 0` for every `n`: the relative singular homology of the pair `(X, A)` with
integer coefficients vanishes in all degrees. -/
def RelHomologyVanishes (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ n, IsZero (Hrel Z (TopCat.of X) A n)

/-- Transport of `RelHomologyVanishes` along equalities of the ambient subset and the subset,
in the form used for strips `(W, V₀)` of a smooth function. -/
theorem RelHomologyVanishes.congr {X : Type u} [TopologicalSpace X] {B B' A A' : Set X}
    (hB : B = B') (hA : A = A') (h : RelHomologyVanishes B (Subtype.val ⁻¹' A)) :
    RelHomologyVanishes B' (Subtype.val ⁻¹' A') := by
  subst hB hA
  exact h

/-- For `A ⊆ B`, the subset `Subtype.val ⁻¹' A` of the subtype `B` is homeomorphic to `A`. -/
def homeomorphPreimageVal {X : Type u} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    (Subtype.val ⁻¹' A : Set B) ≃ₜ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, hAB y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- If the inclusion `A ↪ B` is a homotopy equivalence then `H_*(B, A; ℤ) = 0`. -/
theorem IsHomotopyEquivInclusion.relHomologyVanishes {X : Type u} [TopologicalSpace X]
    {A B : Set X} (h : IsHomotopyEquivInclusion A B) :
    RelHomologyVanishes B (Subtype.val ⁻¹' A) := by
  have hAB : A ⊆ B := h.subset
  obtain ⟨e, he⟩ := h
  -- The inclusion of `Subtype.val ⁻¹' A` into `B` is the homotopy equivalence `e` up to the
  -- homeomorphism `homeomorphPreimageVal hAB`.
  let e' : (Subtype.val ⁻¹' A : Set B) ≃ₕ B := (homeomorphPreimageVal hAB).toHomotopyEquiv.trans e
  have hincl : TopCat.ofHom e'.toFun = incl (TopCat.of B) (Subtype.val ⁻¹' A) := by
    ext x
    exact he _
  have hiso : ∀ n, IsIso (inclMap Z (TopCat.of B) (Subtype.val ⁻¹' A) n) := fun n => by
    rw [inclMap_eq_Hmap, ← hincl]
    exact isIso_Hmap_of_homotopyEquiv Z e' n
  -- `H_n(B) → H_n(B, A)` is zero, since `H_n(A) → H_n(B)` is surjective.
  have hπ : ∀ n, relπ Z (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₂ Z _ _ n).epi_f_iff.1 (haveI := hiso n; inferInstance)
  -- `H_{n+1}(B, A) → H_n(A)` is zero, since `H_n(A) → H_n(B)` is injective.
  have hδ : ∀ n, δ Z (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₁ Z _ _ n).mono_g_iff.1 (haveI := hiso n; inferInstance)
  intro n
  cases n with
  | zero =>
    -- `H_0(B) → H_0(B, A)` is surjective (Mathlib's `SSetPair.instEpiHomologyπOfNatNat`).
    have : Epi (relπ Z (TopCat.of B) (Subtype.val ⁻¹' A) 0) :=
      inferInstanceAs (Epi ((pair (TopCat.of B) (Subtype.val ⁻¹' A)).homologyπ Z 0))
    exact IsZero.of_epi_eq_zero _ (hπ 0)
  | succ n => exact (les_exact₃ Z _ _ n).isZero_X₂ (hπ (n + 1)) (hδ n)

end PoincareHighDim

end
