import Submission.Homology.Relative.PairVanishing
import Submission.Homology.Relative.Excision

/-!
# Relative homotopy invariance for inclusions of pairs

If `A ⊆ B` and `A' ⊆ B'` are subsets of a space `X` with `A ⊆ A'`, `B ⊆ B'`, and both
inclusions `A ↪ A'` and `B ↪ B'` are homotopy equivalences, then the inclusion of pairs
`(B, A) ↪ (B', A')` induces isomorphisms in relative singular homology.  The proof is the five
lemma for the morphism of long exact sequences of the two pairs, packaged in
`Submission.Homology.Relative.Excision` as `isIso_homologyMap_of_quasiIso`: a map of pairs which is a
quasi-isomorphism on the subspaces and on the total spaces is a quasi-isomorphism of relative
chain complexes.

* `isIso_HrelMap_of_isIso_Hmap` : the general five-lemma statement for a map of pairs
  inducing isomorphisms in absolute homology of both members;
* `isIso_HrelMap_inclOfLE_of_homotopyEquiv` : the statement for inclusions of pairs, where
  the subsets `A`, `A'` are regarded as the subsets `Subtype.val ⁻¹' A`, `Subtype.val ⁻¹' A'`
  of the subtypes `B`, `B'`;
* `HrelIsoOfHomotopyEquivInclusion` : the resulting isomorphism
  `H_k(B, A) ≅ H_k(B', A')`;
* `relHomologyVanishes_of_isIso_inclMap` : `H_*(B, A; ℤ) = 0` as soon as the inclusion
  `A ↪ B` induces isomorphisms in absolute integral homology (the long exact sequence argument
  of `IsHomotopyEquivInclusion.relHomologyVanishes`, isolated).
-/

open CategoryTheory Limits HomologicalComplex
open scoped ContinuousMap

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-! ### The five lemma for maps of pairs -/

/-- A map of pairs inducing isomorphisms in absolute homology of the subspaces and of the
total spaces induces isomorphisms in relative homology (five lemma). -/
theorem isIso_HrelMap_of_isIso_Hmap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (h₁ : ∀ n, IsIso (Hmap R (restr f hf) n))
    (h₂ : ∀ n, IsIso (Hmap R f n)) (k : ℕ) : IsIso (HrelMap R f hf k) :=
  isIso_homologyMap_of_quasiIso R (pairMap f hf)
    ⟨fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).2 (h₁ n)⟩
    ⟨fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).2 (h₂ n)⟩ k

/-! ### Inclusions of pairs which are homotopy equivalences on both members -/

section inclusion

variable {X : Type u} [TopologicalSpace X] {A A' B B' : Set X}

/-- For `A ⊆ A'` the inclusion `B ↪ B'` maps `Subtype.val ⁻¹' A` into `Subtype.val ⁻¹' A'`. -/
theorem mapsTo_inclOfLE_preimage (hBB' : B ⊆ B') (hAA' : A ⊆ A') :
    Set.MapsTo (inclOfLE (X := TopCat.of X) hBB') (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' A') :=
  fun _ hx => hAA' hx

/-- The inclusion `Subtype.val ⁻¹' A ↪ Subtype.val ⁻¹' A'` (of subsets of the subtypes `B`
and `B'`) is, up to the homeomorphisms `homeomorphPreimageVal`, the homotopy equivalence
`A ≃ₕ A'` given by `IsHomotopyEquivInclusion A A'`. -/
theorem isIso_Hmap_restr_inclOfLE (hAB : A ⊆ B) (hA'B' : A' ⊆ B') (hBB' : B ⊆ B')
    (hAA' : A ⊆ A') (hA : IsHomotopyEquivInclusion A A') (n : ℕ) :
    IsIso (Hmap R (restr (inclOfLE (X := TopCat.of X) hBB')
      (mapsTo_inclOfLE_preimage hBB' hAA')) n) := by
  obtain ⟨eA, heA⟩ := hA
  let e' : (Subtype.val ⁻¹' A : Set B) ≃ₕ (Subtype.val ⁻¹' A' : Set B') :=
    (homeomorphPreimageVal hAB).toHomotopyEquiv.trans
      (eA.trans (homeomorphPreimageVal hA'B').symm.toHomotopyEquiv)
  have h : TopCat.ofHom e'.toFun =
      restr (inclOfLE (X := TopCat.of X) hBB') (mapsTo_inclOfLE_preimage hBB' hAA') := by
    ext x
    exact heA _
  rw [← h]
  exact isIso_Hmap_of_homotopyEquiv R e' n

/-- The inclusion `B ↪ B'` given by `IsHomotopyEquivInclusion B B'` induces isomorphisms in
homology. -/
theorem isIso_Hmap_inclOfLE (hBB' : B ⊆ B') (hB : IsHomotopyEquivInclusion B B') (n : ℕ) :
    IsIso (Hmap R (inclOfLE (X := TopCat.of X) hBB') n) := by
  obtain ⟨eB, heB⟩ := hB
  have h : TopCat.ofHom eB.toFun = inclOfLE (X := TopCat.of X) hBB' := by
    ext x
    exact heB _
  rw [← h]
  exact isIso_Hmap_of_homotopyEquiv R eB n

/-- **Relative homotopy invariance for inclusions of pairs.**  If `A ⊆ B`, `A' ⊆ B'`,
`A ⊆ A'`, `B ⊆ B'` and the inclusions `A ↪ A'`, `B ↪ B'` are homotopy equivalences, then the
inclusion of pairs `(B, A) ↪ (B', A')` induces isomorphisms in relative homology. -/
theorem isIso_HrelMap_inclOfLE_of_homotopyEquiv (hAB : A ⊆ B) (hA'B' : A' ⊆ B') (hBB' : B ⊆ B')
    (hAA' : A ⊆ A') (hB : IsHomotopyEquivInclusion B B') (hA : IsHomotopyEquivInclusion A A')
    (k : ℕ) :
    IsIso (HrelMap R (inclOfLE (X := TopCat.of X) hBB') (mapsTo_inclOfLE_preimage hBB' hAA') k) :=
  isIso_HrelMap_of_isIso_Hmap R _ _ (isIso_Hmap_restr_inclOfLE R hAB hA'B' hBB' hAA' hA)
    (isIso_Hmap_inclOfLE R hBB' hB) k

/-- The isomorphism `H_k(B, A) ≅ H_k(B', A')` induced by an inclusion of pairs which is a
homotopy equivalence on both members. -/
def HrelIsoOfHomotopyEquivInclusion (hAB : A ⊆ B) (hA'B' : A' ⊆ B') (hBB' : B ⊆ B')
    (hAA' : A ⊆ A') (hB : IsHomotopyEquivInclusion B B') (hA : IsHomotopyEquivInclusion A A')
    (k : ℕ) :
    Hrel R (TopCat.of B) (Subtype.val ⁻¹' A) k ≅ Hrel R (TopCat.of B') (Subtype.val ⁻¹' A') k :=
  haveI := isIso_HrelMap_inclOfLE_of_homotopyEquiv R hAB hA'B' hBB' hAA' hB hA k
  asIso (HrelMap R (inclOfLE (X := TopCat.of X) hBB') (mapsTo_inclOfLE_preimage hBB' hAA') k)

lemma HrelIsoOfHomotopyEquivInclusion_hom (hAB : A ⊆ B) (hA'B' : A' ⊆ B') (hBB' : B ⊆ B')
    (hAA' : A ⊆ A') (hB : IsHomotopyEquivInclusion B B') (hA : IsHomotopyEquivInclusion A A')
    (k : ℕ) :
    (HrelIsoOfHomotopyEquivInclusion R hAB hA'B' hBB' hAA' hB hA k).hom =
      HrelMap R (inclOfLE (X := TopCat.of X) hBB') (mapsTo_inclOfLE_preimage hBB' hAA') k := rfl

end inclusion

/-! ### Vanishing of relative homology from isomorphisms in absolute homology -/

/-- If the inclusion `A ↪ B` induces isomorphisms in absolute integral homology, then
`H_*(B, A; ℤ) = 0`. -/
theorem relHomologyVanishes_of_isIso_inclMap {X : Type u} [TopologicalSpace X] {A B : Set X}
    (h : ∀ k, IsIso (inclMap Z (TopCat.of B) (Subtype.val ⁻¹' A) k)) :
    RelHomologyVanishes B (Subtype.val ⁻¹' A) := by
  -- `H_n(B) → H_n(B, A)` is zero, since `H_n(A) → H_n(B)` is surjective.
  have hπ : ∀ n, relπ Z (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₂ Z _ _ n).epi_f_iff.1 (haveI := h n; inferInstance)
  -- `H_{n+1}(B, A) → H_n(A)` is zero, since `H_n(A) → H_n(B)` is injective.
  have hδ : ∀ n, δ Z (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₁ Z _ _ n).mono_g_iff.1 (haveI := h n; inferInstance)
  intro n
  cases n with
  | zero =>
    have : Epi (relπ Z (TopCat.of B) (Subtype.val ⁻¹' A) 0) :=
      inferInstanceAs (Epi ((pair (TopCat.of B) (Subtype.val ⁻¹' A)).homologyπ Z 0))
    exact IsZero.of_epi_eq_zero _ (hπ 0)
  | succ n => exact (les_exact₃ Z _ _ n).isZero_X₂ (hπ (n + 1)) (hδ n)

end PoincareHighDim.SingularPair

end
