/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Homology.Relative.DeltaIso
import Submission.Homology.Local.ChartTransport
import Submission.Homology.Local.Injectivity
import Submission.Morse.Defs

/-!
# Pairs with contractible subspace, and acyclicity of a punctured homotopy sphere

A space `X` is *acyclic* (`Acyclic R X`) when `H_k(X) = 0` for all `k ≥ 1` and `H̃₀(X) = 0`.

* `isZero_Hrel_of_contractible_of_acyclic`: if `X` is acyclic and `A ⊆ X` is contractible, then
  `H_k(X, A) = 0` for all `k` (long exact sequence of the pair, reduced in degree `0`);
* `acyclic_compl_singleton_of_homotopyEquiv_sphere`: for `n ≥ 2`, a compact Hausdorff space `M`
  charted on `ℝⁿ` and homotopy equivalent to `Sⁿ`, and a point `c` such that
  `H_n(M) → H_n(M, M ∖ {c})` is surjective, the punctured space `M ∖ {c}` is acyclic.  This
  combines `H_*(M) = H_*(Sⁿ)`, the local homology `H_k(M, M ∖ {c}) = 0` for `k ≠ n`
  (`isZero_Hrel_compl_singleton_manifold`) and the injectivity of `H_n(M) → H_n(M, M ∖ {c})`
  (`mono_relπ_compl_singleton`) in the long exact sequence of the pair `(M, M ∖ {c})`;
* `Acyclic.of_homotopyEquiv`, `acyclic_of_homotopyEquivInclusion`: acyclicity is transported
  along homotopy equivalences.

Everything is generic in the coefficient module `R`.
-/

open CategoryTheory Limits
open scoped ContinuousMap

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-! ### Acyclic spaces -/

/-- `X` is acyclic: `H_k(X) = 0` for `k ≥ 1` and `H̃₀(X) = 0` -/
abbrev Acyclic (X : TopCat.{u}) : Prop :=
  (∀ k, 1 ≤ k → IsZero (H R X k)) ∧ IsZero (Hred₀ R X)

/-- acyclicity is invariant under homotopy equivalences -/
theorem Acyclic.of_homotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (h : Acyclic R (TopCat.of Y)) :
    Acyclic R (TopCat.of X) :=
  ⟨fun k hk => (h.1 k hk).of_iso (homologyIso R e k), h.2.of_iso (Hred₀Iso R e)⟩

/-- acyclicity is transported from `B` to `A` along a homotopy equivalence `A ≃ₕ B` given by the
inclusion (`IsHomotopyEquivInclusion A B`) -/
theorem acyclic_of_homotopyEquivInclusion {M : Type u} [TopologicalSpace M] {A B : Set M}
    (hAB : IsHomotopyEquivInclusion A B) (h : Acyclic R (TopCat.of B)) :
    Acyclic R (TopCat.of A) := by
  obtain ⟨e, -⟩ := hAB
  exact Acyclic.of_homotopyEquiv R e h

/-- a contractible space is acyclic -/
theorem Acyclic.of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    Acyclic R (TopCat.of X) :=
  ⟨fun k hk => isZero_of_contractible R X k (by omega), isZero_Hred₀_of_contractible R X⟩

/-! ### Pairs with contractible subspace -/

/-- on a nonempty space with `H̃₀(X) = 0`, the augmentation `ε : H₀(X) → R` is an
isomorphism -/
theorem isIso_ε_of_isZero_Hred₀ (X : TopCat.{u}) [Nonempty X] (h0 : IsZero (Hred₀ R X)) :
    IsIso (ε R X) := by
  have hmono : Mono (ε R X) := Preadditive.mono_of_isZero_kernel _ h0
  have hepi : Epi (ε R X) :=
    IsSplitEpi.epi _ (hf := ⟨⟨⟨εSection R X, εSection_ε R X⟩⟩⟩)
  exact isIso_of_mono_of_epi _

/-- if `H̃₀(X) = 0` and `A ⊆ X` is contractible then `H₀(A) → H₀(X)` is surjective -/
theorem epi_inclMap_zero_of_contractible (X : TopCat.{u}) (A : Set X) [ContractibleSpace A]
    (h0 : IsZero (Hred₀ R X)) : Epi (inclMap R X A 0) := by
  have hA : Nonempty (TopCat.of A) := inferInstanceAs (Nonempty A)
  have hX : Nonempty X := ⟨(Classical.arbitrary A : A).1⟩
  have hεA : IsIso (ε R (TopCat.of A)) := isIso_ε_of_contractible R A
  have hεX : IsIso (ε R X) := isIso_ε_of_isZero_Hred₀ R X h0
  have h : inclMap R X A 0 = ε R (TopCat.of A) ≫ inv (ε R X) := by
    rw [← inclMap_ε, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- **Pairs with contractible subspace.** If `X` is acyclic (`H_k(X) = 0` for `k ≥ 1` and
`H̃₀(X) = 0`) and `A ⊆ X` is contractible, then `H_k(X, A) = 0` for every `k`. -/
theorem isZero_Hrel_of_contractible_of_acyclic {X : TopCat.{u}} {A : Set X} [ContractibleSpace A]
    (h : ∀ k, 1 ≤ k → IsZero (H R X k)) (h0 : IsZero (Hred₀ R X)) (k : ℕ) :
    IsZero (Hrel R X A k) := by
  rcases k with _ | _ | i
  · -- degree `0`: `H₀(A) → H₀(X)` is surjective
    exact isZero_Hrel_zero_of_epi R X A (epi_inclMap_zero_of_contractible R X A h0)
  · -- degree `1`: `H₁(X) → H₁(X, A) → H̃₀(A)` with both ends zero
    exact (les_red_exact₃ R X A).isZero_X₂ ((h 1 le_rfl).eq_zero_of_src _)
      ((isZero_Hred₀_of_contractible R A).eq_zero_of_tgt _)
  · -- degree `i + 2`: `H_{i+2}(X) → H_{i+2}(X, A) → H_{i+1}(A)` with both ends zero
    exact (les_exact₃ R X A (i + 1)).isZero_X₂ ((h (i + 2) (by omega)).eq_zero_of_src _)
      ((isZero_of_contractible R A (i + 1) i.succ_ne_zero).eq_zero_of_tgt _)

/-- the version of `isZero_Hrel_of_contractible_of_acyclic` with the `Acyclic` predicate -/
theorem isZero_Hrel_of_contractible_of_acyclic' {X : TopCat.{u}} {A : Set X}
    [ContractibleSpace A] (h : Acyclic R X) (k : ℕ) : IsZero (Hrel R X A k) :=
  isZero_Hrel_of_contractible_of_acyclic R h.1 h.2 k

/-! ### Acyclicity of a punctured homotopy sphere -/

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M]

/-- a space homotopy equivalent to `Sⁿ`, `n ≥ 1`, is path connected -/
theorem pathConnectedSpace_of_homotopyEquiv_sphere (hn : 1 ≤ n) (e : M ≃ₕ Sph n) :
    PathConnectedSpace M := by
  have := Sphere.pathConnectedSpace_of_one_le hn
  obtain ⟨H⟩ := e.left_inv
  refine ⟨⟨e.invFun (Classical.arbitrary (Sph n))⟩, fun x y => ?_⟩
  have hx : Joined (e.invFun (e.toFun x)) x := ⟨H.evalAt x⟩
  have hy : Joined (e.invFun (e.toFun y)) y := ⟨H.evalAt y⟩
  have hxy : Joined (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) :=
    (PathConnectedSpace.joined (e.toFun x) (e.toFun y)).map e.invFun.continuous
  exact hx.symm.trans (hxy.trans hy)

variable [T2Space M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- **Acyclicity of the punctured space.** Let `n ≥ 2`, `M` a compact Hausdorff space charted on
`ℝⁿ` and homotopy equivalent to `Sⁿ`, and `c ∈ M` a point such that
`H_n(M) → H_n(M, M ∖ {c})` is surjective.  Then `H_k(M ∖ {c}) = 0` for all `k ≥ 1` and
`H̃₀(M ∖ {c}) = 0`. -/
theorem acyclic_compl_singleton_of_homotopyEquiv_sphere (hn : 2 ≤ n) (e : M ≃ₕ Sph n) (c : M)
    (hsurj : Epi (relπ R (TopCat.of M) {c}ᶜ n)) :
    (∀ k, 1 ≤ k → IsZero (H R (TopCat.of ({c}ᶜ : Set M)) k)) ∧
      IsZero (Hred₀ R (TopCat.of ({c}ᶜ : Set M))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hn1 : 1 ≤ m + 2 := by omega
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_sphere hn1 e
  -- the homology of `M`
  have hM : ∀ k, k ≠ m + 2 → k ≠ 0 → IsZero (H R (TopCat.of M) k) := fun k hk hk0 =>
    Sphere.isZero_H_of_homotopyEquiv_sphere R e k hk hk0
  have hMred : IsZero (Hred₀ R (TopCat.of M)) :=
    Sphere.isZero_Hred₀_of_homotopyEquiv_sphere R e (by omega)
  -- the local homology at `c`
  have hrel : ∀ k, k ≠ m + 2 → IsZero (Hrel R (TopCat.of M) {c}ᶜ k) := fun k hk =>
    isZero_Hrel_compl_singleton_manifold R hn1 c hk
  have hmono : Mono (relπ R (TopCat.of M) {c}ᶜ (m + 2)) := mono_relπ_compl_singleton R hn1 c
  refine ⟨fun k hk => ?_, ?_⟩
  · by_cases hkn : k = m + 2
    · -- degree `n`: `H_{n+1}(M, M ∖ c) → H_n(M ∖ c) → H_n(M)` with `δ = 0`, `inclMap = 0`
      subst hkn
      have hincl : inclMap R (TopCat.of M) {c}ᶜ (m + 2) = 0 :=
        (les_exact₂ R (TopCat.of M) {c}ᶜ (m + 2)).mono_g_iff.1 hmono
      exact (les_exact₁ R (TopCat.of M) {c}ᶜ (m + 2)).isZero_X₂
        ((hrel (m + 3) (by omega)).eq_zero_of_src _) hincl
    by_cases hkn' : k = m + 1
    · -- degree `n - 1`: `H_n(M, M ∖ c) → H_{n-1}(M ∖ c) → H_{n-1}(M)` with `δ = 0` (as
      -- `relπ` is surjective) and `H_{n-1}(M) = 0`
      subst hkn'
      have hδ : δ R (TopCat.of M) {c}ᶜ (m + 1) = 0 :=
        (les_exact₃ R (TopCat.of M) {c}ᶜ (m + 1)).epi_f_iff.1 hsurj
      exact (les_exact₁ R (TopCat.of M) {c}ᶜ (m + 1)).isZero_X₂ hδ
        ((hM (m + 1) (by omega) (by omega)).eq_zero_of_tgt _)
    · -- other degrees: `H_{k+1}(M, M ∖ c) → H_k(M ∖ c) → H_k(M)` with both ends zero
      exact (les_exact₁ R (TopCat.of M) {c}ᶜ k).isZero_X₂
        ((hrel (k + 1) (by omega)).eq_zero_of_src _)
        ((hM k hkn (by omega)).eq_zero_of_tgt _)
  · -- reduced degree `0`: `H₁(M, M ∖ c) → H̃₀(M ∖ c) → H̃₀(M)` with both ends zero
    exact (les_red_exact₁ R (TopCat.of M) {c}ᶜ).isZero_X₂
      ((hrel 1 (by omega)).eq_zero_of_src _) (hMred.eq_zero_of_tgt _)

/-- `acyclic_compl_singleton_of_homotopyEquiv_sphere` with the `Acyclic` predicate -/
theorem Acyclic.compl_singleton_of_homotopyEquiv_sphere (hn : 2 ≤ n) (e : M ≃ₕ Sph n) (c : M)
    (hsurj : Epi (relπ R (TopCat.of M) {c}ᶜ n)) : Acyclic R (TopCat.of ({c}ᶜ : Set M)) :=
  acyclic_compl_singleton_of_homotopyEquiv_sphere R hn e c hsurj

end charted

end PoincareHighDim.SingularPair

end
