/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Homology.Bockstein
import Submission.Homology.Punctures.PuncturedAcyclic

/-!
# Surjectivity of `H_n(M;ℤ) → H_n(M, M ∖ {c};ℤ)` for a compact homotopy sphere

Let `n ≥ 2`, `M` a compact Hausdorff space charted on `ℝⁿ` and homotopy equivalent to `Sⁿ`,
and `c ∈ M`.  We prove that the "fundamental class" map `φ := relπ : H_n(M;ℤ) → H_n(M, M ∖ {c};ℤ)`
is surjective (`epi_relπ_compl_singleton_Z`), hence an isomorphism (`isIso_relπ_compl_singleton_Z`),
and that `M ∖ {c}` is acyclic with integral coefficients (`acyclic_compl_singleton_Z`).

The argument (which avoids orientation theory and the existence half of Hatcher 3.27) goes
through one auxiliary coefficient ring `ℤ/d`:

* both sides of `φ` are isomorphic to `ℤ` (`H_self_iso_of_homotopyEquiv_sphere`,
  `HrelComplSingletonManifoldIso`) and `φ` is injective (`mono_relπ_compl_singleton`), so
  `φ(g₀) = a • r₀` for generators `g₀`, `r₀` and some `a ≠ 0`; put `d := |a|`;
* with `R := ℤ/d` the same map is an injective self-map of the finite abelian group `ℤ/d`, hence
  surjective, so `M ∖ {c}` is `ℤ/d`-acyclic (`acyclic_compl_singleton_of_homotopyEquiv_sphere`);
  by the Bockstein sequence every class of `G := H_{n-1}(M ∖ {c};ℤ)` is divisible by `d`
  (`exists_smul_eq_of_isZero`);
* on the other hand `d • G = 0`: every `g ∈ G` is `δ β` (as `H_{n-1}(M;ℤ) = 0`), `β = m • r₀`,
  and `d • r₀ = ± φ(g₀)` is killed by `δ` (`δ ∘ φ = 0`).

Hence `G = 0`, so `δ = 0` and `φ` is surjective by exactness of the long exact sequence.
-/

open CategoryTheory Limits
open scoped ContinuousMap

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

/-! ### Elements of modules isomorphic to `Z` -/

/-- every element of `Z = ULift ℤ` is an integer multiple of `⟨1⟩` -/
lemma Z_eq_zsmul_one (a : Z.{u}) : a = a.down • (ULift.up 1 : Z.{u}) :=
  ULift.ext _ _ (by simp)

/-- every element of a module `A ≅ Z` is an integer multiple of `i.inv ⟨1⟩` -/
lemma exists_zsmul_eq_of_iso_Z {A : ModuleCat.{u} ℤ} (i : A ≅ Z.{u}) (x : A) :
    ∃ m : ℤ, m • i.inv (ULift.up 1) = x := by
  refine ⟨(i.hom x).down, ?_⟩
  rw [← map_zsmul, ← Z_eq_zsmul_one, Iso.hom_inv_id_apply]

/-- the generator `i.inv ⟨1⟩` of a module `A ≅ Z` is nonzero -/
lemma iso_Z_inv_one_ne_zero {A : ModuleCat.{u} ℤ} (i : A ≅ Z.{u}) : i.inv (ULift.up 1) ≠ 0 := by
  intro h
  have h1 : i.hom (i.inv (ULift.up 1)) = (ULift.up 1 : Z.{u}) := Iso.inv_hom_id_apply i _
  rw [h, map_zero] at h1
  exact one_ne_zero (congrArg ULift.down h1).symm

/-! ### Surjectivity of the fundamental-class map -/

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- with finite coefficients `ℤ/d`, the (injective) map `H_n(M) → H_n(M, M ∖ {c})` between two
copies of `ℤ/d` is surjective -/
theorem epi_relπ_compl_singleton_Zd (hn : 2 ≤ n) (e : M ≃ₕ Sph n) (c : M) (d : ℕ) [NeZero d] :
    Epi (relπ (Zd.{u} d) (TopCat.of M) {c}ᶜ n) := by
  have hn1 : 1 ≤ n := by omega
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_sphere hn1 e
  have hmono : Mono (relπ (Zd.{u} d) (TopCat.of M) {c}ᶜ n) :=
    mono_relπ_compl_singleton (Zd d) hn1 c
  let iH : H (Zd.{u} d) (TopCat.of M) n ≅ Zd.{u} d :=
    Sphere.H_self_iso_of_homotopyEquiv_sphere (Zd d) e (by omega)
  let iR : Hrel (Zd.{u} d) (TopCat.of M) {c}ᶜ n ≅ Zd.{u} d :=
    HrelComplSingletonManifoldIso (Zd d) hn1 c
  set f : Zd.{u} d ⟶ Zd.{u} d := iH.inv ≫ relπ (Zd.{u} d) (TopCat.of M) {c}ᶜ n ≫ iR.hom with hf
  have hfmono : Mono f := by infer_instance
  have hfepi : Epi f := by
    rw [ModuleCat.epi_iff_surjective]
    exact (Finite.injective_iff_bijective.1 ((ModuleCat.mono_iff_injective f).1 hfmono)).2
  have : relπ (Zd.{u} d) (TopCat.of M) {c}ᶜ n = iH.hom ≫ f ≫ iR.inv := by
    simp [hf]
  rw [this]
  infer_instance

/-- **Surjectivity of the fundamental-class map.** For `n ≥ 2`, `M` compact Hausdorff, charted on
`ℝⁿ` and homotopy equivalent to `Sⁿ`, the map `H_n(M;ℤ) → H_n(M, M ∖ {c};ℤ)` is surjective. -/
theorem epi_relπ_compl_singleton_Z (hn : 2 ≤ n) (e : M ≃ₕ Sph n) (c : M) :
    Epi (relπ Z.{u} (TopCat.of M) {c}ᶜ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hn1 : 1 ≤ m + 2 := by omega
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_sphere hn1 e
  set X : TopCat.{u} := TopCat.of M with hX
  set φ := relπ Z.{u} X {c}ᶜ (m + 2) with hφ
  have hmono : Mono φ := mono_relπ_compl_singleton Z hn1 c
  let iH : H Z.{u} X (m + 2) ≅ Z.{u} := Sphere.H_self_iso_of_homotopyEquiv_sphere Z e (by omega)
  let iR : Hrel Z.{u} X {c}ᶜ (m + 2) ≅ Z.{u} := HrelComplSingletonManifoldIso Z hn1 c
  set g₀ : H Z.{u} X (m + 2) := iH.inv (ULift.up 1) with hg₀
  set r₀ : Hrel Z.{u} X {c}ᶜ (m + 2) := iR.inv (ULift.up 1) with hr₀
  set a : ℤ := (iR.hom (φ g₀)).down with ha
  -- `φ g₀ = a • r₀`
  have hφg₀ : φ g₀ = a • r₀ := by
    rw [hr₀, ← map_zsmul, ← Z_eq_zsmul_one, Iso.hom_inv_id_apply]
  -- `a ≠ 0`
  have ha0 : a ≠ 0 := by
    intro h0
    apply iso_Z_inv_one_ne_zero iH
    apply (ModuleCat.mono_iff_injective φ).1 hmono
    rw [map_zero, ← hg₀, hφg₀, h0, zero_smul]
  set d : ℕ := a.natAbs with hd
  have : NeZero d := ⟨Int.natAbs_ne_zero.2 ha0⟩
  -- (1) `d • G = 0` for `G := H_{n-1}(M ∖ {c}; ℤ)`
  have hδφ : ∀ x, δ Z.{u} X {c}ᶜ (m + 1) (φ x) = 0 := fun x => by
    have h0 : relπ Z.{u} X {c}ᶜ (m + 2) ≫ δ Z.{u} X {c}ᶜ (m + 1) = 0 :=
      (pair X {c}ᶜ).comp_homologyδ Z (m + 2) (m + 1) rfl
    rw [← ModuleCat.comp_apply, hφ, h0]
    rfl
  have h1 : ∀ g : H Z.{u} (TopCat.of ({c}ᶜ : Set M)) (m + 1), (d : ℤ) • g = 0 := by
    intro g
    have hincl : inclMap Z.{u} X {c}ᶜ (m + 1) g = 0 := by
      rw [(Sphere.isZero_H_of_homotopyEquiv_sphere Z e (m + 1) (by omega) (by omega)).eq_zero_of_tgt
        (inclMap Z.{u} X {c}ᶜ (m + 1))]
      rfl
    obtain ⟨β, hβ⟩ := (ShortComplex.moduleCat_exact_iff _).1 (les_exact₁ Z X {c}ᶜ (m + 1)) g hincl
    obtain ⟨k, hk⟩ := exists_zsmul_eq_of_iso_Z iR β
    obtain ⟨q, hq⟩ : a ∣ (d : ℤ) := Int.dvd_natAbs.2 dvd_rfl
    change δ Z.{u} X {c}ᶜ (m + 1) β = g at hβ
    rw [← hβ, ← map_zsmul, ← hk, smul_comm, hq, mul_smul, smul_comm a, ← hφg₀]
    simp only [map_zsmul, hδφ]
    rw [zsmul_zero, zsmul_zero]
  -- (2) `G` is `d`-divisible, via `ℤ/d` coefficients
  have h2 : IsZero (H (Zd.{u} d) (TopCat.of ({c}ᶜ : Set M)) (m + 1)) :=
    (acyclic_compl_singleton_of_homotopyEquiv_sphere (Zd d) hn e c
      (epi_relπ_compl_singleton_Zd hn e c d)).1 (m + 1) (by omega)
  -- (3) hence `G = 0`
  have hG : IsZero (H Z.{u} (TopCat.of ({c}ᶜ : Set M)) (m + 1)) := by
    have : Subsingleton (H Z.{u} (TopCat.of ({c}ᶜ : Set M)) (m + 1)) := by
      refine subsingleton_of_forall_eq 0 fun g => ?_
      obtain ⟨g', hg'⟩ := exists_smul_eq_of_isZero d _ (m + 1) h2 g
      rw [← hg', h1]
    exact ModuleCat.isZero_of_subsingleton _
  exact (les_exact₃ Z X {c}ᶜ (m + 1)).epi_f_iff.2 (hG.eq_zero_of_tgt _)

/-- the fundamental-class map `H_n(M;ℤ) → H_n(M, M ∖ {c};ℤ)` is an isomorphism -/
theorem isIso_relπ_compl_singleton_Z (hn : 2 ≤ n) (e : M ≃ₕ Sph n) (c : M) :
    IsIso (relπ Z.{u} (TopCat.of M) {c}ᶜ n) := by
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_sphere (by omega) e
  have := mono_relπ_compl_singleton Z (by omega : 1 ≤ n) c
  have := epi_relπ_compl_singleton_Z hn e c
  exact isIso_of_mono_of_epi _

/-- **The punctured homotopy sphere is acyclic** (integral coefficients): for `n ≥ 2`, `M` compact
Hausdorff, charted on `ℝⁿ` and homotopy equivalent to `Sⁿ`, `H_k(M ∖ {c};ℤ) = 0` for `k ≥ 1`
and `H̃₀(M ∖ {c};ℤ) = 0`. -/
theorem acyclic_compl_singleton_Z (hn : 2 ≤ n) (e : M ≃ₕ Sph n) (c : M) :
    Acyclic Z.{u} (TopCat.of ({c}ᶜ : Set M)) :=
  acyclic_compl_singleton_of_homotopyEquiv_sphere Z hn e c (epi_relπ_compl_singleton_Z hn e c)

/-- `H_{n-1}(M ∖ {c};ℤ) = 0` -/
theorem isZero_H_compl_singleton_Z (hn : 2 ≤ n) (e : M ≃ₕ Sph n) (c : M) :
    IsZero (H Z.{u} (TopCat.of ({c}ᶜ : Set M)) (n - 1)) :=
  (acyclic_compl_singleton_Z hn e c).1 (n - 1) (by omega)

end charted

end PoincareHighDim.SingularPair

end
