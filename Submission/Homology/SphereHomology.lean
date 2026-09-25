import Submission.Homology.SingularPair
import Submission.Homology.Naturality
import Submission.Homology.MayerVietoris
import Submission.Homology.SphereTopology

/-!
# The singular homology of spheres

We compute the singular homology of the spheres `Sph n = Metric.sphere (0 : ℝ^(n+1)) 1` by
Mayer–Vietoris induction, using reduced `H₀`.

## Contents

* `mvOpenδredIso`: the degree-one Mayer–Vietoris isomorphism with reduced `H₀`:
  for an open cover `X = U ∪ V` by contractible subsets, `H₁(X) ≅ H̃₀(U ∩ V)`.
* The sphere `Sⁿ` is placed in universe `u` as `SphU n := TopCat.of (ULift.{u} (Sph n))`, so
  that all statements are universe polymorphic (`R : ModuleCat.{u} ℤ`).  The cover by the
  complements of the poles, their contractibility and the homotopy equivalence of the
  intersection with `Sⁿ⁻¹` (`Submission.Homology.SphereTopology`) are transported to `ULift`.
* `H_succ_iso : H_{k+2}(Sⁿ⁺¹) ≅ H_{k+1}(Sⁿ)`, `H1_succ_iso : H₁(Sⁿ⁺¹) ≅ H̃₀(Sⁿ)`.
* The main results `isZero_H_sphere` (`H_k(Sⁿ) = 0` for `k ∉ {0, n}`), `H_sphere_self_iso`
  (`H_n(Sⁿ) ≅ R` for `n ≥ 1`), `H0_sphere_succ_iso` (`H₀(Sⁿ) ≅ R` for `n ≥ 1`),
  `isZero_Hred₀_sphere_succ` (`H̃₀(Sⁿ) = 0` for `n ≥ 1`), `Hred₀_sphere_zero`
  (`H̃₀(S⁰) ≅ R`), `H0_sphere_zero` (`H₀(S⁰) ≅ R ⊞ R`, from the general splitting
  `H0IsoHred₀Biprod : H₀(X) ≅ H̃₀(X) ⊞ R` for nonempty `X`), `isZero_H_sphere_zero`
  (`H_k(S⁰) = 0` for `k ≠ 0`), packaged in `homology_sphere`.
* Versions for the project's sphere type `Sph n` itself (universe `0`) and for any space
  `M : Type u` homotopy equivalent to `Sph n` (`homologyIsoSphere`).
-/

open CategoryTheory Limits HomologicalComplex AlgebraicTopology
open scoped ContinuousMap

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-! ### Mayer–Vietoris in degree one with reduced `H₀` -/

section MVone

variable {X : TopCat.{u}} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- `x ↦ (x, -x)` -/
abbrev antiDiag : R ⟶ R ⊞ R := biprod.lift (𝟙 R) (-𝟙 R)

instance mono_antiDiag : Mono (antiDiag R) :=
  mono_of_mono_fac (biprod.lift_fst (𝟙 R) (-𝟙 R))

/-- compatibility of the first Mayer–Vietoris map with the augmentations -/
lemma mvOpenLift_comp_biprodMap_ε :
    mvOpenLift R X U V 0 ≫ biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V)) =
      ε R (TopCat.of (U ∩ V : Set X)) ≫ antiDiag R := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, mvOpenLift_fst, Category.assoc,
      biprod.lift_fst, Category.comp_id]
    exact ε_natural' R _
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, mvOpenLift_snd, Category.assoc,
      biprod.lift_snd, Preadditive.comp_neg, Category.comp_id]
    exact (Preadditive.neg_comp _ _).trans (congrArg Neg.neg (ε_natural' R _))

@[reassoc (attr := simp)]
lemma mvOpenδ_comp_ε :
    mvOpenδ R hU hV hUV 0 ≫ ε R (TopCat.of (U ∩ V : Set X)) = 0 := by
  have h1 : ε R (TopCat.of (U ∩ V : Set X)) =
      (ε R (TopCat.of (U ∩ V : Set X)) ≫ antiDiag R) ≫ biprod.fst := by
    rw [Category.assoc, biprod.lift_fst, Category.comp_id]
  rw [h1, ← mvOpenLift_comp_biprodMap_ε, ← Category.assoc, ← Category.assoc,
    mvOpenδ_mvOpenLift, zero_comp, zero_comp]

/-- the Mayer–Vietoris connecting morphism `H₁(X) ⟶ H̃₀(U ∩ V)` -/
def mvOpenδred : H R X 1 ⟶ Hred₀ R (TopCat.of (U ∩ V : Set X)) :=
  kernel.lift _ (mvOpenδ R hU hV hUV 0) (mvOpenδ_comp_ε R hU hV hUV)

@[reassoc (attr := simp)]
lemma mvOpenδred_ι :
    mvOpenδred R hU hV hUV ≫ Hred₀ι R (TopCat.of (U ∩ V : Set X)) = mvOpenδ R hU hV hUV 0 :=
  kernel.lift_ι _ _ _

/-- if `H₁(U) = H₁(V) = 0`, then `H₁(X) ⟶ H̃₀(U ∩ V)` is a monomorphism -/
theorem mono_mvOpenδred (hU' : IsZero (H R (TopCat.of U) 1)) (hV' : IsZero (H R (TopCat.of V) 1)) :
    Mono (mvOpenδred R hU hV hUV) :=
  haveI := mono_mvOpenδ R hU hV hUV 0 hU' hV'
  mono_of_mono_fac (mvOpenδred_ι R hU hV hUV)

/-- if the augmentations of `U` and `V` are isomorphisms (e.g. `U`, `V` path connected), then
`H₁(X) ⟶ H̃₀(U ∩ V)` is an epimorphism -/
theorem epi_mvOpenδred [IsIso (ε R (TopCat.of U))] [IsIso (ε R (TopCat.of V))] :
    Epi (mvOpenδred R hU hV hUV) := by
  have hex := exact_kernelLift₂₃ (mayerVietoris_exact₁ R hU hV hUV 0)
    (ε R (TopCat.of (U ∩ V : Set X))) (biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V)))
    (antiDiag R) (mvOpenLift_comp_biprodMap_ε R)
  have hz : IsZero (kernel (biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V)))) := by
    have : IsIso (biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V))) :=
      inferInstanceAs
        (IsIso (biprod.mapIso (asIso (ε R (TopCat.of U))) (asIso (ε R (TopCat.of V)))).hom)
    exact (isZero_zero _).of_iso (kernel.ofMono _)
  exact hex.epi_f (hz.eq_zero_of_tgt _)

/-- for an open cover by contractible subsets, `H₁(X) ⟶ H̃₀(U ∩ V)` is an isomorphism -/
theorem isIso_mvOpenδred [ContractibleSpace U] [ContractibleSpace V] :
    IsIso (mvOpenδred R hU hV hUV) :=
  haveI := mono_mvOpenδred R hU hV hUV (isZero_of_contractible R U 1 one_ne_zero)
    (isZero_of_contractible R V 1 one_ne_zero)
  haveI := epi_mvOpenδred R hU hV hUV
  isIso_of_mono_of_epi _

/-- **Mayer–Vietoris in degree one**: for an open cover `X = U ∪ V` by contractible subsets,
`H₁(X) ≅ H̃₀(U ∩ V)`. -/
def mvOpenδredIso [ContractibleSpace U] [ContractibleSpace V] :
    H R X 1 ≅ Hred₀ R (TopCat.of (U ∩ V : Set X)) :=
  @asIso _ _ _ _ _ (isIso_mvOpenδred R hU hV hUV)

end MVone

/-! ### `H₀(X) ≅ H̃₀(X) ⊞ R` for nonempty `X` -/

section split

variable (X : TopCat.{u})

/-- the short complex `H̃₀(X) ⟶ H₀(X) ⟶ R` -/
abbrev εShortComplex : ShortComplex (ModuleCat.{u} ℤ) :=
  ShortComplex.mk (Hred₀ι R X) (ε R X) (Hred₀ι_ε R X)

lemma εShortComplex_exact : (εShortComplex R X).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (ε R X))

variable [Nonempty X]

/-- the map from a point to `X` -/
def ptMap : TopCat.of PUnit.{u + 1} ⟶ X :=
  TopCat.ofHom ⟨fun _ => Classical.arbitrary X, continuous_const⟩

instance isIso_ε_pt : IsIso (ε R (TopCat.of PUnit.{u + 1})) :=
  isIso_ε_of_contractible R PUnit.{u + 1}

/-- a section of the augmentation `ε : H₀(X) ⟶ R` -/
def εSection : R ⟶ H R X 0 := inv (ε R (TopCat.of PUnit.{u + 1})) ≫ Hmap R (ptMap X) 0

@[reassoc (attr := simp)]
lemma εSection_ε : εSection R X ≫ ε R X = 𝟙 R := by
  rw [εSection, Category.assoc, ε_natural, IsIso.inv_hom_id]

/-- the augmentation sequence splits -/
def εSplitting : (εShortComplex R X).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _ (εShortComplex_exact R X) (εSection R X)
    (εSection_ε R X) (inferInstance : Mono (Hred₀ι R X))

/-- for nonempty `X`, `H₀(X) ≅ H̃₀(X) ⊞ R` -/
def H0IsoHred₀Biprod : H R X 0 ≅ Hred₀ R X ⊞ R :=
  (εSplitting R X).isoBinaryBiproduct

lemma H0IsoHred₀Biprod_hom_snd : (H0IsoHred₀Biprod R X).hom ≫ biprod.snd = ε R X :=
  biprod.lift_snd _ _

lemma inl_H0IsoHred₀Biprod_inv : biprod.inl ≫ (H0IsoHred₀Biprod R X).inv = Hred₀ι R X :=
  biprod.inl_desc _ _

end split

/-! ### Spheres in universe `u` -/

namespace Sphere

/-- the sphere `Sⁿ` lifted to universe `u`, as an object of `TopCat.{u}` -/
abbrev SphU (n : ℕ) : TopCat.{u} := TopCat.of (ULift.{u} (Sph n))

/-- a subset of `Y` and its preimage in `ULift Y` are homeomorphic -/
def uliftSetHomeomorph {Y : Type} [TopologicalSpace Y] (A : Set Y) :
    ↥(ULift.down ⁻¹' A : Set (ULift.{u} Y)) ≃ₜ ↥A :=
  Homeomorph.ulift.sets rfl

/-- the complement of the north pole, in `ULift (Sph n)` -/
abbrev NU (n : ℕ) : Set (ULift.{u} (Sph n)) := ULift.down ⁻¹' {N n}ᶜ

/-- the complement of the south pole, in `ULift (Sph n)` -/
abbrev SU (n : ℕ) : Set (ULift.{u} (Sph n)) := ULift.down ⁻¹' {S n}ᶜ

lemma isOpen_NU (n : ℕ) : IsOpen (NU.{u} n) :=
  (isOpen_compl_singleton (N n)).preimage continuous_uliftDown

lemma isOpen_SU (n : ℕ) : IsOpen (SU.{u} n) :=
  (isOpen_compl_singleton (S n)).preimage continuous_uliftDown

lemma coverU (n : ℕ) : NU.{u} n ∪ SU.{u} n = Set.univ := by
  rw [← Set.preimage_union, cover, Set.preimage_univ]

instance contractibleSpace_NU (n : ℕ) : ContractibleSpace (NU.{u} n) :=
  (uliftSetHomeomorph _).contractibleSpace

instance contractibleSpace_SU (n : ℕ) : ContractibleSpace (SU.{u} n) :=
  (uliftSetHomeomorph _).contractibleSpace

/-- the complement of the poles in `ULift (Sph (n+1))` is homotopy equivalent to
`ULift (Sph n)` -/
def equatorU (n : ℕ) : ↥(NU.{u} (n + 1) ∩ SU.{u} (n + 1)) ≃ₕ ULift.{u} (Sph n) :=
  (uliftSetHomeomorph (({N (n + 1)}ᶜ : Set (Sph (n + 1))) ∩ {S (n + 1)}ᶜ)).toHomotopyEquiv.trans
    ((equatorHomotopyEquiv n).trans Homeomorph.ulift.symm.toHomotopyEquiv)

instance pathConnectedSpace_ulift_succ (n : ℕ) : PathConnectedSpace (ULift.{u} (Sph (n + 1))) :=
  Homeomorph.ulift.symm.pathConnectedSpace

instance totallyDisconnectedSpace_ulift_zero : TotallyDisconnectedSpace (ULift.{u} (Sph 0)) :=
  inferInstance

/-! ### The zero sphere -/

theorem isZero_H_sphere_zero (k : ℕ) (hk : k ≠ 0) : IsZero (H R (SphU.{u} 0) k) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ k R (SphU.{u} 0) hk

/-- `H̃₀(S⁰) ≅ R` -/
def Hred₀_sphere_zero : Hred₀ R (SphU.{u} 0) ≅ R :=
  Hred₀IsoOfTwoPoints R (SphU.{u} 0) ⟨N 0⟩ ⟨S 0⟩
    (fun h => N_ne_S 0 (congrArg ULift.down h))
    (fun z => by
      rcases eq_N_or_eq_S_zero z.down with h | h
      · exact Or.inl (ULift.ext _ _ h)
      · exact Or.inr (ULift.ext _ _ h))

instance nonempty_ulift_sphere (n : ℕ) : Nonempty (ULift.{u} (Sph n)) := ⟨⟨N n⟩⟩

/-- `H₀(S⁰) ≅ R ⊞ R` -/
def H0_sphere_zero : H R (SphU.{u} 0) 0 ≅ R ⊞ R :=
  H0IsoHred₀Biprod R (SphU.{u} 0) ≪≫ biprod.mapIso (Hred₀_sphere_zero R) (Iso.refl R)

/-! ### The inductive step -/

/-- `H_{k+2}(Sⁿ⁺¹) ≅ H_{k+1}(Sⁿ)` -/
def H_succ_iso (n k : ℕ) : H R (SphU.{u} (n + 1)) (k + 2) ≅ H R (SphU.{u} n) (k + 1) :=
  mvOpenδIso_of_contractible R (isOpen_NU (n + 1)) (isOpen_SU (n + 1)) (coverU (n + 1))
    (k + 1) k.succ_ne_zero ≪≫ homologyIso R (equatorU n) (k + 1)

/-- `H₁(Sⁿ⁺¹) ≅ H̃₀(Sⁿ)` -/
def H1_succ_iso (n : ℕ) : H R (SphU.{u} (n + 1)) 1 ≅ Hred₀ R (SphU.{u} n) :=
  mvOpenδredIso R (isOpen_NU (n + 1)) (isOpen_SU (n + 1)) (coverU (n + 1)) ≪≫
    Hred₀Iso R (equatorU n)

theorem isZero_Hred₀_sphere_succ (n : ℕ) : IsZero (Hred₀ R (SphU.{u} (n + 1))) :=
  isZero_Hred₀_of_pathConnected R (SphU.{u} (n + 1))

instance isIso_ε_sphere_succ (n : ℕ) : IsIso (ε R (SphU.{u} (n + 1))) :=
  isIso_ε_of_pathConnected R (SphU.{u} (n + 1))

/-- `H₀(Sⁿ⁺¹) ≅ R` -/
def H0_sphere_succ_iso (n : ℕ) : H R (SphU.{u} (n + 1)) 0 ≅ R :=
  asIso (ε R (SphU.{u} (n + 1)))

/-! ### The induction -/

theorem homology_sphere_aux (n : ℕ) :
    (∀ k, k ≠ n → k ≠ 0 → IsZero (H R (SphU.{u} n) k)) ∧
      (n ≠ 0 → Nonempty (H R (SphU.{u} n) n ≅ R)) := by
  induction n with
  | zero => exact ⟨fun k _ hk => isZero_H_sphere_zero R k hk, fun h => absurd rfl h⟩
  | succ n ih =>
    refine ⟨fun k hk hk0 => ?_, fun _ => ?_⟩
    · obtain _ | _ | k := k
      · exact absurd rfl hk0
      · have hn : n ≠ 0 := by omega
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        have e := H1_succ_iso R (m + 1)
        exact (isZero_Hred₀_sphere_succ R m).of_iso e
      · have e := H_succ_iso R n k
        exact (ih.1 (k + 1) (by omega) (by omega)).of_iso e
    · obtain _ | n := n
      · exact ⟨H1_succ_iso R 0 ≪≫ Hred₀_sphere_zero R⟩
      · obtain ⟨e⟩ := ih.2 n.succ_ne_zero
        exact ⟨H_succ_iso R (n + 1) n ≪≫ e⟩

/-- `H_k(Sⁿ) = 0` for `k ∉ {0, n}` -/
theorem isZero_H_sphere (n k : ℕ) (hk : k ≠ n) (hk0 : k ≠ 0) : IsZero (H R (SphU.{u} n) k) :=
  (homology_sphere_aux R n).1 k hk hk0

/-- `H_n(Sⁿ) ≅ R` for `n ≥ 1` -/
def H_sphere_self_iso (n : ℕ) (hn : n ≠ 0) : H R (SphU.{u} n) n ≅ R :=
  Classical.choice ((homology_sphere_aux R n).2 hn)

/-- `H₀(Sⁿ) ≅ R` for `n ≥ 1` -/
def H0_sphere_iso (n : ℕ) (hn : n ≠ 0) : H R (SphU.{u} n) 0 ≅ R :=
  match n, hn with
  | m + 1, _ => H0_sphere_succ_iso R m

theorem isZero_Hred₀_sphere (n : ℕ) (hn : n ≠ 0) : IsZero (Hred₀ R (SphU.{u} n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact isZero_Hred₀_sphere_succ R m

/-- **The homology of spheres.** For `Sⁿ = Metric.sphere (0 : ℝ^(n+1)) 1` (lifted to universe
`u`) and any coefficient object `R`:
`H_n(Sⁿ) ≅ R` for `n ≥ 1`, `H_k(Sⁿ) = 0` for `k ∉ {0, n}`, `H₀(Sⁿ) ≅ R` for `n ≥ 1`,
`H̃₀(S⁰) ≅ R`, `H₀(S⁰) ≅ R ⊞ R` and `H̃₀(Sⁿ) = 0` for `n ≥ 1`. -/
theorem homology_sphere (n k : ℕ) :
    (k = n → n ≠ 0 → Nonempty (H R (SphU.{u} n) k ≅ R)) ∧
      (k ≠ n → k ≠ 0 → IsZero (H R (SphU.{u} n) k)) ∧
      (n ≠ 0 → Nonempty (H R (SphU.{u} n) 0 ≅ R)) ∧
      (n = 0 → Nonempty (Hred₀ R (SphU.{u} 0) ≅ R)) ∧
      (n = 0 → Nonempty (H R (SphU.{u} 0) 0 ≅ R ⊞ R)) ∧
      (n ≠ 0 → IsZero (Hred₀ R (SphU.{u} n))) :=
  ⟨fun hk hn => by subst hk; exact ⟨H_sphere_self_iso R k hn⟩, isZero_H_sphere R n k,
    fun hn => ⟨H0_sphere_iso R n hn⟩, fun _ => ⟨Hred₀_sphere_zero R⟩, fun _ => ⟨H0_sphere_zero R⟩,
    isZero_Hred₀_sphere R n⟩

/-! ### Spaces homotopy equivalent to a sphere -/

/-- a space `M : Type u` homotopy equivalent to `Sⁿ` has the homology of `SphU n` -/
def homologyIsoSphere {M : Type u} [TopologicalSpace M] {n : ℕ} (e : M ≃ₕ Sph n) (k : ℕ) :
    H R (TopCat.of M) k ≅ H R (SphU.{u} n) k :=
  homologyIso R (e.trans Homeomorph.ulift.symm.toHomotopyEquiv) k

/-- reduced version of `homologyIsoSphere` -/
def Hred₀IsoSphere {M : Type u} [TopologicalSpace M] {n : ℕ} (e : M ≃ₕ Sph n) :
    Hred₀ R (TopCat.of M) ≅ Hred₀ R (SphU.{u} n) :=
  Hred₀Iso R (e.trans Homeomorph.ulift.symm.toHomotopyEquiv)

theorem isZero_H_of_homotopyEquiv_sphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ Sph n) (k : ℕ) (hk : k ≠ n) (hk0 : k ≠ 0) : IsZero (H R (TopCat.of M) k) :=
  (isZero_H_sphere R n k hk hk0).of_iso (homologyIsoSphere R e k)

/-- `H_n(M) ≅ R` for `M ≃ₕ Sⁿ`, `n ≥ 1` -/
def H_self_iso_of_homotopyEquiv_sphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ Sph n) (hn : n ≠ 0) : H R (TopCat.of M) n ≅ R :=
  homologyIsoSphere R e n ≪≫ H_sphere_self_iso R n hn

/-- `H₀(M) ≅ R` for `M ≃ₕ Sⁿ`, `n ≥ 1` -/
def H0_iso_of_homotopyEquiv_sphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ Sph n) (hn : n ≠ 0) : H R (TopCat.of M) 0 ≅ R :=
  homologyIsoSphere R e 0 ≪≫ H0_sphere_iso R n hn

theorem isZero_Hred₀_of_homotopyEquiv_sphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ Sph n) (hn : n ≠ 0) : IsZero (Hred₀ R (TopCat.of M)) :=
  (isZero_Hred₀_sphere R n hn).of_iso (Hred₀IsoSphere R e)

/-- `H̃₀(M) ≅ R` for `M ≃ₕ S⁰` -/
def Hred₀_iso_of_homotopyEquiv_sphere_zero {M : Type u} [TopologicalSpace M]
    (e : M ≃ₕ Sph 0) : Hred₀ R (TopCat.of M) ≅ R :=
  Hred₀IsoSphere R e ≪≫ Hred₀_sphere_zero R

/-- `H₀(M) ≅ R ⊞ R` for `M ≃ₕ S⁰` -/
def H0_iso_of_homotopyEquiv_sphere_zero {M : Type u} [TopologicalSpace M]
    (e : M ≃ₕ Sph 0) : H R (TopCat.of M) 0 ≅ R ⊞ R :=
  homologyIsoSphere R e 0 ≪≫ H0_sphere_zero R

/-! ### The project's sphere type itself (universe `0`) -/

section univZero

variable (R₀ : ModuleCat.{0} ℤ)

/-- `H_k(Sph n) ≅ H_k(SphU n)` in universe `0` -/
def HSphIso (n k : ℕ) : H R₀ (TopCat.of (Sph n)) k ≅ H R₀ (SphU.{0} n) k :=
  homologyIsoSphere R₀ (ContinuousMap.HomotopyEquiv.refl (Sph n)) k

theorem isZero_H_Sph (n k : ℕ) (hk : k ≠ n) (hk0 : k ≠ 0) :
    IsZero (H R₀ (TopCat.of (Sph n)) k) :=
  isZero_H_of_homotopyEquiv_sphere R₀ (ContinuousMap.HomotopyEquiv.refl (Sph n)) k hk hk0

/-- `H_n(Sph n) ≅ R` for `n ≥ 1` -/
def H_Sph_self_iso (n : ℕ) (hn : n ≠ 0) : H R₀ (TopCat.of (Sph n)) n ≅ R₀ :=
  H_self_iso_of_homotopyEquiv_sphere R₀ (ContinuousMap.HomotopyEquiv.refl (Sph n)) hn

/-- `H₀(Sph n) ≅ R` for `n ≥ 1` -/
def H0_Sph_iso (n : ℕ) (hn : n ≠ 0) : H R₀ (TopCat.of (Sph n)) 0 ≅ R₀ :=
  H0_iso_of_homotopyEquiv_sphere R₀ (ContinuousMap.HomotopyEquiv.refl (Sph n)) hn

theorem isZero_Hred₀_Sph (n : ℕ) (hn : n ≠ 0) : IsZero (Hred₀ R₀ (TopCat.of (Sph n))) :=
  isZero_Hred₀_of_homotopyEquiv_sphere R₀ (ContinuousMap.HomotopyEquiv.refl (Sph n)) hn

/-- `H̃₀(Sph 0) ≅ R` -/
def Hred₀_Sph_zero : Hred₀ R₀ (TopCat.of (Sph 0)) ≅ R₀ :=
  Hred₀_iso_of_homotopyEquiv_sphere_zero R₀ (ContinuousMap.HomotopyEquiv.refl (Sph 0))

/-- `H₀(Sph 0) ≅ R ⊞ R` -/
def H0_Sph_zero : H R₀ (TopCat.of (Sph 0)) 0 ≅ R₀ ⊞ R₀ :=
  H0_iso_of_homotopyEquiv_sphere_zero R₀ (ContinuousMap.HomotopyEquiv.refl (Sph 0))

/-- `H_n(Sⁿ; ℤ) ≅ ℤ` for `n ≥ 1`, with the default integral coefficients -/
def H_Sph_self_iso_Z (n : ℕ) (hn : n ≠ 0) : H Z (TopCat.of (Sph n)) n ≅ Z :=
  H_Sph_self_iso Z n hn

end univZero

end Sphere

end PoincareHighDim.SingularPair
