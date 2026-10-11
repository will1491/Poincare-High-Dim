/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Morse.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Changing the model vector space from `EuclideanSpace ℝ (Fin n)` to `Fin n → ℝ`

Mathlib's standard model for `n`-manifolds is `𝓡 n`, whose model vector space is
`EuclideanSpace ℝ (Fin n)` (with the `L²` norm), whereas the Morse theory of the
`DifferentialGeometry` dependency is stated for models whose vector space is `Fin n → ℝ`
(sup norm).  `morseModelI n` is `𝓡 n` transported along the continuous linear equivalence
`EuclideanSpace.equiv (Fin n) ℝ`; Mathlib provides the `IsManifold` instance for it, and the
lemmas below transport smoothness and critical points.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff

/-- The model `𝓡 n` with model vector space `Fin n → ℝ` instead of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable abbrev morseModelI (n : ℕ) :
    ModelWithCorners ℝ (Fin n → ℝ) (EuclideanSpace ℝ (Fin n)) :=
  (𝓡 n).transContinuousLinearEquiv (EuclideanSpace.equiv (Fin n) ℝ)

instance morseModelI_boundaryless (n : ℕ) : (morseModelI n).Boundaryless := by
  refine ⟨?_⟩
  rw [ModelWithCorners.transContinuousLinearEquiv_range,
    ModelWithCorners.Boundaryless.range_eq_univ, Set.image_univ, Set.range_eq_univ]
  exact (EuclideanSpace.equiv (Fin n) ℝ).surjective

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem contMDiff_morseModelI_iff [IsManifold (𝓡 n) ∞ M] {f : M → ℝ} :
    ContMDiff (morseModelI n) 𝓘(ℝ, ℝ) ∞ f ↔ ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f :=
  ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _

theorem isCriticalPt_morseModelI_iff [IsManifold (𝓡 n) ∞ M] {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {x : M} :
    IsCriticalPt (morseModelI n) f x ↔ IsCriticalPt (𝓡 n) f x := by
  -- The identity diffeomorphism between the two smooth structures.
  set Φ : M ≃ₘ^∞⟮𝓡 n, morseModelI n⟯ M :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv (𝓡 n) M (EuclideanSpace.equiv (Fin n) ℝ)
  have hf' : ContMDiff (morseModelI n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_morseModelI_iff.2 hf
  have hfI : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x := hf.mdifferentiableAt (by simp)
  have hfJ : MDifferentiableAt (morseModelI n) 𝓘(ℝ, ℝ) f x := hf'.mdifferentiableAt (by simp)
  have hΦd : MDifferentiableAt (𝓡 n) (morseModelI n) Φ x := Φ.contMDiff.mdifferentiableAt (by simp)
  have hΦsd : MDifferentiableAt (morseModelI n) (𝓡 n) Φ.symm x :=
    Φ.symm.contMDiff.mdifferentiableAt (by simp)
  -- Chain rule in both directions.
  have h1 : mfderiv (morseModelI n) 𝓘(ℝ, ℝ) f x
      = (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x).comp (mfderiv (morseModelI n) (𝓡 n) Φ.symm x) := by
    have := mfderiv_comp (I := morseModelI n) (I' := 𝓡 n) (I'' := 𝓘(ℝ, ℝ)) x
      (f := Φ.symm) (g := f) hfI hΦsd
    exact this
  have h2 : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x
      = (mfderiv (morseModelI n) 𝓘(ℝ, ℝ) f x).comp (mfderiv (𝓡 n) (morseModelI n) Φ x) := by
    have := mfderiv_comp (I := 𝓡 n) (I' := morseModelI n) (I'' := 𝓘(ℝ, ℝ)) x
      (f := Φ) (g := f) hfJ hΦd
    exact this
  unfold IsCriticalPt
  constructor
  · intro h
    rw [h2, h]
    exact ContinuousLinearMap.zero_comp _
  · intro h
    rw [h1, h]
    exact ContinuousLinearMap.zero_comp _

end PoincareHighDim
