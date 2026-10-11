/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.ModelTransport
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Standard Euclidean charts on a product with the real line

Postcomposing every chart with a continuous linear equivalence changes the chart model
without changing the topology or smooth structure. In particular, a smooth `n`-manifold
times the real line has a smooth atlas modeled on `EuclideanSpace ℝ (Fin (n + 1))`.
-/

namespace PoincareHighDim

open Set Function
open scoped Manifold ContDiff

noncomputable section

section LinearRechart

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Postcompose the atlas by a linear change of Euclidean model. -/
@[instance_reducible]
def linearRechart (L : E ≃L[ℝ] F) : ChartedSpace F M where
  atlas := (fun e : OpenPartialHomeomorph M E =>
    e.trans L.toHomeomorph.toOpenPartialHomeomorph) '' atlas E M
  chartAt x := (chartAt E x).trans L.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt E x, chart_mem_atlas E x, rfl⟩

theorem linearRechart_extChartAt (L : E ≃L[ℝ] F) (x : M) :
    (letI := linearRechart (M := M) L; ⇑(extChartAt 𝓘(ℝ, F) x)) =
      L ∘ extChartAt 𝓘(ℝ, E) x := rfl

theorem linearRechart_extChartAt_symm (L : E ≃L[ℝ] F) (x : M) :
    (letI := linearRechart (M := M) L; ⇑(extChartAt 𝓘(ℝ, F) x).symm) =
      (extChartAt 𝓘(ℝ, E) x).symm ∘ L.symm := rfl

theorem linearRechart_extChartAt_target (L : E ≃L[ℝ] F) (x : M) :
    (letI := linearRechart (M := M) L; (extChartAt 𝓘(ℝ, F) x).target) =
      L '' (extChartAt 𝓘(ℝ, E) x).target := by
  change (univ ∩ (fun y : F => y) ⁻¹' (univ ∩ L.symm ⁻¹' (chartAt E x).target)) =
    L '' (univ ∩ (fun y : E => y) ⁻¹' (chartAt E x).target)
  simp only [univ_inter, ContinuousLinearEquiv.image_eq_preimage_symm]
  rfl

/-- Linear changes of the chart model preserve manifold regularity. -/
theorem linearRechart_isManifold (L : E ≃L[ℝ] F) (r : ℕ∞ω)
    [IsManifold 𝓘(ℝ, E) r M] :
    letI := linearRechart (M := M) L
    IsManifold 𝓘(ℝ, F) r M := by
  let := linearRechart (M := M) L
  refine isManifold_of_contDiffOn 𝓘(ℝ, F) r M ?_
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  have h := ((contDiffGroupoid r 𝓘(ℝ, E)).compatible he he').1
  refine L.contDiff.comp_contDiffOn (h.comp L.symm.contDiff.contDiffOn ?_)
  simp [mapsTo_iff_subset_preimage, mfld_simps]
  exact fun _ hx => hx.2

/-- The identity is a diffeomorphism between the original atlas and its linear recharting. -/
def linearRechartDiffeomorph (L : E ≃L[ℝ] F) (r : ℕ∞ω) :
    letI := linearRechart (M := M) L
    M ≃ₘ^r⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ M := by
  let := linearRechart (M := M) L
  refine { toEquiv := Equiv.refl M, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine L.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Equiv.coe_refl, id, Function.comp_def, linearRechart_extChartAt,
        Function.comp_apply, (extChartAt 𝓘(ℝ, E) x).right_inv hy.1]
    · exact ⟨(extChartAt 𝓘(ℝ, E) x).map_source (mem_extChartAt_source x), trivial,
        by simp only [mfld_simps]⟩
  · intro x
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine L.symm.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [mem_inter_iff, linearRechart_extChartAt_target,
        ContinuousLinearEquiv.image_eq_preimage_symm, mem_preimage] at hy
      simp only [Equiv.coe_refl, Equiv.refl_symm, id, Function.comp_def,
        linearRechart_extChartAt_symm, Function.comp_apply,
        (extChartAt 𝓘(ℝ, E) x).right_inv hy.1]
    · exact ⟨(extChartAt 𝓘(ℝ, F) x).map_source (mem_extChartAt_source x), trivial,
        by simp only [mfld_simps]⟩

@[simp]
theorem linearRechartDiffeomorph_apply (L : E ≃L[ℝ] F) (r : ℕ∞ω) (x : M) :
    letI := linearRechart (M := M) L
    linearRechartDiffeomorph (M := M) L r x = x := rfl

@[simp]
theorem linearRechartDiffeomorph_symm_apply (L : E ≃L[ℝ] F) (r : ℕ∞ω) (x : M) :
    letI := linearRechart (M := M) L
    (linearRechartDiffeomorph (M := M) L r).symm x = x := rfl

/-- Scalar-valued smoothness is unchanged by a linear recharting. -/
theorem contMDiff_linearRechart_iff (L : E ≃L[ℝ] F) (r : ℕ∞ω)
    [IsManifold 𝓘(ℝ, E) r M] {f : M → ℝ} :
    (letI := linearRechart (M := M) L; ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) r f) ↔
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) r f := by
  let := linearRechart (M := M) L
  have := linearRechart_isManifold (M := M) L r
  let Φ := linearRechartDiffeomorph (M := M) L r
  constructor
  · intro h
    exact h.comp Φ.contMDiff
  · intro h
    exact h.comp Φ.symm.contMDiff

/-- Scalar critical points are unchanged by a linear recharting. -/
theorem isCriticalPt_linearRechart_iff (L : E ≃L[ℝ] F)
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (letI := linearRechart (M := M) L; IsCriticalPt 𝓘(ℝ, F) f x) ↔
      IsCriticalPt 𝓘(ℝ, E) f x := by
  let := linearRechart (M := M) L
  have := linearRechart_isManifold (M := M) L ∞
  let Φ := linearRechartDiffeomorph (M := M) L ∞
  have hf' : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f :=
    (contMDiff_linearRechart_iff L ∞).2 hf
  have h1 : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f x =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) Φ.symm x) :=
    mfderiv_comp (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, ℝ)) x
      (f := Φ.symm) (g := f) (hf.mdifferentiableAt (by simp))
      (Φ.symm.contMDiff.mdifferentiableAt (by simp))
  have h2 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x =
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ x) :=
    mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, ℝ)) x
      (f := Φ) (g := f) (hf'.mdifferentiableAt (by simp))
      (Φ.contMDiff.mdifferentiableAt (by simp))
  unfold IsCriticalPt
  constructor
  · intro h
    rw [h2, h]
    exact ContinuousLinearMap.zero_comp _
  · intro h
    rw [h1, h]
    exact ContinuousLinearMap.zero_comp _

end LinearRechart

/-- A continuous linear equivalence identifying the model of a product with the real line
with the standard Euclidean space of one higher dimension. -/
def productModelEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  Classical.choice (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by
    simp [Module.finrank_prod]))

/-- The standard-dimensional atlas on a product with the real line. This is a definition rather
than a global instance, so callers can choose exactly when to install the transported atlas. -/
@[instance_reducible]
def productChartedSpace (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (M × ℝ) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (M × ℝ) :=
    inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) ℝ) (M × ℝ))
  exact linearRechart (M := M × ℝ) (productModelEquiv n)

section Product

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The transported product atlas is smooth over `𝓡 (n + 1)`. -/
theorem product_isManifold :
    letI := productChartedSpace n M
    IsManifold (𝓡 (n + 1)) ∞ (M × ℝ) := by
  have hprod : IsManifold ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (M × ℝ) := inferInstance
  let : ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (M × ℝ) :=
    inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) ℝ) (M × ℝ))
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact hprod
  exact linearRechart_isManifold (M := M × ℝ) (productModelEquiv n) ∞

/-- Smooth scalar functions on the product remain smooth for the standard-dimensional atlas. -/
theorem contMDiff_productChartedSpace_iff {f : M × ℝ → ℝ} :
    (letI := productChartedSpace n M; ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f) ↔
      ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f := by
  have hprod : IsManifold ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (M × ℝ) := inferInstance
  let : ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (M × ℝ) :=
    inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) ℝ) (M × ℝ))
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact hprod
  have h := contMDiff_linearRechart_iff (M := M × ℝ) (f := f) (productModelEquiv n) ∞
  rwa [modelWithCornersSelf_prod] at h

/-- Critical points agree for the product atlas and its standard-dimensional recharting. -/
theorem isCriticalPt_productChartedSpace_iff {f : M × ℝ → ℝ}
    (hf : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f) (x : M × ℝ) :
    (letI := productChartedSpace n M; IsCriticalPt (𝓡 (n + 1)) f x) ↔
      IsCriticalPt ((𝓡 n).prod 𝓘(ℝ, ℝ)) f x := by
  have hprod : IsManifold ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (M × ℝ) := inferInstance
  let : ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (M × ℝ) :=
    inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) ℝ) (M × ℝ))
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact hprod
  have hf' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) 𝓘(ℝ, ℝ) ∞ f := by
    rwa [modelWithCornersSelf_prod]
  have h := isCriticalPt_linearRechart_iff (M := M × ℝ) (productModelEquiv n) hf' x
  rwa [modelWithCornersSelf_prod] at h

end Product

end

end PoincareHighDim
