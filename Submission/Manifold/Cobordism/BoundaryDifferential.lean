/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.BoundaryFunction
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Tangent spaces and conormals of the induced boundary

The ambient extension of boundary coordinates is a local left inverse of the boundary
inclusion. Its derivative proves injectivity of the inclusion's derivative. A function
vanishing on the boundary has differential annihilating its tangent space.
-/

namespace PoincareHighDim

open Set Topology
open scoped Manifold ContDiff

variable {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- The differential of the induced boundary inclusion is injective. -/
theorem boundary_inclusion_mfderiv_injective (b : (𝓡∂ (n + 1)).boundary W) :
    let := boundaryChartedSpace (n := n) (W := W)
    Function.Injective (mfderiv 𝓘(ℝ, Fin n → ℝ) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary W → W) b) := by
  let := boundaryChartedSpace (n := n) (W := W)
  let := boundary_isManifold (n := n) (W := W)
  let inc : (𝓡∂ (n + 1)).boundary W → W := Subtype.val
  have hloc : (boundaryChartExtension b ∘ inc) =ᶠ[𝓝 b]
      (extChartAt 𝓘(ℝ, Fin n → ℝ) b) := by
    filter_upwards [(boundaryChartAt b).open_source.mem_nhds (mem_boundaryChartAt_source b)]
      with y hy
    change boundaryChartExtension b y.1 = boundaryChartAt b y
    exact (boundaryChartAt_apply b y (by simpa using hy)).symm
  have hbase := (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, Fin n → ℝ))
    (mem_chart_source (Fin n → ℝ) b)).hasMFDerivAt
  rw [mfderiv_extChartAt_self] at hbase
  have hleft := (hbase.congr_of_eventuallyEq_abuse hloc).mfderiv
  have hext := (contMDiffOn_boundaryChartExtension b).contMDiffAt
    ((chartAt (EuclideanHalfSpace (n + 1)) b.1).open_source.mem_nhds (mem_chart_source _ _))
  rw [mfderiv_comp b (hext.mdifferentiableAt (by simp))
    (contMDiff_boundary_subtypeVal.mdifferentiable (by simp) b)] at hleft
  have hli : Function.LeftInverse
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, Fin n → ℝ) (boundaryChartExtension b) b.1)
      (mfderiv 𝓘(ℝ, Fin n → ℝ) (𝓡∂ (n + 1)) inc b) := by
    intro v
    exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L v) hleft
  exact hli.injective

/-- A smooth function constant on the boundary annihilates all boundary tangent vectors. -/
theorem boundary_conormal_annihilates {h : W → ℝ}
    (hh : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ h)
    (hzero : ∀ b : (𝓡∂ (n + 1)).boundary W, h b.1 = 0)
    (b : (𝓡∂ (n + 1)).boundary W) :
    let := boundaryChartedSpace (n := n) (W := W)
    (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) h b.1).comp
      (mfderiv 𝓘(ℝ, Fin n → ℝ) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary W → W) b) = 0 := by
  let := boundaryChartedSpace (n := n) (W := W)
  let := boundary_isManifold (n := n) (W := W)
  have hc : h ∘ (Subtype.val : (𝓡∂ (n + 1)).boundary W → W) = fun _ => (0 : ℝ) :=
    funext hzero
  have hchain := mfderiv_comp b (hh.mdifferentiable (by simp) b.1)
    (contMDiff_boundary_subtypeVal.mdifferentiable (by simp) b)
  have hz := mfderiv_congr (I := 𝓘(ℝ, Fin n → ℝ)) (I' := 𝓘(ℝ, ℝ)) (x := b) hc
  rw [mfderiv_const] at hz
  exact hchain.symm.trans hz

/-- In any fixed ambient chart, the coordinate expression of a smooth scalar function is
smooth on the chart target, including its boundary. -/
theorem contDiffOn_boundary_function_chart {h : W → ℝ}
    (hh : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ h) (c : W) :
    ContDiffOn ℝ ∞ (h ∘ (extChartAt (𝓡∂ (n + 1)) c).symm)
      (extChartAt (𝓡∂ (n + 1)) c).target := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact hh.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)

/-- The conormal's coefficients in a fixed chart vary smoothly up to the boundary. -/
theorem contDiffOn_boundary_conormal_chart {h : W → ℝ}
    (hh : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ h) (c : W) :
    ContDiffOn ℝ ∞
      (fderivWithin ℝ (h ∘ (extChartAt (𝓡∂ (n + 1)) c).symm)
        (extChartAt (𝓡∂ (n + 1)) c).target)
      (extChartAt (𝓡∂ (n + 1)) c).target :=
  (contDiffOn_boundary_function_chart hh c).fderivWithin
    (uniqueDiffOn_extChartAt_target c) (by simp)

end PoincareHighDim
