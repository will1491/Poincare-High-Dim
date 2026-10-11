/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.BoundaryAtlas
import Submission.Manifold.RegularLevel.SmoothAtlas

/-!
# Smoothness of the induced boundary atlas

Boundary chart transitions are restrictions of the smooth ambient chart transitions.
The coordinate projections extend smoothly into the ambient manifold, and each
inverse chart is the ambient inverse chart composed with the zero-normal inclusion.
-/

namespace PoincareHighDim

open Set Topology WithLp
open scoped Manifold ContDiff

theorem contMDiff_boundaryHalfSpaceInclusion (n : ℕ) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓡∂ (n + 1)) ∞ (boundaryHalfSpaceInclusion n) := by
  rw [← contMDiffOn_univ]
  have h := (𝓡∂ (n + 1)).contMDiffOn_symm.comp
    (contDiff_boundaryCoordinateInclusion n).contMDiff.contMDiffOn
    (show MapsTo (boundaryCoordinateInclusion n) univ (range (𝓡∂ (n + 1))) from
      fun y _ => ⟨boundaryHalfSpaceInclusion n y, rfl⟩)
  simpa only [Function.comp_def, model_symm_boundaryCoordinateInclusion] using h

variable {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- The smooth ambient extension of boundary coordinates drops the chart's normal coordinate. -/
noncomputable def boundaryChartExtension (x : (𝓡∂ (n + 1)).boundary W) (y : W) (i : Fin n) : ℝ :=
  (chartAt (EuclideanHalfSpace (n + 1)) x.1 y).1 i.succ

theorem contMDiffOn_boundaryChartExtension (x : (𝓡∂ (n + 1)).boundary W) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Fin n → ℝ) ∞ (boundaryChartExtension x)
      (chartAt (EuclideanHalfSpace (n + 1)) x.1).source := by
  have hp : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      fun i : Fin n => y i.succ) := by
    apply contDiff_pi.mpr
    intro i
    exact (contDiff_apply ℝ ℝ i.succ).comp PiLp.contDiff_ofLp
  exact hp.contMDiff.comp_contMDiffOn
    ((chartAt (EuclideanHalfSpace (n + 1)) x.1).contMDiffOn_extend
      (IsManifold.chart_mem_maximalAtlas x.1))

theorem contMDiffOn_boundaryChartAt_symm (x : (𝓡∂ (n + 1)).boundary W) :
    ContMDiffOn 𝓘(ℝ, Fin n → ℝ) (𝓡∂ (n + 1)) ∞
      (fun y => ((boundaryChartAt x).symm y : W)) (boundaryChartAt x).target := by
  have h := (contMDiffOn_chart_symm (I := 𝓡∂ (n + 1)) (x := x.1)).comp
    (contMDiff_boundaryHalfSpaceInclusion n).contMDiffOn
    (show MapsTo (boundaryHalfSpaceInclusion n) (boundaryChartAt x).target
      (chartAt (EuclideanHalfSpace (n + 1)) x.1).target from fun y hy => by simpa using hy)
  exact h.congr (fun y hy => boundaryChartAt_symm_apply x hy)

/-- The induced boundary coordinates satisfy the smooth extension and inverse conditions. -/
noncomputable def boundaryInducedAtlas :
    InducedAtlas (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).boundary W) (Fin n → ℝ) where
  chart := boundaryChartAt
  mem_source := mem_boundaryChartAt_source
  ambientSource x := (chartAt (EuclideanHalfSpace (n + 1)) x.1).source
  open_ambientSource x := (chartAt (EuclideanHalfSpace (n + 1)) x.1).open_source
  source_eq := boundaryChartAt_source
  extension := boundaryChartExtension
  extension_eq x y hy := (boundaryChartAt_apply x y (by simpa using hy)).symm
  smooth_extension := contMDiffOn_boundaryChartExtension
  smooth_inverse := contMDiffOn_boundaryChartAt_symm

/-- The actual boundary of a smooth half-space manifold is a smooth boundaryless manifold
of one lower dimension, with the atlas induced by the original smooth structure. -/
theorem boundary_isManifold :
    letI := boundaryChartedSpace (n := n) (W := W)
    IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ ((𝓡∂ (n + 1)).boundary W) :=
  (boundaryInducedAtlas (n := n) (W := W)).isManifold

/-- The inclusion of the boundary is smooth for its induced atlas. -/
theorem contMDiff_boundary_subtypeVal :
    letI := boundaryChartedSpace (n := n) (W := W)
    ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓡∂ (n + 1)) ∞
      (Subtype.val : (𝓡∂ (n + 1)).boundary W → W) :=
  (boundaryInducedAtlas (n := n) (W := W)).contMDiff_subtypeVal

/-- A continuous map into the boundary is smooth exactly when its ambient map is smooth. -/
theorem contMDiff_into_boundary_iff
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (J : ModelWithCorners ℝ E H) [IsManifold J ∞ N]
    {f : N → (𝓡∂ (n + 1)).boundary W} :
    letI := boundaryChartedSpace (n := n) (W := W)
    ContMDiff J 𝓘(ℝ, Fin n → ℝ) ∞ f ↔
      Continuous f ∧ ContMDiff J (𝓡∂ (n + 1)) ∞ (fun x => (f x : W)) :=
  (boundaryInducedAtlas (n := n) (W := W)).contMDiff_iff J

end PoincareHighDim
