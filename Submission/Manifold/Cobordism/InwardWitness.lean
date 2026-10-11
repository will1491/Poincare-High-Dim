/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.EmbeddedNormalChart
import Submission.Manifold.Cobordism.HalfSpaceThickening

/-! # The embedded inward ray accumulates on the positive side of a normal chart -/

namespace PoincareHighDim
namespace EmbeddedNormalChart

open Set Topology Filter
open scoped Manifold ContDiff

variable {n : ℕ} {W M F H : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {J : ModelWithCorners ℝ F H} [J.Boundaryless] [IsManifold J ∞ M]
    {f : W → M} {b : (𝓡∂ (n + 1)).boundary W}

omit [J.Boundaryless] [IsManifold J ∞ M] in
/-- The original inward coordinate ray gives embedded points on the positive side,
arbitrarily close to the boundary point. -/
theorem mem_closure_positive (C : EmbeddedNormalChart (J := J) f b)
    (hf : Continuous f) :
    f b.1 ∈ closure {y | y ∈ range f ∧ 0 < (C.chart.symm y).2} := by
  let c : ℝ → ((Fin n → ℝ) × ℝ) := fun t ↦ (boundaryCoordinateCenter b, t)
  let σ : ℝ → W := fun t ↦ (extChartAt (𝓡∂ (n + 1)) b.1).symm
    (halfSpaceCoordinateEquiv n (c t))
  let γ : ℝ → M := fun t ↦ f (σ t)
  have hc : halfSpaceCoordinateEquiv n (c 0) =
      extChartAt (𝓡∂ (n + 1)) b.1 b.1 := halfSpaceCoordinateEquiv_center b
  have hσ0 : σ 0 = b.1 := by
    change (extChartAt (𝓡∂ (n + 1)) b.1).symm (halfSpaceCoordinateEquiv n (c 0)) = _
    rw [hc, (extChartAt (𝓡∂ (n + 1)) b.1).left_inv (mem_extChartAt_source b.1)]
  have hσ : ContinuousAt σ 0 := by
    apply ContinuousAt.comp (f := fun t ↦ halfSpaceCoordinateEquiv n (c t))
    · rw [hc]
      exact continuousAt_extChartAt_symm b.1
    · exact ((halfSpaceCoordinateEquiv n).continuous.comp
        (continuous_const.prodMk continuous_id)).continuousAt
  have hγ : Tendsto γ (𝓝 0) (𝓝 (f b.1)) := by
    change Tendsto (f ∘ σ) (𝓝 0) (𝓝 (f b.1))
    have h := hf.continuousAt.comp hσ
    simpa only [ContinuousAt, Function.comp_apply, hσ0] using h
  have he : C.coordinateChart (boundaryCoordinateCenter b, 0) =
      embeddedBoundaryExpression (J := J) f b (boundaryCoordinateCenter b, 0) := by
    rw [C.coordinate_eq _ C.coordinate_center_mem]
    simp only [show ((0 : Fin n → ℝ), (0 : ℝ)) = 0 from rfl, map_zero, add_zero]
  have hpos := HalfSpaceThickening.eventually_inward_normalCoordinate_pos C.derivative
    C.hasFDerivWithinAt C.coordinateChart.toOpenPartialHomeomorph C.coordinate_center_mem he
    C.hasFDerivAt_coordinateChart
  apply mem_closure_of_tendsto (b := 𝓝[>] (0 : ℝ))
    (hγ.mono_left nhdsWithin_le_nhds)
  filter_upwards [hpos] with t ht
  refine ⟨mem_range_self (σ t), ?_⟩
  rw [C.chart_symm_eq]
  exact ht

end EmbeddedNormalChart
end PoincareHighDim
