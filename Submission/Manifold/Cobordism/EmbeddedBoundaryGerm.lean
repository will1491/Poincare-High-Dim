/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.EmbeddedNormalChart
import Submission.Manifold.Cobordism.BoundaryGerm

/-! # The embedded boundary is the zero slice of its normal chart -/

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
/-- The topology of the actual embedding rules out any other boundary branch near the
normal chart's center, so the embedded boundary is exactly its zero slice there. -/
theorem eventually_mem_image_boundary_iff_normal_zero
    (C : EmbeddedNormalChart (J := J) f b) (hemb : IsEmbedding f) :
    ∀ᶠ y in 𝓝 (f b.1),
      y ∈ f '' (𝓡∂ (n + 1)).boundary W ↔ (C.chart.symm y).2 = 0 := by
  let e : (𝓡∂ (n + 1)).boundary W → M := fun z ↦ f z.1
  have he : IsEmbedding e := hemb.comp IsEmbedding.subtypeVal
  have hcenter : (boundaryChartAt b b, (0 : ℝ)) ∈ C.chart.source := by
    rw [boundaryChartAt_eq_boundaryCoordinateCenter]
    exact C.center_mem
  have h := BoundaryGerm.eventually_mem_range_iff_normal_zero he
    (boundaryChartAt b) (mem_boundaryChartAt_source b)
    C.chart.toOpenPartialHomeomorph hcenter C.zero_section
  have hrange : range e = f '' (𝓡∂ (n + 1)).boundary W := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  filter_upwards [h] with y hy
  have hy' : y ∈ range e ↔ (C.chart.symm y).2 = 0 := hy.2
  rwa [hrange] at hy'

end EmbeddedNormalChart
end PoincareHighDim
