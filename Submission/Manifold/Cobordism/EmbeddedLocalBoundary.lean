/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.LocalBoundaryAssembly
import Submission.Manifold.Cobordism.EmbeddedBoundaryGerm
import Submission.Manifold.Cobordism.InwardWitness
import Submission.Manifold.Cobordism.WitnessTransport

/-! # Local defining functions for the actual embedded cobordism -/

namespace PoincareHighDim

open Set Topology
open scoped Manifold ContDiff

variable {n : ℕ} {W M F H : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W] [CompactSpace W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {J : ModelWithCorners ℝ F H} [J.Boundaryless] [IsManifold J ∞ M]

/-- Every full-rank smooth embedding of a compact manifold with boundary into a
boundaryless manifold admits genuine local signed defining functions. -/
theorem nonempty_localBoundaryFunction_of_embedding (f : W → M)
    (hemb : IsEmbedding f) (hf : ContMDiff (𝓡∂ (n + 1)) J ∞ f)
    (hD : ∀ x, (mfderiv (𝓡∂ (n + 1)) J f x).IsInvertible)
    (b : (𝓡∂ (n + 1)).boundary W) :
    Nonempty (StripFunction.LocalBoundaryFunction J (range f)
      (f '' (𝓡∂ (n + 1)).boundary W) (f b.1)) := by
  obtain ⟨C⟩ := nonempty_embeddedNormalChart f b hf (hD b.1)
  apply StripFunction.LocalBoundaryFunction.nonempty_of_normal_germs
    C.chart C.center_mem C.chart_center (isCompact_range hemb.continuous).isClosed
    (image_subset_range _ _) (frontier_range_subset_image_boundary hf hD)
    (C.eventually_mem_image_boundary_iff_normal_zero hemb)
    (C.mem_closure_positive hf.continuous)
  simpa only [C.chart_center] using WitnessTransport.mem_closure_normalChart_outside b hemb C

end PoincareHighDim
