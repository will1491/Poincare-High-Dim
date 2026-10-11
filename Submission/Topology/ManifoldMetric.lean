/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity

/-! A compact Hausdorff Euclidean-charted space admits a compatible metric. -/

namespace PoincareHighDim

open TopologicalSpace

/-- Compactness supplies a finite, hence countable, chart cover; the usual
metrization theorem then supplies a metric with the original topology. -/
theorem metrizableSpace_of_compact_charted {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : MetrizableSpace M := by
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  infer_instance

end PoincareHighDim
