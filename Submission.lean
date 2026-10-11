/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Smooth

/-!
# The generalized Poincaré conjecture in dimensions `≥ 5`

`Submission.poincare_high_dim_topological` is the benchmark statement (the `proof_wanted`
`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` of
`Mathlib.Geometry.Manifold.PoincareConjecture` restricted to `n ≥ 5`).  It is derived from
the smooth theorem `PoincareHighDim.poincare_smooth` (Smale's h-cobordism route, developed in
the modules under `Submission/`) and the proved compactness and smoothability theorems
`PoincareHighDim.compactSpace_of_homotopyEquiv_sphere` and
`PoincareHighDim.exists_smooth_structure_of_homotopyEquiv_sphere`.
-/

open Metric (sphere)
open ContinuousMap

namespace Submission

/-- **The generalized Poincaré conjecture, `n ≥ 5`** (Smale for smooth manifolds; Newman and
Connell in general). -/
theorem poincare_high_dim_topological {n : ℕ} (_h5 : 5 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (_h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have : CompactSpace M := PoincareHighDim.compactSpace_of_homotopyEquiv_sphere _h
  obtain ⟨cs, hcs⟩ := PoincareHighDim.exists_smooth_structure_of_homotopyEquiv_sphere _h5 _h
  exact @PoincareHighDim.poincare_smooth n _h5 M _ _ _ cs hcs _h

end Submission
