/-
Copyright 2026 The DifferentialGeometry contributors.
Modifications copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The DifferentialGeometry contributors; Will (Ziang) Li (local modifications)
-/

/-
Vendored from https://github.com/qinz1yang/differential-geometry
(commit 4fbccdfc73f986ce59d7bb66e8bb078f8007ffe2, Apache License 2.0; see Submission/DifferentialGeometry/LICENSE),
with the statements generalised from analytic to smooth atlases and from `Type` to `Type*`
and module paths prefixed by `Submission.`.
-/
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

namespace DifferentialGeometry.Analysis.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem time_dependent_vf_pointwise_local_flow
    (X : ℝ → ∀ x : M, TangentSpace I x) (x₀ : M)
    (hCont :
      ContinuousOn (Function.uncurry (fun t x => X t x)) (Set.univ : Set (ℝ × M)))
    (hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H x₀).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H x₀) x₀)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ r' : ℝ, 0 < r' ∧
      ∃ flow : E → ℝ → E,
        (∀ y ∈ Metric.closedBall (I ((chartAt H x₀) x₀)) r',
          flow y 0 = y ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            HasDerivWithinAt (flow y)
              ((X t ((chartAt H x₀).symm (I.symm (flow y t)))) : E)
              (Set.Icc (0 : ℝ) T) t) := by
  obtain ⟨T, hT_pos, r', hr'_pos, flow, hflow⟩ :=
    time_dependent_vf_chart_local_picard_with_lipschitz X x₀ hCont hLip
  exact ⟨T, hT_pos, r', hr'_pos, flow, hflow⟩

end DifferentialGeometry.Analysis.ODE
