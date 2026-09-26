import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Smooth
import Submission.Morse.CriticalFinite
import Submission.Morse.MonotoneShift
import Submission.Morse.DistinctValues
import Submission.Morse.ModelField
import Submission.Morse.GradientLike
import Submission.Morse.StripFlow
import Submission.Morse.TrajectoryCutoff
import Submission.Morse.Rearrange
import Submission.Morse.Transversality
import Submission.Morse.Swap
import Submission.Morse.NegDual
import Submission.Morse.DistinctSelfIndexing
import Submission.Morse.Terminal
import Submission.Morse.StripConnected
import Submission.Morse.EqualIndexPosition
import Submission.Morse.Bridge
import Submission.Morse.Isolate
import Submission.Morse.CancelPair
import Submission.Homology.SingularPair
import Submission.Homology.Naturality
import Submission.Homology.SingularSubcomplex
import Submission.Homology.MVShortExact
import Submission.Homology.AffineChains
import Submission.Homology.Subdivision
import Submission.Homology.DiameterBound
import Submission.Homology.SmallSimplices
import Submission.Homology.MayerVietoris
import Submission.Homology.Excision
import Submission.Homology.SphereTopology
import Submission.Homology.SphereHomology
import Submission.Homology.Support
import Submission.Homology.Radial
import Submission.Homology.DeltaIso
import Submission.Homology.RelativeMV
import Submission.Homology.RelativeMVOpen
import Submission.Homology.LocalHomology
import Submission.Homology.LocalGood
import Submission.Homology.LocalGoodUnion
import Submission.Homology.CompactEuclidean
import Submission.Homology.ChartTransport
import Submission.Homology.PointRestriction
import Submission.Homology.Injectivity
import Submission.Homology.Noncompact
import Submission.Homology.ChartDiskRetract
import Submission.Homology.RelHomotopy
import Submission.Homology.DiskExcision
import Submission.Homology.PuncturedAcyclic
import Submission.Homology.Bockstein
import Submission.Homology.FundamentalClass
import Submission.Homology.DiskComplement
import Submission.Homology.CompactZero
import Submission.Homology.PairVanishing

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
