import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Smooth
import Submission.Morse.Foundations.CriticalFinite
import Submission.Morse.Rearrangement.MonotoneShift
import Submission.Morse.Rearrangement.DistinctValues
import Submission.Morse.Foundations.ModelField
import Submission.Morse.Foundations.GradientLike
import Submission.Morse.Strips.StripFlow
import Submission.Morse.Strips.TrajectoryCutoff
import Submission.Morse.Rearrangement.Rearrange
import Submission.Morse.Rearrangement.Transversality
import Submission.Morse.Rearrangement.Swap
import Submission.Morse.Rearrangement.NegDual
import Submission.Morse.Rearrangement.DistinctSelfIndexing
import Submission.Morse.Strips.Terminal
import Submission.Morse.Strips.StripConnected
import Submission.Morse.Rearrangement.EqualIndexPosition
import Submission.Morse.Cancellation.Setup.Bridge
import Submission.Morse.Cancellation.Setup.Isolate
import Submission.Morse.Cancellation.CancelPair
import Submission.Homology.SingularPair
import Submission.Homology.Naturality
import Submission.Homology.SingularSubcomplex
import Submission.Homology.MayerVietoris.MVShortExact
import Submission.Homology.Subdivision.AffineChains
import Submission.Homology.Subdivision.Subdivision
import Submission.Homology.Subdivision.DiameterBound
import Submission.Homology.Subdivision.SmallSimplices
import Submission.Homology.MayerVietoris.MayerVietoris
import Submission.Homology.Relative.Excision
import Submission.Homology.Spheres.SphereTopology
import Submission.Homology.Spheres.SphereHomology
import Submission.Homology.Support
import Submission.Homology.Local.Radial
import Submission.Homology.Relative.DeltaIso
import Submission.Homology.MayerVietoris.RelativeMV
import Submission.Homology.MayerVietoris.RelativeMVOpen
import Submission.Homology.Local.LocalHomology
import Submission.Homology.Local.LocalGood
import Submission.Homology.Local.LocalGoodUnion
import Submission.Homology.Local.CompactEuclidean
import Submission.Homology.Local.ChartTransport
import Submission.Homology.Local.PointRestriction
import Submission.Homology.Local.Injectivity
import Submission.Homology.Local.Noncompact
import Submission.Homology.Punctures.ChartDiskRetract
import Submission.Homology.Relative.RelHomotopy
import Submission.Homology.Punctures.DiskExcision
import Submission.Homology.Punctures.PuncturedAcyclic
import Submission.Homology.Bockstein
import Submission.Homology.Punctures.FundamentalClass
import Submission.Homology.Punctures.DiskComplement
import Submission.Homology.Spheres.CompactZero
import Submission.Homology.Relative.PairVanishing

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
