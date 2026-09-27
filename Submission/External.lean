import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv
import Submission.Homology.Local.Noncompact
import Submission.Homology.Spheres.CompactZero
import Submission.SmoothFive
import Submission.Topology.Engulfing.NewmanTheorem
import Submission.Topology.Recognition.PoincareFromNewman

/-!
# Former external theorems

The compactness, smoothability, and five-dimensional smooth results are proved
here from the developments imported below.

* `compactSpace_of_homotopyEquiv_sphere`: a topological `n`-manifold homotopy equivalent to `Sⁿ`
  is compact.  **Now proved** (no longer external): for `n = 0` the manifold is discrete and
  `M` injects into `S⁰` (`Submission.Homology.Spheres.CompactZero`); for `n ≥ 1`,
  `H_n(M; ℤ) ≅ H_n(Sⁿ; ℤ) ≅ ℤ ≠ 0` by homotopy invariance and the sphere computation, while a
  connected noncompact `n`-manifold has `H_n = 0` (Hatcher, Proposition 3.29, formalised in
  `Submission.Homology.Local.Noncompact`).  Needed only because the target statement does not assume
  compactness.
* `exists_smooth_structure_of_homotopyEquiv_sphere`: **now proved** by Newman's relative
  topological engulfing theorem, Connell's two-cell cover, and Brown's sphere recognition.
  The resulting homeomorphism pulls the standard sphere's smooth atlas back to the manifold.
* `smooth_poincare_five`: **now proved** by the rounded-product argument in
  `Submission.SmoothFive`. The punctured homotopy sphere is simply connected and acyclic;
  its rounded product with `ℝ` is a six-dimensional filling recognized by h-cobordism.
  Brown's Schoenflies theorem recognizes the collared halves of its boundary as disks,
  and the Alexander trick completes the gluing.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff ContinuousMap
open Metric

/-- A topological manifold homotopy equivalent to a sphere is compact (Hatcher, Prop. 3.29 and
homotopy invariance of `H_n`).  Proved: the case `n = 0` is
`SingularPair.compactSpace_of_homotopyEquiv_sphere_zero` (a `0`-manifold is discrete, and a
homotopy equivalence out of a discrete space is injective, so `M` is finite); the case `n ≥ 1` is
`SingularPair.compactSpace_of_homotopyEquiv_sphere_of_one_le` (`M` is path-connected since `Sⁿ`
is, and a noncompact connected `n`-manifold has `H_n(M; ℤ) = 0`, contradicting
`H_n(M; ℤ) ≅ H_n(Sⁿ; ℤ) ≅ ℤ`). -/
theorem compactSpace_of_homotopyEquiv_sphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : CompactSpace M := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact SingularPair.compactSpace_of_homotopyEquiv_sphere_zero e
  · exact SingularPair.compactSpace_of_homotopyEquiv_sphere_of_one_le hn e

/-- A topological homotopy `n`-sphere, `n ≥ 5`, admits a smooth structure, by
relative engulfing, two-cell recognition, and transport of the standard smooth atlas. -/
theorem exists_smooth_structure_of_homotopyEquiv_sphere {n : ℕ} (h5 : 5 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) M,
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _ (𝓡 n) ∞ M _
        cs := by
  let : CompactSpace M := compactSpace_of_homotopyEquiv_sphere e
  exact exists_smooth_structure_of_uniform_relativeNewman h5 e
    (fun N _ q => Engulfing.relativeNewmanAt N n (n - 3) q)

/-- A closed smooth homotopy `5`-sphere is homeomorphic to `S⁵`, by the rounded-product
construction, six-dimensional h-cobordism, and Brown's Schoenflies theorem. -/
theorem smooth_poincare_five {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 5)) M] [IsManifold (𝓡 5) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin 6)) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 6)) 1) := by
  exact poincare_smooth_via_rounded_double (m := 4) (by norm_num) e

end PoincareHighDim
