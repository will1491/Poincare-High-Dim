import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv
import Submission.Homology.Noncompact
import Submission.Homology.CompactZero

/-!
# External theorems

Deep results outside the Morse-theoretic route, each recorded as a named theorem with a
literature citation so that `#print axioms` on the final theorem exhibits exactly which
mathematical debts remain.

* `compactSpace_of_homotopyEquiv_sphere`: a topological `n`-manifold homotopy equivalent to `Sⁿ`
  is compact.  **Now proved** (no longer external): for `n = 0` the manifold is discrete and
  `M` injects into `S⁰` (`Submission.Homology.CompactZero`); for `n ≥ 1`,
  `H_n(M; ℤ) ≅ H_n(Sⁿ; ℤ) ≅ ℤ ≠ 0` by homotopy invariance and the sphere computation, while a
  connected noncompact `n`-manifold has `H_n = 0` (Hatcher, Proposition 3.29, formalised in
  `Submission.Homology.Noncompact`).  Needed only because the target statement does not assume
  compactness.
* `exists_smooth_structure_of_homotopyEquiv_sphere`: a topological homotopy `n`-sphere, `n ≥ 5`,
  admits a smooth structure.  WARNING: the known proof goes through the Kirby–Siebenmann
  obstruction (`ks(M) ∈ H⁴(M; ℤ/2) = 0`, so `M` is PL) and the PL Poincaré conjecture
  (Smale/Stallings/Zeeman), or through Newman's topological engulfing theorem; it is *not* a
  lemma weaker than the topological Poincaré conjecture itself.  It is isolated here so that the
  smooth theorem `poincare_smooth` carries all the Morse-theoretic content.
* `smooth_poincare_five`: the smooth case `n = 5`.  The h-cobordism theorem needs cobordisms of
  dimension `≥ 6`, so a homotopy `5`-sphere is handled by Kervaire–Milnor (`Θ₅ = 0`: every
  homotopy `5`-sphere bounds a contractible `6`-manifold, whose complement of a ball is a
  `6`-dimensional h-cobordism), cf. Scorpan p. 31, Milnor *Lectures* p. 109.
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

/-- A topological homotopy `n`-sphere, `n ≥ 5`, admits a smooth structure (Kirby–Siebenmann
plus the PL Poincaré conjecture, or Newman's engulfing theorem). External. -/
theorem exists_smooth_structure_of_homotopyEquiv_sphere {n : ℕ} (h5 : 5 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) M,
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _ (𝓡 n) ∞ M _
        cs := by
  sorry

/-- A closed smooth homotopy `5`-sphere is homeomorphic to `S⁵` (Kervaire–Milnor, `Θ₅ = 0`,
together with the `6`-dimensional h-cobordism theorem). External. -/
theorem smooth_poincare_five {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 5)) M] [IsManifold (𝓡 5) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin 6)) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 6)) 1) := by
  sorry

end PoincareHighDim
