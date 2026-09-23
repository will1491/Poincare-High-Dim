import Submission.ChartDisks
import Submission.Topology.SphereSimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Homotopy spheres: point-set consequences and the h-cobordism input

* `nonempty_of_homotopyEquiv`, `pathConnectedSpace_of_homotopyEquiv`: elementary transport of
  nonemptiness and path-connectedness along a homotopy equivalence.
* `simplyConnectedSpace_sphere`: `Sᵏ` is simply connected for `k ≥ 2` (not in Mathlib; proved in
  `Submission.Topology.SphereSimplyConnected` by pushing a loop off a point and using that
  `Sᵏ` minus a point is contractible via stereographic projection).
* `hcobordism_input_of_homotopy_sphere`: for a closed smooth homotopy `n`-sphere `M`, `n ≥ 3`,
  the complement `W` of two disjoint open chart disks is simply connected and the inclusion of
  the first boundary sphere into `W` is a homotopy equivalence (the same holds for the second
  one by symmetry, but only the first is consumed).  This is the algebraic-topological
  input to the h-cobordism theorem (Milnor, *Lectures*, proof of Proposition B; Scorpan p. 30):
  simple connectivity follows from `π₁(M) = 0` by general position (`n ≥ 3`), and the homotopy
  equivalence from `H_*(W, ∂₀W) = 0` (excision, the long exact sequence, homotopy invariance,
  and the fundamental class of the closed manifold `M`, Hatcher Theorem 3.26 / Proposition 3.29)
  together with Whitehead's theorem.  None of this algebraic topology (relative homology,
  excision, Whitehead) exists in Mathlib, so this node is recorded as a documented external
  theorem.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff ContinuousMap
open Metric Set Topology

theorem nonempty_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] (e : X ≃ₕ Y) : Nonempty X :=
  ⟨e.invFun (Classical.arbitrary Y)⟩

theorem pathConnectedSpace_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X := by
  obtain ⟨H⟩ := e.left_inv
  refine ⟨nonempty_of_homotopyEquiv e, fun x y => ?_⟩
  -- `H.evalAt x : Path (e.invFun (e.toFun x)) x`.
  have hx : Joined (e.invFun (e.toFun x)) x := ⟨H.evalAt x⟩
  have hy : Joined (e.invFun (e.toFun y)) y := ⟨H.evalAt y⟩
  have hxy : Joined (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) :=
    (PathConnectedSpace.joined (e.toFun x) (e.toFun y)).map e.invFun.continuous
  exact hx.symm.trans (hxy.trans hy)

/-- The sphere `Sᵏ`, `k ≥ 2`, is simply connected. -/
theorem simplyConnectedSpace_sphere {k : ℕ} (hk : 2 ≤ k) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
  simplyConnectedSpace_sphere_of_two_le hk

/-- The boundary sphere of a chart disk in an `n`-manifold, `n ≥ 3`, is simply connected. -/
theorem IsChartDisk.simplyConnectedSpace_image_diskSphere {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : Disk n → M} (he : IsChartDisk e) : SimplyConnectedSpace (e '' diskSphere n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 2 ≤ k := by omega
  obtain ⟨φ⟩ := he.nonempty_homeomorph_image_diskSphere
  have := simplyConnectedSpace_sphere hk
  exact φ.toHomotopyEquiv.simplyConnectedSpace

/-- **The h-cobordism input** for a closed smooth homotopy `n`-sphere, `n ≥ 3`: the complement
of two disjoint open chart disks is simply connected, and the inclusion of the first boundary
sphere into it is a homotopy equivalence. External (algebraic topology); see the module
docstring. -/
theorem hcobordism_input_of_homotopy_sphere {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {e₀ e₁ : Disk n → M} (h₀ : IsChartDisk e₀) (h₁ : IsChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    SimplyConnectedSpace ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M) ∧
      IsHomotopyEquivInclusion (e₀ '' diskSphere n)
        (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ := by
  sorry

end PoincareHighDim
