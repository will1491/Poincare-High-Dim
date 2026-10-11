/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.ChartDisks
import Submission.Topology.Spheres.SphereSimplyConnected
import Submission.Topology.Connectivity.PushOff
import Submission.Homology.Relative.PairVanishing
import Submission.Homology.Punctures.DiskComplement
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Homotopy spheres: point-set consequences and the h-cobordism input

* `nonempty_of_homotopyEquiv`, `pathConnectedSpace_of_homotopyEquiv`: elementary transport of
  nonemptiness and path-connectedness along a homotopy equivalence.
* `simplyConnectedSpace_sphere`: `Sᵏ` is simply connected for `k ≥ 2` (not in Mathlib; proved in
  `Submission.Topology.Spheres.SphereSimplyConnected` by pushing a loop off a point and using that
  `Sᵏ` minus a point is contractible via stereographic projection).
* `simplyConnectedSpace_compl_chartDisks`: if `M` is a simply connected Hausdorff space with an
  `ℝⁿ`-atlas, `n ≥ 3`, then the complement `W` of two disjoint open chart disks is simply
  connected.  This is the general-position argument: `W` is path connected
  (`isPathConnected_compl_chartDisks`), and a null-homotopy in `M` of a loop in `W` can be
  pushed off the two open disks (`exists_push_off_two` of `Submission.Topology.Connectivity.PushOff`: blend,
  inside each chart ball, with a Sard-generic differentiable approximation so as to miss the
  centre, then retract radially onto the boundary sphere), giving a null-homotopy inside `W`
  (`exists_homotopy_refl_compl_chartDisks`); the conclusion follows from
  `isSimplyConnected_iff_exists_homotopy_refl_forall_mem`.
* `relHomologyVanishes_compl_chartDisks`: for a closed smooth homotopy `n`-sphere `M`, `n ≥ 3`,
  `H_*(W, ∂₀W; ℤ) = 0`, where `∂₀W` is the first boundary sphere (the same holds for the second
  one by symmetry, but only the first is consumed).  This follows from excision, the long exact
  sequence of a pair, homotopy invariance, and the fundamental class of the closed manifold `M`
  (Hatcher Theorem 3.26 / Proposition 3.29); it is proved in
  `Submission.Homology.Punctures.DiskComplement` from the singular homology of pairs, excision, the long
  exact sequence and the fundamental class developed in `Submission.Homology`.
* `hcobordism_input_of_homotopy_sphere`: the two statements above combined; this is the
  algebraic-topological input to the h-cobordism theorem (Milnor, *Lectures*, proof of
  Proposition B; Scorpan p. 30).  Simple connectivity of `M` itself is transported from the
  sphere along the homotopy equivalence.  Whitehead's theorem is *not* needed: the h-cobordism
  theorem (`hcobordism_strip`) takes the homological hypothesis directly.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff ContinuousMap
open Metric Set Topology unitInterval

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

/-! ### Simple connectivity of the complement of two open chart disks -/

/-- The complement of two disjoint open chart disks in a path connected Hausdorff space with an
`ℝⁿ`-atlas, `n ≥ 3`, is path connected: a path in `M` between two of its points is pushed off
the two open disks by `exists_push_off_two`. -/
theorem isPathConnected_compl_chartDisks {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [PathConnectedSpace M]
    {e₀ e₁ : Disk n → M} (h₀ : IsChartDisk e₀) (h₁ : IsChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    IsPathConnected ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M) := by
  rw [isPathConnected_iff]
  refine ⟨?_, fun x hx y hy => ?_⟩
  · -- a point of the boundary sphere of the first disk lies in the complement
    have hi : (0 : ℕ) < n := by omega
    let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hi⟩ 1
    have hv : ‖v‖ = 1 := by simp [v]
    let w : Disk n := ⟨v, mem_closedBall_zero_iff.2 hv.le⟩
    refine ⟨e₀ w, ?_⟩
    simp only [mem_compl_iff, mem_union, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h₀.injective.mem_set_image, mem_diskInterior] at h
      exact absurd h (by simp [w, hv])
    · exact Set.disjoint_left.1 hdisj ⟨w, rfl⟩ (image_subset_range _ _ h)
  · -- push a path from `x` to `y` off the two open disks
    set γ := PathConnectedSpace.somePath x y with hγ
    obtain ⟨F', hF', hmem, hfix⟩ := exists_push_off_two hn h₀ h₁ hdisj
      (F := fun z : I × I => γ z.2) (γ.continuous.comp continuous_snd)
    refine ⟨⟨⟨fun s => F' (0, s), hF'.comp (continuous_const.prodMk continuous_id)⟩, ?_, ?_⟩,
      fun t => hmem (0, t)⟩
    · show F' (0, 0) = x
      rw [hfix (0, 0) (by show γ 0 ∈ _; rw [γ.source]; exact hx)]
      exact γ.source
    · show F' (0, 1) = y
      rw [hfix (0, 1) (by show γ 1 ∈ _; rw [γ.target]; exact hy)]
      exact γ.target

/-- Every loop in the complement of two disjoint open chart disks of a simply connected
Hausdorff space with an `ℝⁿ`-atlas, `n ≥ 3`, is null-homotopic inside the complement: a
null-homotopy in `M` is pushed off the two open disks by `exists_push_off_two`, which does not
move the boundary of the square. -/
theorem exists_homotopy_refl_compl_chartDisks {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SimplyConnectedSpace M] {e₀ e₁ : Disk n → M} (h₀ : IsChartDisk e₀) (h₁ : IsChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) (x : M) (p : Path x x)
    (hp : ∀ t, p t ∈ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ) :
    ∃ F : p.Homotopy (.refl x), ∀ t, F t ∈ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ := by
  obtain ⟨G⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl x)
  obtain ⟨F', hF', hmem, hfix⟩ := exists_push_off_two hn h₀ h₁ hdisj
    (F := fun z : I × I => G z) G.continuous
  have hx : x ∈ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ := p.source ▸ hp 0
  refine ⟨{ toFun := F'
            continuous_toFun := hF'
            map_zero_left := fun s => ?_
            map_one_left := fun s => ?_
            prop' := fun t s hs => ?_ }, hmem⟩
  · rw [hfix (0, s) (by show G (0, s) ∈ _; rw [G.apply_zero]; exact hp s)]
    exact G.apply_zero s
  · rw [hfix (1, s) (by show G (1, s) ∈ _; rw [G.apply_one]; exact hx)]
    exact G.apply_one s
  · rcases hs with rfl | rfl
    · show F' (t, 0) = p 0
      rw [hfix (t, 0) (by show G (t, 0) ∈ _; rw [G.source]; exact hx)]
      show G (t, 0) = p 0
      rw [G.source, p.source]
    · show F' (t, 1) = p 1
      rw [hfix (t, 1) (by show G (t, 1) ∈ _; rw [G.target]; exact hx)]
      show G (t, 1) = p 1
      rw [G.target, p.target]

/-- **Simple connectivity of the strip.**  The complement of two disjoint open chart disks in a
simply connected Hausdorff space with an `ℝⁿ`-atlas, `n ≥ 3`, is simply connected. -/
theorem simplyConnectedSpace_compl_chartDisks {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SimplyConnectedSpace M] {e₀ e₁ : Disk n → M} (h₀ : IsChartDisk e₀) (h₁ : IsChartDisk e₁)
    (hdisj : Disjoint (Set.range e₀) (Set.range e₁)) :
    SimplyConnectedSpace ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M) := by
  change IsSimplyConnected _
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  exact ⟨isPathConnected_compl_chartDisks hn h₀ h₁ hdisj,
    exists_homotopy_refl_compl_chartDisks hn h₀ h₁ hdisj⟩

/-! ### The h-cobordism input -/

/-- **Homological input for the h-cobordism theorem.**  For a closed smooth homotopy
`n`-sphere `M`, `n ≥ 3`, and the complement `W` of two disjoint open chart disks,
`H_*(W, ∂₀W; ℤ) = 0` for the first boundary sphere `∂₀W ⊆ W` (as the subset
`Subtype.val ⁻¹' (e₀ '' diskSphere n)` of the subtype `W`).  This is
`SingularPair.relHomologyVanishes_compl_chartDisks` of `Submission.Homology.Punctures.DiskComplement`:
excision, the long exact sequence of a pair, homotopy invariance and the fundamental class of
the closed manifold `M` (Hatcher Theorem 3.26 / Proposition 3.29); no Whitehead theorem is
needed.  See the module docstring. -/
theorem relHomologyVanishes_compl_chartDisks {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {e₀ e₁ : Disk n → M} (h₀ : IsChartDisk e₀) (h₁ : IsChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    RelHomologyVanishes ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M)
      (Subtype.val ⁻¹' (e₀ '' diskSphere n)) :=
  SingularPair.relHomologyVanishes_compl_chartDisks (by omega) e h₀ h₁ hdisj

/-- **The h-cobordism input** for a closed smooth homotopy `n`-sphere, `n ≥ 3`: the complement
`W` of two disjoint open chart disks is simply connected, and `H_*(W, ∂₀W; ℤ) = 0` for the
first boundary sphere `∂₀W ⊆ W` (as the subset `Subtype.val ⁻¹' (e₀ '' diskSphere n)` of the
subtype `W`).  Simple connectivity of `M` is transported from `Sⁿ` along `e`, and that of `W`
is `simplyConnectedSpace_compl_chartDisks`; the homological statement is
`relHomologyVanishes_compl_chartDisks`. -/
theorem hcobordism_input_of_homotopy_sphere {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {e₀ e₁ : Disk n → M} (h₀ : IsChartDisk e₀) (h₁ : IsChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    SimplyConnectedSpace ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M) ∧
      RelHomologyVanishes ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M)
        (Subtype.val ⁻¹' (e₀ '' diskSphere n)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := simplyConnectedSpace_sphere (by omega : 2 ≤ k + 1)
  have : SimplyConnectedSpace M := e.simplyConnectedSpace
  exact ⟨simplyConnectedSpace_compl_chartDisks hn h₀ h₁ hdisj,
    relHomologyVanishes_compl_chartDisks hn e h₀ h₁ hdisj⟩

end PoincareHighDim
