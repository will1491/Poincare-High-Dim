/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Filling.SmoothFivePreparation
import Submission.Filling.RoundedFilling
import Submission.Morse.Rounded.RoundedCollar
import Submission.Topology.Rounded.RoundedSimplyConnected
import Submission.Topology.Rounded.RoundedDisk
import Submission.Topology.Schoenflies.BrownSchoenflies

/-!
# Smooth Poincaré via a rounded product

Puncture the homotopy sphere by one chart disk. Its complement is simply connected and
acyclic. The rounded product with the real line is a filling one dimension higher, whose
boundary is the double of the punctured sphere. The h-cobordism theorem recognizes that
boundary as a sphere, and Brown's Schoenflies theorem recognizes each collared half as a
disk. Gluing back the original chart disk gives the standard sphere.

The filling has dimension at least six when the original manifold has dimension five, so
this argument includes the case excluded by the direct two-puncture h-cobordism argument.
-/

namespace PoincareHighDim

open Set Metric Topology
open scoped Manifold ContDiff ContinuousMap

/-- The rounded-product argument proves smooth Poincaré starting in dimension five. -/
theorem poincare_smooth_via_rounded_double {m : ℕ} (h5 : 5 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) := by
  obtain ⟨p⟩ := exists_smoothSpherePuncture (by omega : 3 ≤ m + 1) e
  have : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
    simplyConnectedSpace_sphere (by omega : 2 ≤ m)
  have hzero : IsPathConnected (p.g ⁻¹' {0}) :=
    isPathConnected_iff_pathConnectedSpace.mpr p.levelHomeomorph.symm.pathConnectedSpace
  obtain ⟨η₀, hη₀, Ψ₀, hΨ₀, -⟩ :=
    RoundedDouble.exists_equatorial_collar p.smooth p.regular_zero
  have hV := RoundedDouble.simplyConnectedSpace_boundary_of_collar p.smooth.continuous
    p.simplyConnected_base hzero hη₀ Ψ₀ hΨ₀
  obtain ⟨eV⟩ := RoundedDouble.nonempty_homeomorph_boundary_sphere h5 p.smooth
    p.negative_nonempty p.regular_zero p.simplyConnected_base hV p.acyclic_base
  have : CompactSpace (RoundedDouble.boundary p.g) :=
    isCompact_iff_compactSpace.mp (RoundedDouble.isCompact_boundary p.smooth.continuous)
  have : TopologicalSpace.MetrizableSpace (RoundedDouble.boundary p.g) := eV.isEmbedding.metrizableSpace
  let : MetricSpace (RoundedDouble.boundary p.g) :=
    TopologicalSpace.metrizableSpaceMetric (RoundedDouble.boundary p.g)
  obtain ⟨η, hη, Ψ, hΨ⟩ := RoundedDouble.exists_unit_equatorial_collar p.smooth p.regular_zero
  let t : RoundedDouble.boundary p.g → ℝ := fun x => x.1.2 / η
  let Φ : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) ≃ₜ
      {x : RoundedDouble.boundary p.g // t x ∈ Icc (-1 : ℝ) 1} :=
    (Homeomorph.prodCongr p.levelHomeomorph.symm (Homeomorph.refl SuspensionInterval)).trans Ψ
  have hΦ (q : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) :
      t (Φ q).1 = q.2.1 := hΨ (p.levelHomeomorph.symm q.1, q.2)
  obtain ⟨d, hd, hdrange, hdboundary⟩ := (exists_side_disks_of_height_collar eV t
    (continuous_subtype_val.snd.div_const η) Φ hΦ).1
  have hdrange' : range d = {x : RoundedDouble.boundary p.g | x.1.2 ≤ 0} := by
    rw [hdrange]
    ext x
    change x.1.2 / η ≤ 0 ↔ x.1.2 ≤ 0
    rw [div_le_iff₀ hη, zero_mul]
  have hdboundary' : d '' diskSphere (m + 1) =
      {x : RoundedDouble.boundary p.g | x.1.2 = 0} := by
    rw [hdboundary]
    ext x
    change x.1.2 / η = 0 ↔ x.1.2 = 0
    simp only [div_eq_zero_iff, hη.ne', or_false]
  exact RoundedDouble.sphere_homeomorph_of_lower_disk p.chartDisk.isClosedEmbedding
    p.positive_eq_range.symm p.zero_eq_boundary.symm hd hdrange' hdboundary'

end PoincareHighDim
