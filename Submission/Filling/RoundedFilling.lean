/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Filling.AcyclicFilling
import Submission.Homology.Punctures.RoundedDouble
import Submission.Morse.Rounded.RoundedDouble
import Submission.Manifold.ProductModel

/-!
# The boundary of a rounded acyclic filling

The product with the real line raises the filling dimension by one, allowing the
h-cobordism theorem to recognize the rounded boundary even when the base has dimension
five. The remaining boundary connectivity hypothesis is established using its collar.
-/

namespace PoincareHighDim.RoundedDouble

open Set Topology
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem nonempty_homeomorph_boundary_sphere (hn : 5 ≤ n) {g : M → ℝ}
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) (hne : (g ⁻¹' Iio 0).Nonempty)
    (hreg : ∀ x, g x = 0 → ¬ IsCriticalPt (𝓡 n) g x)
    (hB : SimplyConnectedSpace (base g)) (hV : SimplyConnectedSpace (boundary g))
    (hacyclic : SingularPair.Acyclic SingularPair.Z.{u} (TopCat.of (base g))) :
    Nonempty (boundary g ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let G : M × ℝ → ℝ := fun p => g p.1 + p.2 ^ 2
  have hGprod := contMDiff_height (𝓡 n) hg
  have hregprod := regular_height_zero (𝓡 n) hg hreg
  let := productChartedSpace n M
  let : IsManifold (𝓡 (n + 1)) ∞ (M × ℝ) := product_isManifold
  have hG : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ G :=
    contMDiff_productChartedSpace_iff.mpr hGprod
  have hGregular : ∀ p, G p = 0 → ¬ IsCriticalPt (𝓡 (n + 1)) G p := by
    intro p hp
    rw [isCriticalPt_productChartedSpace_iff hGprod p]
    exact hregprod p hp
  have hGne : (G ⁻¹' Iio 0).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨(x, 0), by simpa only [G, mem_preimage, mem_Iio, zero_pow (by decide : 2 ≠ 0),
      add_zero] using hx⟩
  let := hB
  exact nonempty_homeomorph_boundary_of_acyclic_filling (by omega : 6 ≤ n + 1)
    hG (isCompact_filling hg.continuous) hGne hGregular
    (simplyConnectedSpace_filling g) hV (acyclic_filling SingularPair.Z g hacyclic)

end PoincareHighDim.RoundedDouble
