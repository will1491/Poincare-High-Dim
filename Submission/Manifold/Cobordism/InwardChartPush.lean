/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.BoundaryAtlas
import Submission.Manifold.Cobordism.ChartPush
import Submission.Manifold.Cobordism.EuclideanPush

/-!
# Supported inward pushes on manifolds with boundary

Every boundary point admits a smooth injective chart modification which sends
that point to the interior. A point whose image remains on the boundary is fixed.
Consequently a finite family of these modifications can move the entire boundary
into the interior without ever moving an interior point onto the boundary.
-/

namespace PoincareHighDim

open Set Topology WithLp
open scoped Manifold ContDiff

variable {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- A genuine smooth inward modification exists around every boundary point. -/
theorem exists_inward_chartPush (c : (𝓡∂ (n + 1)).boundary W) :
    ∃ D : ChartPushData (𝓡∂ (n + 1)) c.1,
      (𝓡∂ (n + 1)).IsInteriorPoint (D.push c.1) ∧
      ∀ y, (𝓡∂ (n + 1)).IsBoundaryPoint (D.push y) → D.push y = y := by
  let I := 𝓡∂ (n + 1)
  let e := chartAt (EuclideanHalfSpace (n + 1)) c.1
  let U : Set (EuclideanSpace ℝ (Fin (n + 1))) := I.symm ⁻¹' e.target
  have hU : U ∈ nhds (extChartAt I c.1 c.1) := by
    apply (e.open_target.preimage I.continuous_symm).mem_nhds
    change I.symm (I (e c.1)) ∈ e.target
    rw [I.left_inv]
    exact mem_chart_target _ _
  let ℓ : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ := EuclideanSpace.proj 0
  let v : EuclideanSpace ℝ (Fin (n + 1)) := toLp 2 (Pi.single 0 1)
  obtain ⟨K, Φ, hK, hKU, hfix, hmono, hstrict, hfixedCoord⟩ :=
    exists_supported_inward_displacement hU ℓ v (by simp [ℓ, v])
  have hΦU : MapsTo Φ U U := diffeomorph_mapsTo_of_eqOn_compl Φ (by
    intro z hz
    exact hfix (fun h => hz (hKU h)))
  have hΦrange : MapsTo Φ (range I) (range I) := by
    intro z hz
    change z ∈ range (𝓡∂ (n + 1)) at hz
    change Φ z ∈ range (𝓡∂ (n + 1))
    rw [range_modelWithCornersEuclideanHalfSpace] at hz ⊢
    exact le_trans hz (hmono z)
  let D : ChartPushData I c.1 :=
    { coordMap := Φ
      carrier := K
      compact_carrier := hK
      carrier_subset := by
        rw [extChartAt_target]
        exact fun z hz => ⟨hKU hz.1, hz.2⟩
      mapsTo_target := by
        rw [extChartAt_target]
        exact fun z hz => ⟨hΦU hz.1, hΦrange hz.2⟩
      eq_outside := fun z hz => hfix hz }
  have hcoord (y : W) (hy : y ∈ e.source) :
      (e (D.push y)).1 0 = ℓ (Φ (extChartAt I c.1 y)) := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z 0)
      (D.extChart_push hy)
    exact h
  have hzero : ℓ (extChartAt I c.1 c.1) = 0 := by
    exact (isBoundaryPoint_iff_chart_zero (chart_mem_atlas _ c.1)
      (mem_chart_source _ _)).mp c.2
  refine ⟨D, ?_, ?_⟩
  · rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
      isBoundaryPoint_iff_chart_zero (chart_mem_atlas _ c.1)
        (D.push_mem_source (mem_chart_source _ _)), hcoord c.1 (mem_chart_source _ _)]
    exact ne_of_gt (hzero ▸ hstrict)
  · intro y hy
    by_cases hs : y ∈ e.source
    · have hz : ℓ (Φ (extChartAt I c.1 y)) = 0 := by
        rw [← hcoord y hs]
        exact (isBoundaryPoint_iff_chart_zero (chart_mem_atlas _ c.1)
          (D.push_mem_source hs)).mp hy
      have hnonneg : 0 ≤ ℓ (extChartAt I c.1 y) := (e y).2
      have hnormal : ℓ (extChartAt I c.1 y) = 0 := by
        have hm := hmono (extChartAt I c.1 y)
        rw [hz] at hm
        exact le_antisymm hm hnonneg
      have hf : Φ (extChartAt I c.1 y) = extChartAt I c.1 y :=
        hfixedCoord _ (hz.trans hnormal.symm)
      rw [D.push_of_mem hs]
      change (extChartAt I c.1).symm (Φ (extChartAt I c.1 y)) = y
      rw [hf]
      exact (extChartAt I c.1).left_inv (by simpa only [extChartAt_source] using hs)
    · exact D.push_of_not_mem hs

end PoincareHighDim
