/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Compactness.Compact

/-!
# Smooth chart modifications with compact support

A Euclidean diffeomorphism that preserves an extended chart target induces an
injective smooth self-map of the manifold, equal to the identity away from a
compact subset of that chart. The inverse Euclidean coordinates detect smoothness
of every continuous map into the original manifold. Surjectivity onto the
manifold is neither assumed nor needed, so this includes inward boundary pushes.
-/

namespace PoincareHighDim

open Set Topology Filter
open scoped Manifold ContDiff

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace W] [ChartedSpace H W]
    (I : ModelWithCorners ℝ E H) (c : W)

/-- Euclidean data for a compactly supported modification of one manifold chart. -/
structure ChartPushData where
  coordMap : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E
  carrier : Set E
  compact_carrier : IsCompact carrier
  carrier_subset : carrier ∩ range I ⊆ (extChartAt I c).target
  mapsTo_target : MapsTo coordMap (extChartAt I c).target (extChartAt I c).target
  eq_outside : ∀ z, z ∉ carrier → coordMap z = z

namespace ChartPushData

variable {I c} (D : ChartPushData I c)

/-- The compact support region transferred back to the original chart. -/
def supportRegion : Set W := (extChartAt I c).symm '' (D.carrier ∩ range I)

theorem isCompact_supportRegion : IsCompact D.supportRegion :=
  (D.compact_carrier.inter_right I.isClosed_range).image_of_continuousOn
    ((chartAt H c).continuousOn_extend_symm.mono D.carrier_subset)

theorem supportRegion_subset : D.supportRegion ⊆ (chartAt H c).source := by
  rintro y ⟨z, hz, rfl⟩
  simpa only [extChartAt_source] using (extChartAt I c).map_target (D.carrier_subset hz)

/-- Use the chart modification inside its source and the identity elsewhere. -/
noncomputable def push (x : W) : W := by
  classical
  exact if x ∈ (chartAt H c).source then
    (extChartAt I c).symm (D.coordMap (extChartAt I c x)) else x

theorem push_of_mem {x : W} (hx : x ∈ (chartAt H c).source) :
    D.push x = (extChartAt I c).symm (D.coordMap (extChartAt I c x)) := by
  simp only [push, ite_eq_left hx]

theorem push_of_not_mem {x : W} (hx : x ∉ (chartAt H c).source) : D.push x = x := by
  simp only [push, ite_eq_right hx]

theorem push_mem_source {x : W} (hx : x ∈ (chartAt H c).source) :
    D.push x ∈ (chartAt H c).source := by
  rw [D.push_of_mem hx]
  simpa only [extChartAt_source] using (extChartAt I c).map_target
    (D.mapsTo_target ((extChartAt I c).map_source (by simpa only [extChartAt_source] using hx)))

theorem extChart_push {x : W} (hx : x ∈ (chartAt H c).source) :
    extChartAt I c (D.push x) = D.coordMap (extChartAt I c x) := by
  rw [D.push_of_mem hx]
  exact (extChartAt I c).right_inv
    (D.mapsTo_target ((extChartAt I c).map_source (by simpa only [extChartAt_source] using hx)))

theorem push_eq_of_not_mem_supportRegion {x : W} (hx : x ∉ D.supportRegion) : D.push x = x := by
  by_cases hs : x ∈ (chartAt H c).source
  · have hk : extChartAt I c x ∉ D.carrier := by
      intro hk
      apply hx
      exact ⟨extChartAt I c x, ⟨hk, mem_range_self _⟩,
        (extChartAt I c).left_inv (by simpa only [extChartAt_source] using hs)⟩
    rw [D.push_of_mem hs, D.eq_outside _ hk]
    exact (extChartAt I c).left_inv (by simpa only [extChartAt_source] using hs)
  · exact D.push_of_not_mem hs

theorem injective : Function.Injective D.push := by
  intro x y hxy
  by_cases hx : x ∈ (chartAt H c).source
  · by_cases hy : y ∈ (chartAt H c).source
    · have h := congrArg (extChartAt I c) hxy
      rw [D.extChart_push hx, D.extChart_push hy] at h
      exact (extChartAt I c).injOn (by simpa only [extChartAt_source] using hx)
        (by simpa only [extChartAt_source] using hy) (D.coordMap.injective h)
    · have hm := D.push_mem_source hx
      rw [hxy, D.push_of_not_mem hy] at hm
      exact (hy hm).elim
  · by_cases hy : y ∈ (chartAt H c).source
    · have hm := D.push_mem_source hy
      rw [← hxy, D.push_of_not_mem hx] at hm
      exact (hx hm).elim
    · simpa only [D.push_of_not_mem hx, D.push_of_not_mem hy] using hxy

variable [IsManifold I ∞ W] [T2Space W]

theorem contMDiff : ContMDiff I I ∞ D.push := by
  intro x
  by_cases hx : x ∈ (chartAt H c).source
  · have h := (contMDiffOn_extChartAt_symm (I := I) c).comp
      (D.coordMap.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt (I := I) (x := c)))
      (fun y hy => D.mapsTo_target
        ((extChartAt I c).map_source (by simpa only [extChartAt_source] using hy)))
    apply (h.contMDiffAt ((chartAt H c).open_source.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [(chartAt H c).open_source.mem_nhds hx] with y hy
    exact D.push_of_mem hy
  · have hc : x ∉ D.supportRegion := fun h => hx (D.supportRegion_subset h)
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [D.isCompact_supportRegion.isClosed.isOpen_compl.mem_nhds hc] with y hy
    exact D.push_eq_of_not_mem_supportRegion hy

/-- On a compact manifold the chart modification is a topological embedding. -/
theorem isEmbedding [CompactSpace W] : IsEmbedding D.push :=
  (D.contMDiff.continuous.isClosedEmbedding D.injective).isEmbedding

/-- The Euclidean inverse coordinates recover smoothness before a chart push. -/
theorem smooth_lift
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    (J : ModelWithCorners ℝ F G) [IsManifold J ∞ N]
    {k : N → W} (hk : Continuous k)
    (hcomp : ContMDiff J I ∞ (fun y => D.push (k y))) : ContMDiff J I ∞ k := by
  intro x
  by_cases hx : k x ∈ (chartAt H c).source
  · rw [contMDiffAt_iff_target_of_mem_source hx]
    refine ⟨hk.continuousAt, ?_⟩
    have hs : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I c) (D.push (k x)) :=
      (contMDiffOn_extChartAt (I := I) (x := c)).contMDiffAt
        ((chartAt H c).open_source.mem_nhds (D.push_mem_source hx))
    have h := D.coordMap.symm.contMDiff.contMDiffAt.comp x (hs.comp x (hcomp x))
    apply h.congr_of_eventuallyEq
    have hnear : ∀ᶠ y in 𝓝 x, k y ∈ (chartAt H c).source :=
      hk.continuousAt.preimage_mem_nhds ((chartAt H c).open_source.mem_nhds hx)
    filter_upwards [hnear] with y hy
    change extChartAt I c (k y) = D.coordMap.symm (extChartAt I c (D.push (k y)))
    rw [D.extChart_push hy, D.coordMap.symm_apply_apply]
  · have hc : k x ∉ D.supportRegion := fun h => hx (D.supportRegion_subset h)
    apply (hcomp x).congr_of_eventuallyEq
    have hnear : ∀ᶠ y in 𝓝 x, k y ∉ D.supportRegion :=
      hk.continuousAt.preimage_mem_nhds (D.isCompact_supportRegion.isClosed.isOpen_compl.mem_nhds hc)
    filter_upwards [hnear] with y hy
    exact (D.push_eq_of_not_mem_supportRegion hy).symm

end ChartPushData

end PoincareHighDim
