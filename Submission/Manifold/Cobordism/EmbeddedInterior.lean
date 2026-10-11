/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.PushDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The interior of a full-rank embedded manifold

An invertible differential at an interior point makes a smooth map locally open.
Consequently the frontier of a compact embedded manifold is contained in the image
of its original manifold boundary.
-/

namespace PoincareHighDim

open Set Topology Filter
open scoped Manifold ContDiff

section OpenMap

variable {E F H G W M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace W] [ChartedSpace H W]
    [TopologicalSpace M] [ChartedSpace G M]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {f : W → M} {x : W}

/-- The inverse function theorem expressed directly in manifold neighborhoods. -/
theorem map_nhds_eq_of_isInvertible_mfderiv
    (hf : ContMDiffAt I J ∞ f x) (hx : I.IsInteriorPoint x)
    (hy : J.IsInteriorPoint (f x)) (hD : (mfderiv I J f x).IsInvertible) :
    Filter.map f (𝓝 x) = 𝓝 (f x) := by
  have hmd := hf.mdifferentiableAt (by simp)
  have hcont := (contMDiffAt_iff.mp hf).2.contDiffAt (range_mem_nhds_isInteriorPoint hx)
  obtain ⟨A, hA⟩ := hD
  let L : E ≃L[ℝ] F := (tangentSpaceCastModel I x).symm.trans
    (A.trans (tangentSpaceCastModel J (f x)))
  have hd : HasFDerivAt (writtenInExtChartAt I J x f) (L : E →L[ℝ] F)
      (extChartAt I x x) := by
    have hd := hmd.hasMFDerivAt.2.hasFDerivAt (range_mem_nhds_isInteriorPoint hx)
    rw [← hA] at hd
    exact hd
  have hm := (hcont.hasStrictFDerivAt' hd (by simp)).map_nhds_eq_of_equiv
  change Filter.map (writtenInExtChartAt I J x f) (𝓝 (extChartAt I x x)) =
    𝓝 (writtenInExtChartAt I J x f (extChartAt I x x)) at hm
  have hsource : Filter.map (extChartAt I x) (𝓝 x) = 𝓝 (extChartAt I x x) := by
    rw [map_extChartAt_nhds, nhdsWithin_eq_nhds.mpr (range_mem_nhds_isInteriorPoint hx)]
  have htarget : Filter.map (extChartAt J (f x)).symm
      (𝓝 (extChartAt J (f x) (f x))) = 𝓝 (f x) := by
    rw [← nhdsWithin_eq_nhds.mpr (range_mem_nhds_isInteriorPoint hy)]
    exact map_extChartAt_symm_nhdsWithin_range _
  calc
    Filter.map f (𝓝 x) = Filter.map
        ((extChartAt J (f x)).symm ∘ writtenInExtChartAt I J x f ∘ extChartAt I x)
        (𝓝 x) := by
      apply Filter.map_congr
      filter_upwards [extChartAt_source_mem_nhds (I := I) x,
        hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := J) (f x))]
        with z hz hzf
      simp only [Function.comp_apply, writtenInExtChartAt,
        (extChartAt I x).left_inv hz, (extChartAt J (f x)).left_inv hzf]
    _ = 𝓝 (f x) := by
      rw [← Filter.map_map, ← Filter.map_map, hsource, hm]
      simpa only [writtenInExtChartAt, Function.comp_apply,
        (extChartAt I x).left_inv (mem_extChartAt_source x)] using htarget

end OpenMap

section EmbeddedImage

variable {E F H G W M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace W] [ChartedSpace H W]
    [TopologicalSpace M] [ChartedSpace G M]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [IsManifold I ∞ W] [J.Boundaryless]
    {f : W → M} (hf : ContMDiff I J ∞ f)
    (hD : ∀ x, (mfderiv I J f x).IsInvertible)

include hf hD

/-- The image of the manifold interior is open when the differential has full rank. -/
theorem isOpen_image_manifoldInterior : IsOpen (f '' I.interior W) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  rw [← map_nhds_eq_of_isInvertible_mfderiv (hf x) hx
    (BoundarylessManifold.isInteriorPoint (I := J)) (hD x)]
  change f ⁻¹' (f '' I.interior W) ∈ 𝓝 x
  exact Filter.mem_of_superset ((I.isOpen_interior (n := ∞) (by simp)).mem_nhds hx)
    (fun z hz => ⟨z, hz, rfl⟩)

/-- No point from the original interior becomes a frontier point of the embedded image. -/
theorem frontier_range_subset_image_boundary [CompactSpace W] [T2Space M] :
    frontier (range f) ⊆ f '' I.boundary W := by
  intro y hy
  have hclosed : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  obtain ⟨x, rfl⟩ := hclosed.closure_eq ▸ hy.1
  refine ⟨x, ?_, rfl⟩
  apply (I.isBoundaryPoint_iff_not_isInteriorPoint x).mpr
  intro hx
  apply hy.2
  exact (isOpen_image_manifoldInterior hf hD).subset_interior_iff.mpr
    (image_subset_range _ _) ⟨x, hx, rfl⟩

end EmbeddedImage

namespace InwardCopy

variable {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W] [CompactSpace W] [T2Space W]
    (C : InwardCopy (𝓡∂ (n + 1)) W)

/-- The constructed copy has no additional boundary in its boundaryless ambient interior. -/
theorem frontier_range_embedding_subset :
    frontier (range C.embedding) ⊆ C.embedding '' (𝓡∂ (n + 1)).boundary W := by
  let := (ManifoldInterior.inducedAtlas (𝓡∂ (n + 1)) (W := W)).chartedSpace
  exact frontier_range_subset_image_boundary C.contMDiff_embedding
    C.isInvertible_mfderiv_embedding

end InwardCopy

end PoincareHighDim
