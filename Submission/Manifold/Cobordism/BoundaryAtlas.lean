/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.Basic
import Submission.Manifold.RegularLevel.Atlas

/-!
# Charts induced on the boundary of a smooth manifold

An ambient half-space chart restricts to a chart on the boundary. The coordinate
normal to the boundary is zero; deleting it leaves Euclidean coordinates of one
lower dimension. All constructions use the existing subspace topology.
-/

open Set Topology WithLp
open scoped Manifold ContDiff

namespace PoincareHighDim

/-- The boundary hyperplane in the standard half-space. -/
def halfSpaceBoundary (n : ℕ) : Set (EuclideanHalfSpace (n + 1)) :=
  {x | x.1 0 = 0}

/-- Insert a zero normal coordinate into a boundary coordinate vector. -/
def boundaryCoordinateInclusion (n : ℕ) (y : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) := toLp 2 (Fin.cons 0 y)

/-- The same coordinate inclusion, valued in the half-space. -/
def boundaryHalfSpaceInclusion (n : ℕ) (y : Fin n → ℝ) :
    EuclideanHalfSpace (n + 1) := ⟨boundaryCoordinateInclusion n y, by simp [boundaryCoordinateInclusion]⟩

theorem contDiff_boundaryCoordinateInclusion (n : ℕ) :
    ContDiff ℝ ∞ (boundaryCoordinateInclusion n) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin n → ℝ => (0 : ℝ)))
  · simpa using (contDiff_apply ℝ ℝ j : ContDiff ℝ ∞ (fun y : Fin n → ℝ => y j))

@[simp] theorem model_symm_boundaryCoordinateInclusion (n : ℕ) (y : Fin n → ℝ) :
    (𝓡∂ (n + 1)).symm (boundaryCoordinateInclusion n y) = boundaryHalfSpaceInclusion n y :=
  modelWithCornersEuclideanHalfSpace_symm_apply_of_le _

instance (n : ℕ) : Nonempty (halfSpaceBoundary n) := ⟨⟨0, rfl⟩⟩

/-- Deleting the zero normal coordinate identifies the half-space boundary with `ℝⁿ`. -/
noncomputable def halfSpaceBoundaryHomeomorph (n : ℕ) :
    halfSpaceBoundary n ≃ₜ (Fin n → ℝ) where
  toFun x i := x.1.1 i.succ
  invFun y := ⟨⟨toLp 2 (Fin.cons 0 y), by simp⟩, by simp [halfSpaceBoundary]⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using x.2.symm
    · simp
  right_inv y := by ext i; simp
  continuous_toFun := continuous_pi fun i =>
    (PiLp.continuous_apply 2 _ i.succ).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ)))
    · simpa using (continuous_apply j : Continuous (fun y : Fin n → ℝ => y j))

section BoundaryCharts

variable {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- Any smooth half-space chart detects boundary points by its zero normal coordinate. -/
theorem isBoundaryPoint_iff_chart_zero
    {e : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) W) {x : W} (hx : x ∈ e.source) :
    (𝓡∂ (n + 1)).IsBoundaryPoint x ↔ (e x).1 0 = 0 := by
  have hi : (𝓡∂ (n + 1)).IsInteriorPoint x ↔ 0 < (e x).1 0 := by
    rw [(𝓡∂ (n + 1)).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) he hx]
    have hmem : e.extend (𝓡∂ (n + 1)) x ∈ interior (e.extend (𝓡∂ (n + 1))).target ↔
        e.extend (𝓡∂ (n + 1)) x ∈ interior (range (𝓡∂ (n + 1))) :=
      ⟨fun h => e.interior_extend_target_subset_interior_range h,
        fun h => e.mem_interior_extend_target (e.map_source hx) h⟩
    rw [hmem, interior_range_modelWithCornersEuclideanHalfSpace]
    rfl
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, hi, not_lt]
  exact ⟨fun h => le_antisymm h (e x).2, fun h => h.le⟩

/-- A chart identifies the manifold boundary with the boundary hyperplane. -/
theorem chart_isImage_boundary
    {e : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) W) :
    e.IsImage ((𝓡∂ (n + 1)).boundary W) (halfSpaceBoundary n) :=
  fun {_} hx => (isBoundaryPoint_iff_chart_zero he hx).symm

/-- The boundary chart induced by the ambient preferred chart at a boundary point. -/
noncomputable def boundaryChartAt (x : (𝓡∂ (n + 1)).boundary W) :
    OpenPartialHomeomorph ((𝓡∂ (n + 1)).boundary W) (Fin n → ℝ) := by
  let : Nonempty ((𝓡∂ (n + 1)).boundary W) := ⟨x⟩
  exact (chart_isImage_boundary (chart_mem_atlas (EuclideanHalfSpace (n + 1)) x.1)).subtype.trans
    (halfSpaceBoundaryHomeomorph n).toOpenPartialHomeomorph

@[simp] theorem boundaryChartAt_source (x : (𝓡∂ (n + 1)).boundary W) :
    (boundaryChartAt x).source =
      Subtype.val ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) x.1).source := by
  simp only [boundaryChartAt, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.IsImage.subtype_source, Homeomorph.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ]

@[simp] theorem boundaryChartAt_target (x : (𝓡∂ (n + 1)).boundary W) :
    (boundaryChartAt x).target = boundaryHalfSpaceInclusion n ⁻¹'
      (chartAt (EuclideanHalfSpace (n + 1)) x.1).target := by
  simp only [boundaryChartAt, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.IsImage.subtype_target, Homeomorph.toOpenPartialHomeomorph_target,
    univ_inter]
  rfl

theorem boundaryChartAt_apply (x y : (𝓡∂ (n + 1)).boundary W)
    (hy : y.1 ∈ (chartAt (EuclideanHalfSpace (n + 1)) x.1).source) :
    boundaryChartAt x y =
      fun i => (chartAt (EuclideanHalfSpace (n + 1)) x.1 y.1).1 i.succ := by
  let : Nonempty ((𝓡∂ (n + 1)).boundary W) := ⟨x⟩
  ext i
  change (((chart_isImage_boundary
    (chart_mem_atlas (EuclideanHalfSpace (n + 1)) x.1)).subtype y).1).1 i.succ = _
  rw [OpenPartialHomeomorph.IsImage.subtype_apply_val _ hy]

theorem boundaryChartAt_symm_apply (x : (𝓡∂ (n + 1)).boundary W) {y : Fin n → ℝ}
    (hy : y ∈ (boundaryChartAt x).target) :
    ((boundaryChartAt x).symm y).1 =
      (chartAt (EuclideanHalfSpace (n + 1)) x.1).symm (boundaryHalfSpaceInclusion n y) := by
  let : Nonempty ((𝓡∂ (n + 1)).boundary W) := ⟨x⟩
  exact OpenPartialHomeomorph.IsImage.subtype_symm_apply_val
    (chart_isImage_boundary (chart_mem_atlas (EuclideanHalfSpace (n + 1)) x.1))
    (show boundaryHalfSpaceInclusion n y ∈
      (chartAt (EuclideanHalfSpace (n + 1)) x.1).target by simpa using hy)

theorem mem_boundaryChartAt_source (x : (𝓡∂ (n + 1)).boundary W) :
    x ∈ (boundaryChartAt x).source := by
  simp only [boundaryChartAt, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.IsImage.subtype_source, Homeomorph.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ, mem_preimage]
  exact mem_chart_source (EuclideanHalfSpace (n + 1)) x.1

/-- A charted-space structure on the actual boundary, with its original subspace topology. -/
@[instance_reducible] noncomputable def boundaryChartedSpace :
    ChartedSpace (Fin n → ℝ) ((𝓡∂ (n + 1)).boundary W) where
  atlas := range boundaryChartAt
  chartAt := boundaryChartAt
  mem_chart_source := mem_boundaryChartAt_source
  chart_mem_atlas x := mem_range_self x

end BoundaryCharts

end PoincareHighDim
