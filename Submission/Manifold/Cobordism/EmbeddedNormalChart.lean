/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.EmbeddedBoundaryChart
import Submission.Manifold.Cobordism.AmbientCollar
import Submission.Manifold.Cobordism.HalfSpaceThickening

/-!
# Ambient normal charts for an embedded manifold boundary

Thickening the actual boundary parametrization in its derivative's normal direction
produces an ambient smooth chart. Its zero section is the original embedded boundary.
-/

namespace PoincareHighDim

open Set Topology Filter Manifold
open scoped Manifold ContDiff

section AmbientChart

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (J : ModelWithCorners ℝ F H) [J.Boundaryless] [IsManifold J ∞ M]

/-- An extended chart of a boundaryless manifold is a partial diffeomorphism. -/
noncomputable def ambientChartDiffeomorph (x : M) :
    PartialDiffeomorph J 𝓘(ℝ, F) M F ∞ where
  toPartialEquiv := extChartAt J x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := J) (x := x) (n := ∞))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

end AmbientChart

section NormalChart

variable {n : ℕ} {W M F H : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {J : ModelWithCorners ℝ F H} [J.Boundaryless] [IsManifold J ∞ M]
    (f : W → M) (b : (𝓡∂ (n + 1)).boundary W)

theorem boundaryChartAt_eq_boundaryCoordinateCenter :
    boundaryChartAt b b = boundaryCoordinateCenter b := by
  rw [boundaryChartAt_apply b b (mem_chart_source _ _)]
  rfl

omit [J.Boundaryless] [IsManifold J ∞ M] in
theorem embeddedBoundaryExpression_zero {z : Fin n → ℝ}
    (hz : z ∈ (boundaryChartAt b).target) :
    embeddedBoundaryExpression (J := J) f b (z, 0) =
      extChartAt J (f b.1) (f ((boundaryChartAt b).symm z).1) := by
  rw [boundaryChartAt_symm_apply b hz]
  change (extChartAt J (f b.1))
    (f ((chartAt (EuclideanHalfSpace (n + 1)) b.1).symm
      ((𝓡∂ (n + 1)).symm (boundaryCoordinateInclusion n z)))) = _
  rw [model_symm_boundaryCoordinateInclusion]

/-- The coordinate inverse-function construction and its realization in the ambient
manifold. Keeping both charts records the actual normal direction used in the construction. -/
structure EmbeddedNormalChart where
  derivative : ((Fin n → ℝ) × ℝ) ≃L[ℝ] F
  hasFDerivWithinAt : HasFDerivWithinAt (embeddedBoundaryExpression (J := J) f b)
    (derivative : ((Fin n → ℝ) × ℝ) →L[ℝ] F) {p | 0 ≤ p.2}
    (boundaryCoordinateCenter b, 0)
  coordinateChart : PartialDiffeomorph 𝓘(ℝ, (Fin n → ℝ) × ℝ) 𝓘(ℝ, F)
    ((Fin n → ℝ) × ℝ) F ∞
  coordinate_center_mem : (boundaryCoordinateCenter b, 0) ∈ coordinateChart.source
  coordinate_eq : ∀ p ∈ coordinateChart.source,
    coordinateChart p = embeddedBoundaryExpression (J := J) f b (p.1, 0) + derivative (0, p.2)
  chart : PartialDiffeomorph 𝓘(ℝ, (Fin n → ℝ) × ℝ) J ((Fin n → ℝ) × ℝ) M ∞
  center_mem : (boundaryCoordinateCenter b, 0) ∈ chart.source
  source_subset_coordinate : chart.source ⊆ coordinateChart.source
  chart_eq : ∀ p, chart p = (extChartAt J (f b.1)).symm (coordinateChart p)
  chart_symm_eq : ∀ y, chart.symm y = coordinateChart.symm (extChartAt J (f b.1) y)
  zero_section : ∀ z, (z, 0) ∈ chart.source →
    z ∈ (boundaryChartAt b).target ∧ chart (z, 0) = f ((boundaryChartAt b).symm z).1

namespace EmbeddedNormalChart

variable {f b} (C : EmbeddedNormalChart (J := J) f b)

omit [J.Boundaryless] [IsManifold J ∞ M] in
theorem coordinateChart_center :
    C.coordinateChart (boundaryCoordinateCenter b, 0) = extChartAt J (f b.1) (f b.1) := by
  rw [C.coordinate_eq _ C.coordinate_center_mem,
    show C.derivative (0, (0 : ℝ)) = 0 from map_zero C.derivative, add_zero,
    embeddedBoundaryExpression_center]

omit [J.Boundaryless] [IsManifold J ∞ M] in
theorem hasFDerivAt_coordinateChart :
    HasFDerivAt C.coordinateChart (C.derivative : ((Fin n → ℝ) × ℝ) →L[ℝ] F)
      (boundaryCoordinateCenter b, 0) := by
  apply (HalfSpaceThickening.hasFDerivAt_thickening C.derivative
    C.hasFDerivWithinAt).congr_of_eventuallyEq
  filter_upwards [C.coordinateChart.open_source.mem_nhds C.coordinate_center_mem] with p hp
  exact C.coordinate_eq p hp

omit [J.Boundaryless] [IsManifold J ∞ M] in
theorem formula {p : (Fin n → ℝ) × ℝ} (hp : p ∈ C.chart.source) :
    C.chart p = (extChartAt J (f b.1)).symm
      (embeddedBoundaryExpression (J := J) f b (p.1, 0) + C.derivative (0, p.2)) := by
  rw [C.chart_eq, C.coordinate_eq _ (C.source_subset_coordinate hp)]

omit [J.Boundaryless] [IsManifold J ∞ M] in
theorem chart_center : C.chart (boundaryCoordinateCenter b, 0) = f b.1 := by
  rw [(C.zero_section _ C.center_mem).2, ← boundaryChartAt_eq_boundaryCoordinateCenter b,
    (boundaryChartAt b).left_inv (mem_boundaryChartAt_source b)]

end EmbeddedNormalChart

/-- A smooth map with invertible differential at a boundary point has a normal chart
whose zero section is its actual boundary parametrization. -/
theorem nonempty_embeddedNormalChart
    (hf : ContMDiff (𝓡∂ (n + 1)) J ∞ f)
    (hD : (mfderiv (𝓡∂ (n + 1)) J f b.1).IsInvertible) :
    Nonempty (EmbeddedNormalChart (J := J) f b) := by
  obtain ⟨D, hD⟩ := embeddedBoundaryExpression_hasFDerivWithinAt f b hf hD
  obtain ⟨U, hU, hbU, hq⟩ := exists_contDiffOn_embeddedBoundaryExpression f b hf
  obtain ⟨Ω, hbΩ, hΩ⟩ := AmbientCollar.isLocalDiffeomorphAt_thickening_of_halfspace_smooth
    hU hbU hq D hD
  let A := ambientChartDiffeomorph J (f b.1)
  let V : Set (Fin n → ℝ) := (boundaryChartAt b).target ∩
    (fun z => f ((boundaryChartAt b).symm z).1) ⁻¹' A.source
  have hV : IsOpen V :=
    (hf.continuous.comp_continuousOn
      (contMDiffOn_boundaryChartAt_symm b).continuousOn).isOpen_inter_preimage
        (boundaryChartAt b).open_target A.open_source
  have hbV : boundaryCoordinateCenter b ∈ V := by
    rw [← boundaryChartAt_eq_boundaryCoordinateCenter b]
    refine ⟨(boundaryChartAt b).map_source (mem_boundaryChartAt_source b), ?_⟩
    change f ((boundaryChartAt b).symm ((boundaryChartAt b) b)).1 ∈ A.source
    rw [(boundaryChartAt b).left_inv (mem_boundaryChartAt_source b)]
    exact mem_extChartAt_source _
  let Ψ := Ω.trans A.symm
  have hbΨ : (boundaryCoordinateCenter b, 0) ∈ Ψ.source := by
    refine ⟨hbΩ, ?_⟩
    change Ω (boundaryCoordinateCenter b, 0) ∈ (extChartAt J (f b.1)).target
    rw [← hΩ hbΩ]
    dsimp only
    rw [show D (0, (0 : ℝ)) = 0 from map_zero D, add_zero,
      embeddedBoundaryExpression_center]
    exact (extChartAt J (f b.1)).map_source (mem_extChartAt_source _)
  let R := Ψ.toOpenPartialHomeomorph.restrOpen (V ×ˢ (univ : Set ℝ))
    (hV.prod isOpen_univ)
  let Φ : PartialDiffeomorph 𝓘(ℝ, (Fin n → ℝ) × ℝ) J ((Fin n → ℝ) × ℝ) M ∞ := {
    R with
    contMDiffOn_toFun := Ψ.contMDiffOn_toFun.mono inter_subset_left
    contMDiffOn_invFun := Ψ.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨{
    derivative := D
    hasFDerivWithinAt := hD
    coordinateChart := Ω
    coordinate_center_mem := hbΩ
    coordinate_eq := fun p hp => (hΩ hp).symm
    chart := Φ
    center_mem := ⟨hbΨ, hbV, mem_univ _⟩
    source_subset_coordinate := fun p hp => hp.1.1
    chart_eq := fun _ => rfl
    chart_symm_eq := fun _ => rfl
    zero_section := ?_ }⟩
  intro z hz
  have hzV : z ∈ V := hz.2.1
  refine ⟨hzV.1, ?_⟩
  change (extChartAt J (f b.1)).symm (Ω (z, 0)) = _
  rw [← hΩ hz.1.1]
  dsimp only
  rw [show D (0, (0 : ℝ)) = 0 from map_zero D, add_zero,
    embeddedBoundaryExpression_zero f b hzV.1]
  exact (extChartAt J (f b.1)).left_inv hzV.2

end NormalChart
end PoincareHighDim
