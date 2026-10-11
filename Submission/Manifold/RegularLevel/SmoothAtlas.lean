/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smooth atlases induced from ambient coordinates

Charts on a subspace define its induced smooth structure when their coordinate maps
extend smoothly to ambient neighborhoods and their inverses are smooth as ambient maps.
-/

namespace PoincareHighDim

open Set Topology
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (s : Set M)
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]

/-- Local coordinates on a subspace, with smooth ambient extensions and inverses. -/
structure InducedAtlas where
  chart : s → OpenPartialHomeomorph s E₀
  mem_source : ∀ x, x ∈ (chart x).source
  ambientSource : s → Set M
  open_ambientSource : ∀ x, IsOpen (ambientSource x)
  source_eq : ∀ x, (chart x).source = Subtype.val ⁻¹' ambientSource x
  extension : s → M → E₀
  extension_eq : ∀ x y, y ∈ (chart x).source → extension x y.1 = chart x y
  smooth_extension : ∀ x, ContMDiffOn I 𝓘(ℝ, E₀) ∞ (extension x) (ambientSource x)
  smooth_inverse : ∀ x, ContMDiffOn 𝓘(ℝ, E₀) I ∞
    (fun y => ((chart x).symm y : M)) (chart x).target

namespace InducedAtlas

variable {I s E₀} (A : InducedAtlas I s E₀)

/-- The atlas consists of the specified subspace charts. -/
@[instance_reducible] def chartedSpace : ChartedSpace E₀ s where
  atlas := range A.chart
  chartAt := A.chart
  mem_chart_source := A.mem_source
  chart_mem_atlas x := mem_range_self x

theorem isManifold [IsManifold I ∞ M] :
    letI := A.chartedSpace
    IsManifold 𝓘(ℝ, E₀) ∞ s := by
  let := A.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  have hs : ContMDiffOn 𝓘(ℝ, E₀) 𝓘(ℝ, E₀) ∞
      (fun y => A.extension x' ((A.chart x).symm y))
      ((A.chart x).symm.trans (A.chart x')).source := by
    refine (A.smooth_extension x').comp ((A.smooth_inverse x).mono ?_) ?_
    · exact inter_subset_left
    · intro y hy
      change ((A.chart x).symm y : M) ∈ A.ambientSource x'
      have hy' := hy.2
      rwa [A.source_eq x'] at hy'
  have heq : EqOn (fun y => A.chart x' ((A.chart x).symm y))
      (fun y => A.extension x' ((A.chart x).symm y))
      ((A.chart x).symm.trans (A.chart x')).source := by
    intro y hy
    exact (A.extension_eq x' _ hy.2).symm
  simpa only [modelWithCornersSelf_coe, Function.comp_def, id_eq,
    modelWithCornersSelf_coe_symm, Set.preimage_id, Set.range_id, Set.inter_univ,
    OpenPartialHomeomorph.trans_apply]
    using contMDiffOn_iff_contDiffOn.mp (hs.congr heq)

theorem contMDiff_subtypeVal [IsManifold I ∞ M] :
    letI := A.chartedSpace
    ContMDiff 𝓘(ℝ, E₀) I ∞ (Subtype.val : s → M) := by
  let := A.chartedSpace
  intro x
  rw [contMDiffAt_iff_source]
  simp only [contMDiffWithinAt_univ,
    extChartAt, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
    id_eq, Set.range_id]
  change ContMDiffAt 𝓘(ℝ, E₀) I ∞ (fun y => ((A.chart x).symm y : M))
    (A.chart x x)
  exact (A.smooth_inverse x).contMDiffAt
    ((A.chart x).open_target.mem_nhds ((A.chart x).map_source (A.mem_source x)))

/-- Smoothness into the induced subspace is detected in the ambient manifold. -/
theorem contMDiff_iff [IsManifold I ∞ M]
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    (J : ModelWithCorners ℝ F G) [IsManifold J ∞ N] {f : N → s} :
    letI := A.chartedSpace
    ContMDiff J 𝓘(ℝ, E₀) ∞ f ↔
      Continuous f ∧ ContMDiff J I ∞ (fun x => (f x : M)) := by
  let := A.chartedSpace
  let := A.isManifold
  constructor
  · intro hf
    exact ⟨hf.continuous, A.contMDiff_subtypeVal.comp hf⟩
  · rintro ⟨hc, hf⟩ x
    rw [contMDiffAt_iff_target_of_mem_source (A.mem_source (f x))]
    refine ⟨hc.continuousAt, ?_⟩
    have hx : (f x : M) ∈ A.ambientSource (f x) := by
      have hx := A.mem_source (f x)
      rwa [A.source_eq] at hx
    have he := (A.smooth_extension (f x)).contMDiffAt
      ((A.open_ambientSource (f x)).mem_nhds hx)
    apply (he.comp x (hf x)).congr_of_eventuallyEq
    have hnear : ∀ᶠ y in 𝓝 x, f y ∈ (A.chart (f x)).source :=
      hc.continuousAt.preimage_mem_nhds
        ((A.chart (f x)).open_source.mem_nhds (A.mem_source (f x)))
    filter_upwards [hnear] with y hy
    exact (A.extension_eq (f x) (f y) hy).symm

end InducedAtlas
end PoincareHighDim
