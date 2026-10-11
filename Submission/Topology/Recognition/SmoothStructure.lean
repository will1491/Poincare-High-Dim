/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Transporting smooth structures through homeomorphisms

A homeomorphism to a smooth manifold pulls its atlas back to a smooth atlas.  In particular,
a homeomorphism to a sphere supplies the smooth structure requested by the smoothability
statement in `Submission.External`, without any dependence on that external statement.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff
open Metric Set

noncomputable section

section Transport

variable {H M N : Type*} [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H N]

/-- Pull an atlas back along a homeomorphism, using the full original atlas. -/
@[instance_reducible]
def pullbackChartedSpace (h : M ≃ₜ N) : ChartedSpace H M where
  atlas := h.transOpenPartialHomeomorph '' atlas H N
  chartAt x := h.transOpenPartialHomeomorph (chartAt H (h x))
  mem_chart_source x := mem_chart_source H (h x)
  chart_mem_atlas x := ⟨chartAt H (h x), chart_mem_atlas H (h x), rfl⟩

omit [ChartedSpace H N] in
/-- Pulling back both charts leaves their coordinate transition unchanged. -/
theorem pullbackChartedSpace_transition (h : M ≃ₜ N)
    (e e' : OpenPartialHomeomorph N H) :
    (h.transOpenPartialHomeomorph e).symm.trans (h.transOpenPartialHomeomorph e') =
      e.symm.trans e' := by
  apply OpenPartialHomeomorph.ext
  · intro x
    simp
  · intro x
    simp
  · ext x
    simp

/-- The pullback atlas has the same structure groupoid as the original atlas. -/
theorem pullbackChartedSpace_hasGroupoid (h : M ≃ₜ N) (G : StructureGroupoid H)
    [HasGroupoid N G] :
    letI := pullbackChartedSpace (H := H) h
    HasGroupoid M G := by
  let := pullbackChartedSpace (H := H) h
  constructor
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  rw [pullbackChartedSpace_transition]
  exact G.compatible he he'

end Transport

/-- A homeomorphism to a manifold transports its smooth structure to the source. -/
theorem exists_manifold_structure_of_homeomorph
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (r : ℕ∞ω)
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I r N] (h : M ≃ₜ N) :
    ∃ cs : ChartedSpace H M, @IsManifold 𝕜 _ E _ _ H _ I r M _ cs := by
  let := pullbackChartedSpace (H := H) h
  have := pullbackChartedSpace_hasGroupoid h (contDiffGroupoid r I)
  exact ⟨inferInstance, IsManifold.mk' I r M⟩

/-- Every space homeomorphic to the standard sphere admits a compatible smooth structure. -/
theorem exists_smooth_structure_of_homeomorph_sphere {n : ℕ} {M : Type*}
    [TopologicalSpace M]
    (h : M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) M,
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _ (𝓡 n) ∞ M _
        cs :=
  exists_manifold_structure_of_homeomorph (𝓡 n) ∞ h

end

end PoincareHighDim
