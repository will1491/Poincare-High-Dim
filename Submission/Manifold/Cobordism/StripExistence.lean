/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.LocalBoundaryAssembly
import Submission.Manifold.Cobordism.OpenStrip
import Submission.Manifold.Cobordism.EmbeddedLocalBoundary

/-! # Presenting a compact smooth triad as a regular strip -/

namespace PoincareHighDim
namespace SmoothTriad

open Set Topology
open scoped Manifold ContDiff

universe u

variable {m : ℕ} {W V₀ V₁ M : Type u} {H : Type*}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (m + 1)) W]
    [TopologicalSpace V₀] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1 - 1))) V₀]
    [TopologicalSpace V₁] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1 - 1))) V₁]
    [TopologicalSpace M] [TopologicalSpace H] [ChartedSpace H M]
    (T : SmoothTriad (m + 1) W V₀ V₁)
    (I : ModelWithCorners ℝ (Fin (m + 1) → ℝ) H)

/-- Compactness and the local signed boundary descriptions produce the full regular-strip
data, with the original boundary labels and smooth lifting property. -/
theorem nonempty_openStripPresentation_of_localBoundaryFunctions
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (e : W → M) (he : IsEmbedding e) (hse : ContMDiff (𝓡∂ (m + 1)) I ∞ e)
    (hD : ∀ x, (mfderiv (𝓡∂ (m + 1)) I e x).IsInvertible)
    (hlift :
      ∀ {EN HN : Type} {N : Type u} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
        [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
        (J : ModelWithCorners ℝ EN HN) [IsManifold J ∞ N] (k : N → W),
        Continuous k → ContMDiff J I ∞ (e ∘ k) → ContMDiff J (𝓡∂ (m + 1)) ∞ k)
    (hlocal : ∀ b : (𝓡∂ (m + 1)).boundary W,
      Nonempty (StripFunction.LocalBoundaryFunction I (range e)
        (e '' (𝓡∂ (m + 1)).boundary W) (e b.1))) :
    Nonempty (T.OpenStripPresentation (M := M) I) := by
  let := T.smooth
  let := T.compact
  let B := e '' (𝓡∂ (m + 1)).boundary W
  let B₀ := range (e ∘ T.incoming)
  let B₁ := range (e ∘ T.outgoing)
  have hB : B = B₀ ∪ B₁ := by
    dsimp only [B, B₀, B₁]
    rw [T.boundary_eq, image_union, range_comp, range_comp]
  have hB₀S : B₀ ⊆ range e := range_comp_subset_range T.incoming e
  have hB₁S : B₁ ⊆ range e := range_comp_subset_range T.outgoing e
  have hB₀ : IsCompact B₀ := by
    change IsCompact (range (e ∘ T.incoming))
    rw [range_comp]
    exact T.isCompact_incoming.image he.continuous
  have hB₁ : IsCompact B₁ := by
    change IsCompact (range (e ∘ T.outgoing))
    rw [range_comp]
    exact T.isCompact_outgoing.image he.continuous
  have hdisj : Disjoint B₀ B₁ := by
    apply Set.disjoint_left.mpr
    rintro x ⟨v, hv⟩ ⟨w, hw⟩
    exact T.incoming_ne_outgoing v w (he.injective (hv.trans hw.symm))
  have hfront : frontier (range e) = B := by
    apply Subset.antisymm (frontier_range_subset_image_boundary hse hD)
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨L⟩ := hlocal ⟨w, hw⟩
    exact L.mem_frontier ⟨w, hw, rfl⟩ (mem_range_self w)
  have hlocal₀ : ∀ b ∈ B₀, Nonempty (StripFunction.LocalBoundaryFunction I (range e) B₀ b) := by
    rintro b ⟨v, rfl⟩
    obtain ⟨L⟩ := hlocal ⟨T.incoming v, T.incoming_mem_boundary v⟩
    exact ⟨L.of_boundary_piece hB hdisj hB₁.isClosed (mem_range_self v)⟩
  have hlocal₁ : ∀ b ∈ B₁, Nonempty (StripFunction.LocalBoundaryFunction I (range e) B₁ b) := by
    rintro b ⟨v, rfl⟩
    obtain ⟨L⟩ := hlocal ⟨T.outgoing v, T.outgoing_mem_boundary v⟩
    exact ⟨L.of_boundary_piece (hB.trans (union_comm _ _)) hdisj.symm hB₀.isClosed
      (mem_range_self v)⟩
  apply OpenStripPresentation.nonempty_of_regular_strip_function (T := T) (I := I) e he hse hlift
  exact StripFunction.exists_regular_strip_function_of_local_boundary I
    (isCompact_range he.continuous) hB₀ hB₁ hB₀S hB₁S hdisj (hfront.trans hB)
    hlocal₀ hlocal₁

/-- Every compact smooth triad has a regular-strip presentation in a boundaryless
ambient manifold, preserving its original smooth structure. The ambient manifold is
an open neighborhood of a smooth copy of the triad in its own interior. -/
theorem nonempty_openStripPresentation :
    letI := T.smooth
    letI := (ManifoldInterior.inducedAtlas (𝓡∂ (m + 1)) (W := W)).chartedSpace
    Nonempty (T.OpenStripPresentation (M := (𝓡∂ (m + 1)).interior W)
      (interiorModel (m + 1))) := by
  let := T.smooth
  let := T.compact
  let := T.hausdorff
  let := (ManifoldInterior.inducedAtlas (𝓡∂ (m + 1)) (W := W)).chartedSpace
  let := interior_isManifold (n := m + 1) (W := W)
  let := ManifoldInterior.sigmaCompactSpace (𝓡∂ (m + 1)) (W := W)
  obtain ⟨C⟩ := nonempty_inwardCopy (n := m) (W := W)
  apply T.nonempty_openStripPresentation_of_localBoundaryFunctions (interiorModel (m + 1))
    C.embedding C.isEmbedding C.contMDiff_embedding C.isInvertible_mfderiv_embedding
  · intro EN HN N _ _ _ _ _ J _ k hk hs
    exact C.smooth_lift J hk hs
  · exact nonempty_localBoundaryFunction_of_embedding C.embedding C.isEmbedding
      C.contMDiff_embedding C.isInvertible_mfderiv_embedding

end SmoothTriad
end PoincareHighDim
