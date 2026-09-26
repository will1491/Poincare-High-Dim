import Submission.Topology.Engulfing.SubcomplexNeighborhood

/-!
# Whole-face chart neighborhoods from a small image mesh

Faces meeting an inner chart ball stay inside a larger ball when their raw
coordinate oscillation is small. The protected neighborhood can therefore be
formed from whole existing faces, preserving general-position cells.
-/

namespace PoincareHighDim.Engulfing

open Set Metric Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem image_simplicialNeighborhood_subset_ball
    (K : SimplicialComplex ℝ E) (a : E → F) (c : F) {r δ : ℝ}
    (hmesh : ∀ s ∈ K.faces, ∀ x ∈ convexHull ℝ (s : Set E),
      ∀ y ∈ convexHull ℝ (s : Set E), dist (a x) (a y) < δ) :
    a '' (simplicialNeighborhood K (a ⁻¹' ball c r)).space ⊆ ball c (r + δ) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨t, ht, hst, y, hyt, hy⟩ := hs.2
  have hxy := hmesh t ht x (convexHull_mono hst hxs) y hyt
  have hyc := mem_ball.mp hy
  apply mem_ball.mpr
  exact (dist_triangle (a x) (a y) c).trans_lt (by linarith)

theorem chart_preimage_subset_simplicialNeighborhood
    (K : SimplicialComplex ℝ E) (a : E → F) (c : F) (r : ℝ) :
    K.space ∩ a ⁻¹' ball c r ⊆ (simplicialNeighborhood K (a ⁻¹' ball c r)).space := by
  classical
  intro x hx
  exact subset_simplicialNeighborhood K _ ⟨hx.2, hx.1⟩

end PoincareHighDim.Engulfing
