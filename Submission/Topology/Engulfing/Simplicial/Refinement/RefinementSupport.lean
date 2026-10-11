/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Topology.Engulfing.Simplicial.Refinement.RefinementRestriction

/-!
# Supports of refined simplices

A refined simplex whose centroid lies in an old face lies entirely in that face.
This lets a subdivision inherit geometric bounds from an old subcomplex.
-/

namespace PoincareHighDim.Engulfing

open Set Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem SimplicialRefines.convexHull_subset_old_face_of_centroid_mem
    {P K : SimplicialComplex ℝ E} (href : SimplicialRefines P K)
    {s t : Finset E} (hs : s ∈ P.faces) (ht : t ∈ K.faces)
    (hc : s.centroid ℝ id ∈ convexHull ℝ (t : Set E)) :
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  classical
  let u := s.filter (fun x => x ∈ convexHull ℝ (t : Set E))
  have hcu : s.centroid ℝ id ∈ convexHull ℝ (u : Set E) := by
    rw [← href.convexHull_inter_old_face hs ht]
    exact ⟨s.centroid_mem_convexHull (P.nonempty_of_mem_faces hs), hc⟩
  have hu : u.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hcu⟩)
  have hsu := face_subset_of_centroid_mem P hs
    (P.down_closed hs (Finset.filter_subset _ _) hu) hcu
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  exact (Finset.mem_filter.mp (hsu hx)).2

/-- A refined face lying in an old subcomplex has a supporting face in that
subcomplex, even when its vertices were introduced by the subdivision. -/
theorem SimplicialRefines.exists_old_face_of_convexHull_subset
    {P K H : SimplicialComplex ℝ E} (href : SimplicialRefines P K)
    (hHK : H.faces ⊆ K.faces) {s : Finset E} (hs : s ∈ P.faces)
    (hH : convexHull ℝ (s : Set E) ⊆ H.space) :
    ∃ t ∈ H.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp
    (hH (s.centroid_mem_convexHull (P.nonempty_of_mem_faces hs)))
  exact ⟨t, ht, href.convexHull_subset_old_face_of_centroid_mem hs (hHK ht) hct⟩

/-- A refined simplex supported on a union of old subcomplexes is supported
on one of them. -/
theorem SimplicialRefines.convexHull_subset_or_of_subset_union
    {P K H J : SimplicialComplex ℝ E} (href : SimplicialRefines P K)
    (hHK : H.faces ⊆ K.faces) (hJK : J.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ P.faces)
    (hH : convexHull ℝ (s : Set E) ⊆ H.space ∪ J.space) :
    convexHull ℝ (s : Set E) ⊆ H.space ∨ convexHull ℝ (s : Set E) ⊆ J.space := by
  have hc := hH (s.centroid_mem_convexHull (P.nonempty_of_mem_faces hs))
  rcases hc with hc | hc
  · obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp hc
    exact Or.inl ((href.convexHull_subset_old_face_of_centroid_mem hs (hHK ht) hct).trans
      (H.convexHull_subset_space ht))
  · obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp hc
    exact Or.inr ((href.convexHull_subset_old_face_of_centroid_mem hs (hJK ht) hct).trans
      (J.convexHull_subset_space ht))

/-- The same dichotomy with a single old simplex as the second summand. -/
theorem SimplicialRefines.convexHull_subset_or_old_face
    {P K H : SimplicialComplex ℝ E} (href : SimplicialRefines P K)
    (hHK : H.faces ⊆ K.faces) {s t : Finset E} (hs : s ∈ P.faces) (ht : t ∈ K.faces)
    (hH : convexHull ℝ (s : Set E) ⊆ H.space ∪ convexHull ℝ (t : Set E)) :
    convexHull ℝ (s : Set E) ⊆ H.space ∨
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  have hc := hH (s.centroid_mem_convexHull (P.nonempty_of_mem_faces hs))
  rcases hc with hc | hc
  · obtain ⟨u, hu, hcu⟩ := SimplicialComplex.mem_space_iff.mp hc
    exact Or.inl ((href.convexHull_subset_old_face_of_centroid_mem hs (hHK hu) hcu).trans
      (H.convexHull_subset_space hu))
  · exact Or.inr (href.convexHull_subset_old_face_of_centroid_mem hs ht hc)

end PoincareHighDim.Engulfing
