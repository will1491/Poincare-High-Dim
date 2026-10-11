/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Topology.Engulfing.Simplicial.Subcomplex.SubcomplexInterior
import Submission.Topology.Engulfing.Newman.Data.NewmanLocalData

/-!
# Fixed chart formulas from a local affine model

When the chart core meets the fixed part only inside a source subcomplex,
every relevant fixed face belongs to that subcomplex. Local affine formulas
then supply the full fixed-part chart data.
-/

namespace PoincareHighDim.Engulfing

open Set Geometry Topology

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [TopologicalSpace M] {n p : ℕ}

theorem fixed_affine_of_local_model
    (K L D : SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces) (hDK : D.faces ⊆ K.faces)
    (f : K.space → M) (b : BufferedChart M n) (a : E → EuclideanSpace ℝ (Fin n))
    (ha : ∀ s ∈ D.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn a A (convexHull ℝ (s : Set E)))
    (hcoords : ∀ x : K.space, x.val ∈ L.space → x.val ∈ D.space → b.chart (f x) = a x.val)
    (hcore : ∀ x : K.space, x.val ∈ L.space → f x ∈ b.core →
      x ∈ interior (Subtype.val ⁻¹' D.space)) :
    ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → f x ∈ b.core → b.chart (f x) = A x.val := by
  classical
  intro s hs
  by_cases hmeet : ∃ x : K.space, x.val ∈ convexHull ℝ (s : Set E) ∧ f x ∈ b.core
  · obtain ⟨x, hxs, hxcore⟩ := hmeet
    have hsD : s ∈ D.faces := face_mem_subcomplex_of_mem_interior K D hDK (hLK hs) hxs
      (hcore x (L.convexHull_subset_space hs hxs) hxcore)
    obtain ⟨A, hA⟩ := ha s hsD
    refine ⟨A, fun y hy _ => ?_⟩
    exact (hcoords y (L.convexHull_subset_space hs hy) (D.convexHull_subset_space hsD hy)).trans (hA hy)
  · exact ⟨AffineMap.const ℝ E 0, fun x hx hxcore => (hmeet ⟨x, hx, hxcore⟩).elim⟩

noncomputable def LocalPLChartData.of_local_model
    (K L D : SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces) (hDK : D.faces ⊆ K.faces)
    (f : C(K.space, M)) (b : BufferedChart M n) (a : E → EuclideanSpace ℝ (Fin n))
    (ha : ∀ s ∈ D.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn a A (convexHull ℝ (s : Set E)))
    (hcoords : ∀ x : K.space, x.val ∈ L.space → x.val ∈ D.space → b.chart (f x) = a x.val)
    (hcore : ∀ x : K.space, x.val ∈ L.space → f x ∈ b.core →
      x ∈ interior (Subtype.val ⁻¹' D.space))
    (hinj : InjOn f (Subtype.val ⁻¹' L.space)) (X : Set M)
    (O : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hO : O.faces.Finite)
    (hOd : ∀ s ∈ O.faces, s.card ≤ p + 1) (hXO : b.chart '' (X ∩ b.core) ⊆ O.space) :
    LocalPLChartData K L f X n p where
  toBufferedChart := b
  fixed_affine := fixed_affine_of_local_model K L D hLK hDK f b a ha hcoords hcore
  fixed_injective := by
    intro x hx y hy he
    exact hinj hx.1 hy.1 (b.chart.injOn hx.2.1 hy.2.1 he)
  obstacle := O
  obstacle_finite := hO
  obstacle_dimension := hOd
  obstacle_contains := hXO

end PoincareHighDim.Engulfing
