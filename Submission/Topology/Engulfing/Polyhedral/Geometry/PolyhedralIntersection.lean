/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Topology.Engulfing.Approximation.GeneralPosition
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Intersections of faces in general position

Small unions of vertices have the usual simplex intersection property. Larger unions span
the ambient Euclidean space, and intersecting face spans have the expected dimension.
-/

namespace PoincareHighDim.Engulfing

open Set Metric Topology
open Module

variable {n : ℕ} {ι : Type*} [DecidableEq ι]
    {w : ι → EuclideanSpace ℝ (Fin n)} {u s t : Finset ι}

/-- Independent vertices force two convex faces to meet exactly in their common face. -/
theorem convexHull_inter_of_affineIndependent_union
    (hw : AffineIndependent ℝ (fun i : (s ∪ t : Finset ι) => w i)) :
    convexHull ℝ (w '' (s : Set ι)) ∩ convexHull ℝ (w '' (t : Set ι)) =
      convexHull ℝ (w '' ((s ∩ t : Finset ι) : Set ι)) := by
  classical
  have hinj : Set.InjOn w ((s ∪ t : Finset ι) : Set ι) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hw.injective (show w (⟨x, hx⟩ : (s ∪ t : Finset ι)) =
      w (⟨y, hy⟩ : (s ∪ t : Finset ι)) from hxy))
  have himage : AffineIndependent ℝ
      ((↑) : ((s ∪ t).image w : Finset (EuclideanSpace ℝ (Fin n))) →
        EuclideanSpace ℝ (Fin n)) := by
    have h := hw.range
    have heq : range (fun i : (s ∪ t : Finset ι) => w i) =
        ((s ∪ t).image w : Set (EuclideanSpace ℝ (Fin n))) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact Finset.mem_image.mpr ⟨i, i.2, rfl⟩
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [heq] at h
    exact h
  have hconv := himage.convexHull_inter
    (Finset.image_subset_image Finset.subset_union_left)
    (Finset.image_subset_image Finset.subset_union_right)
  have heq : w '' ((s : Set ι) ∩ (t : Set ι)) = w '' (s : Set ι) ∩ w '' (t : Set ι) :=
    Set.image_inter_on (fun x hx y hy => hinj (Finset.mem_union.mpr (Or.inr hx))
      (Finset.mem_union.mpr (Or.inl hy)))
  simpa only [Finset.coe_image, Finset.coe_inter, ← heq] using hconv.symm

/-- The simplex intersection property for faces whose combined vertex count is at most
one more than the ambient dimension. -/
theorem InGeneralPositionOn.convexHull_inter (hw : InGeneralPositionOn u w)
    (hs : s ⊆ u) (ht : t ⊆ u) (hcard : (s ∪ t).card ≤ n + 1) :
    convexHull ℝ (w '' (s : Set ι)) ∩ convexHull ℝ (w '' (t : Set ι)) =
      convexHull ℝ (w '' ((s ∩ t : Finset ι) : Set ι)) :=
  convexHull_inter_of_affineIndependent_union (hw (s ∪ t) (Finset.union_subset hs ht) hcard)

omit [DecidableEq ι] in
/-- A general-position family with at least `n + 1` vertices spans the ambient space. -/
theorem InGeneralPositionOn.affineSpan_eq_top (hw : InGeneralPositionOn u w)
    (hs : s ⊆ u) (hcard : n + 1 ≤ s.card) : affineSpan ℝ (w '' (s : Set ι)) = ⊤ := by
  obtain ⟨r, hrs, hrcard⟩ := Finset.exists_subset_card_eq hcard
  have hr := hw r (hrs.trans hs) hrcard.le
  have hrspan : affineSpan ℝ (w '' (r : Set ι)) = ⊤ := by
    rw [Set.image_eq_range]
    apply hr.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simpa using hrcard
  apply top_unique
  rw [← hrspan]
  exact affineSpan_mono ℝ (image_mono hrs)

omit [DecidableEq ι] in
/-- The dimension of an independent nonempty finite affine span, in a form without
truncated subtraction. -/
theorem finrank_direction_affineSpan_add_one
    (hw : AffineIndependent ℝ (fun i : s => w i)) (hs : s.Nonempty) :
    finrank ℝ (affineSpan ℝ (w '' (s : Set ι))).direction + 1 = s.card := by
  have : Nonempty s := hs.to_subtype
  rw [direction_affineSpan, Set.image_eq_range]
  simpa using hw.finrank_vectorSpan_add_one

/-- Two nonempty intersecting face spans in general position have exactly the expected
intersection dimension as soon as their combined vertices span the ambient space. -/
theorem InGeneralPositionOn.finrank_affineSpan_inf_add_eq
    (hw : InGeneralPositionOn u w) (hs : s ⊆ u) (ht : t ⊆ u)
    (hscard : s.card ≤ n + 1) (htcard : t.card ≤ n + 1)
    (hlarge : n + 1 ≤ (s ∪ t).card)
    (hmeet : ((affineSpan ℝ (w '' (s : Set ι)) : Set (EuclideanSpace ℝ (Fin n))) ∩
      (affineSpan ℝ (w '' (t : Set ι)) : Set (EuclideanSpace ℝ (Fin n)))).Nonempty) :
    finrank ℝ ((affineSpan ℝ (w '' (s : Set ι))) ⊓
      (affineSpan ℝ (w '' (t : Set ι)))).direction + n + 2 = s.card + t.card := by
  obtain ⟨p, hps, hpt⟩ := hmeet
  have hsne : s.Nonempty := by
    have h := (affineSpan_nonempty (k := ℝ)).mp ⟨p, hps⟩
    obtain ⟨_, ⟨i, hi, rfl⟩⟩ := h
    exact ⟨i, hi⟩
  have htne : t.Nonempty := by
    have h := (affineSpan_nonempty (k := ℝ)).mp ⟨p, hpt⟩
    obtain ⟨_, ⟨i, hi, rfl⟩⟩ := h
    exact ⟨i, hi⟩
  have hsdim := finrank_direction_affineSpan_add_one (hw s hs hscard) hsne
  have htdim := finrank_direction_affineSpan_add_one (hw t ht htcard) htne
  have hsup : affineSpan ℝ (w '' (s : Set ι)) ⊔ affineSpan ℝ (w '' (t : Set ι)) = ⊤ := by
    rw [← AffineSubspace.span_union, ← image_union, ← Finset.coe_union]
    exact hw.affineSpan_eq_top (Finset.union_subset hs ht) hlarge
  have hdir : (affineSpan ℝ (w '' (s : Set ι))).direction ⊔
      (affineSpan ℝ (w '' (t : Set ι))).direction = ⊤ := by
    rw [← AffineSubspace.direction_sup_eq_sup_direction hps hpt, hsup,
      AffineSubspace.direction_top]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (affineSpan ℝ (w '' (s : Set ι))).direction
    (affineSpan ℝ (w '' (t : Set ι))).direction
  rw [hdir, finrank_top, finrank_euclideanSpace_fin] at hdim
  rw [AffineSubspace.direction_inf_of_mem hps hpt]
  omega

/-- The intersection of two convex faces lies in an affine subspace of the expected
dimension. This form can be applied directly to the images of faces of a piecewise linear map. -/
theorem InGeneralPositionOn.exists_affineSubspace_convexHull_inter
    (hw : InGeneralPositionOn u w) (hs : s ⊆ u) (ht : t ⊆ u)
    (hscard : s.card ≤ n + 1) (htcard : t.card ≤ n + 1)
    (hlarge : n + 1 ≤ (s ∪ t).card)
    (hmeet : (convexHull ℝ (w '' (s : Set ι)) ∩
      convexHull ℝ (w '' (t : Set ι))).Nonempty) :
    ∃ P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
      convexHull ℝ (w '' (s : Set ι)) ∩ convexHull ℝ (w '' (t : Set ι)) ⊆ P ∧
        finrank ℝ P.direction + n + 2 = s.card + t.card := by
  have hsub : convexHull ℝ (w '' (s : Set ι)) ∩ convexHull ℝ (w '' (t : Set ι)) ⊆
      (affineSpan ℝ (w '' (s : Set ι)) : Set (EuclideanSpace ℝ (Fin n))) ∩
      (affineSpan ℝ (w '' (t : Set ι)) : Set (EuclideanSpace ℝ (Fin n))) :=
    fun _ hx => ⟨convexHull_subset_affineSpan _ hx.1, convexHull_subset_affineSpan _ hx.2⟩
  exact ⟨affineSpan ℝ (w '' (s : Set ι)) ⊓ affineSpan ℝ (w '' (t : Set ι)), hsub,
    hw.finrank_affineSpan_inf_add_eq hs ht hscard htcard hlarge (hmeet.mono hsub)⟩

end PoincareHighDim.Engulfing
