/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.BoundarySmooth
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Local smooth boundary collars

The standard half-space is the product of its boundary coordinates and an inward
half-line. Composing these product coordinates with an ambient inverse chart gives
local smooth collars of the boundary of an arbitrary smooth manifold with boundary.
-/

namespace PoincareHighDim

open Set Topology WithLp
open scoped Manifold ContDiff

/-- Product coordinates on the half-space, with the half-line as the normal coordinate. -/
noncomputable def halfSpaceProductHomeomorph (n : ℕ) :
    ((Fin n → ℝ) × EuclideanHalfSpace 1) ≃ₜ EuclideanHalfSpace (n + 1) where
  toFun p := ⟨toLp 2 (Fin.cons (p.2.1 0) p.1), by simpa using p.2.2⟩
  invFun z := (fun i => z.1 i.succ, ⟨toLp 2 (fun _ : Fin 1 => z.1 0), z.2⟩)
  left_inv p := by
    apply Prod.ext
    · ext i; simp
    · apply Subtype.ext
      apply PiLp.ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
  right_inv z := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (PiLp.continuous_apply 2 _ 0).comp
        (continuous_subtype_val.comp continuous_snd)
    · exact (continuous_apply j).comp continuous_fst
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun i => (PiLp.continuous_apply 2 _ i.succ).comp
        continuous_subtype_val
    · apply Continuous.subtype_mk
      exact (PiLp.continuous_toLp 2 _).comp
        (continuous_pi fun _ => (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val)

/-- The product half-space coordinates are smooth in both directions. -/
noncomputable def halfSpaceProductDiffeomorph (n : ℕ) :
    ((Fin n → ℝ) × EuclideanHalfSpace 1) ≃ₘ⟮(𝓘(ℝ, Fin n → ℝ)).prod (𝓡∂ 1),
      𝓡∂ (n + 1)⟯ EuclideanHalfSpace (n + 1) where
  toEquiv := (halfSpaceProductHomeomorph n).toEquiv
  contMDiff_toFun := by
    let L : ((Fin n → ℝ) × EuclideanSpace ℝ (Fin 1)) →
        EuclideanSpace ℝ (Fin (n + 1)) := fun p => toLp 2 (Fin.cons (p.2 0) p.1)
    have hL : ContDiff ℝ ∞ L := by
      apply PiLp.contDiff_toLp.comp
      apply contDiff_pi.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero, Function.comp_def] using
          ((contDiff_apply ℝ ℝ 0).comp (PiLp.contDiff_ofLp.comp contDiff_snd) :
            ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 1) => p.2 0))
      · simpa only [Fin.cons_succ, Function.comp_def] using
          ((contDiff_apply ℝ ℝ j).comp contDiff_fst :
            ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 1) => p.1 j))
    have hp : ContMDiff ((𝓘(ℝ, Fin n → ℝ)).prod (𝓡∂ 1))
        𝓘(ℝ, (Fin n → ℝ) × EuclideanSpace ℝ (Fin 1)) ∞
        (fun p : (Fin n → ℝ) × EuclideanHalfSpace 1 => (p.1, p.2.1)) :=
      contMDiff_fst.prodMk_space ((𝓡∂ 1).contMDiff.comp contMDiff_snd)
    have h := (𝓡∂ (n + 1)).contMDiffOn_symm.comp
      (hL.contMDiff.comp hp).contMDiffOn
      (show MapsTo (fun p : (Fin n → ℝ) × EuclideanHalfSpace 1 => L (p.1, p.2.1))
        univ (range (𝓡∂ (n + 1))) from
        fun p _ => ⟨halfSpaceProductHomeomorph n p, rfl⟩)
    apply contMDiffOn_univ.mp
    apply h.congr
    intro p _
    exact ((𝓡∂ (n + 1)).left_inv (halfSpaceProductHomeomorph n p)).symm
  contMDiff_invFun := by
    let L : EuclideanSpace ℝ (Fin (n + 1)) →
        ((Fin n → ℝ) × EuclideanSpace ℝ (Fin 1)) := fun z =>
      (fun i => z i.succ, toLp 2 (fun _ : Fin 1 => z 0))
    have hL : ContDiff ℝ ∞ L := by
      apply ContDiff.prodMk
      · exact contDiff_pi.mpr fun i => (contDiff_apply ℝ ℝ i.succ).comp PiLp.contDiff_ofLp
      · exact PiLp.contDiff_toLp.comp
          (contDiff_pi.mpr fun _ => (contDiff_apply ℝ ℝ 0).comp PiLp.contDiff_ofLp)
    have hreal := hL.contMDiff.comp (𝓡∂ (n + 1)).contMDiff
    have hfirst := contDiff_fst.contMDiff.comp hreal
    have hsecond := contDiff_snd.contMDiff.comp hreal
    have h := (𝓡∂ 1).contMDiffOn_symm.comp hsecond.contMDiffOn
      (show MapsTo (fun z : EuclideanHalfSpace (n + 1) => (L z.1).2) univ
        (range (𝓡∂ 1)) from
        fun z _ => ⟨((halfSpaceProductHomeomorph n).symm z).2, rfl⟩)
    have hnormal : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ 1) ∞
        (fun z => ((halfSpaceProductHomeomorph n).symm z).2) := by
      apply contMDiffOn_univ.mp
      apply h.congr
      intro z _
      exact ((𝓡∂ 1).left_inv ((halfSpaceProductHomeomorph n).symm z).2).symm
    exact hfirst.prodMk hnormal

section LocalCollar

variable {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- Product coordinates in a neighborhood of a boundary point, with smooth inverse. -/
noncomputable def localBoundaryCollar (x : (𝓡∂ (n + 1)).boundary W) :
    OpenPartialHomeomorph ((Fin n → ℝ) × EuclideanHalfSpace 1) W :=
  (halfSpaceProductHomeomorph n).toOpenPartialHomeomorph.trans
    (chartAt (EuclideanHalfSpace (n + 1)) x.1).symm

theorem contMDiffOn_localBoundaryCollar (x : (𝓡∂ (n + 1)).boundary W) :
    ContMDiffOn ((𝓘(ℝ, Fin n → ℝ)).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
      (localBoundaryCollar x) (localBoundaryCollar x).source := by
  exact (contMDiffOn_chart_symm (I := 𝓡∂ (n + 1)) (x := x.1)).comp
    (halfSpaceProductDiffeomorph n).contMDiff.contMDiffOn fun _ hp => hp.2

theorem contMDiffOn_localBoundaryCollar_symm (x : (𝓡∂ (n + 1)).boundary W) :
    ContMDiffOn (𝓡∂ (n + 1)) ((𝓘(ℝ, Fin n → ℝ)).prod (𝓡∂ 1)) ∞
      (localBoundaryCollar x).symm (localBoundaryCollar x).target := by
  exact (halfSpaceProductDiffeomorph n).symm.contMDiff.comp_contMDiffOn
    ((contMDiffOn_chart (I := 𝓡∂ (n + 1)) (x := x.1)).mono inter_subset_left)

theorem isLocalDiffeomorphAt_localBoundaryCollar (x : (𝓡∂ (n + 1)).boundary W)
    {p : (Fin n → ℝ) × EuclideanHalfSpace 1} (hp : p ∈ (localBoundaryCollar x).source) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, Fin n → ℝ)).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
      (localBoundaryCollar x) p := by
  refine ⟨{ toPartialEquiv := (localBoundaryCollar x).toPartialEquiv
            open_source := (localBoundaryCollar x).open_source
            open_target := (localBoundaryCollar x).open_target
            contMDiffOn_toFun := contMDiffOn_localBoundaryCollar x
            contMDiffOn_invFun := contMDiffOn_localBoundaryCollar_symm x }, hp, ?_⟩
  exact eqOn_refl _ _

/-- Positive collar height moves into the manifold interior. -/
theorem localBoundaryCollar_isInteriorPoint (x : (𝓡∂ (n + 1)).boundary W)
    {p : (Fin n → ℝ) × EuclideanHalfSpace 1}
    (hp : p ∈ (localBoundaryCollar x).source) (ht : 0 < p.2.1 0) :
    (𝓡∂ (n + 1)).IsInteriorPoint (localBoundaryCollar x p) := by
  have he : halfSpaceProductHomeomorph n p ∈
      (chartAt (EuclideanHalfSpace (n + 1)) x.1).target := hp.2
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  change ¬ (𝓡∂ (n + 1)).IsBoundaryPoint
    ((chartAt (EuclideanHalfSpace (n + 1)) x.1).symm (halfSpaceProductHomeomorph n p))
  rw [isBoundaryPoint_iff_chart_zero (chart_mem_atlas (EuclideanHalfSpace (n + 1)) x.1)
      ((chartAt (EuclideanHalfSpace (n + 1)) x.1).map_target he)]
  change ((chartAt (EuclideanHalfSpace (n + 1)) x.1)
    ((chartAt (EuclideanHalfSpace (n + 1)) x.1).symm
      (halfSpaceProductHomeomorph n p))).1 0 ≠ 0
  rw [(chartAt (EuclideanHalfSpace (n + 1)) x.1).right_inv he]
  exact ne_of_gt ht

theorem halfSpaceProductHomeomorph_boundaryChartAt_zero
    (x y : (𝓡∂ (n + 1)).boundary W)
    (hy : y.1 ∈ (chartAt (EuclideanHalfSpace (n + 1)) x.1).source) :
    halfSpaceProductHomeomorph n (boundaryChartAt x y, 0) =
      chartAt (EuclideanHalfSpace (n + 1)) x.1 y.1 := by
  rw [boundaryChartAt_apply x y hy]
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun _ => rfl) i
  exact ((isBoundaryPoint_iff_chart_zero
    (chart_mem_atlas (EuclideanHalfSpace (n + 1)) x.1) hy).mp y.2).symm

/-- At normal coordinate zero the local collar is the given boundary inclusion. -/
theorem localBoundaryCollar_zero (x y : (𝓡∂ (n + 1)).boundary W)
    (hy : y.1 ∈ (chartAt (EuclideanHalfSpace (n + 1)) x.1).source) :
    localBoundaryCollar x (boundaryChartAt x y, 0) = y.1 := by
  change (chartAt (EuclideanHalfSpace (n + 1)) x.1).symm
    (halfSpaceProductHomeomorph n (boundaryChartAt x y, 0)) = y.1
  rw [halfSpaceProductHomeomorph_boundaryChartAt_zero x y hy]
  exact (chartAt (EuclideanHalfSpace (n + 1)) x.1).left_inv hy

theorem mem_localBoundaryCollar_source (x y : (𝓡∂ (n + 1)).boundary W)
    (hy : y.1 ∈ (chartAt (EuclideanHalfSpace (n + 1)) x.1).source) :
    (boundaryChartAt x y, 0) ∈ (localBoundaryCollar x).source := by
  refine ⟨mem_univ _, ?_⟩
  change halfSpaceProductHomeomorph n (boundaryChartAt x y, 0) ∈
    (chartAt (EuclideanHalfSpace (n + 1)) x.1).target
  rw [halfSpaceProductHomeomorph_boundaryChartAt_zero x y hy]
  exact (chartAt (EuclideanHalfSpace (n + 1)) x.1).map_source hy

/-- The collar coordinates are defined on a product neighborhood of each boundary point. -/
theorem exists_localBoundaryCollar_product_neighborhood
    (x : (𝓡∂ (n + 1)).boundary W) :
    ∃ (u : Set (Fin n → ℝ)) (v : Set (EuclideanHalfSpace 1)),
      IsOpen u ∧ boundaryChartAt x x ∈ u ∧ IsOpen v ∧ 0 ∈ v ∧
      u ×ˢ v ⊆ (localBoundaryCollar x).source := by
  exact mem_nhds_prod_iff'.mp ((localBoundaryCollar x).open_source.mem_nhds
    (mem_localBoundaryCollar_source x x (mem_chart_source _ _)))

/-- Compactness supplies finitely many genuine smooth local collars covering the boundary. -/
theorem exists_finite_localBoundaryCollar_cover [CompactSpace W] :
    ∃ s : Finset ((𝓡∂ (n + 1)).boundary W),
      (𝓡∂ (n + 1)).boundary W ⊆ ⋃ x ∈ s, (localBoundaryCollar x).target := by
  apply ((𝓡∂ (n + 1)).isClosed_boundary (n := ∞) (by simp)).isCompact.elim_finite_subcover
    (fun x : (𝓡∂ (n + 1)).boundary W => (localBoundaryCollar x).target)
    (fun x => (localBoundaryCollar x).open_target)
  intro y hy
  refine mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
  exact ⟨mem_chart_source (EuclideanHalfSpace (n + 1)) y, mem_univ _⟩

end LocalCollar

end PoincareHighDim
