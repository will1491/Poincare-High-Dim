/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.EmbeddedInterior
import Submission.Manifold.Cobordism.BoundarySmooth

/-!
# Embedded boundary coordinates

The coordinate expression of a full-rank smooth embedding is smooth on a genuine
half-space neighborhood and has an invertible derivative there. These statements
refer to the original half-space atlas, including at the boundary itself.
-/

namespace PoincareHighDim

open Set Topology Filter WithLp
open scoped Manifold ContDiff

/-- The normal coordinate is written last in product coordinates and first in the
standard Euclidean half-space convention. -/
noncomputable def halfSpaceCoordinateEquiv (n : ℕ) :
    ((Fin n → ℝ) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun p => toLp 2 (Fin.cons p.2 p.1)
    invFun := fun z => (fun i => z i.succ, z 0)
    left_inv := by intro p; rfl
    right_inv := by
      intro z
      apply PiLp.ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    map_add' := by
      intro p q
      apply PiLp.ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    map_smul' := by
      intro r p
      apply PiLp.ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl }

@[simp] theorem halfSpaceCoordinateEquiv_zero (n : ℕ) (p : (Fin n → ℝ) × ℝ) :
    halfSpaceCoordinateEquiv n p 0 = p.2 := rfl

@[simp] theorem halfSpaceCoordinateEquiv_succ (n : ℕ) (p : (Fin n → ℝ) × ℝ) (i : Fin n) :
    halfSpaceCoordinateEquiv n p i.succ = p.1 i := rfl

theorem halfSpaceCoordinateEquiv_mem_range (n : ℕ) (p : (Fin n → ℝ) × ℝ) :
    halfSpaceCoordinateEquiv n p ∈ range (𝓡∂ (n + 1)) ↔ 0 ≤ p.2 := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  rfl

section Coordinates

variable {n : ℕ} {W M F H : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {J : ModelWithCorners ℝ F H} [IsManifold J ∞ M]
    (f : W → M) (b : (𝓡∂ (n + 1)).boundary W)

/-- Tangential coordinates of the chosen boundary point. -/
noncomputable def boundaryCoordinateCenter : Fin n → ℝ :=
  fun i => (extChartAt (𝓡∂ (n + 1)) b.1 b.1) i.succ

theorem halfSpaceCoordinateEquiv_center :
    halfSpaceCoordinateEquiv n (boundaryCoordinateCenter b, 0) =
      extChartAt (𝓡∂ (n + 1)) b.1 b.1 := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => rfl) i
  exact ((isBoundaryPoint_iff_chart_zero (chart_mem_atlas _ b.1)
    (mem_chart_source _ b.1)).mp b.2).symm

/-- The full ambient coordinate expression, used only on its half-space domain. -/
noncomputable def embeddedBoundaryExpression : ((Fin n → ℝ) × ℝ) → F :=
  writtenInExtChartAt (𝓡∂ (n + 1)) J b.1 f ∘ halfSpaceCoordinateEquiv n

omit [IsManifold J ∞ M] in
@[simp] theorem embeddedBoundaryExpression_center :
    embeddedBoundaryExpression (J := J) f b (boundaryCoordinateCenter b, 0) =
      extChartAt J (f b.1) (f b.1) := by
  simp only [embeddedBoundaryExpression, Function.comp_apply,
    halfSpaceCoordinateEquiv_center, writtenInExtChartAt,
    (extChartAt (𝓡∂ (n + 1)) b.1).left_inv (mem_extChartAt_source b.1)]

omit [IsManifold J ∞ M] in
/-- The derivative in the original half-space is an actual linear equivalence. -/
theorem embeddedBoundaryExpression_hasFDerivWithinAt
    (hf : ContMDiff (𝓡∂ (n + 1)) J ∞ f)
    (hD : (mfderiv (𝓡∂ (n + 1)) J f b.1).IsInvertible) :
    ∃ D : ((Fin n → ℝ) × ℝ) ≃L[ℝ] F,
      HasFDerivWithinAt (embeddedBoundaryExpression (J := J) f b)
        (D : ((Fin n → ℝ) × ℝ) →L[ℝ] F) {p | 0 ≤ p.2}
        (boundaryCoordinateCenter b, 0) := by
  obtain ⟨A, hA⟩ := hD
  let L := halfSpaceCoordinateEquiv n
  let D := L.trans ((tangentSpaceCastModel (𝓡∂ (n + 1)) b.1).symm.trans
    (A.trans (tangentSpaceCastModel J (f b.1))))
  refine ⟨D, ?_⟩
  have hd := (hf.mdifferentiable (by simp) b.1).hasMFDerivAt.2
  rw [← hA, ← halfSpaceCoordinateEquiv_center b] at hd
  exact hd.comp _ L.hasFDerivAt.hasFDerivWithinAt
    (fun p hp => (halfSpaceCoordinateEquiv_mem_range n p).mpr hp)

/-- The coordinate expression is smooth on an open neighborhood intersected with the
closed half-space; there is no assumed smooth extension across its boundary. -/
theorem exists_contDiffOn_embeddedBoundaryExpression
    (hf : ContMDiff (𝓡∂ (n + 1)) J ∞ f) :
    ∃ U : Set ((Fin n → ℝ) × ℝ), IsOpen U ∧
      (boundaryCoordinateCenter b, 0) ∈ U ∧
      ContDiffOn ℝ ∞ (embeddedBoundaryExpression (J := J) f b)
        (U ∩ {p | 0 ≤ p.2}) := by
  let I := 𝓡∂ (n + 1)
  let S := (extChartAt I b.1).target ∩
    (extChartAt I b.1).symm ⁻¹' f ⁻¹' (extChartAt J (f b.1)).source
  have hS : S ∈ 𝓝[range I] (extChartAt I b.1 b.1) := by
    apply Filter.inter_mem (extChartAt_target_mem_nhdsWithin b.1)
    apply mem_nhdsWithin_of_mem_nhds
    apply (continuousAt_extChartAt_symm (I := I) b.1).preimage_mem_nhds
    simpa only [(extChartAt I b.1).left_inv (mem_extChartAt_source b.1)] using
      hf.continuous.continuousAt.preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := J) (f b.1))
  obtain ⟨V, hV, hVS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hS
  have hpre : halfSpaceCoordinateEquiv n ⁻¹' V ∈
      𝓝 (boundaryCoordinateCenter b, 0) := by
    apply (halfSpaceCoordinateEquiv n).continuous.continuousAt.preimage_mem_nhds
    simpa only [halfSpaceCoordinateEquiv_center] using hV
  obtain ⟨U, hUV, hU, hbU⟩ := mem_nhds_iff.mp hpre
  refine ⟨U, hU, hbU, ?_⟩
  exact ((contMDiff_iff.mp hf).2 b.1 (f b.1)).comp
    (halfSpaceCoordinateEquiv n).contDiff.contDiffOn
    (fun p hp => hVS ⟨hUV hp.1, (halfSpaceCoordinateEquiv_mem_range n p).mpr hp.2⟩)

end Coordinates

end PoincareHighDim
