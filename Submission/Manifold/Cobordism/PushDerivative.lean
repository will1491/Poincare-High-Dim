/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.InwardEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Nonsingular differentials of inward coordinate modifications

The original smooth structure is retained not only at the level of smooth maps:
the differential of each chart modification, and of their finite composition,
is a linear equivalence at boundary points as well as interior points.
-/

namespace PoincareHighDim

open Set Topology Filter
open scoped Manifold ContDiff

namespace ChartPushData

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace W] [ChartedSpace H W]
    {I : ModelWithCorners ℝ E H} [IsManifold I ∞ W] [T2Space W]
    {c : W} (D : ChartPushData I c)

theorem isInvertible_mfderiv (x : W) :
    (mfderiv I I D.push x).IsInvertible := by
  by_cases hx : x ∈ (chartAt H c).source
  · have hs : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I c) x :=
      (contMDiffOn_extChartAt (I := I) (n := ∞) (x := c)).contMDiffAt
        ((chartAt H c).open_source.mem_nhds hx) |>.mdifferentiableAt (by simp)
    have ht : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I c) (D.push x) :=
      (contMDiffOn_extChartAt (I := I) (n := ∞) (x := c)).contMDiffAt
        ((chartAt H c).open_source.mem_nhds (D.push_mem_source hx))
        |>.mdifferentiableAt (by simp)
    have heq : (extChartAt I c ∘ D.push) =ᶠ[𝓝 x] (D.coordMap ∘ extChartAt I c) := by
      filter_upwards [(chartAt H c).open_source.mem_nhds hx] with y hy
      exact D.extChart_push hy
    have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, E))
    rw [mfderiv_comp x ht (D.contMDiff.mdifferentiable (by simp) x),
      mfderiv_comp x (D.coordMap.mdifferentiable (by simp) _) hs] at hd
    have hsource : (mfderiv I 𝓘(ℝ, E) (extChartAt I c) x).IsInvertible :=
      isInvertible_mfderiv_extChartAt (I := I) (by simpa only [extChartAt_source] using hx)
    have htarget : (mfderiv I 𝓘(ℝ, E) (extChartAt I c) (D.push x)).IsInvertible :=
      isInvertible_mfderiv_extChartAt (I := I)
        (by simpa only [extChartAt_source] using D.push_mem_source hx)
    have hcoord : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) D.coordMap (extChartAt I c x)).IsInvertible :=
      (D.coordMap.isLocalDiffeomorph _).isInvertible_mfderiv (by simp)
    have hcomp : ((mfderiv I 𝓘(ℝ, E) (extChartAt I c) (D.push x)) ∘L
        mfderiv I I D.push x).IsInvertible := by
      rw [hd]
      have hcast := ContinuousLinearMap.isInvertible_equiv (f :=
        tangentSpaceCast 𝓘(ℝ, E) ((D.coordMap ∘ extChartAt I c) x)
          ((extChartAt I c ∘ D.push) x))
      exact (hcast.comp hcoord).comp hsource
    obtain ⟨A, hA⟩ := htarget
    rw [← hA] at hcomp
    exact ContinuousLinearMap.isInvertible_equiv_comp.mp hcomp
  · have hc : x ∉ D.supportRegion := fun h => hx (D.supportRegion_subset h)
    have heq : D.push =ᶠ[𝓝 x] id := by
      filter_upwards [D.isCompact_supportRegion.isClosed.isOpen_compl.mem_nhds hc] with y hy
      exact D.push_eq_of_not_mem_supportRegion hy
    rw [heq.mfderiv_eq, mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩

theorem compose_isInvertible_mfderiv (ds : List (Σ c : W, ChartPushData I c)) (x : W) :
    (mfderiv I I (compose ds) x).IsInvertible := by
  induction ds with
  | nil =>
    change (mfderiv I I id x).IsInvertible
    rw [mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  | cons d ds ih =>
    change (mfderiv I I (d.2.push ∘ compose ds) x).IsInvertible
    rw [mfderiv_comp x (d.2.contMDiff.mdifferentiable (by simp) _)
      ((compose_contMDiff ds).mdifferentiable (by simp) x)]
    exact (d.2.isInvertible_mfderiv _).comp ih

end ChartPushData

namespace InwardCopy

variable {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W] [CompactSpace W] [T2Space W]
    (C : InwardCopy (𝓡∂ (n + 1)) W)

omit [CompactSpace W] in
/-- Moving a compact manifold into its own interior preserves full tangent rank,
including at its original boundary. -/
theorem isInvertible_mfderiv_embedding (x : W) :
    letI := (ManifoldInterior.inducedAtlas (𝓡∂ (n + 1)) (W := W)).chartedSpace
    (mfderiv (𝓡∂ (n + 1)) (interiorModel (n + 1)) C.embedding x).IsInvertible := by
  let := (ManifoldInterior.inducedAtlas (𝓡∂ (n + 1)) (W := W)).chartedSpace
  let := interior_isManifold (n := n + 1) (W := W)
  have hi := contMDiff_interior_inclusion (n := n + 1) (W := W)
  have he := C.contMDiff_embedding
  have hc := ChartPushData.compose_isInvertible_mfderiv C.modifications x
  change (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
    ((Subtype.val : (𝓡∂ (n + 1)).interior W → W) ∘ C.embedding) x).IsInvertible at hc
  rw [mfderiv_comp x (hi.mdifferentiable (by simp) _) (he.mdifferentiable (by simp) x)] at hc
  obtain ⟨A, hA⟩ := hc
  have hinj : Function.Injective
      (mfderiv (𝓡∂ (n + 1)) (interiorModel (n + 1)) C.embedding x) := by
    apply Function.Injective.of_comp (f :=
      mfderiv (interiorModel (n + 1)) (𝓡∂ (n + 1)) Subtype.val (C.embedding x))
    rw [← ContinuousLinearMap.coe_comp, ← hA]
    exact A.injective
  have hdim : Module.finrank ℝ (TangentSpace (𝓡∂ (n + 1)) x) =
      Module.finrank ℝ (TangentSpace (interiorModel (n + 1)) (C.embedding x)) := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) =
      Module.finrank ℝ (Fin (n + 1) → ℝ)
    simp
  let L := (mfderiv (𝓡∂ (n + 1)) (interiorModel (n + 1)) C.embedding x).toLinearMap
  exact ⟨(L.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv, rfl⟩

end InwardCopy

end PoincareHighDim
