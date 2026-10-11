/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.BoundarySmooth
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Smooth functions defining the boundary

The normal coordinates in half-space charts are nonnegative and vanish precisely on the
boundary. A subordinate smooth partition of unity patches them into a global function.
-/

namespace PoincareHighDim

open Set Topology WithLp
open scoped Manifold ContDiff

namespace BoundaryFunction

variable {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- The normal coordinate of an ambient half-space chart. -/
noncomputable def normalCoordinate (c : W) (x : W) : ℝ :=
  (chartAt (EuclideanHalfSpace (n + 1)) c x).1 0

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
theorem normalCoordinate_nonneg (c x : W) : 0 ≤ normalCoordinate (n := n) c x :=
  (chartAt (EuclideanHalfSpace (n + 1)) c x).2

theorem normalCoordinate_eq_zero_iff (c x : W)
    (hx : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) c).source) :
    normalCoordinate (n := n) c x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x :=
  (isBoundaryPoint_iff_chart_zero (chart_mem_atlas _ c) hx).symm

theorem contMDiffOn_normalCoordinate (c : W) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ (normalCoordinate (n := n) c)
      (chartAt (EuclideanHalfSpace (n + 1)) c).source := by
  have hq : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y 0) :=
    (contDiff_apply ℝ ℝ (0 : Fin (n + 1))).comp PiLp.contDiff_ofLp
  exact hq.contMDiff.comp_contMDiffOn
    (contMDiffOn_extChartAt (I := 𝓡∂ (n + 1)) (x := c))

/-- A finite smooth partition subordinate to half-space coordinate domains. -/
structure ChartPartition where
  size : ℕ
  center : Fin size → W
  partition : SmoothPartitionOfUnity (Fin size) (𝓡∂ (n + 1)) W univ
  subordinate : partition.IsSubordinate
    (fun i => (chartAt (EuclideanHalfSpace (n + 1)) (center i)).source)

theorem nonempty_chartPartition [CompactSpace W] [T2Space W] :
    Nonempty (ChartPartition (n := n) (W := W)) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun c : W => (chartAt (EuclideanHalfSpace (n + 1)) c).source)
    (fun c => (chartAt (EuclideanHalfSpace (n + 1)) c).open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source _ _⟩)
  let center : Fin s.card → W := fun i => (s.equivFin.symm i).1
  have hcover : (univ : Set W) ⊆ ⋃ i, (chartAt (EuclideanHalfSpace (n + 1)) (center i)).source := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := mem_iUnion₂.mp (hs hx)
    refine mem_iUnion.mpr ⟨s.equivFin ⟨c, hc⟩, ?_⟩
    simpa only [center, Equiv.symm_apply_apply] using hcx
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡∂ (n + 1))
    isClosed_univ _ (fun i => (chartAt (EuclideanHalfSpace (n + 1)) (center i)).open_source) hcover
  exact ⟨⟨s.card, center, ρ, hρ⟩⟩

namespace ChartPartition

variable (P : ChartPartition (n := n) (W := W))

/-- A globally smooth nonnegative summand, zero outside the support of its chart weight. -/
noncomputable def summand (i : Fin P.size) (x : W) : ℝ :=
  P.partition i x * normalCoordinate (n := n) (P.center i) x

/-- The global boundary defining function assembled from the finite coordinate cover. -/
noncomputable def definingFunction (x : W) : ℝ := ∑ i, P.summand i x

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
theorem summand_nonneg (i : Fin P.size) (x : W) : 0 ≤ P.summand i x :=
  mul_nonneg (P.partition.nonneg i x) (normalCoordinate_nonneg (n := n) _ _)

theorem smooth_summand (i : Fin P.size) :
    ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ (P.summand i) := by
  have h := P.partition.contMDiff_smul (g := normalCoordinate (n := n) (P.center i))
    (n := ⊤) (fun x hx => (contMDiffOn_normalCoordinate (n := n) (P.center i)).contMDiffAt
      ((chartAt (EuclideanHalfSpace (n + 1)) (P.center i)).open_source.mem_nhds
        (P.subordinate i hx)))
  change ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞
    (fun x => P.partition i x * normalCoordinate (n := n) (P.center i) x)
  simpa only [smul_eq_mul] using h

theorem smooth : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ P.definingFunction :=
  ContMDiff.sum fun i _ => P.smooth_summand i

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
theorem nonneg (x : W) : 0 ≤ P.definingFunction x :=
  Finset.sum_nonneg fun i _ => P.summand_nonneg i x

theorem summand_eq_zero_of_boundary (i : Fin P.size) (x : W)
    (hx : (𝓡∂ (n + 1)).IsBoundaryPoint x) : P.summand i x = 0 := by
  by_cases hρ : P.partition i x = 0
  · simp [summand, hρ]
  · have hsource : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) (P.center i)).source :=
      P.subordinate i (subset_tsupport _ hρ)
    rw [summand, (normalCoordinate_eq_zero_iff (n := n) _ _ hsource).mpr hx, mul_zero]

theorem eq_zero_of_boundary (x : W) (hx : (𝓡∂ (n + 1)).IsBoundaryPoint x) :
    P.definingFunction x = 0 :=
  Finset.sum_eq_zero fun i _ => P.summand_eq_zero_of_boundary i x hx

theorem pos_of_interior (x : W) (hx : (𝓡∂ (n + 1)).IsInteriorPoint x) :
    0 < P.definingFunction x := by
  obtain ⟨i, hi⟩ := P.partition.exists_pos_of_mem (mem_univ x)
  have hsource : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) (P.center i)).source :=
    P.subordinate i (subset_tsupport _ (ne_of_gt hi))
  have hn : normalCoordinate (n := n) (P.center i) x ≠ 0 := by
    intro hz
    exact (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (I := 𝓡∂ (n + 1)) x).mp hx
      ((normalCoordinate_eq_zero_iff (n := n) _ _ hsource).mp hz)
  have hp : 0 < P.summand i x := mul_pos hi
    (lt_of_le_of_ne (normalCoordinate_nonneg (n := n) _ _) (Ne.symm hn))
  exact hp.trans_le (Finset.single_le_sum (fun j _ => P.summand_nonneg j x)
    (Finset.mem_univ i))

theorem eq_zero_iff_boundary (x : W) :
    P.definingFunction x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x := by
  constructor
  · intro hz
    by_contra hx
    have hi : (𝓡∂ (n + 1)).IsInteriorPoint x :=
      (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (I := 𝓡∂ (n + 1)) x).mpr hx
    exact (ne_of_gt (P.pos_of_interior x hi)) hz
  · exact P.eq_zero_of_boundary x

/-- The chart expression of each weighted normal coordinate is differentiable up to the
boundary. -/
theorem differentiableWithinAt_summand_chart (i : Fin P.size) (c x : W)
    (hx : x ∈ (extChartAt (𝓡∂ (n + 1)) c).source) :
    DifferentiableWithinAt ℝ (P.summand i ∘ (extChartAt (𝓡∂ (n + 1)) c).symm)
      (range (𝓡∂ (n + 1))) (extChartAt (𝓡∂ (n + 1)) c x) := by
  apply mdifferentiableWithinAt_iff_differentiableWithinAt.mp
  exact ((P.smooth_summand i).contMDiffAt.comp_contMDiffWithinAt _
    (contMDiffWithinAt_extChartAt_symm_range c
      ((extChartAt (𝓡∂ (n + 1)) c).map_source hx))).mdifferentiableWithinAt (by simp)

/-- A weighted coordinate has nonnegative inward directional derivative at the boundary. -/
theorem derivative_summand_nonneg (i : Fin P.size) (c x : W)
    (hx : x ∈ (extChartAt (𝓡∂ (n + 1)) c).source)
    (hb : (𝓡∂ (n + 1)).IsBoundaryPoint x)
    (v : EuclideanSpace ℝ (Fin (n + 1)))
    (hv : v ∈ posTangentConeAt (range (𝓡∂ (n + 1)))
      (extChartAt (𝓡∂ (n + 1)) c x)) :
    0 ≤ fderivWithin ℝ (P.summand i ∘ (extChartAt (𝓡∂ (n + 1)) c).symm)
      (range (𝓡∂ (n + 1))) (extChartAt (𝓡∂ (n + 1)) c x) v := by
  apply IsLocalMinOn.fderivWithin_nonneg (s := range (𝓡∂ (n + 1))) _ hv
  apply IsMinOn.isLocalMinOn
  intro y _
  simpa only [mem_ofPred_eq, Function.comp_apply, (extChartAt (𝓡∂ (n + 1)) c).left_inv hx,
    P.summand_eq_zero_of_boundary i x hb] using P.summand_nonneg i
      ((extChartAt (𝓡∂ (n + 1)) c).symm y)

/-- In its own active chart, the normal summand has derivative equal to its positive
partition weight in the unit inward direction. -/
theorem derivative_summand_own_chart (i : Fin P.size) (x : W)
    (hx : x ∈ (extChartAt (𝓡∂ (n + 1)) (P.center i)).source)
    (hb : (𝓡∂ (n + 1)).IsBoundaryPoint x) :
    fderivWithin ℝ (P.summand i ∘ (extChartAt (𝓡∂ (n + 1)) (P.center i)).symm)
      (range (𝓡∂ (n + 1))) (extChartAt (𝓡∂ (n + 1)) (P.center i) x)
      (toLp 2 (Pi.single 0 1)) = P.partition i x := by
  let e := extChartAt (𝓡∂ (n + 1)) (P.center i)
  let z := e x
  let S := range (𝓡∂ (n + 1))
  let q : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj 0).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).toContinuousLinearMap
  have hz : z ∈ S := mem_range_self _
  have hu : UniqueDiffWithinAt ℝ S z := (𝓡∂ (n + 1)).uniqueDiffOn z hz
  have hinv : e.symm z = x := e.left_inv hx
  have hqzero : q z = 0 := (normalCoordinate_eq_zero_iff (n := n) _ _
    (by simpa only [extChartAt_source] using hx)).mpr hb
  have heq : (P.summand i ∘ e.symm) =ᶠ[𝓝[S] z]
      (fun y => P.partition i (e.symm y) * q y) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin' hx] with y hy
    change P.partition i (e.symm y) * normalCoordinate (n := n) (P.center i) (e.symm y) = _
    have hn : normalCoordinate (n := n) (P.center i) (e.symm y) = q y := by
      change (e (e.symm y)) 0 = y 0
      rw [e.right_inv hy]
    rw [hn]
  have hdρ : DifferentiableWithinAt ℝ (fun y => P.partition i (e.symm y)) S z := by
    apply mdifferentiableWithinAt_iff_differentiableWithinAt.mp
    exact ((P.partition i).contMDiff.contMDiffAt.comp_contMDiffWithinAt _
      (contMDiffWithinAt_extChartAt_symm_range (P.center i) (e.map_source hx))).mdifferentiableWithinAt
      (by simp)
  change fderivWithin ℝ (P.summand i ∘ e.symm) S z _ = _
  rw [heq.fderivWithin_eq (heq.self_of_nhdsWithin hz), fderivWithin_fun_mul hu hdρ
    q.differentiableAt.differentiableWithinAt, q.fderivWithin hu, hqzero]
  simp [q, hinv]

/-- The patched function retains a strictly positive inward derivative at every boundary
point: all summands contribute nonnegatively and an active chart contributes positively. -/
theorem mfderiv_ne_zero (x : W) (hb : (𝓡∂ (n + 1)).IsBoundaryPoint x) :
    mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) P.definingFunction x ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := P.partition.exists_pos_of_mem (mem_univ x)
  let e := extChartAt (𝓡∂ (n + 1)) (P.center i)
  let z := e x
  let S := range (𝓡∂ (n + 1))
  let v : EuclideanSpace ℝ (Fin (n + 1)) := toLp 2 (Pi.single 0 1)
  have hx : x ∈ e.source := by
    rw [extChartAt_source]
    exact P.subordinate i (subset_tsupport _ (ne_of_gt hi))
  have hz : z ∈ S := mem_range_self _
  have hu : UniqueDiffWithinAt ℝ S z := (𝓡∂ (n + 1)).uniqueDiffOn z hz
  have hzv : z + v ∈ S := by
    simp only [S, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] at hz ⊢
    change 0 ≤ z 0 + 1
    exact add_nonneg hz zero_le_one
  have hv : v ∈ posTangentConeAt S z := by
    simpa only [add_sub_cancel_left] using
      (sub_mem_posTangentConeAt_of_segment_subset
        ((𝓡∂ (n + 1)).convex_range.segment_subset hz hzv))
  have hsum : fderivWithin ℝ (P.definingFunction ∘ e.symm) S z =
      ∑ j, fderivWithin ℝ (P.summand j ∘ e.symm) S z := by
    change fderivWithin ℝ (fun y => ∑ j, P.summand j (e.symm y)) S z = _
    exact
      (fderivWithin_fun_sum hu (fun j (_ : j ∈ Finset.univ) =>
        P.differentiableWithinAt_summand_chart j (P.center i) x hx))
  have hpositive : 0 < fderivWithin ℝ (P.definingFunction ∘ e.symm) S z v := by
    rw [hsum, sum_apply]
    have hactive : 0 < fderivWithin ℝ (P.summand i ∘ e.symm) S z v := by
      rw [P.derivative_summand_own_chart i x hx hb]
      exact hi
    exact hactive.trans_le (Finset.single_le_sum
      (fun j _ => P.derivative_summand_nonneg j (P.center i) x hx hb v hv)
      (Finset.mem_univ i))
  intro hzero
  have hinv : e.symm z = x := e.left_inv hx
  have hchain := mfderiv_comp_mfderivWithin z
    (P.smooth.mdifferentiable (by simp) (e.symm z))
    ((contMDiffWithinAt_extChartAt_symm_range (n := ∞) (P.center i)
      (e.map_source hx)).mdifferentiableWithinAt (by simp)) hu.uniqueMDiffWithinAt
  have hzero' : (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) P.definingFunction (e.symm z) :
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) = 0 := by
    exact hinv.symm ▸ hzero
  have heval := congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ => L v) hchain
  simp only [mfderivWithin_eq_fderivWithin, hzero'] at heval
  exact (ne_of_gt hpositive) heval

end ChartPartition

/-- Every compact smooth manifold with boundary admits a globally smooth, nonnegative
boundary defining function whose differential is nonzero on its zero set. -/
theorem exists_boundary_defining_function [CompactSpace W] [T2Space W] :
    ∃ h : W → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ x, 0 ≤ h x) ∧
      (∀ x, h x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x) ∧
      (∀ x, (𝓡∂ (n + 1)).IsBoundaryPoint x →
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) h x ≠ 0) := by
  obtain ⟨P⟩ := nonempty_chartPartition (n := n) (W := W)
  exact ⟨P.definingFunction, P.smooth, P.nonneg, P.eq_zero_iff_boundary, P.mfderiv_ne_zero⟩

end BoundaryFunction

end PoincareHighDim
