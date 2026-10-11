/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.BoundaryGerm
import Submission.Manifold.Cobordism.BoundarySign
import Submission.Manifold.Cobordism.EmbeddedNormalChart

/-!
# Transporting inward and outward witnesses through actual manifold charts

The half-space coordinate derivative excludes a short outward ray. The embedding
property excludes other branches of the original manifold from that ray as well.
-/

namespace PoincareHighDim
namespace WitnessTransport

open Set Topology Filter
open scoped Manifold ContDiff

variable {n : ℕ} {W M F H : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {J : ModelWithCorners ℝ F H} [J.Boundaryless]
    {f : W → M} (b : (𝓡∂ (n + 1)).boundary W)

/-- The actual ambient outward normal ray misses the whole embedded manifold for small
positive parameters, using only its original half-space derivative and the embedding. -/
theorem eventually_outward_not_mem_range (hemb : IsEmbedding f)
    (D : ((Fin n → ℝ) × ℝ) ≃L[ℝ] F)
    (hD : HasFDerivWithinAt (embeddedBoundaryExpression (J := J) f b)
      (D : ((Fin n → ℝ) × ℝ) →L[ℝ] F) {p | 0 ≤ p.2}
      (boundaryCoordinateCenter b, 0)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (extChartAt J (f b.1)).symm
        (embeddedBoundaryExpression (J := J) f b (boundaryCoordinateCenter b, 0) -
          D (0, t)) ∉ range f := by
  let e := extChartAt (𝓡∂ (n + 1)) b.1
  let a := extChartAt J (f b.1)
  let c := (boundaryCoordinateCenter b, (0 : ℝ))
  let q := embeddedBoundaryExpression (J := J) f b
  let z : W → ((Fin n → ℝ) × ℝ) := fun w => (halfSpaceCoordinateEquiv n).symm (e w)
  let r : ℝ → F := fun t => q c - D (0, t)
  let γ : ℝ → M := fun t => a.symm (r t)
  have hz0 : z b.1 = c := by
    change (halfSpaceCoordinateEquiv n).symm
      (extChartAt (𝓡∂ (n + 1)) b.1 b.1) = c
    rw [← halfSpaceCoordinateEquiv_center b]
    exact (halfSpaceCoordinateEquiv n).symm_apply_apply c
  have hzc : ContinuousAt z b.1 :=
    (halfSpaceCoordinateEquiv n).symm.continuous.continuousAt.comp
      (continuousAt_extChartAt b.1)
  have hzn (w : W) : 0 ≤ (z w).2 :=
    (chartAt (EuclideanHalfSpace (n + 1)) b.1 w).2
  have hzt : Tendsto z (𝓝 b.1) (𝓝[{p | 0 ≤ p.2}] c) := by
    rw [← hz0]
    exact tendsto_nhdsWithin_iff.mpr ⟨hzc, Eventually.of_forall hzn⟩
  have hexz := hzt.eventually (LocalDomain.eventually_ne_outwardRay D hD)
  have hr0 : r 0 = a (f b.1) := by
    simp [r, q, c, a]
  have hrc : Continuous r := continuous_const.sub
    (D.continuous.comp (continuous_const.prodMk continuous_id))
  have hrt : Tendsto r (𝓝 0) (𝓝 (a (f b.1))) := hr0 ▸ hrc.continuousAt.tendsto
  have hrsource : ∀ᶠ t in 𝓝 (0 : ℝ), r t ∈ a.target :=
    hrt.eventually (extChartAt_target_mem_nhds (I := J) (f b.1))
  have hγt : Tendsto γ (𝓝 0) (𝓝 (f b.1)) := by
    have hh := (continuousAt_extChartAt_symm (I := J) (f b.1)).tendsto.comp hrt
    change Tendsto (a.symm ∘ r) (𝓝 0) (𝓝 (f b.1))
    simpa only [a, (extChartAt J (f b.1)).left_inv (mem_extChartAt_source (f b.1))]
      using hh
  apply BoundaryGerm.eventually_not_mem_range_of_local_exclusion hemb hγt
  have hfst : Tendsto (Prod.fst : W × ℝ → W) (𝓝 (b.1, 0)) (𝓝 b.1) :=
    continuous_fst.continuousAt.tendsto
  have hsnd : Tendsto (Prod.snd : W × ℝ → ℝ) (𝓝 (b.1, 0)) (𝓝 0) :=
    continuous_snd.continuousAt.tendsto
  filter_upwards [hfst.eventually hexz,
    hfst.eventually (extChartAt_source_mem_nhds (I := 𝓡∂ (n + 1)) b.1),
    hsnd.eventually hrsource] with p hp hps hpt
  intro ht heq
  apply hp p.2 ht
  have hq : q (z p.1) = a (f p.1) := by
    change a (f (e.symm (halfSpaceCoordinateEquiv n
      ((halfSpaceCoordinateEquiv n).symm (e p.1))))) = _
    rw [(halfSpaceCoordinateEquiv n).apply_symm_apply, e.left_inv hps]
  change q (z p.1) = r p.2
  rw [hq, heq]
  exact a.right_inv hpt

/-- The negative axis of the constructed normal chart is genuinely outside the image. -/
theorem eventually_normalChart_outside (hemb : IsEmbedding f)
    (C : EmbeddedNormalChart (J := J) f b) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), C.chart (boundaryCoordinateCenter b, -t) ∉ range f := by
  have hsource : ∀ᶠ t in 𝓝 (0 : ℝ),
      (boundaryCoordinateCenter b, -t) ∈ C.chart.source := by
    have hc : Continuous (fun t : ℝ => (boundaryCoordinateCenter b, -t)) :=
      continuous_const.prodMk continuous_neg
    exact hc.continuousAt.preimage_mem_nhds
      (C.chart.open_source.mem_nhds (by simpa using C.center_mem))
  filter_upwards [eventually_outward_not_mem_range b hemb C.derivative C.hasFDerivWithinAt,
    hsource.filter_mono nhdsWithin_le_nhds] with t ht hs
  rw [C.formula hs]
  have hneg : C.derivative (0, -t) = -C.derivative (0, t) := by
    simpa only [Prod.neg_mk, neg_zero] using C.derivative.map_neg (0, t)
  simpa only [hneg, sub_eq_add_neg] using ht

/-- Outward points in a normal chart accumulate at the actual embedded boundary point. -/
theorem mem_closure_normalChart_outside (hemb : IsEmbedding f)
    (C : EmbeddedNormalChart (J := J) f b) :
    C.chart (boundaryCoordinateCenter b, 0) ∈
      closure {y | y ∉ range f ∧ (C.chart.symm y).2 < 0} := by
  let γ : ℝ → M := fun t => C.chart (boundaryCoordinateCenter b, -t)
  have hp : Continuous (fun t : ℝ => (boundaryCoordinateCenter b, -t)) :=
    continuous_const.prodMk continuous_neg
  have hγ : Tendsto γ (𝓝[>] (0 : ℝ))
      (𝓝 (C.chart (boundaryCoordinateCenter b, 0))) := by
    have hΦ : ContinuousAt C.chart (boundaryCoordinateCenter b, 0) :=
      C.chart.contMDiffOn_toFun.continuousOn.continuousAt
        (C.chart.open_source.mem_nhds C.center_mem)
    have h := hΦ.comp_of_eq (hp.continuousAt (x := 0)) (by simp)
    change Tendsto (C.chart ∘ (fun t : ℝ => (boundaryCoordinateCenter b, -t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (C.chart (boundaryCoordinateCenter b, 0)))
    simpa only [Function.comp_apply, neg_zero] using h.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply mem_closure_of_tendsto hγ
  have hsource : ∀ᶠ t in 𝓝 (0 : ℝ),
      (boundaryCoordinateCenter b, -t) ∈ C.chart.source :=
    hp.continuousAt.preimage_mem_nhds
      (C.chart.open_source.mem_nhds (by simpa only [neg_zero] using C.center_mem))
  filter_upwards [eventually_normalChart_outside b hemb C,
    hsource.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hs hpos
  refine ⟨ht, ?_⟩
  have heq : (C.chart.symm (γ t)).2 = -t := congrArg Prod.snd (C.chart.left_inv hs)
  exact heq.symm ▸ neg_neg_of_pos hpos

end WitnessTransport
end PoincareHighDim
