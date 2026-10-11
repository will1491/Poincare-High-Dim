/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.LocalDomain
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Smooth thickenings of half-space charts

The boundary restriction of a half-space map has an ambient thickening with the same
derivative. Shrinking any such chart to a product ball makes both sides connected;
local frontier information and accumulating inward and outward points then determine
the occupied side throughout the smaller chart.
-/

namespace PoincareHighDim
namespace HalfSpaceThickening

open Set Topology Filter Manifold
open scoped ContDiff

section Derivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Linear thickening of the boundary trace preserves the original half-space derivative. -/
theorem hasFDerivAt_thickening {q : E × ℝ → F} {x : E}
    (D : (E × ℝ) ≃L[ℝ] F)
    (hq : HasFDerivWithinAt q (D : (E × ℝ) →L[ℝ] F) {p | 0 ≤ p.2} (x, 0)) :
    HasFDerivAt (fun p : E × ℝ ↦ q (p.1, 0) + D (0, p.2))
      (D : (E × ℝ) →L[ℝ] F) (x, 0) := by
  have hzero : HasFDerivAt (fun z : E ↦ (z, (0 : ℝ)))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const (0 : ℝ) x)
  have htrace := hq.comp_hasFDerivAt x hzero
    (Eventually.of_forall (fun z : E ↦
      (show (z, (0 : ℝ)) ∈ {p : E × ℝ | 0 ≤ p.2} from by simp)))
  have hnormal : HasFDerivAt (fun p : E × ℝ ↦ D (0, p.2))
      ((D : (E × ℝ) →L[ℝ] F).comp
        ((0 : (E × ℝ) →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E ℝ))) (x, 0) :=
    D.hasFDerivAt.comp (x, 0)
      ((hasFDerivAt_const (0 : E) (x, (0 : ℝ))).prodMk hasFDerivAt_snd)
  convert (htrace.comp (x, 0) hasFDerivAt_fst).add hnormal using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro p
  change D p = D (p.1, 0) + D (0, p.2)
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.eta]

/-- The inward ray has positive normal coordinate in every sufficiently short interval. -/
theorem eventually_inward_normalCoordinate_pos {q : E × ℝ → F} {x : E}
    (D : (E × ℝ) ≃L[ℝ] F)
    (hq : HasFDerivWithinAt q (D : (E × ℝ) →L[ℝ] F) {p | 0 ≤ p.2} (x, 0))
    (e : OpenPartialHomeomorph (E × ℝ) F) (hp : (x, 0) ∈ e.source)
    (he : e (x, 0) = q (x, 0))
    (hDe : HasFDerivAt e (D : (E × ℝ) →L[ℝ] F) (x, 0)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (e.symm (q (x, t))).2 := by
  have hder := LocalDomain.hasDerivWithinAt_inward_normalCoordinate D hq e hp he hDe
  have h := BoundarySign.eventually_gt_of_hasDerivWithinAt_pos hder (by norm_num)
  have hz : (e.symm (q (x, 0))).2 = 0 := by rw [← he, e.left_inv hp]
  rwa [hz] at h

/-- Local recovery of points of a domain from the half-space excludes the outward ray.
The recovery hypothesis is supplied by an embedding and its original boundary chart. -/
theorem eventually_outwardRay_not_mem_of_recovery {q : E × ℝ → F} {x : E}
    {S : Set F} (D : (E × ℝ) ≃L[ℝ] F)
    (hq : HasFDerivWithinAt q (D : (E × ℝ) →L[ℝ] F) {p | 0 ≤ p.2} (x, 0))
    (hrecover : ∀ A ∈ 𝓝[{p : E × ℝ | 0 ≤ p.2}] (x, 0),
      ∀ᶠ y in 𝓝 (q (x, 0)), y ∈ S → ∃ p ∈ A, q p = y) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), q (x, 0) - D (0, t) ∉ S := by
  have hlocal := LocalDomain.eventually_ne_outwardRay D hq
  have hrec := hrecover _ hlocal
  have hc : Continuous (fun t : ℝ ↦ q (x, 0) - D (0, t)) :=
    continuous_const.sub (D.continuous.comp (continuous_const.prodMk continuous_id))
  have htend : Tendsto (fun t : ℝ ↦ q (x, 0) - D (0, t)) (𝓝 0) (𝓝 (q (x, 0))) := by
    simpa only [ContinuousAt, show ((0 : E), (0 : ℝ)) = (0 : E × ℝ) from rfl,
      map_zero, sub_zero] using (hc.continuousAt (x := 0))
  filter_upwards [(htend.eventually hrec).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t ht htpos
  intro hS
  obtain ⟨p, hp, he⟩ := ht hS
  exact hp t htpos he

end Derivative

section Restriction

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {J : ModelWithCorners ℝ F H}

/-- Restriction of a smooth partial diffeomorphism to an open source subset. -/
noncomputable def restrict (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) J (E × ℝ) M ∞)
    (U : Set (E × ℝ)) (hU : IsOpen U) :
    PartialDiffeomorph 𝓘(ℝ, E × ℝ) J (E × ℝ) M ∞ where
  __ := Φ.toOpenPartialHomeomorph.restrOpen U hU
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left

/-- A small product ball in a smooth chart has connected positive and negative sides.
Only local frontier and zero-slice information is needed; the two sides are oriented by
points of the domain and its complement accumulating at the center. -/
theorem exists_productChart_mem_iff_nonneg_within
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) J (E × ℝ) M ∞)
    {x : E} (hx : (x, 0) ∈ Φ.source) {S : Set M} (hS : IsClosed S)
    (hfront : ∀ᶠ y in 𝓝 (Φ (x, 0)), y ∈ frontier S → (Φ.symm y).2 = 0)
    (hzero : ∀ᶠ z in 𝓝 x, Φ (z, 0) ∈ S)
    (hpos : Φ (x, 0) ∈ closure {y | y ∈ S ∧ 0 < (Φ.symm y).2})
    (hneg : Φ (x, 0) ∈ closure {y | y ∉ S ∧ (Φ.symm y).2 < 0})
    {V : Set M} (hV : V ∈ 𝓝 (Φ (x, 0))) :
    ∃ r > (0 : ℝ), ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) J (E × ℝ) M ∞,
      Ψ.source = Metric.ball x r ×ˢ Ioo (-r) r ∧
      (x, 0) ∈ Ψ.source ∧ Ψ.target ⊆ Φ.target ∧ Ψ.target ⊆ V ∧
      (∀ p, Ψ p = Φ p) ∧ (∀ y, Ψ.symm y = Φ.symm y) ∧
      (∀ y ∈ Ψ.target, y ∈ S ↔ 0 ≤ (Ψ.symm y).2) := by
  have hΦ := Φ.toOpenPartialHomeomorph.continuousAt hx
  have hf : ∀ᶠ p in 𝓝 (x, (0 : ℝ)),
      Φ p ∈ frontier S → (Φ.symm (Φ p)).2 = 0 := hΦ.eventually hfront
  have hz : ∀ᶠ p in 𝓝 (x, (0 : ℝ)), Φ (p.1, 0) ∈ S :=
    (continuous_fst.continuousAt : ContinuousAt (Prod.fst : E × ℝ → E) (x, 0)).eventually
      hzero
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (Φ.open_source.mem_nhds hx)
      (inter_mem hf (inter_mem hz (hΦ.preimage_mem_nhds hV))))
  let Ψ := restrict Φ (Metric.ball (x, (0 : ℝ)) r) Metric.isOpen_ball
  have hsub : Metric.ball (x, (0 : ℝ)) r ⊆ Φ.source := fun p hp ↦ (hball hp).1
  have hsource : Ψ.source = Metric.ball x r ×ˢ Ioo (-r) r := by
    change Φ.source ∩ Metric.ball (x, (0 : ℝ)) r = _
    rw [inter_eq_right.mpr hsub, ← ball_prod_same, Real.ball_eq_Ioo]
    simp only [zero_sub, zero_add]
  have hxΨ : (x, 0) ∈ Ψ.source := ⟨hx, Metric.mem_ball_self hr⟩
  have htarget : Ψ.target ⊆ Φ.target := inter_subset_left
  have htargetV : Ψ.target ⊆ V := by
    intro y hy
    have hp := Ψ.map_target hy
    have h := (hball hp.2).2.2.2
    change Ψ (Ψ.symm y) ∈ V at h
    have he : Ψ (Ψ.symm y) = y := Ψ.right_inv hy
    rwa [he] at h
  have hbase : Φ (x, 0) ∈ Ψ.target := Ψ.map_source hxΨ
  refine ⟨r, hr, Ψ, hsource, hxΨ, htarget, htargetV, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  apply LocalDomain.mem_iff_nonneg_in_productChart Ψ.toOpenPartialHomeomorph
    hsource Metric.isPreconnected_ball hr hS
  · intro y hy
    have hp := Ψ.map_target hy.2
    have h := (hball hp.2).2.1
    change Φ (Ψ.symm y) ∈ frontier S → (Φ.symm (Φ (Ψ.symm y))).2 = 0 at h
    have he : Φ (Ψ.symm y) = y := Ψ.right_inv hy.2
    change (Φ.symm y).2 = 0
    simpa only [he] using h (he.symm ▸ hy.1)
  · intro z hzball
    have hp : (z, (0 : ℝ)) ∈ Metric.ball (x, (0 : ℝ)) r := by
      rw [← ball_prod_same]
      exact ⟨hzball, Metric.mem_ball_self hr⟩
    exact (hball hp).2.2.1
  · obtain ⟨y, hy, hyS, hypos⟩ := mem_closure_iff.mp hpos _ Ψ.open_target hbase
    refine ⟨Ψ.symm y, Ψ.map_target hy, hypos, ?_⟩
    change Ψ (Ψ.symm y) ∈ S
    have he : Ψ (Ψ.symm y) = y := Ψ.right_inv hy
    rwa [he]
  · obtain ⟨y, hy, hyS, hyneg⟩ := mem_closure_iff.mp hneg _ Ψ.open_target hbase
    refine ⟨Ψ.symm y, Ψ.map_target hy, hyneg, ?_⟩
    change Ψ (Ψ.symm y) ∉ S
    have he : Ψ (Ψ.symm y) = y := Ψ.right_inv hy
    rwa [he]

/-- The product-chart side classification without a prescribed ambient neighborhood. -/
theorem exists_productChart_mem_iff_nonneg
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) J (E × ℝ) M ∞)
    {x : E} (hx : (x, 0) ∈ Φ.source) {S : Set M} (hS : IsClosed S)
    (hfront : ∀ᶠ y in 𝓝 (Φ (x, 0)), y ∈ frontier S → (Φ.symm y).2 = 0)
    (hzero : ∀ᶠ z in 𝓝 x, Φ (z, 0) ∈ S)
    (hpos : Φ (x, 0) ∈ closure {y | y ∈ S ∧ 0 < (Φ.symm y).2})
    (hneg : Φ (x, 0) ∈ closure {y | y ∉ S ∧ (Φ.symm y).2 < 0}) :
    ∃ r > (0 : ℝ), ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) J (E × ℝ) M ∞,
      Ψ.source = Metric.ball x r ×ˢ Ioo (-r) r ∧
      (x, 0) ∈ Ψ.source ∧ Ψ.target ⊆ Φ.target ∧
      (∀ p, Ψ p = Φ p) ∧ (∀ y, Ψ.symm y = Φ.symm y) ∧
      (∀ y ∈ Ψ.target, y ∈ S ↔ 0 ≤ (Ψ.symm y).2) := by
  obtain ⟨r, hr, Ψ, hs, hxΨ, ht, _, he, hei, hside⟩ :=
    exists_productChart_mem_iff_nonneg_within Φ hx hS hfront hzero hpos hneg
      (V := univ) univ_mem
  exact ⟨r, hr, Ψ, hs, hxΨ, ht, he, hei, hside⟩

end Restriction

end HalfSpaceThickening
end PoincareHighDim
