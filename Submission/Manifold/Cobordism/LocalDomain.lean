/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.AmbientCollar
import Submission.Manifold.Cobordism.BoundarySign
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Recognizing the side occupied by an embedded manifold with boundary

Away from the frontier of a closed set, membership is constant on connected sets.
In local normal coordinates this reduces identifying the occupied half-space to finding
one inward point and one outward point. Differential estimates provide the witnesses.
-/

namespace PoincareHighDim
namespace LocalDomain

open Set Topology
open scoped ContDiff

section Sides

variable {M : Type*} [TopologicalSpace M] {S T U : Set M}

/-- A connected set avoiding the frontier of a closed set lies entirely inside or outside. -/
theorem subset_or_subset_compl_of_disjoint_frontier (hS : IsClosed S)
    (hT : IsPreconnected T) (hdisj : Disjoint T (frontier S)) :
    T ⊆ S ∨ T ⊆ Sᶜ := by
  have hcover : T ⊆ interior S ∪ Sᶜ := by
    intro x hx
    by_cases hxS : x ∈ S
    · left
      by_contra hxint
      exact Set.disjoint_left.mp hdisj hx ⟨subset_closure hxS, hxint⟩
    · exact Or.inr hxS
  rcases hT.subset_or_subset isOpen_interior hS.isOpen_compl
      (Set.disjoint_left.mpr (fun _ h h' ↦ h' (interior_subset h))) hcover with h | h
  · exact Or.inl (h.trans interior_subset)
  · exact Or.inr h

/-- A zero slice and one witness on each connected side determine a closed domain. -/
theorem mem_iff_nonneg_of_connected_sides (hS : IsClosed S) (g : M → ℝ)
    (hfront : frontier S ∩ U ⊆ g ⁻¹' {0})
    (hzero : ∀ x ∈ U, g x = 0 → x ∈ S)
    (hpos : IsPreconnected {x | x ∈ U ∧ 0 < g x})
    (hneg : IsPreconnected {x | x ∈ U ∧ g x < 0})
    (hposw : ∃ x ∈ U, 0 < g x ∧ x ∈ S)
    (hnegw : ∃ x ∈ U, g x < 0 ∧ x ∉ S) :
    ∀ x ∈ U, x ∈ S ↔ 0 ≤ g x := by
  have hposdisj : Disjoint {x | x ∈ U ∧ 0 < g x} (frontier S) := by
    apply Set.disjoint_left.mpr
    intro x hx hf
    exact (ne_of_gt hx.2) (hfront ⟨hf, hx.1⟩)
  have hnegdisj : Disjoint {x | x ∈ U ∧ g x < 0} (frontier S) := by
    apply Set.disjoint_left.mpr
    intro x hx hf
    exact (ne_of_lt hx.2) (hfront ⟨hf, hx.1⟩)
  have hposS : {x | x ∈ U ∧ 0 < g x} ⊆ S := by
    rcases subset_or_subset_compl_of_disjoint_frontier hS hpos hposdisj with h | h
    · exact h
    · obtain ⟨x, hx, hg, hSx⟩ := hposw
      exact False.elim (h ⟨hx, hg⟩ hSx)
  have hnegS : {x | x ∈ U ∧ g x < 0} ⊆ Sᶜ := by
    rcases subset_or_subset_compl_of_disjoint_frontier hS hneg hnegdisj with h | h
    · obtain ⟨x, hx, hg, hSx⟩ := hnegw
      exact False.elim (hSx (h ⟨hx, hg⟩))
    · exact h
  intro x hx
  constructor
  · intro hSx
    by_contra hn
    exact hnegS ⟨hx, lt_of_not_ge hn⟩ hSx
  · intro hg
    rcases eq_or_lt_of_le hg with hz | hp
    · exact hzero x hx hz.symm
    · exact hposS ⟨hx, hp⟩

/-- For an embedding, local exclusion near a source point excludes an approaching curve
from the entire image. This rules out distant branches entering the coordinate neighborhood. -/
theorem eventually_not_mem_range_of_isEmbedding
    {X : Type*} [TopologicalSpace X] {f : X → M} (hf : IsEmbedding f)
    {x : X} {γ : ℝ → M} (hγ : Filter.Tendsto γ (𝓝 0) (𝓝 (f x)))
    (hlocal : ∀ᶠ z in 𝓝 x, ∀ t > (0 : ℝ), f z ≠ γ t) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∉ range f := by
  rw [hf.isInducing.nhds_eq_comap x] at hlocal
  obtain ⟨U, hU, hsub⟩ := Filter.mem_comap.mp hlocal
  filter_upwards [(hγ.eventually hU).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t ht htpos
  rintro ⟨z, hz⟩
  exact hsub (show f z ∈ U from hz ▸ ht) t htpos hz

end Sides

section ProductChart

variable {V M : Type*} [TopologicalSpace V] [TopologicalSpace M]
    {A : Set V} {ε : ℝ} {S : Set M}

/-- The two sides of a product chart are connected when its tangential slice is connected. -/
theorem isPreconnected_positive_side (e : OpenPartialHomeomorph (V × ℝ) M)
    (hsource : e.source = A ×ˢ Ioo (-ε) ε) (hA : IsPreconnected A) (hε : 0 < ε) :
    IsPreconnected {y | y ∈ e.target ∧ 0 < (e.symm y).2} := by
  have hsub : A ×ˢ Ioo 0 ε ⊆ e.source := by
    rw [hsource]
    intro p hp
    exact ⟨hp.1, (neg_neg_of_pos hε).trans hp.2.1, hp.2.2⟩
  have heq : {y | y ∈ e.target ∧ 0 < (e.symm y).2} = e '' (A ×ˢ Ioo 0 ε) := by
    ext y
    constructor
    · rintro ⟨hy, ht⟩
      have hs := e.map_target hy
      rw [hsource] at hs
      exact ⟨e.symm y, ⟨hs.1, ht, hs.2.2⟩, e.right_inv hy⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨e.map_source (hsub hp), by rw [e.left_inv (hsub hp)]; exact hp.2.1⟩
  rw [heq]
  exact (hA.prod isPreconnected_Ioo).image e (e.continuousOn.mono hsub)

theorem isPreconnected_negative_side (e : OpenPartialHomeomorph (V × ℝ) M)
    (hsource : e.source = A ×ˢ Ioo (-ε) ε) (hA : IsPreconnected A) (hε : 0 < ε) :
    IsPreconnected {y | y ∈ e.target ∧ (e.symm y).2 < 0} := by
  have hsub : A ×ˢ Ioo (-ε) 0 ⊆ e.source := by
    rw [hsource]
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans hε⟩
  have heq : {y | y ∈ e.target ∧ (e.symm y).2 < 0} = e '' (A ×ˢ Ioo (-ε) 0) := by
    ext y
    constructor
    · rintro ⟨hy, ht⟩
      have hs := e.map_target hy
      rw [hsource] at hs
      exact ⟨e.symm y, ⟨hs.1, hs.2.1, ht⟩, e.right_inv hy⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨e.map_source (hsub hp), by rw [e.left_inv (hsub hp)]; exact hp.2.2⟩
  rw [heq]
  exact (hA.prod isPreconnected_Ioo).image e (e.continuousOn.mono hsub)

/-- A local product chart identifies a closed domain with the nonnegative half-space
once an inward and an outward point have been found. -/
theorem mem_iff_nonneg_in_productChart (e : OpenPartialHomeomorph (V × ℝ) M)
    (hsource : e.source = A ×ˢ Ioo (-ε) ε) (hA : IsPreconnected A) (hε : 0 < ε)
    (hS : IsClosed S)
    (hfront : ∀ y ∈ frontier S ∩ e.target, (e.symm y).2 = 0)
    (hzero : ∀ v ∈ A, e (v, 0) ∈ S)
    (hpos : ∃ p ∈ e.source, 0 < p.2 ∧ e p ∈ S)
    (hneg : ∃ p ∈ e.source, p.2 < 0 ∧ e p ∉ S) :
    ∀ y ∈ e.target, y ∈ S ↔ 0 ≤ (e.symm y).2 := by
  apply mem_iff_nonneg_of_connected_sides hS (fun y ↦ (e.symm y).2)
    (fun y hy ↦ hfront y hy)
  · intro y hy ht
    have hs := e.map_target hy
    rw [hsource] at hs
    have h := hzero (e.symm y).1 hs.1
    simpa only [← ht, Prod.mk.eta, e.right_inv hy] using h
  · exact isPreconnected_positive_side e hsource hA hε
  · exact isPreconnected_negative_side e hsource hA hε
  · obtain ⟨p, hp, ht, hSp⟩ := hpos
    exact ⟨e p, e.map_source hp, by rwa [e.left_inv hp], hSp⟩
  · obtain ⟨p, hp, ht, hSp⟩ := hneg
    exact ⟨e p, e.map_source hp, by rwa [e.left_inv hp], hSp⟩

end ProductChart

section OutwardRay

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
/-- In product coordinates, moving outward only increases distance to a point in the
nonnegative half-space. -/
theorem norm_le_outward_sub {z : E × ℝ} {x : E} {t : ℝ} (hz : 0 ≤ z.2) (ht : 0 ≤ t) :
    ‖z - (x, 0)‖ ≤ ‖-(0, t) - (z - (x, 0))‖ := by
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
    neg_zero, zero_sub, sub_zero, norm_neg, Real.norm_eq_abs, abs_of_nonneg hz]
  apply max_le_max le_rfl
  rw [abs_of_nonpos (by linarith : -t - z.2 ≤ 0)]
  linarith

/-- First-order invertibility excludes a short outward normal ray from the image of a
nearby half-space. Only differentiability within the half-space is needed. -/
theorem eventually_ne_outwardRay_of_derivative_id {f : E × ℝ → E × ℝ} {x : E}
    (hf : HasFDerivWithinAt f (ContinuousLinearMap.id ℝ (E × ℝ))
      {z | 0 ≤ z.2} (x, 0)) :
    ∀ᶠ z in 𝓝[{z : E × ℝ | 0 ≤ z.2}] (x, 0),
      ∀ t > (0 : ℝ), f z ≠ f (x, 0) - (0, t) := by
  have hbound := hf.isLittleO.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, self_mem_nhdsWithin] with z hz hzS
  intro t ht heq
  have hnorm : ‖z - (x, 0)‖ ≤ ‖f z - f (x, 0) - (z - (x, 0))‖ := by
    rw [heq, sub_sub_cancel_left]
    exact norm_le_outward_sub hzS ht.le
  have hzero : z = (x, 0) := by
    have hn : ‖z - (x, 0)‖ = 0 := by
      change ‖f z - f (x, 0) - (z - (x, 0))‖ ≤ 1 / 2 * ‖z - (x, 0)‖ at hz
      have := norm_nonneg (z - (x, 0))
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  rw [hzero] at heq
  have hzpair : (0, t) = (0 : E × ℝ) := (sub_eq_self.mp heq.symm)
  have htzero : t = 0 := congrArg Prod.snd hzpair
  exact ht.ne' htzero

/-- The same outward-ray exclusion in arbitrary invertible derivative coordinates. -/
theorem eventually_ne_outwardRay {f : E × ℝ → F} {x : E}
    (D : (E × ℝ) ≃L[ℝ] F)
    (hf : HasFDerivWithinAt f (D : (E × ℝ) →L[ℝ] F) {z | 0 ≤ z.2} (x, 0)) :
    ∀ᶠ z in 𝓝[{z : E × ℝ | 0 ≤ z.2}] (x, 0),
      ∀ t > (0 : ℝ), f z ≠ f (x, 0) - D (0, t) := by
  have hcomp := D.symm.hasFDerivAt.comp_hasFDerivWithinAt (x, 0) hf
  have hid : (D.symm : F →L[ℝ] (E × ℝ)).comp (D : (E × ℝ) →L[ℝ] F) = ContinuousLinearMap.id ℝ (E × ℝ) := by
    apply ContinuousLinearMap.ext
    intro z
    exact D.symm_apply_apply z
  rw [hid] at hcomp
  filter_upwards [eventually_ne_outwardRay_of_derivative_id hcomp] with z hz
  intro t ht heq
  apply hz t ht
  change D.symm (f z) = D.symm (f (x, 0)) - (0, t)
  rw [heq, map_sub, D.symm_apply_apply]

/-- An embedded half-space with invertible derivative omits all sufficiently short
outward normal segments. -/
theorem eventually_outwardRay_not_mem_image {f : E × ℝ → F} {x : E}
    (D : (E × ℝ) ≃L[ℝ] F)
    (hf : HasFDerivWithinAt f (D : (E × ℝ) →L[ℝ] F) {z | 0 ≤ z.2} (x, 0))
    (hemb : IsEmbedding ({z : E × ℝ | 0 ≤ z.2}.domRestrict f)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x, 0) - D (0, t) ∉ f '' {z | 0 ≤ z.2} := by
  have hlocal := eventually_ne_outwardRay D hf
  rw [nhdsWithin_eq_map_subtype_coe (show (x, (0 : ℝ)) ∈ {z : E × ℝ | 0 ≤ z.2}
    from by simp)] at hlocal
  have hγ : Filter.Tendsto (fun t : ℝ ↦ f (x, 0) - D (0, t)) (𝓝 0) (𝓝 (f (x, 0))) := by
    have hc : Continuous (fun t : ℝ ↦ f (x, 0) - D (0, t)) :=
      continuous_const.sub (D.continuous.comp (continuous_const.prodMk continuous_id))
    simpa only [ContinuousAt, show ((0 : E), (0 : ℝ)) = (0 : E × ℝ) from rfl, map_zero, sub_zero]
      using (hc.continuousAt (x := 0))
  have h := eventually_not_mem_range_of_isEmbedding hemb hγ hlocal
  have hr : range ({z : E × ℝ | 0 ≤ z.2}.domRestrict f) = f '' {z | 0 ≤ z.2} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  rwa [hr] at h

/-- If a normal chart and the original half-space map have the same derivative at the
boundary, the original inward half-ray has normal-coordinate derivative one. -/
theorem hasDerivWithinAt_inward_normalCoordinate {f : E × ℝ → F} {x : E}
    (D : (E × ℝ) ≃L[ℝ] F)
    (hf : HasFDerivWithinAt f (D : (E × ℝ) →L[ℝ] F) {z | 0 ≤ z.2} (x, 0))
    (e : OpenPartialHomeomorph (E × ℝ) F) (hp : (x, 0) ∈ e.source)
    (he : e (x, 0) = f (x, 0))
    (hDe : HasFDerivAt e (D : (E × ℝ) →L[ℝ] F) (x, 0)) :
    HasDerivWithinAt (fun t ↦ (e.symm (f (x, t))).2) 1 (Ici 0) 0 := by
  have hinv := e.hasFDerivAt_symm (e.map_source hp)
    (show HasFDerivAt e (D : (E × ℝ) →L[ℝ] F) (e.symm (e (x, 0))) from by
      rwa [e.left_inv hp])
  rw [he] at hinv
  have hc : HasDerivWithinAt (fun t : ℝ ↦ (x, t)) (0, 1) (Ici 0) 0 :=
    ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ))).hasDerivWithinAt
  have hfc := hf.comp_hasDerivWithinAt 0 hc (fun _ ht ↦ ht)
  have hinvc := hinv.comp_hasDerivWithinAt 0 hfc
  have h := hasFDerivAt_snd.comp_hasDerivWithinAt 0 hinvc
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] at h
  convert h using 1
  rfl

/-- The original inward half-ray supplies an occupied point on the positive side of
any compatible normal chart. -/
theorem exists_positive_image_point {f : E × ℝ → F} {x : E}
    (D : (E × ℝ) ≃L[ℝ] F)
    (hf : HasFDerivWithinAt f (D : (E × ℝ) →L[ℝ] F) {z | 0 ≤ z.2} (x, 0))
    (e : OpenPartialHomeomorph (E × ℝ) F) (hp : (x, 0) ∈ e.source)
    (he : e (x, 0) = f (x, 0))
    (hDe : HasFDerivAt e (D : (E × ℝ) →L[ℝ] F) (x, 0)) :
    ∃ y ∈ e.target, 0 < (e.symm y).2 ∧ y ∈ f '' {z | 0 ≤ z.2} := by
  have hder := hasDerivWithinAt_inward_normalCoordinate D hf e hp he hDe
  have hpos := BoundarySign.eventually_gt_of_hasDerivWithinAt_pos hder (by norm_num)
  have hz : (e.symm (f (x, 0))).2 = 0 := by rw [← he, e.left_inv hp]
  rw [hz] at hpos
  have hfc : ContinuousWithinAt (fun t : ℝ ↦ f (x, t)) (Ici 0) 0 :=
    hf.continuousWithinAt.comp (show ContinuousWithinAt (fun t : ℝ ↦ (x, t)) (Ici 0) 0 from
      (continuous_const.prodMk continuous_id).continuousWithinAt) (fun _ ht ↦ ht)
  have htarget' : ∀ᶠ t in 𝓝[Ici 0] (0 : ℝ), f (x, t) ∈ e.target :=
    hfc (e.open_target.mem_nhds (show f (x, 0) ∈ e.target from he ▸ e.map_source hp))
  have htarget : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x, t) ∈ e.target :=
    htarget'.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  obtain ⟨t, htpos, httarget, ht⟩ := (hpos.and (htarget.and self_mem_nhdsWithin)).exists
  exact ⟨f (x, t), httarget, htpos, (x, t), ht.le, rfl⟩

end OutwardRay

end LocalDomain
end PoincareHighDim
