/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform ambient collars of compact hypersurfaces

A map locally diffeomorphic near the zero section of a compact product, and injective
on that section, is a diffeomorphism on a uniform open cylinder. Its inverse supplies
a smooth signed normal coordinate on an open neighborhood of the hypersurface.
-/

namespace PoincareHighDim
namespace AmbientCollar

open Set Topology Manifold
open scoped ContDiff

section Topology

variable {V M : Type*} [TopologicalSpace V] [TopologicalSpace M] [CompactSpace V]

/-- An open neighborhood of a compact zero section contains a uniform open cylinder. -/
theorem exists_uniform_cylinder {U : Set (V × ℝ)} (hU : IsOpen U)
    (hzero : ∀ v, (v, (0 : ℝ)) ∈ U) :
    ∃ ε > (0 : ℝ), (univ : Set V) ×ˢ Ioo (-ε) ε ⊆ U := by
  obtain ⟨A, B, _, hB, hA, hzeroB, hAB⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hU
      (show (univ : Set V) ×ˢ ({0} : Set ℝ) ⊆ U from by
        rintro ⟨v, t⟩ ⟨_, ht⟩
        have ht' : t = 0 := mem_singleton_iff.mp ht
        subst t
        exact hzero v)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds (hzeroB (show (0 : ℝ) ∈ {0} from rfl)))
  refine ⟨ε, hε, fun p hp ↦ hAB ⟨hA hp.1, hball ?_⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hp.2

/-- Local injectivity around an injective compact zero section gives uniform injectivity. -/
theorem exists_uniform_injective [T2Space M] {F : V × ℝ → M}
    (hzero : Function.Injective fun v ↦ F (v, 0))
    (hcont : ∀ v, ContinuousAt F (v, 0))
    (hlocal : ∀ v, ∃ U ∈ 𝓝 (v, (0 : ℝ)), InjOn F U) :
    ∃ ε > (0 : ℝ), InjOn F ((univ : Set V) ×ˢ Ioo (-ε) ε) := by
  have hinj : InjOn F ((univ : Set V) ×ˢ ({0} : Set ℝ)) := by
    rintro ⟨v, s⟩ ⟨_, hs⟩ ⟨w, t⟩ ⟨_, ht⟩ h
    have hs' : s = 0 := mem_singleton_iff.mp hs
    have ht' : t = 0 := mem_singleton_iff.mp ht
    subst s; subst t
    exact Prod.ext (hzero h) rfl
  obtain ⟨U, hU, hzeroU, hinjU⟩ := hinj.exists_isOpen_superset
    (isCompact_univ.prod isCompact_singleton)
    (by rintro ⟨v, t⟩ ⟨_, ht⟩; have ht' : t = 0 := ht; subst t; exact hcont v)
    (by rintro ⟨v, t⟩ ⟨_, ht⟩; have ht' : t = 0 := ht; subst t; exact hlocal v)
  obtain ⟨ε, hε, hsub⟩ := exists_uniform_cylinder hU (fun v ↦ hzeroU (by simp))
  exact ⟨ε, hε, hinjU.mono hsub⟩

end Topology

section LocalDiffeomorph

variable {E E' H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    {F : M → N} {s : Set M}

/-- The locus on which a map is a local diffeomorphism is open. -/
theorem isOpen_localDiffeomorphLocus :
    IsOpen {x | IsLocalDiffeomorphAt I J ∞ F x} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨Φ, hx, heq⟩
  exact Filter.mem_of_superset (Φ.open_source.mem_nhds hx)
    (fun y hy ↦ ⟨Φ, hy, heq⟩)

/-- An injective local diffeomorphism on an open set has a smooth inverse there. -/
noncomputable def of_injective [Nonempty M] (hs : IsOpen s) (hinj : InjOn F s)
    (hlocal : IsLocalDiffeomorphOn I J ∞ F s) : PartialDiffeomorph I J M N ∞ := by
  let hh := hlocal.isLocalHomeomorphOn
  have hopen : IsOpenMap (s.domRestrict F) := by
    apply IsOpenMap.of_nhds_le
    intro x
    change 𝓝 (F x.1) ≤ Filter.map (F ∘ Subtype.val) (𝓝 x)
    rw [← Filter.map_map, hs.isOpenEmbedding_subtypeVal.map_nhds_eq x,
      hh.map_nhds_eq x.property]
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hinj.toPartialEquiv F s) hh.continuousOn hopen hs
  refine { e with
    contMDiffOn_toFun := hlocal.contMDiffOn
    contMDiffOn_invFun := ?_ }
  intro y hy
  have hx : e.symm y ∈ s := e.map_target hy
  let hl := hlocal ⟨e.symm y, hx⟩
  have hyF : F (e.symm y) = y := e.right_inv hy
  have heq : e.symm =ᶠ[𝓝 y] hl.localInverse := by
    have htarget := e.open_target.mem_nhds hy
    have hpre := (e.continuousAt_symm hy).preimage_mem_nhds
      (hl.localInverse.open_target.mem_nhds hl.localInverse_mem_target)
    filter_upwards [htarget, hpre] with z hz hzpre
    have hzinv := hl.localInverse_left_inv hzpre
    change hl.localInverse (F (e.symm z)) = e.symm z at hzinv
    rw [show F (e.symm z) = z from e.right_inv hz] at hzinv
    exact hzinv.symm
  exact ((hyF ▸ hl.localInverse_contMDiffAt).congr_of_eventuallyEq heq).contMDiffWithinAt

end LocalDiffeomorph

section EuclideanInverse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The ordinary smooth inverse function theorem, packaged as a manifold local
 diffeomorphism. Smoothness is required on an open neighborhood of the base point. -/
theorem isLocalDiffeomorphAt_of_hasFDerivAt {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (D : E ≃L[ℝ] F) (hD : HasFDerivAt f (D : E →L[ℝ] F) x) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  let S := U ∩ (fderiv ℝ f) ⁻¹'
    range (ContinuousLinearEquiv.toContinuousLinearMap : (E ≃L[ℝ] F) → (E →L[ℝ] F))
  have hS : IsOpen S :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      ContinuousLinearEquiv.isOpen
  have hxS : x ∈ S := ⟨hx, D, hD.fderiv.symm⟩
  let e₀ := (hf.contDiffAt (hU.mem_nhds hx)).toOpenPartialHomeomorph f hD (by simp)
  let e := e₀.restrOpen S hS
  have he : (e : E → F) = f := rfl
  have heU : e.source ⊆ U := fun _ h ↦ h.2.1
  have hxe : x ∈ e.source :=
    ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hxS⟩
  have hinv : ContDiffOn ℝ ∞ e.symm e.target := by
    intro y hy
    have hys := e.map_target hy
    obtain ⟨Dy, hDy⟩ := hys.2.2
    have hfy := hf.contDiffAt (hU.mem_nhds (heU hys))
    have hderiv : HasFDerivAt f (Dy : E →L[ℝ] F) (e.symm y) := by
      rw [hDy]
      exact (hfy.differentiableAt (by simp)).hasFDerivAt
    rw [← he] at hderiv hfy
    exact (e.contDiffAt_symm hy hderiv hfy).contDiffWithinAt
  exact ⟨{ e with
    contMDiffOn_toFun := (hf.mono heU).contMDiffOn
    contMDiffOn_invFun := hinv.contMDiffOn }, hxe, fun _ _ ↦ rfl⟩

/-- A transverse vector completes an injective hypersurface differential to a linear
isomorphism. The covector records the chosen normal direction. -/
noncomputable def thickeningLinearEquiv [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (D : E →L[ℝ] F) (hD : Function.Injective D)
    (ℓ : F →L[ℝ] ℝ) (hℓD : ∀ z, ℓ (D z) = 0)
    (v : F) (hℓv : ℓ v ≠ 0) (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1) :
    (E × ℝ) ≃L[ℝ] F := by
  let L : (E × ℝ) →L[ℝ] F :=
    D.comp (ContinuousLinearMap.fst ℝ E ℝ) + (ContinuousLinearMap.snd ℝ E ℝ).smulRight v
  have hL : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    rintro ⟨z, t⟩ hzt
    have hzt' : D z + t • v = 0 := hzt
    have ht : t = 0 := by
      have h := congrArg ℓ hzt'
      simp only [map_add, map_smul, hℓD, map_zero, zero_add, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_right hℓv
    subst t
    simp only [zero_smul, add_zero] at hzt'
    exact Prod.ext (hD (hzt'.trans (map_zero D).symm)) rfl
  exact ((L : (E × ℝ) →ₗ[ℝ] F).linearEquivOfInjective hL
    (by simpa only [Module.finrank_prod, Module.finrank_self] using hdim.symm)).toContinuousLinearEquiv

/-- A smooth parametrized hypersurface admits a local ambient thickening in any transverse
constant direction. This is the ordinary inverse function theorem in adapted coordinates. -/
theorem isLocalDiffeomorphAt_thickening [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {q : E → F} {U : Set E} {x : E} (hU : IsOpen U) (hx : x ∈ U)
    (hq : ContDiffOn ℝ ∞ q U) (hD : Function.Injective (fderiv ℝ q x))
    (ℓ : F →L[ℝ] ℝ) (hℓD : ∀ z, ℓ (fderiv ℝ q x z) = 0)
    (v : F) (hℓv : ℓ v ≠ 0) (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ∞
      (fun p : E × ℝ ↦ q p.1 + p.2 • v) (x, 0) := by
  let D := thickeningLinearEquiv (fderiv ℝ q x) hD ℓ hℓD v hℓv hdim
  refine isLocalDiffeomorphAt_of_hasFDerivAt
    (U := U ×ˢ (univ : Set ℝ)) (hU.prod isOpen_univ) ⟨hx, mem_univ 0⟩ ?_ D ?_
  · exact (hq.comp contDiffOn_fst (fun _ h ↦ h.1)).add
      (contDiffOn_snd.smul contDiffOn_const)
  · have hqD := ((hq.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    exact (hqD.comp (x, 0) hasFDerivAt_fst).add
      (hasFDerivAt_snd.smul_const v)

/-- The boundary restriction of a map with invertible half-space derivative can be
thickened using that derivative's inward normal. No extension across the boundary is needed. -/
theorem isLocalDiffeomorphAt_thickening_of_halfspace_derivative
    {f : E × ℝ → F} {U : Set E} {x : E} (hU : IsOpen U) (hx : x ∈ U)
    (hq : ContDiffOn ℝ ∞ (fun z ↦ f (z, 0)) U)
    (D : (E × ℝ) ≃L[ℝ] F)
    (hf : HasFDerivWithinAt f (D : (E × ℝ) →L[ℝ] F) {z | 0 ≤ z.2} (x, 0)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ∞
      (fun p : E × ℝ ↦ f (p.1, 0) + D (0, p.2)) (x, 0) := by
  have hzero : HasFDerivAt (fun z : E ↦ (z, (0 : ℝ)))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const (0 : ℝ) x)
  have hqD := hf.comp_hasFDerivAt x hzero
    (Filter.Eventually.of_forall (fun z : E ↦ (show (z, (0 : ℝ)) ∈ {z : E × ℝ | 0 ≤ z.2}
      from by simp)))
  refine isLocalDiffeomorphAt_of_hasFDerivAt (U := U ×ˢ (univ : Set ℝ))
    (hU.prod isOpen_univ) ⟨hx, mem_univ 0⟩ ?_ D ?_
  · exact (hq.comp contDiffOn_fst (fun _ hp ↦ hp.1)).add
      (D.contDiff.comp (contDiff_const.prodMk contDiff_snd)).contDiffOn
  · have hnormal : HasFDerivAt (fun p : E × ℝ ↦ D (0, p.2))
        ((D : (E × ℝ) →L[ℝ] F).comp
          ((0 : (E × ℝ) →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E ℝ))) (x, 0) :=
      D.hasFDerivAt.comp (x, 0) ((hasFDerivAt_const (0 : E) (x, (0 : ℝ))).prodMk
        hasFDerivAt_snd)
    convert (hqD.comp (x, 0) hasFDerivAt_fst).add hnormal using 1 <;> try rfl
    apply ContinuousLinearMap.ext
    intro p
    change D p = D (p.1, 0) + D (0, p.2)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.eta]

/-- An arbitrary open coordinate neighborhood suffices for the half-space thickening
construction; smoothness is required only on its nonnegative half. -/
theorem isLocalDiffeomorphAt_thickening_of_halfspace_smooth
    {f : E × ℝ → F} {U : Set (E × ℝ)} {x : E} (hU : IsOpen U) (hx : (x, 0) ∈ U)
    (hf : ContDiffOn ℝ ∞ f (U ∩ {z | 0 ≤ z.2}))
    (D : (E × ℝ) ≃L[ℝ] F)
    (hD : HasFDerivWithinAt f (D : (E × ℝ) →L[ℝ] F) {z | 0 ≤ z.2} (x, 0)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ∞
      (fun p : E × ℝ ↦ f (p.1, 0) + D (0, p.2)) (x, 0) := by
  apply isLocalDiffeomorphAt_thickening_of_halfspace_derivative
    (U := (fun z : E ↦ (z, (0 : ℝ))) ⁻¹' U)
    (hU.preimage (continuous_id.prodMk continuous_const)) hx ?_ D hD
  exact hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (fun _ hz ↦ ⟨hz, by simp⟩)

end EuclideanInverse

section UniformCollar

variable {E E' H H' V M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    [TopologicalSpace V] [ChartedSpace H V] [CompactSpace V] [Nonempty V]
    [TopologicalSpace M] [ChartedSpace H' M] [T2Space M]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    {F : V × ℝ → M}

/-- Local smooth thickenings of an injectively parametrized compact hypersurface have a
uniform collar width. No global injectivity or product neighborhood is assumed. -/
theorem exists_uniform_partialDiffeomorph
    (hzero : Function.Injective fun v ↦ F (v, 0))
    (hlocal : ∀ v, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, ℝ)) J ∞ F (v, 0)) :
    ∃ ε > (0 : ℝ), ∃ Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (V × ℝ) M ∞,
      Φ.source = (univ : Set V) ×ˢ Ioo (-ε) ε ∧
      Φ.target = F '' ((univ : Set V) ×ˢ Ioo (-ε) ε) ∧
      ∀ p, Φ p = F p := by
  obtain ⟨ε₁, hε₁, hinj⟩ := exists_uniform_injective hzero
    (fun v ↦ (hlocal v).contMDiffAt.continuousAt) (fun v ↦ by
      obtain ⟨φ, hv, heq⟩ := hlocal v
      refine ⟨φ.source, φ.open_source.mem_nhds hv, ?_⟩
      intro p hp q hq he
      apply φ.toPartialEquiv.injOn hp hq
      rw [← heq hp, ← heq hq]
      exact he)
  obtain ⟨ε₂, hε₂, hlocalU⟩ := exists_uniform_cylinder
    (isOpen_localDiffeomorphLocus (I := I.prod 𝓘(ℝ, ℝ)) (J := J) (F := F)) hlocal
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hsub₁ : (univ : Set V) ×ˢ Ioo (-ε) ε ⊆ univ ×ˢ Ioo (-ε₁) ε₁ := by
    intro p hp
    exact ⟨hp.1, (neg_le_neg (min_le_left ε₁ ε₂)).trans_lt hp.2.1,
      hp.2.2.trans_le (min_le_left ε₁ ε₂)⟩
  have hsub₂ : (univ : Set V) ×ˢ Ioo (-ε) ε ⊆ univ ×ˢ Ioo (-ε₂) ε₂ := by
    intro p hp
    exact ⟨hp.1, (neg_le_neg (min_le_right ε₁ ε₂)).trans_lt hp.2.1,
      hp.2.2.trans_le (min_le_right ε₁ ε₂)⟩
  let Φ := of_injective (isOpen_univ.prod isOpen_Ioo) (hinj.mono hsub₁)
    (fun p ↦ hlocalU (hsub₂ p.property))
  exact ⟨ε, hε, Φ, rfl, rfl, fun _ ↦ rfl⟩

omit [CompactSpace V] [Nonempty V] [T2Space M] in
/-- The inverse collar's last coordinate is smooth on the ambient collar neighborhood. -/
theorem contMDiffOn_normalCoordinate
    (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (V × ℝ) M ∞) :
    ContMDiffOn J 𝓘(ℝ, ℝ) ∞ (fun y ↦ (Φ.symm y).2) Φ.target :=
  contMDiff_snd.comp_contMDiffOn Φ.contMDiffOn_invFun

omit [CompactSpace V] [Nonempty V] [T2Space M] in
/-- The normal coordinate of a point in the parametrized collar is its height. -/
theorem normalCoordinate_apply
    {Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (V × ℝ) M ∞}
    (hΦ : ∀ p, Φ p = F p) {p : V × ℝ} (hp : p ∈ Φ.source) :
    (Φ.symm (F p)).2 = p.2 := by
  rw [← hΦ p]
  exact congrArg Prod.snd (Φ.left_inv hp)

omit [CompactSpace V] [Nonempty V] [T2Space M] in
/-- Inside the collar neighborhood, the zero set of the normal coordinate is exactly
 the given embedded hypersurface. -/
theorem normalCoordinate_eq_zero_iff
    {Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (V × ℝ) M ∞}
    (hΦ : ∀ p, Φ p = F p) (hzero : ∀ v, (v, (0 : ℝ)) ∈ Φ.source)
    {y : M} (hy : y ∈ Φ.target) :
    (Φ.symm y).2 = 0 ↔ y ∈ range (fun v ↦ F (v, 0)) := by
  constructor
  · intro hz
    refine ⟨(Φ.symm y).1, ?_⟩
    change F ((Φ.symm y).1, 0) = y
    rw [← hz, Prod.mk.eta, ← hΦ]
    exact Φ.right_inv hy
  · rintro ⟨v, rfl⟩
    exact normalCoordinate_apply hΦ (hzero v)

omit [CompactSpace V] [Nonempty V] [T2Space M] in
/-- The signed normal coordinate has nonzero differential throughout its domain. -/
theorem mfderiv_normalCoordinate_ne_zero
    (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (V × ℝ) M ∞)
    {y : M} (hy : y ∈ Φ.target) :
    mfderiv J 𝓘(ℝ, ℝ) (fun z ↦ (Φ.symm z).2) y ≠ 0 := by
  let p := Φ.symm y
  have hp : p ∈ Φ.source := Φ.map_target hy
  have heq : (fun x ↦ (Φ.symm (Φ x)).2) =ᶠ[𝓝 p] Prod.snd := by
    filter_upwards [Φ.open_source.mem_nhds hp] with x hx
    exact congrArg Prod.snd (Φ.left_inv hx)
  have hcoord := (contMDiffOn_normalCoordinate Φ).contMDiffAt
    (Φ.open_target.mem_nhds hy)
  have hΦp : Φ p = y := Φ.right_inv hy
  have hderiv := heq.mfderiv_eq (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
    ((fun z ↦ (Φ.symm z).2) ∘ Φ) p = _ at hderiv
  rw [mfderiv_comp p (hΦp.symm ▸ hcoord.mdifferentiableAt (by simp))
    (Φ.mdifferentiableAt (by simp) hp), hΦp, mfderiv_snd] at hderiv
  intro hzero
  rw [hzero] at hderiv
  have h := congrArg (fun L ↦ L (0, (1 : ℝ))) hderiv
  change (0 : ℝ) = 1 at h
  exact zero_ne_one h

end UniformCollar

end AmbientCollar
end PoincareHighDim
