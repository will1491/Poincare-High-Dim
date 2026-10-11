/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.BoundaryGerm
import Submission.Manifold.Cobordism.HalfSpaceThickening
import Submission.Manifold.Cobordism.SignedChart

/-! # From normal-coordinate germs to signed boundary functions -/

namespace PoincareHighDim
namespace StripFunction.LocalBoundaryFunction

open Set Topology Filter
open scoped Manifold ContDiff

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M]
    {J : ModelWithCorners ℝ F H}
    {S B B₀ B₁ : Set M} {b : M}

/-- The normal-coordinate construction for charts whose source uses the normed-space
atlas on `E × ℝ`. -/
noncomputable def ofEuclideanPartialDiffeomorph
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) J (E × ℝ) M ∞)
    (hb : b ∈ Φ.target)
    (hside : ∀ y ∈ Φ.target, y ∈ S ↔ 0 ≤ (Φ.symm y).2)
    (hzero : ∀ y ∈ Φ.target, y ∈ B ↔ (Φ.symm y).2 = 0) :
    StripFunction.LocalBoundaryFunction J S B b where
  domain := Φ.target
  open_domain := Φ.open_target
  mem_domain := hb
  value y := (Φ.symm y).2
  smooth := contDiff_snd.contMDiff.comp_contMDiffOn Φ.contMDiffOn_invFun
  side := hside
  zero := hzero
  inward y hy hyB := by
    let z := Φ.symm y
    have hz : z ∈ Φ.source := Φ.map_target hy
    have hz0 : z.2 = 0 := (hzero y hy).mp hyB
    have hzbase : (z.1, (0 : ℝ)) ∈ Φ.source := by simpa only [← hz0] using hz
    let γ : ℝ → M := fun t => Φ (z.1, t)
    have hp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E × ℝ) ∞ (fun t : ℝ => (z.1, t)) :=
      (contDiff_const.prodMk contDiff_id).contMDiff
    have hγ : ContMDiffAt 𝓘(ℝ, ℝ) J ∞ γ 0 :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hzbase)).comp 0 hp.contMDiffAt
    have hγ0 : γ 0 = y := by
      change Φ (z.1, 0) = y
      rw [← hz0]
      exact Φ.right_inv hy
    have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), (z.1, t) ∈ Φ.source :=
      hp.continuous.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hzbase)
    have hcoord : (fun t => (Φ.symm (γ t)).2) =ᶠ[𝓝 (0 : ℝ)] id := by
      filter_upwards [hevent] with t ht
      exact congrArg Prod.snd (Φ.left_inv ht)
    refine ⟨γ, 1, hγ, hγ0, ?_, ?_, zero_lt_one⟩
    · filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with t ht ht0
      apply (hside (γ t) (Φ.map_source ht)).mpr
      have heq : (Φ.symm (γ t)).2 = t := congrArg Prod.snd (Φ.left_inv ht)
      exact heq.symm ▸ ht0
    · exact (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq hcoord

/-- Restrict a boundary defining function to either closed, disjoint boundary piece. -/
noncomputable def of_boundary_piece (L : StripFunction.LocalBoundaryFunction J S B b)
    (hB : B = B₀ ∪ B₁) (hdisj : Disjoint B₀ B₁) (hB₁ : IsClosed B₁)
    (hb : b ∈ B₀) : StripFunction.LocalBoundaryFunction J S B₀ b where
  domain := L.domain ∩ B₁ᶜ
  open_domain := L.open_domain.inter hB₁.isOpen_compl
  mem_domain := ⟨L.mem_domain, fun h => Set.disjoint_left.mp hdisj hb h⟩
  value := L.value
  smooth := L.smooth.mono inter_subset_left
  side x hx := L.side x hx.1
  zero x hx := by
    rw [← L.zero x hx.1, hB]
    exact (or_iff_left hx.2).symm
  inward x hx hxB := L.inward x hx.1 (hB ▸ Or.inl hxB)

/-- A regular signed boundary function prevents its base boundary point from being
an interior point of the domain. -/
theorem mem_frontier (L : StripFunction.LocalBoundaryFunction J S B b)
    (hb : b ∈ B) (hS : b ∈ S) : b ∈ frontier S := by
  refine ⟨subset_closure hS, ?_⟩
  intro hint
  obtain ⟨γ, d, hγ, hγ0, _, hd, hdpos⟩ := L.inward b L.mem_domain hb
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ L.domain ∧ γ t ∈ S := by
    have hc : Tendsto γ (𝓝 0) (𝓝 b) := hγ0 ▸ hγ.continuousAt
    exact hc.eventually (inter_mem (L.open_domain.mem_nhds L.mem_domain)
      (mem_interior_iff_mem_nhds.mp hint))
  have hmin : IsLocalMin (L.value ∘ γ) 0 := by
    filter_upwards [hnear] with t ht
    change L.value (γ 0) ≤ L.value (γ t)
    rw [hγ0, (L.zero b L.mem_domain).mp hb]
    exact (L.side (γ t) ht.1).mp ht.2
  exact (ne_of_gt hdpos) (hmin.hasDerivAt_eq_zero hd)

/-- A normal chart, its exact boundary germ, and accumulating points on both sides
give an actual local signed boundary function. -/
theorem nonempty_of_normal_germs
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) J (E × ℝ) M ∞)
    {x : E} (hx : (x, 0) ∈ Φ.source) (hbase : Φ (x, 0) = b)
    (hS : IsClosed S) (hBS : B ⊆ S) (hfront : frontier S ⊆ B)
    (hB : ∀ᶠ y in 𝓝 b, y ∈ B ↔ (Φ.symm y).2 = 0)
    (hpos : b ∈ closure {y | y ∈ S ∧ 0 < (Φ.symm y).2})
    (hneg : b ∈ closure {y | y ∉ S ∧ (Φ.symm y).2 < 0}) :
    Nonempty (StripFunction.LocalBoundaryFunction J S B b) := by
  obtain ⟨O, hOB, hO, hbO⟩ := mem_nhds_iff.mp hB
  let U := Φ.source ∩ Φ ⁻¹' O
  have hU : IsOpen U := Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hO
  let Φ' := HalfSpaceThickening.restrict Φ U hU
  have hx' : (x, 0) ∈ Φ'.source :=
    ⟨hx, hx, show Φ (x, 0) ∈ O by rw [hbase]; exact hbO⟩
  have htargetO : Φ'.target ⊆ O := by
    intro y hy
    have hp := Φ'.map_target hy
    have h : Φ (Φ'.symm y) ∈ O := hp.2.2
    change Φ' (Φ'.symm y) ∈ O at h
    have he : Φ' (Φ'.symm y) = y := Φ'.right_inv hy
    rwa [he] at h
  have hfront' : ∀ᶠ y in 𝓝 (Φ' (x, 0)),
      y ∈ frontier S → (Φ'.symm y).2 = 0 := by
    change ∀ᶠ y in 𝓝 (Φ (x, 0)), y ∈ frontier S → (Φ.symm y).2 = 0
    rw [hbase]
    filter_upwards [hB] with y hy
    exact fun h => hy.mp (hfront h)
  have hzero : ∀ᶠ z in 𝓝 x, Φ' (z, 0) ∈ S := by
    have hp : ∀ᶠ z in 𝓝 x, (z, (0 : ℝ)) ∈ Φ'.source :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (Φ'.open_source.mem_nhds hx')
    filter_upwards [hp] with z hz
    apply hBS
    apply (hOB (htargetO (Φ'.map_source hz))).mpr
    exact congrArg Prod.snd (Φ'.left_inv hz)
  obtain ⟨r, hr, Ψ, hsource, hxΨ, htarget, heq, hinv, hside⟩ :=
    HalfSpaceThickening.exists_productChart_mem_iff_nonneg Φ' hx' hS hfront' hzero
      (hbase ▸ hpos) (hbase ▸ hneg)
  have hbΨ : b ∈ Ψ.target := by
    have h := Ψ.map_source hxΨ
    rw [heq] at h
    change Φ (x, 0) ∈ Ψ.target at h
    rwa [hbase] at h
  have hzeroΨ : ∀ y ∈ Ψ.target, y ∈ B ↔ (Ψ.symm y).2 = 0 := by
    intro y hy
    rw [hinv]
    exact hOB (htargetO (htarget hy))
  exact ⟨ofEuclideanPartialDiffeomorph Ψ hbΨ hside hzeroΨ⟩

end StripFunction.LocalBoundaryFunction
end PoincareHighDim
