/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.EmbeddedBoundaryChart
import Submission.Manifold.Cobordism.LocalDomain

/-!
# Identifying the embedded boundary near a normal chart

The embedding property excludes distant branches. A local parametrization of the
boundary therefore identifies its entire image near the base point with the zero
slice, not merely with a subset of that slice.
-/

namespace PoincareHighDim
namespace BoundaryGerm

open Set Topology Filter

variable {B E M : Type*} [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace M]

/-- An embedded boundary locally parametrized by a normal chart is exactly its zero slice
near the base point. -/
theorem eventually_mem_range_iff_normal_zero {e : B → M} (he : IsEmbedding e)
    (p : OpenPartialHomeomorph B E) {b : B} (hb : b ∈ p.source)
    (Φ : OpenPartialHomeomorph (E × ℝ) M) (hΦ : (p b, 0) ∈ Φ.source)
    (hzero : ∀ z, (z, 0) ∈ Φ.source → z ∈ p.target ∧ Φ (z, 0) = e (p.symm z)) :
    ∀ᶠ y in 𝓝 (e b), y ∈ Φ.target ∧
      (y ∈ range e ↔ (Φ.symm y).2 = 0) := by
  have hbase : Φ (p b, 0) = e b := by
    rw [(hzero (p b) hΦ).2, p.left_inv hb]
  have hG : ∀ᶠ b' in 𝓝 b, b' ∈ p.source ∧ (p b', (0 : ℝ)) ∈ Φ.source := by
    filter_upwards [p.open_source.mem_nhds hb,
      ((p.continuousAt hb).prodMk continuousAt_const).preimage_mem_nhds
        (Φ.open_source.mem_nhds hΦ)] with b' hb' hΦ'
    exact ⟨hb', hΦ'⟩
  rw [he.isInducing.nhds_eq_comap b] at hG
  obtain ⟨U, hU, hGU⟩ := Filter.mem_comap.mp hG
  filter_upwards [hU, Φ.open_target.mem_nhds (hbase ▸ Φ.map_source hΦ)] with y hy hyt
  refine ⟨hyt, ?_⟩
  constructor
  · rintro ⟨b', rfl⟩
    obtain ⟨hb', hp'⟩ := hGU hy
    have hz : Φ (p b', 0) = e b' := by
      rw [(hzero (p b') hp').2, p.left_inv hb']
    rw [← hz, Φ.left_inv hp']
  · intro hyzero
    have hp' : ((Φ.symm y).1, 0) ∈ Φ.source := by
      simpa only [← hyzero, Prod.eta] using Φ.map_target hyt
    refine ⟨p.symm (Φ.symm y).1, ?_⟩
    rw [← (hzero (Φ.symm y).1 hp').2, ← hyzero, Prod.eta, Φ.right_inv hyt]

/-- A local exclusion uniform in a small positive parameter excludes the approaching curve
from the whole image of an embedding. -/
theorem eventually_not_mem_range_of_local_exclusion {X : Type*} [TopologicalSpace X]
    {e : X → M} (he : IsEmbedding e) {x : X} {γ : ℝ → M}
    (hγ : Tendsto γ (𝓝 0) (𝓝 (e x)))
    (hex : ∀ᶠ p : X × ℝ in 𝓝 (x, 0), 0 < p.2 → e p.1 ≠ γ p.2) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∉ range e := by
  obtain ⟨A, hA, T, hT, hAT⟩ := mem_nhds_prod_iff.mp hex
  rw [he.isInducing.nhds_eq_comap x] at hA
  obtain ⟨U, hU, hUA⟩ := Filter.mem_comap.mp hA
  filter_upwards [(hγ.eventually hU).filter_mono nhdsWithin_le_nhds,
    mem_nhdsWithin_of_mem_nhds hT, self_mem_nhdsWithin] with t htU htT htpos
  rintro ⟨z, hz⟩
  have hzU : e z ∈ U := by rw [hz]; exact htU
  exact hAT (a := (z, t)) ⟨hUA hzU, htT⟩ htpos hz

end BoundaryGerm
end PoincareHighDim
