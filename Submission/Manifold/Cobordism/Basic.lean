/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Compact smooth manifold triads

A smooth manifold triad consists of a compact smooth manifold with boundary `W`
and two closed smooth manifolds embedded as the two disjoint parts of its boundary.
The boundary is the boundary of the specified smooth atlas on `W`; neither a collar
nor a product decomposition is part of the data.

The parameter `n` is the dimension of `W`, so the ends have dimension `n - 1`.
-/

open Set Topology
open scoped Manifold ContDiff

namespace PoincareHighDim

/-- A compact smooth manifold triad `(W; V₀, V₁)`, with its original smooth structures.
The embeddings specify the identifications of the two ends with the boundary of `W`. -/
structure SmoothTriad (n : ℕ) [NeZero n] (W V₀ V₁ : Type*)
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace n) W]
    [TopologicalSpace V₀] [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) V₀]
    [TopologicalSpace V₁] [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) V₁] where
  [smooth : IsManifold (𝓡∂ n) ∞ W]
  [smooth₀ : IsManifold (𝓡 (n - 1)) ∞ V₀]
  [smooth₁ : IsManifold (𝓡 (n - 1)) ∞ V₁]
  [compact : CompactSpace W]
  [compact₀ : CompactSpace V₀]
  [compact₁ : CompactSpace V₁]
  [hausdorff : T2Space W]
  /-- Inclusion of the incoming end. -/
  incoming : V₀ → W
  /-- Inclusion of the outgoing end. -/
  outgoing : V₁ → W
  incoming_embedding : Manifold.IsSmoothEmbedding (𝓡 (n - 1)) (𝓡∂ n) ∞ incoming
  outgoing_embedding : Manifold.IsSmoothEmbedding (𝓡 (n - 1)) (𝓡∂ n) ∞ outgoing
  disjoint : Disjoint (range incoming) (range outgoing)
  boundary_eq : (𝓡∂ n).boundary W = range incoming ∪ range outgoing

namespace SmoothTriad

variable {n : ℕ} [NeZero n] {W V₀ V₁ : Type*}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace n) W]
    [TopologicalSpace V₀] [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) V₀]
    [TopologicalSpace V₁] [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) V₁]
    (T : SmoothTriad n W V₀ V₁)

theorem incoming_mem_boundary (v : V₀) : T.incoming v ∈ (𝓡∂ n).boundary W := by
  rw [T.boundary_eq]
  exact Or.inl ⟨v, rfl⟩

theorem outgoing_mem_boundary (v : V₁) : T.outgoing v ∈ (𝓡∂ n).boundary W := by
  rw [T.boundary_eq]
  exact Or.inr ⟨v, rfl⟩

theorem incoming_ne_outgoing (v : V₀) (w : V₁) : T.incoming v ≠ T.outgoing w := by
  intro h
  exact Set.disjoint_left.mp T.disjoint ⟨v, rfl⟩ ⟨w, h.symm⟩

theorem isCompact_incoming : IsCompact (range T.incoming) := by
  let := T.compact₀
  exact isCompact_range T.incoming_embedding.contMDiff.continuous

theorem isCompact_outgoing : IsCompact (range T.outgoing) := by
  let := T.compact₁
  exact isCompact_range T.outgoing_embedding.contMDiff.continuous

theorem isClosed_incoming : IsClosed (range T.incoming) := by
  let := T.hausdorff
  exact T.isCompact_incoming.isClosed

theorem isClosed_outgoing : IsClosed (range T.outgoing) := by
  let := T.hausdorff
  exact T.isCompact_outgoing.isClosed

/-- The incoming component, viewed as a subset of the manifold boundary. -/
def boundaryIncoming : Set ((𝓡∂ n).boundary W) := Subtype.val ⁻¹' range T.incoming

/-- The outgoing component, viewed as a subset of the manifold boundary. -/
def boundaryOutgoing : Set ((𝓡∂ n).boundary W) := Subtype.val ⁻¹' range T.outgoing

theorem compl_boundaryIncoming : T.boundaryIncomingᶜ = T.boundaryOutgoing := by
  ext x
  change x.1 ∉ range T.incoming ↔ x.1 ∈ range T.outgoing
  constructor
  · intro hx
    have hmem : x.1 ∈ range T.incoming ∪ range T.outgoing := by
      simpa only [T.boundary_eq] using x.2
    exact hmem.resolve_left hx
  · intro hx hx'
    exact Set.disjoint_left.mp T.disjoint hx' hx

theorem isClopen_boundaryIncoming : IsClopen T.boundaryIncoming := by
  constructor
  · exact T.isClosed_incoming.preimage continuous_subtype_val
  · rw [← isClosed_compl_iff, T.compl_boundaryIncoming]
    exact T.isClosed_outgoing.preimage continuous_subtype_val

theorem isClopen_boundaryOutgoing : IsClopen T.boundaryOutgoing := by
  rw [← T.compl_boundaryIncoming]
  exact T.isClopen_boundaryIncoming.compl

/-- The two ends can be exchanged without changing the cobordism's smooth structure. -/
def reverse : SmoothTriad n W V₁ V₀ where
  smooth := T.smooth
  smooth₀ := T.smooth₁
  smooth₁ := T.smooth₀
  compact := T.compact
  compact₀ := T.compact₁
  compact₁ := T.compact₀
  hausdorff := T.hausdorff
  incoming := T.outgoing
  outgoing := T.incoming
  incoming_embedding := T.outgoing_embedding
  outgoing_embedding := T.incoming_embedding
  disjoint := T.disjoint.symm
  boundary_eq := T.boundary_eq.trans (union_comm _ _)

/-- The map identifying the disjoint union of the ends with the actual boundary. -/
def boundaryMap : V₀ ⊕ V₁ → (𝓡∂ n).boundary W :=
  Sum.elim (fun v => ⟨T.incoming v, T.incoming_mem_boundary v⟩)
    (fun v => ⟨T.outgoing v, T.outgoing_mem_boundary v⟩)

theorem boundaryMap_bijective : Function.Bijective T.boundaryMap := by
  constructor
  · intro x y h
    have hval := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact congrArg Sum.inl (T.incoming_embedding.isEmbedding.injective hval)
      | inr y => exact (T.incoming_ne_outgoing x y hval).elim
    | inr x =>
      cases y with
      | inl y => exact (T.incoming_ne_outgoing y x hval.symm).elim
      | inr y =>
        exact congrArg Sum.inr (T.outgoing_embedding.isEmbedding.injective hval)
  · intro x
    have hx : x.1 ∈ range T.incoming ∪ range T.outgoing := by
      rw [← T.boundary_eq]
      exact x.2
    rcases hx with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨Sum.inl v, Subtype.ext hv⟩
    · exact ⟨Sum.inr v, Subtype.ext hv⟩

/-- The boundary decomposition is a homeomorphism for the existing subspace topology. -/
noncomputable def boundaryHomeomorph : V₀ ⊕ V₁ ≃ₜ (𝓡∂ n).boundary W := by
  letI := T.compact₀
  letI := T.compact₁
  letI := T.hausdorff
  let e := Equiv.ofBijective T.boundaryMap T.boundaryMap_bijective
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    ((T.incoming_embedding.contMDiff.continuous.subtype_mk _).sumElim
      (T.outgoing_embedding.contMDiff.continuous.subtype_mk _))

@[simp] theorem boundaryHomeomorph_inl (v : V₀) :
    (T.boundaryHomeomorph (Sum.inl v)).1 = T.incoming v := rfl

@[simp] theorem boundaryHomeomorph_inr (v : V₁) :
    (T.boundaryHomeomorph (Sum.inr v)).1 = T.outgoing v := rfl

end SmoothTriad

end PoincareHighDim
