/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.Basic
import Submission.HCobordismSmoothProduct
import Submission.Homology.Relative.PairTransport

/-!
# Transporting a smooth strip product to an abstract cobordism

A strip presentation embeds the original smooth cobordism into a manifold without boundary
as the region between two regular levels. Given such a presentation, the smooth strip theorem
provides a product diffeomorphism for the original smooth structures and fixes the incoming
boundary. The existence of a strip presentation is a separate geometric theorem; it is not
assumed as part of the definition of a smooth manifold triad.
-/

namespace PoincareHighDim

open Set Topology Manifold
open scoped Manifold ContDiff

universe u

namespace SmoothTriad

variable {m : ℕ} {W V₀ V₁ M : Type u} {H : Type*}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (m + 1)) W]
    [TopologicalSpace V₀] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1 - 1))) V₀]
    [TopologicalSpace V₁] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1 - 1))) V₁]
    [TopologicalSpace M] [TopologicalSpace H] [ChartedSpace H M]
    (T : SmoothTriad (m + 1) W V₀ V₁)
    (I : ModelWithCorners ℝ (Fin (m + 1) → ℝ) H)

/-- A geometric presentation of a smooth triad as a compact strip. The critical points
inside the strip are unrestricted. No collar or product decomposition is included. -/
structure StripPresentation where
  embedding : W → M
  isEmbedding : IsEmbedding embedding
  contMDiff_embedding : ContMDiff (𝓡∂ (m + 1)) I ∞ embedding
  smooth_lift :
    ∀ {EN HN : Type} {N : Type u} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
      (J : ModelWithCorners ℝ EN HN) [IsManifold J ∞ N] (k : N → W),
      Continuous k → ContMDiff J I ∞ (embedding ∘ k) → ContMDiff J (𝓡∂ (m + 1)) ∞ k
  function : M → ℝ
  smooth_function : ContMDiff I 𝓘(ℝ, ℝ) ∞ function
  lower : ℝ
  upper : ℝ
  lt : lower < upper
  range_eq : range embedding = function ⁻¹' Icc lower upper
  incoming_eq : range (embedding ∘ T.incoming) = function ⁻¹' {lower}
  outgoing_eq : range (embedding ∘ T.outgoing) = function ⁻¹' {upper}
  regular : ∀ x, function x = lower ∨ function x = upper → ¬ IsCriticalPt I function x

namespace StripPresentation

variable {T I} (P : T.StripPresentation (M := M) I)

/-- The original cobordism and its strip have the same topology. -/
noncomputable def cobordismHomeomorph : W ≃ₜ (P.function ⁻¹' Icc P.lower P.upper) :=
  P.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr P.range_eq)

/-- The incoming boundary and the lower level have the same topology. -/
noncomputable def incomingHomeomorph : V₀ ≃ₜ (P.function ⁻¹' {P.lower}) :=
  (P.isEmbedding.comp T.incoming_embedding.isEmbedding).toHomeomorph.trans
    (Homeomorph.setCongr P.incoming_eq)

/-- The outgoing boundary and the upper level have the same topology. -/
noncomputable def outgoingHomeomorph : V₁ ≃ₜ (P.function ⁻¹' {P.upper}) :=
  (P.isEmbedding.comp T.outgoing_embedding.isEmbedding).toHomeomorph.trans
    (Homeomorph.setCongr P.outgoing_eq)

@[simp] theorem cobordismHomeomorph_apply_val (x : W) :
    (P.cobordismHomeomorph x).1 = P.embedding x := rfl

@[simp] theorem incomingHomeomorph_apply_val (x : V₀) :
    (P.incomingHomeomorph x).1 = P.embedding (T.incoming x) := rfl

@[simp] theorem outgoingHomeomorph_apply_val (x : V₁) :
    (P.outgoingHomeomorph x).1 = P.embedding (T.outgoing x) := rfl

@[simp] theorem embedding_cobordismHomeomorph_symm (x : P.function ⁻¹' Icc P.lower P.upper) :
    P.embedding (P.cobordismHomeomorph.symm x) = x.1 :=
  congrArg Subtype.val (P.cobordismHomeomorph.apply_symm_apply x)

@[simp] theorem embedding_incomingHomeomorph_symm (x : P.function ⁻¹' {P.lower}) :
    P.embedding (T.incoming (P.incomingHomeomorph.symm x)) = x.1 :=
  congrArg Subtype.val (P.incomingHomeomorph.apply_symm_apply x)

theorem incoming_mem_iff (x : W) :
    x ∈ range T.incoming ↔ P.function (P.embedding x) = P.lower := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (P.incomingHomeomorph v).2
  · intro hx
    have hmem : P.embedding x ∈ range (P.embedding ∘ T.incoming) := by
      rw [P.incoming_eq]
      exact hx
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, P.isEmbedding.injective hv⟩

theorem outgoing_mem_iff (x : W) :
    x ∈ range T.outgoing ↔ P.function (P.embedding x) = P.upper := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (P.outgoingHomeomorph v).2
  · intro hx
    have hmem : P.embedding x ∈ range (P.embedding ∘ T.outgoing) := by
      rw [P.outgoing_eq]
      exact hx
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, P.isEmbedding.injective hv⟩

/-- The strip is compact because the original cobordism is compact. -/
theorem isCompact_band : IsCompact (P.function ⁻¹' Icc P.lower P.upper) := by
  let := T.compact
  rw [← P.range_eq]
  exact isCompact_range P.contMDiff_embedding.continuous

/-- The relative integral homology hypothesis transfers without strengthening it to a
homotopy equivalence hypothesis. -/
theorem relHomologyVanishes (h : RelHomologyVanishes W (range T.incoming)) :
    RelHomologyVanishes (P.function ⁻¹' Icc P.lower P.upper)
      (Subtype.val ⁻¹' (P.function ⁻¹' {P.lower})) := by
  apply h.homeomorph_of_mem_iff P.cobordismHomeomorph
  intro x
  exact P.incoming_mem_iff x

/-- The strip homeomorphism respects the original smooth structure on the cobordism.
Both directions are smooth because the strip structure is induced by the ambient inclusion. -/
noncomputable def cobordismDiffeomorph
    {EB HB : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    (J : ModelWithCorners ℝ EB HB)
    (A : InducedSmoothStructure I J (P.function ⁻¹' Icc P.lower P.upper)) :
    letI := A.chartedSpace
    W ≃ₘ⟮𝓡∂ (m + 1), J⟯ (P.function ⁻¹' Icc P.lower P.upper) := by
  letI := T.smooth
  letI := A.chartedSpace
  letI := A.isManifold
  refine { P.cobordismHomeomorph.toEquiv with
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · exact A.smooth_lift (𝓡∂ (m + 1)) _ P.cobordismHomeomorph.continuous
      P.contMDiff_embedding
  · apply P.smooth_lift J
    · exact P.cobordismHomeomorph.symm.continuous
    · exact A.smooth_inclusion.congr (fun x => P.embedding_cobordismHomeomorph_symm x)

/-- The incoming-level homeomorphism respects the original smooth structure on the boundary. -/
noncomputable def incomingDiffeomorph
    {EB HB : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    (J : ModelWithCorners ℝ EB HB)
    (A : InducedSmoothStructure I J (P.function ⁻¹' {P.lower})) :
    letI := A.chartedSpace
    V₀ ≃ₘ⟮𝓡 (m + 1 - 1), J⟯ (P.function ⁻¹' {P.lower}) := by
  letI := T.smooth
  letI := T.smooth₀
  letI := A.chartedSpace
  letI := A.isManifold
  refine { P.incomingHomeomorph.toEquiv with
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · exact A.smooth_lift (𝓡 (m + 1 - 1)) _ P.incomingHomeomorph.continuous
      (P.contMDiff_embedding.comp T.incoming_embedding.contMDiff)
  · rw [ContMDiff.iff_comp_isImmersion T.incoming_embedding.isImmersion]
    refine ⟨P.incomingHomeomorph.symm.continuous, ?_⟩
    apply P.smooth_lift J
    · exact T.incoming_embedding.contMDiff.continuous.comp P.incomingHomeomorph.symm.continuous
    · exact A.smooth_inclusion.congr (fun x => P.embedding_incomingHomeomorph_symm x)

/-- Transport an ambient smooth product to the original cobordism and its original incoming
boundary, retaining the given smooth structures and the boundary identifications. -/
theorem exists_product_of_inducedSmoothProduct
    (Q : InducedSmoothProduct I 𝓘(ℝ, Fin m → ℝ)
      (P.function ⁻¹' {P.lower}) (P.function ⁻¹' Icc P.lower P.upper)
      (P.function ⁻¹' {P.upper})) :
    ∃ Φ : (V₀ × unitInterval) ≃ₘ⟮(𝓡 (m + 1 - 1)).prod (𝓡∂ 1), 𝓡∂ (m + 1)⟯ W,
      (∀ v, Φ (v, 0) = T.incoming v) ∧
      (∀ p, Φ p ∈ range T.incoming ↔ p.2 = 0) ∧
      (∀ p, Φ p ∈ range T.outgoing ↔ p.2 = 1) := by
  let := Q.incoming.chartedSpace
  let := Q.cobordism.chartedSpace
  let dV := P.incomingDiffeomorph 𝓘(ℝ, Fin m → ℝ) Q.incoming
  let dW := P.cobordismDiffeomorph (𝓘(ℝ, Fin m → ℝ).prod (𝓡∂ 1)) Q.cobordism
  let Φ := ((dV.prodCongr (Diffeomorph.refl (𝓡∂ 1) unitInterval ∞)).trans
    Q.diffeomorph).trans dW.symm
  have hΦ (p : V₀ × unitInterval) :
      P.embedding (Φ p) = (Q.diffeomorph (dV p.1, p.2)).1 :=
    P.embedding_cobordismHomeomorph_symm _
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro v
    apply P.isEmbedding.injective
    rw [hΦ, Q.fixes_incoming]
    rfl
  · intro p
    rw [P.incoming_mem_iff, hΦ]
    exact Q.incoming_iff (dV p.1, p.2)
  · intro p
    rw [P.outgoing_mem_iff, hΦ]
    exact Q.outgoing_iff (dV p.1, p.2)

include P

/-- The smooth h-cobordism product conclusion on the original smooth manifolds, conditional
only on an explicit strip presentation. Constructing such a presentation for every smooth
triad is a separate geometric requirement. -/
theorem exists_product_diffeomorph [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (h6 : 6 ≤ m + 1)
    [SimplyConnectedSpace W] [SimplyConnectedSpace V₀] [SimplyConnectedSpace V₁]
    (hH : RelHomologyVanishes W (range T.incoming)) :
    ∃ Φ : (V₀ × unitInterval) ≃ₘ⟮(𝓡 (m + 1 - 1)).prod (𝓡∂ 1), 𝓡∂ (m + 1)⟯ W,
      (∀ v, Φ (v, 0) = T.incoming v) ∧
      (∀ p, Φ p ∈ range T.incoming ↔ p.2 = 0) ∧
      (∀ p, Φ p ∈ range T.outgoing ↔ p.2 = 1) := by
  have hW : SimplyConnectedSpace (P.function ⁻¹' Icc P.lower P.upper) :=
    P.cobordismHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  have hV₀ : SimplyConnectedSpace (P.function ⁻¹' {P.lower}) :=
    P.incomingHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  have hV₁ : SimplyConnectedSpace (P.function ⁻¹' {P.upper}) :=
    P.outgoingHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨Q⟩ := nonempty_hcobordism_inducedSmoothProduct h6 P.smooth_function P.lt
    P.isCompact_band P.regular hW hV₀ hV₁ (P.relHomologyVanishes hH)
  exact P.exists_product_of_inducedSmoothProduct Q

end StripPresentation
end SmoothTriad
end PoincareHighDim
