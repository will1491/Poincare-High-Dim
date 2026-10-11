/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.StripProduct

/-!
# Restricting a strip presentation to an open neighborhood

A defining function only needs to be smooth on a neighborhood of the cobordism.
Restricting the ambient manifold and function to that neighborhood gives the global
strip presentation required by the smooth product theorem.
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

/-- A strip defining function on an open neighborhood of an embedded smooth triad. -/
structure OpenStripPresentation where
  embedding : W → M
  isEmbedding : IsEmbedding embedding
  contMDiff_embedding : ContMDiff (𝓡∂ (m + 1)) I ∞ embedding
  smooth_lift :
    ∀ {EN HN : Type} {N : Type u} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
      (J : ModelWithCorners ℝ EN HN) [IsManifold J ∞ N] (k : N → W),
      Continuous k → ContMDiff J I ∞ (embedding ∘ k) → ContMDiff J (𝓡∂ (m + 1)) ∞ k
  neighborhood : TopologicalSpace.Opens M
  range_subset : range embedding ⊆ neighborhood
  function : M → ℝ
  smooth_function : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ function neighborhood
  band_iff : ∀ x ∈ neighborhood, function x ∈ Icc (0 : ℝ) 1 ↔ x ∈ range embedding
  incoming_iff : ∀ x ∈ neighborhood, function x = 0 ↔ x ∈ range (embedding ∘ T.incoming)
  outgoing_iff : ∀ x ∈ neighborhood, function x = 1 ↔ x ∈ range (embedding ∘ T.outgoing)
  regular : ∀ x ∈ neighborhood, function x = 0 ∨ function x = 1 →
    mfderiv I 𝓘(ℝ, ℝ) function x ≠ 0

namespace OpenStripPresentation

variable {T I} (P : T.OpenStripPresentation (M := M) I)

/-- Restrict the embedding to the neighborhood carrying the defining function. -/
def restrictedEmbedding : W → P.neighborhood :=
  fun x => ⟨P.embedding x, P.range_subset (mem_range_self x)⟩

theorem isEmbedding_restrictedEmbedding : IsEmbedding P.restrictedEmbedding :=
  P.isEmbedding.codRestrict _ _

theorem smooth_restrictedEmbedding :
    ContMDiff (𝓡∂ (m + 1)) I ∞ P.restrictedEmbedding :=
  (ContMDiff.subtypeVal_comp_iff P.neighborhood P.restrictedEmbedding).mp
    P.contMDiff_embedding

theorem smooth_restrictedFunction :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : P.neighborhood => P.function x) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr
    (P.smooth_function.contMDiffAt (P.neighborhood.isOpen.mem_nhds x.property))

/-- The inclusion of an open subset has surjective differential in the same
finite-dimensional ambient model. Thus a nonzero differential stays nonzero on restriction. -/
theorem regular_restrictedFunction [IsManifold I ∞ M] (x : P.neighborhood)
    (hx : P.function x = 0 ∨ P.function x = 1) :
    ¬ IsCriticalPt I (fun y : P.neighborhood => P.function y) x := by
  have hi := (Manifold.IsImmersion.of_opens (I := I) (n := ∞) P.neighborhood).injective_mfderiv
    (by simp) x
  have hs : Function.Surjective (mfderiv I I (Subtype.val : P.neighborhood → M) x) :=
    LinearMap.injective_iff_surjective.mp hi
  have hf := (P.smooth_function.contMDiffAt
    (P.neighborhood.isOpen.mem_nhds x.property)).mdifferentiableAt (by simp)
  have hv := (contMDiff_subtype_val (I := I) (U := P.neighborhood) (n := ∞)).mdifferentiableAt
    (by simp) (x := x)
  intro hzero
  apply P.regular x x.property hx
  ext v
  obtain ⟨w, rfl⟩ := hs v
  have hcomp := congrArg (fun L => L w) hzero
  change (mfderiv I 𝓘(ℝ, ℝ) (P.function ∘ Subtype.val) x) w = 0 at hcomp
  rw [mfderiv_comp x hf hv] at hcomp
  exact hcomp

/-- Pass from neighborhood data to a global strip presentation on the open submanifold. -/
noncomputable def toStripPresentation [IsManifold I ∞ M] :
    T.StripPresentation (M := P.neighborhood) I where
  embedding := P.restrictedEmbedding
  isEmbedding := P.isEmbedding_restrictedEmbedding
  contMDiff_embedding := P.smooth_restrictedEmbedding
  smooth_lift := by
    intro EN HN N _ _ _ _ _ J _ k hk hf
    exact P.smooth_lift J k hk (contMDiff_subtype_val.comp hf)
  function := fun x => P.function x
  smooth_function := P.smooth_restrictedFunction
  lower := 0
  upper := 1
  lt := zero_lt_one
  range_eq := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (P.band_iff _ (P.restrictedEmbedding w).property).mpr (mem_range_self w)
    · intro hx
      obtain ⟨w, hw⟩ := (P.band_iff x x.property).mp hx
      exact ⟨w, Subtype.ext hw⟩
  incoming_eq := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (P.incoming_iff _ (P.restrictedEmbedding (T.incoming v)).property).mpr
        (mem_range_self v)
    · intro hx
      obtain ⟨v, hv⟩ := (P.incoming_iff x x.property).mp hx
      exact ⟨v, Subtype.ext hv⟩
  outgoing_eq := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (P.outgoing_iff _ (P.restrictedEmbedding (T.outgoing v)).property).mpr
        (mem_range_self v)
    · intro hx
      obtain ⟨v, hv⟩ := (P.outgoing_iff x x.property).mp hx
      exact ⟨v, Subtype.ext hv⟩
  regular := P.regular_restrictedFunction

/-- Package a regular defining function on a set-valued open neighborhood together
with a smooth embedding and its smooth lifting property. -/
theorem nonempty_of_regular_strip_function
    (e : W → M) (he : IsEmbedding e) (hse : ContMDiff (𝓡∂ (m + 1)) I ∞ e)
    (hlift : ∀ {EN HN : Type} {N : Type u} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
      (J : ModelWithCorners ℝ EN HN) [IsManifold J ∞ N] (k : N → W),
      Continuous k → ContMDiff J I ∞ (e ∘ k) → ContMDiff J (𝓡∂ (m + 1)) ∞ k)
    (hdata : ∃ (O : Set M) (f : M → ℝ), IsOpen O ∧ range e ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f O ∧
      (∀ x ∈ O, f x ∈ Icc (0 : ℝ) 1 ↔ x ∈ range e) ∧
      (∀ x ∈ O, f x = 0 ↔ x ∈ range (e ∘ T.incoming)) ∧
      (∀ x ∈ O, f x = 1 ↔ x ∈ range (e ∘ T.outgoing)) ∧
      (∀ x ∈ range (e ∘ T.incoming) ∪ range (e ∘ T.outgoing),
        mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)) :
    Nonempty (T.OpenStripPresentation (M := M) I) := by
  obtain ⟨O, f, hO, hsub, hf, hband, hin, hout, hreg⟩ := hdata
  refine ⟨{
    embedding := e
    isEmbedding := he
    contMDiff_embedding := hse
    smooth_lift := hlift
    neighborhood := ⟨O, hO⟩
    range_subset := hsub
    function := f
    smooth_function := hf
    band_iff := hband
    incoming_iff := hin
    outgoing_iff := hout
    regular := ?_ }⟩
  intro x hx heq
  exact hreg x (heq.elim (fun h => Or.inl ((hin x hx).mp h))
    (fun h => Or.inr ((hout x hx).mp h)))

include P

/-- Apply the smooth strip product theorem to neighborhood defining data. -/
theorem exists_product_diffeomorph [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SecondCountableTopology M] [LocallyCompactSpace H] (h6 : 6 ≤ m + 1)
    [SimplyConnectedSpace W] [SimplyConnectedSpace V₀] [SimplyConnectedSpace V₁]
    (hH : RelHomologyVanishes W (range T.incoming)) :
    ∃ Φ : (V₀ × unitInterval) ≃ₘ⟮(𝓡 (m + 1 - 1)).prod (𝓡∂ 1), 𝓡∂ (m + 1)⟯ W,
      (∀ v, Φ (v, 0) = T.incoming v) ∧
      (∀ p, Φ p ∈ range T.incoming ↔ p.2 = 0) ∧
      (∀ p, Φ p ∈ range T.outgoing ↔ p.2 = 1) := by
  let : LocallyCompactSpace P.neighborhood := ChartedSpace.locallyCompactSpace H _
  exact P.toStripPresentation.exists_product_diffeomorph h6 hH

end OpenStripPresentation
end SmoothTriad
end PoincareHighDim
