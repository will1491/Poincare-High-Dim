/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.StripExistence

/-!
# Milnor's smooth h-cobordism theorem

Milnor, *Lectures on the h-Cobordism Theorem*, Theorem 9.1: a compact smooth
manifold triad `(W; V₀, V₁)` of dimension at least six, with all three manifolds
simply connected and `H_*(W,V₀; ℤ) = 0`, is diffeomorphic to `V₀ × [0,1]`.
The diffeomorphism restricts to the given incoming boundary identification.

The strip presentation is constructed for the original smooth triad; no collar,
ambient extension, Morse function, or strip presentation is assumed.
-/

namespace PoincareHighDim
namespace SmoothTriad

open Set Topology
open scoped Manifold ContDiff

universe u

/-- Milnor's Theorem 9.1, with the dimension of the cobordism written as `m + 1`. -/
theorem milnor_9_1_succ {m : ℕ} {W V₀ V₁ : Type u}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (m + 1)) W]
    [TopologicalSpace V₀] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1 - 1))) V₀]
    [TopologicalSpace V₁] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1 - 1))) V₁]
    (T : SmoothTriad (m + 1) W V₀ V₁) (h6 : 6 ≤ m + 1)
    [SimplyConnectedSpace W] [SimplyConnectedSpace V₀] [SimplyConnectedSpace V₁]
    (hH : RelHomologyVanishes W (range T.incoming)) :
    ∃ Φ : (V₀ × unitInterval) ≃ₘ⟮(𝓡 (m + 1 - 1)).prod (𝓡∂ 1), 𝓡∂ (m + 1)⟯ W,
      (∀ v, Φ (v, 0) = T.incoming v) ∧
      (∀ p, Φ p ∈ range T.incoming ↔ p.2 = 0) ∧
      (∀ p, Φ p ∈ range T.outgoing ↔ p.2 = 1) := by
  let := T.smooth
  let := T.compact
  let := T.hausdorff
  let : SecondCountableTopology W :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanHalfSpace (m + 1)) W
  let := (ManifoldInterior.inducedAtlas (𝓡∂ (m + 1)) (W := W)).chartedSpace
  let := interior_isManifold (n := m + 1) (W := W)
  obtain ⟨P⟩ := T.nonempty_openStripPresentation
  exact P.exists_product_diffeomorph h6 hH

/-- **Milnor's Theorem 9.1.** A compact smooth manifold triad of dimension `n ≥ 6`,
with simply connected cobordism and ends and vanishing integral homology relative
to the incoming end, is a smooth product relative to that end. -/
theorem milnor_9_1 {n : ℕ} [NeZero n] {W V₀ V₁ : Type u}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace n) W]
    [TopologicalSpace V₀] [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) V₀]
    [TopologicalSpace V₁] [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) V₁]
    (T : SmoothTriad n W V₀ V₁) (h6 : 6 ≤ n)
    [SimplyConnectedSpace W] [SimplyConnectedSpace V₀] [SimplyConnectedSpace V₁]
    (hH : RelHomologyVanishes W (range T.incoming)) :
    ∃ Φ : (V₀ × unitInterval) ≃ₘ⟮(𝓡 (n - 1)).prod (𝓡∂ 1), 𝓡∂ n⟯ W,
      (∀ v, Φ (v, 0) = T.incoming v) ∧
      (∀ p, Φ p ∈ range T.incoming ↔ p.2 = 0) ∧
      (∀ p, Φ p ∈ range T.outgoing ↔ p.2 = 1) := by
  cases n with
  | zero => omega
  | succ m => exact T.milnor_9_1_succ h6 hH

end SmoothTriad
end PoincareHighDim
