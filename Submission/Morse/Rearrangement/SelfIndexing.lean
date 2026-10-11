/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Morse.Rearrangement.Swap

/-!
# Rearrangement and self-indexing Morse functions

Milnor, *Lectures on the h-cobordism theorem*, §4 (Theorems 4.1, 4.4, 4.8): a Morse function on
a strip can be replaced, without changing its critical points, their indices, or its behaviour
near the ends of the strip, by a Morse function whose critical values are ordered by index.  The
proof rearranges critical levels along a gradient-like vector field after making left- and
right-hand spheres of wrongly ordered critical points disjoint by general position (Sard).

The proof here first makes the critical values pairwise distinct
(`exists_distinct_critical_values`, Milnor 2.8) and then removes the inverted pairs one adjacent
swap at a time (`Swap.exists_swap`, `Swap.exists_selfIndexing_of_injOn`,
`Submission/Morse/Rearrangement/Swap.lean`).
-/

namespace PoincareHighDim

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **Self-indexing** (Milnor, Theorem 4.8, alternate version). -/
theorem exists_selfIndexing (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
      (∀ x, f x ∈ Ioo a b → (IsCriticalPt I g x ↔ IsCriticalPt I f x)) ∧
      (∀ x, f x ∈ Ioo a b → IsCriticalPt I f x → morseIndex I g x = morseIndex I f x) := by
  obtain ⟨f₁, hmod₁, hf₁, hcrit₁, hidx₁, hinj₁⟩ := exists_distinct_critical_values I hf
  have hpre : ∀ x, f₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₁.preimage_Ioo x
  have hinj : InjOn f₁ {x | f₁ x ∈ Ioo a b ∧ IsCriticalPt I f₁ x} := by
    refine hinj₁.mono fun x hx => ?_
    have hfx : f x ∈ Ioo a b := (hpre x).1 hx.1
    exact ⟨hfx, (hcrit₁ x hfx).1 hx.2⟩
  obtain ⟨g, hmod₂, hg, hself, hcrit₂, hidx₂⟩ :=
    Swap.exists_selfIndexing_of_injOn _ f₁ hf₁ hinj rfl
  refine ⟨g, hmod₁.trans hmod₂, hg, hself, fun x hx => (hcrit₂ x).trans (hcrit₁ x hx),
    fun x hx hc => ?_⟩
  rw [hidx₂ x ((hcrit₁ x hx).2 hc), hidx₁ x hx hc]

end PoincareHighDim
