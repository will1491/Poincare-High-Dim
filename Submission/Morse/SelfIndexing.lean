import Submission.Morse.Defs

/-!
# Rearrangement and self-indexing Morse functions

Milnor, *Lectures on the h-cobordism theorem*, §4 (Theorems 4.1, 4.4, 4.8): a Morse function on
a strip can be replaced, without changing its critical points, their indices, or its behaviour
near the ends of the strip, by a Morse function whose critical values are ordered by index.  The
proof rearranges critical levels along a gradient-like vector field after making left- and
right-hand spheres of wrongly ordered critical points disjoint by general position (Sard).
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
  sorry

end PoincareHighDim
