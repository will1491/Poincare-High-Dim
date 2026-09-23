import Submission.Morse.Defs

/-!
# Elimination of critical points of extremal index

Milnor, *Lectures on the h-cobordism theorem*, Theorem 8.1.

* `exists_no_extremal_index` (index `0` and `n`): if every component of the strip meets both
  ends (here: the strip is connected and both ends are nonempty), the critical points of index
  `0` can be cancelled against index-`1` points (Milnor's First Cancellation Theorem 5.4 applied
  to a pair whose spheres meet in one point), and dually for index `n`.
* `exists_index_in_middle` (index `1` and `n - 1`): if the strip and its ends are simply
  connected and `n ≥ 5`, index-`1` points are traded for index-`3` points (insertion of an
  auxiliary cancelling pair of index `2, 3` followed by a cancellation), and dually for index
  `n - 1`.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **Elimination of index `0` and `n`** (Milnor, Theorem 8.1, index 0, and its dual). -/
theorem exists_no_extremal_index (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : IsSelfIndexing I f a b)
    (hconn : ConnectedSpace (f ⁻¹' Icc a b))
    (ha : (f ⁻¹' {a}).Nonempty) (hb : (f ⁻¹' {b}).Nonempty) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
      ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x → 0 < morseIndex I g x ∧ morseIndex I g x < n := by
  sorry

/-- **Elimination of index `1` and `n - 1`** (Milnor, Theorem 8.1, index 1, and its dual). -/
theorem exists_index_in_middle (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h5 : 5 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : IsSelfIndexing I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → IsCriticalPt I f x → 0 < morseIndex I f x ∧ morseIndex I f x < n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b})) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
      ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
        2 ≤ morseIndex I g x ∧ morseIndex I g x + 2 ≤ n := by
  sorry

end PoincareHighDim
