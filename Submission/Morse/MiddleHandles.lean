import Submission.Morse.Defs
import Submission.Morse.RegularInterval
import Submission.Homology.PairVanishing

/-!
# Cancellation of critical points in the middle dimensions

Milnor, *Lectures on the h-cobordism theorem*, Theorem 7.8: a strip `W` of dimension `n ≥ 6`
whose Morse function has all critical points of index in `[2, n - 2]`, whose strip and ends
`V₀`, `V₁` are simply connected, and with `H_*(W, V₀; ℤ) = 0` (`RelHomologyVanishes`, the
relative singular homology of `Submission.Homology.SingularPair`), is a product cobordism.
This is Milnor's hypothesis verbatim; the homotopy-theoretic form (the inclusion `V₀ ↪ W` is a
homotopy equivalence) implies it by `IsHomotopyEquivInclusion.relHomologyVanishes`.

This single node hides the deepest parts of the theory: the handle chain complex and the fact
that it computes `H_*(W, V₀)` (Theorem 7.4, which needs singular homology of pairs with
excision), the basis theorem realising elementary basis changes by handle slides (Theorem 7.6),
the Whitney trick (Theorem 6.6) and the Second Cancellation Theorem (Theorem 6.4), and finally
the First Cancellation Theorem (Theorem 5.4) and the regular interval theorem (`regular_interval`).
-/

namespace PoincareHighDim

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **Middle-dimensional cancellation** (Milnor, Theorem 7.8, strip form): `W = f ⁻¹' [a, b]`
of dimension `n ≥ 6`, all critical points of index in `[2, n - 2]`, `W`, `V₀ = f ⁻¹' {a}` and
`V₁ = f ⁻¹' {b}` simply connected, and `H_*(W, V₀; ℤ) = 0`. -/
theorem product_of_middle_indices (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h6 : 6 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → IsCriticalPt I f x →
      2 ≤ morseIndex I f x ∧ morseIndex I f x + 2 ≤ n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : RelHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a}))) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, Φ '' (f ⁻¹' Iic a) = f ⁻¹' Iic b ∧ Φ '' (f ⁻¹' {a}) = f ⁻¹' {b} := by
  sorry

end PoincareHighDim
