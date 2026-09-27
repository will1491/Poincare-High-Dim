import Submission.Morse.Cancellation.FirstCancellation
import Submission.Homology.Relative.PairVanishing
import Submission.Morse.Handles.Middle.MiddleAssembly

/-!
# One step of the middle-dimensional cancellation (Milnor 7.8)

Milnor, *Lectures on the h-cobordism theorem*, Theorem 7.8, one inductive step: under the
hypotheses of the middle-dimensional cancellation (`n ≥ 6`, all critical points of index in
`[2, n - 2]`, `W`, `V₀`, `V₁` simply connected, `H_*(W, V₀; ℤ) = 0`), a strip with at least one
critical point can be modified so that some critical point disappears and no new critical point
appears.

Milnor's proof: make `f` self-indexing (Theorem 4.8); the handle chain complex
`C_λ = H_λ(W_λ, W_{λ-1})`, free on the left-hand discs, computes `H_*(W, V₀) = 0` (Theorem 7.4),
and its boundary is the matrix of intersection numbers of right-hand and left-hand spheres
(Lemma 7.2); by the basis theorem (Theorem 7.6: handle slides realise elementary basis changes)
the bases can be chosen so that some index-`λ` point `p` and index-`(λ + 1)` point `q` have
intersection number `±1`; the Whitney trick (Theorem 6.6) then makes the two spheres meet in a
single transverse point (Second Cancellation Theorem 6.4, or 6.5 for `-f`), and the First
Cancellation Theorem 5.4 removes `p` and `q`.

`exists_middle_cancel_step` is `middle_target` (`Submission/Morse/Handles/Middle/MiddleAssembly.lean`), proved
in the modules `MiddleSard` … `MiddleAssembly`.
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **One step of the middle-dimensional cancellation** (Milnor 7.8): under the hypotheses of
`product_of_middle_indices`, if the open strip contains a critical point, then `f` can be
modified within the strip so that some critical point disappears and every critical point of the
modification is an old critical point with its old index. -/
theorem exists_middle_cancel_step (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h6 : 6 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → IsCriticalPt I f x →
      2 ≤ morseIndex I f x ∧ morseIndex I f x + 2 ≤ n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : RelHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a})))
    {p₀ : M} (hp₀ : f p₀ ∈ Ioo a b ∧ IsCriticalPt I f p₀) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
        IsCriticalPt I f x ∧ morseIndex I g x = morseIndex I f x) ∧
      ∃ p, f p ∈ Ioo a b ∧ IsCriticalPt I f p ∧ ¬ IsCriticalPt I g p := by
  exact middle_target I h6 hf hidx hW hV₀ hV₁ hH hp₀

end PoincareHighDim
