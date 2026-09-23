import Submission.Morse.Defs
import Submission.Morse.ExistenceProof

/-!
# Existence of Morse functions on a strip

Milnor, *Lectures on the h-cobordism theorem*, Theorem 2.5 (with Lemmas 2.6, A, B, 2.7) in strip
form: a smooth function with two regular values `a < b` and compact strip can be perturbed inside
the open strip into a Morse function.  The proof (in `Submission.Morse.ExistenceProof`)
adds small linear functions chart by chart (Sard's theorem in the equidimensional case, available
in Mathlib as `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) and uses the stability of
nondegeneracy under `C²`-small perturbations.

Throughout the Morse-theoretic chain the model vector space is `Fin n → ℝ`, the model used by
the `DifferentialGeometry` dependency (`MorseModel n`), so that its theorems apply verbatim.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **Existence of Morse functions** (Milnor, Theorem 2.5, strip form). A smooth function with
regular values `a < b` and compact strip can be modified inside the open strip so that it becomes
a Morse function on the strip. -/
theorem exists_morseStrip (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPt I f x) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b :=
  exists_morseStrip_proof I f hf hab hcompact hreg

end PoincareHighDim
