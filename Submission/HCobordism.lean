import Submission.Morse.Existence
import Submission.Morse.SelfIndexing
import Submission.Morse.LowHandles
import Submission.Morse.MiddleHandles

/-!
# The h-cobordism theorem (strip form)

Smale's h-cobordism theorem in the form of Milnor, *Lectures on the h-cobordism theorem*,
Theorem 9.1, with the homological hypothesis `H_*(W, V₀; ℤ) = 0` replaced by the (stronger but
equivalent under simple connectivity) hypothesis that the inclusion `V₀ ↪ W` is a homotopy
equivalence: a simply connected strip of dimension `≥ 6` with simply connected ends, whose lower
end is included by a homotopy equivalence, is a product cobordism.

The proof is the assembly of the Morse-theoretic nodes: produce a Morse function on the strip
(`exists_morseStrip`), make it self-indexing (`exists_selfIndexing`), eliminate the critical
points of index `0` and `n` (`exists_no_extremal_index`), then of index `1` and `n - 1`
(`exists_index_in_middle`), and cancel the remaining ones (`product_of_middle_indices`).  The
hypotheses transfer along each modification because a modification supported in the open strip
does not change the strip, its ends, or the two sublevel sets (`ModifiedWithin.preimage_Icc`
and friends).
-/

namespace PoincareHighDim

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **The h-cobordism theorem** (Smale; Milnor, Theorem 9.1) in strip form. -/
theorem hcobordism_strip (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h6 : 6 ≤ n)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPt I f x)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (he₀ : IsHomotopyEquivInclusion (f ⁻¹' {a}) (f ⁻¹' Icc a b)) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, Φ '' (f ⁻¹' Iic a) = f ⁻¹' Iic b ∧ Φ '' (f ⁻¹' {a}) = f ⁻¹' {b} := by
  -- Step 1: a Morse function on the strip.
  obtain ⟨g₁, hg₁, hM₁⟩ := exists_morseStrip I f hf hab hcompact hreg
  -- Step 2: make it self-indexing.
  obtain ⟨g₂, hg₂, hM₂, hsi₂, -, -⟩ := exists_selfIndexing I hM₁
  have hf₂ : ModifiedWithin f a b g₂ := hg₁.trans hg₂
  -- Step 3: eliminate the critical points of index `0` and `n`.
  have hconn₂ : ConnectedSpace (g₂ ⁻¹' Icc a b) := by
    rw [hf₂.preimage_Icc]
    infer_instance
  have ha₂ : (g₂ ⁻¹' {a}).Nonempty := by
    rw [hf₂.preimage_singleton_left]
    exact IsSimplyConnected.nonempty hV₀
  have hb₂ : (g₂ ⁻¹' {b}).Nonempty := by
    rw [hf₂.preimage_singleton_right]
    exact IsSimplyConnected.nonempty hV₁
  obtain ⟨g₃, hg₃, hM₃, hsi₃, hidx₃⟩ := exists_no_extremal_index I hM₂ hsi₂ hconn₂ ha₂ hb₂
  have hf₃ : ModifiedWithin f a b g₃ := hf₂.trans hg₃
  -- Step 4: eliminate the critical points of index `1` and `n - 1`.
  have hW₃ : SimplyConnectedSpace (g₃ ⁻¹' Icc a b) := by
    rw [hf₃.preimage_Icc]
    exact hW
  have hV₀₃ : SimplyConnectedSpace (g₃ ⁻¹' {a}) := by
    rw [hf₃.preimage_singleton_left]
    exact hV₀
  have hV₁₃ : SimplyConnectedSpace (g₃ ⁻¹' {b}) := by
    rw [hf₃.preimage_singleton_right]
    exact hV₁
  obtain ⟨g₄, hg₄, hM₄, -, hidx₄⟩ :=
    exists_index_in_middle I (le_trans (by norm_num) h6) hM₃ hsi₃ hidx₃ hW₃ hV₀₃ hV₁₃
  have hf₄ : ModifiedWithin f a b g₄ := hf₃.trans hg₄
  -- Step 5: cancel the remaining middle-dimensional critical points.
  have hW₄ : SimplyConnectedSpace (g₄ ⁻¹' Icc a b) := by
    rw [hf₄.preimage_Icc]
    exact hW
  have hV₀₄ : SimplyConnectedSpace (g₄ ⁻¹' {a}) := by
    rw [hf₄.preimage_singleton_left]
    exact hV₀
  have hV₁₄ : SimplyConnectedSpace (g₄ ⁻¹' {b}) := by
    rw [hf₄.preimage_singleton_right]
    exact hV₁
  have he₀₄ : IsHomotopyEquivInclusion (g₄ ⁻¹' {a}) (g₄ ⁻¹' Icc a b) := by
    rw [hf₄.preimage_singleton_left, hf₄.preimage_Icc]
    exact he₀
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ :=
    product_of_middle_indices I h6 hM₄ hidx₄ hW₄ hV₀₄ hV₁₄ he₀₄
  -- Step 6: transport the conclusion back to `f`.
  refine ⟨Φ, ?_, ?_⟩
  · rwa [hf₄.preimage_Iic_left, hf₄.preimage_Iic_right] at hΦ₁
  · rwa [hf₄.preimage_singleton_left, hf₄.preimage_singleton_right] at hΦ₂

end PoincareHighDim
