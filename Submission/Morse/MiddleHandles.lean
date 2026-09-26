import Submission.Morse.Defs
import Submission.Morse.RegularInterval
import Submission.Homology.PairVanishing
import Submission.Morse.MiddleStep

/-!
# Cancellation of critical points in the middle dimensions

Milnor, *Lectures on the h-cobordism theorem*, Theorem 7.8: a strip `W` of dimension `n ≥ 6`
whose Morse function has all critical points of index in `[2, n - 2]`, whose strip and ends
`V₀`, `V₁` are simply connected, and with `H_*(W, V₀; ℤ) = 0` (`RelHomologyVanishes`, the
relative singular homology of `Submission.Homology.SingularPair`), is a product cobordism.
This is Milnor's hypothesis verbatim; the homotopy-theoretic form (the inclusion `V₀ ↪ W` is a
homotopy equivalence) implies it by `IsHomotopyEquivInclusion.relHomologyVanishes`.

The proof is a strong induction on the number of critical points in the open strip: without
critical points the regular interval theorem (`regular_interval`) applies, and otherwise one
critical point is cancelled by `exists_middle_cancel_step` (`Submission/Morse/MiddleStep.lean`).
That step rests on the deepest parts of the theory: the handle chain complex and the fact that it
computes `H_*(W, V₀)` (Theorem 7.4, which needs singular homology of pairs with excision), the basis
theorem realising elementary basis changes by handle slides (Theorem 7.6), the Whitney trick
(Theorem 6.6) and the Second Cancellation Theorem (Theorem 6.4), and finally the First Cancellation
Theorem (Theorem 5.4).
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
  -- Strong induction on the number of critical points in the open strip.
  have key : ∀ N : ℕ, ∀ f : M → ℝ, Set.ncard {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x} = N →
      MorseStrip I f a b →
      (∀ x, f x ∈ Ioo a b → IsCriticalPt I f x →
        2 ≤ morseIndex I f x ∧ morseIndex I f x + 2 ≤ n) →
      SimplyConnectedSpace (f ⁻¹' Icc a b) →
      SimplyConnectedSpace (f ⁻¹' {a}) → SimplyConnectedSpace (f ⁻¹' {b}) →
      RelHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a})) →
      ∃ Φ : M ≃ₘ⟮I, I⟯ M, Φ '' (f ⁻¹' Iic a) = f ⁻¹' Iic b ∧
        Φ '' (f ⁻¹' {a}) = f ⁻¹' {b} := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro f hN hf hidx hW hV₀ hV₁ hH
    have hfin : {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x}.Finite :=
      hf.finite_critical.subset fun x hx => ⟨Ioo_subset_Icc_self hx.1, hx.2⟩
    by_cases hemp : {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x} = ∅
    · -- No critical point in the open strip: the regular interval theorem applies.
      apply regular_interval I f hf.smooth hf.lt.le hf.compact
      intro x hx hcrit
      rcases eq_or_ne (f x) a with ha | ha
      · exact hf.regular x (Or.inl ha) hcrit
      rcases eq_or_ne (f x) b with hb | hb
      · exact hf.regular x (Or.inr hb) hcrit
      have hxo : f x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm ha), lt_of_le_of_ne hx.2 hb⟩
      have hmem : x ∈ {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x} := ⟨hxo, hcrit⟩
      rw [hemp] at hmem
      exact hmem
    · -- Some critical point: cancel one and apply the induction hypothesis.
      obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hemp
      obtain ⟨g, hmod, hg, hcrit, p, hpf, hpc, hpg⟩ :=
        exists_middle_cancel_step I h6 hf hidx hW hV₀ hV₁ hH hp₀
      have hsub : {x | g x ∈ Ioo a b ∧ IsCriticalPt I g x} ⊆
          {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x} := by
        intro x hx
        have hx1 : x ∈ g ⁻¹' Ioo a b := hx.1
        rw [hmod.preimage_Ioo] at hx1
        exact ⟨hx1, (hcrit x hx.1 hx.2).1⟩
      have hssub : {x | g x ∈ Ioo a b ∧ IsCriticalPt I g x} ⊂
          {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x} :=
        ⟨hsub, fun h => hpg (h ⟨hpf, hpc⟩).2⟩
      have hlt : Set.ncard {x | g x ∈ Ioo a b ∧ IsCriticalPt I g x} < N := by
        rw [← hN]
        exact Set.ncard_lt_ncard hssub hfin
      have hidx' : ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
          2 ≤ morseIndex I g x ∧ morseIndex I g x + 2 ≤ n := by
        intro x hx hc
        obtain ⟨hcf, heq⟩ := hcrit x hx hc
        rw [heq]
        have hx1 : x ∈ g ⁻¹' Ioo a b := hx
        rw [hmod.preimage_Ioo] at hx1
        exact hidx x hx1 hcf
      have hW' : SimplyConnectedSpace (g ⁻¹' Icc a b) := by
        rw [hmod.preimage_Icc]
        exact hW
      have hV₀' : SimplyConnectedSpace (g ⁻¹' {a}) := by
        rw [hmod.preimage_singleton_left]
        exact hV₀
      have hV₁' : SimplyConnectedSpace (g ⁻¹' {b}) := by
        rw [hmod.preimage_singleton_right]
        exact hV₁
      have hH' : RelHomologyVanishes (g ⁻¹' Icc a b) (Subtype.val ⁻¹' (g ⁻¹' {a})) := by
        rw [hmod.preimage_singleton_left, hmod.preimage_Icc]
        exact hH
      obtain ⟨Φ, hΦ₁, hΦ₂⟩ := ih _ hlt g rfl hg hidx' hW' hV₀' hV₁' hH'
      refine ⟨Φ, ?_, ?_⟩
      · rwa [hmod.preimage_Iic_left, hmod.preimage_Iic_right] at hΦ₁
      · rwa [hmod.preimage_singleton_left, hmod.preimage_singleton_right] at hΦ₂
  exact key _ f rfl hf hidx hW hV₀ hV₁ hH

end PoincareHighDim
