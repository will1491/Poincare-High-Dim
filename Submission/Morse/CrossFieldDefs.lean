import Submission.Morse.CancellingPair

/-!
# Crossing fields

`IsCrossingField I f a' b' V'` : `V'` is a smooth compactly supported vector field on `M`, of
unit descending speed on two collars of the ends of the strip `[a', b']`, all of whose
trajectories starting in the strip reach the level `a'` in forward time (see
`Submission/Morse/CrossingField.lean`).
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- `V'` is a **crossing field** for the strip `[a', b']` of `f`: smooth, compactly supported,
of unit descending speed on the collars `[a', a' + η₀]` and `[b' - η₀, b']` (some
`0 < η₀`, `2 η₀ < b' - a'`), and every integral curve starting in the strip reaches the level
`a'` (or below) in forward time. -/
def IsCrossingField (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M] (f : M → ℝ)
    (a' b' : ℝ) (V' : (x : M) → TangentSpace I x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle I M)) ∧
    IsCompact (tsupport V') ∧
    ∃ η₀ : ℝ, 0 < η₀ ∧ 2 * η₀ < b' - a' ∧
      (∀ x, f x ∈ Icc a' (a' + η₀) ∪ Icc (b' - η₀) b' → dfV I f V' x = -1) ∧
      ∀ x, f x ∈ Icc a' b' → ∀ γ : ℝ → M, γ 0 = x → IsMIntegralCurve γ V' →
        ∃ t, 0 ≤ t ∧ f (γ t) ≤ a'

end PoincareHighDim
