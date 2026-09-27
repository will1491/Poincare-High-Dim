import Submission.Morse.Cancellation.CancelFunction
import Submission.Morse.Cancellation.Flow.CancelGoodExists

/-!
# Cancellation, step C6: the First Cancellation Theorem for index `0`

Phase B, step C6 (`CancelIndexZero`). The conclusion of the cancellation programme for an
index-`0`/index-`1` pair, in the packaged form `CancelData` of `Submission/Morse/Cancellation/Setup/CancelSetup.lean`:

```
theorem CancelData.main (c : CancelData I f a' b' p q) :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ IsCriticalPt I g x
```

It is the composition of the two closing steps of the programme: `CancelData.exists_good`
(module `CancelGoodExists`) produces transverse constants `k : c.CancelConsts` together with
the smallness hypotheses `hk : k.Good` needed by the dynamics (`reaches_bottom`,
`reaches_top`), and `CancelConsts.exists_modification` (module `CancelFunction`) builds from
them the modified function `g` (crossing times of the altered field `V'`, interpolated by the
smooth cut-offs of `CancelInterp`), which is a Morse function on the strip without critical
points and agrees with `f` near the two boundary levels.

`GradientLikeStrip.exists_cancel_pair_index_zero` (module `CancelPair`) is this statement
with the fields of `CancelData` as explicit hypotheses.
-/

open Set

namespace PoincareHighDim

open scoped Manifold ContDiff

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace CancelData

variable [DecidableEq M] {a' b' : ℝ} {p q : M}

/-- **The First Cancellation Theorem for index `0`** (Milnor 5.4 for `λ = 0`), for packaged
cancellation data: `f` can be modified within the strip `[a', b']` to a Morse function without
critical points. Proof: choose good constants (`exists_good`) and take the modified function
`g` of `CancelFunction` (`exists_modification`). -/
theorem main (c : CancelData I f a' b' p q) :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ IsCriticalPt I g x := by
  obtain ⟨k, ⟨hk⟩⟩ := c.exists_good
  exact k.exists_modification hk

end CancelData

end GradientLikeStrip

end PoincareHighDim
