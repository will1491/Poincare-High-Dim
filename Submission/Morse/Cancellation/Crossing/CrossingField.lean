/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Morse.Cancellation.Crossing.CrossFieldDefs
import Submission.Morse.Cancellation.Crossing.CrossingFlow
import Submission.Morse.Cancellation.Crossing.CrossFieldBand

/-!
# Crossing fields and the First Cancellation Theorem (Milnor 5.4, Assertions 1–6)

The proof of the First Cancellation Theorem splits into two parts.

* `IsCrossingField I f a' b' V'` : `V'` is a smooth compactly supported vector field on `M`,
  of unit descending speed (`df(V') = -1`) on two collars `[a', a' + η₀]` and `[b' - η₀, b']`
  of the ends of the strip, all of whose trajectories starting in the strip reach the level `a'`
  in forward time.
* `exists_modification_of_crossing` (Milnor 5.4, Assertions 4–5): a crossing field for the
  Morse strip `[a', b']` yields a modification `g` of `f` within the strip without critical
  points.  The proof: the first forward time `τ₀` at which a trajectory reaches `a'` and the
  first backward time `τ₁` at which it reaches `b'` (which exists by an `α`-limit argument from
  the forward crossing and the compactness of the strip) are smooth on the open strip by the
  constant-shift trick through the collars, and `g = a' + S(τ₁, τ₀)` for a suitable
  interpolation `S`, equal to `f` near the ends, strictly decreases along `V'`.  (This is the
  construction of `Submission/Morse/Cancellation/CancelFunction.lean`, where it is carried out for the field
  of the index-`0` cancellation.)
* `exists_crossing_field` (Milnor 5.4, Preliminary Hypothesis 5.5, Assertions 1–3 and 6,
  Theorem 5.6, Lemma 5.7, Lemma 4.7): a cancelling pair admits a crossing field.  Milnor's
  proof: after altering the gradient-like field between two levels near `p` and `q` (Lemma 4.7,
  with the local isotopy of Theorem 5.6 and Lemma 5.7 — this is where the transversality and the
  uniqueness of the intersection point enter), there is a chart around the connecting trajectory
  in which the field is a positive multiple of `(-v(x₁), x₂, …, x_{λ+1}, -x_{λ+2}, …, -xₙ)` with
  `v > 0` on `(0, 1)`, `v(0) = v(1) = 0`; replacing `v` near the axis by a function that is
  negative on the axis produces a nowhere-zero field; no trajectory leaves a smaller
  neighbourhood of the trajectory and comes back (Assertion 1, compactness and uniqueness of the
  connecting trajectory), and every trajectory entering the chart leaves it (Assertion 2), so
  every trajectory crosses the strip (Assertion 3).

`exists_modification_of_crossing` is `CrossingData.exists_modification`
(`Submission/Morse/Cancellation/Crossing/CrossingFlow.lean`) and `exists_crossing_field` is
`CrossField.crossfield_target` (`Submission/Morse/Cancellation/Crossing/CrossFieldBand.lean`).
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **A crossing field yields a function without critical points** (Milnor 5.4, Assertions 4
and 5): if `f` is a Morse function on the strip `[a', b']` admitting a crossing field, then `f`
can be modified within the strip to a Morse function without critical points. -/
theorem exists_modification_of_crossing (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} {a' b' : ℝ} (hf : MorseStrip I f a' b') {V' : (x : M) → TangentSpace I x}
    (hV' : IsCrossingField I f a' b' V') :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ IsCriticalPt I g x := by
  obtain ⟨hsm, hcpt, η₀, hη₀, h2η₀, hcol, hcr⟩ := hV'
  exact (CrossingData.mk V' hsm hcpt hf η₀ hη₀ h2η₀ hcol hcr).exists_modification

/-- **A cancelling pair admits a crossing field** (Milnor 5.4, Preliminary Hypothesis 5.5,
Assertions 1–3 and 6, Theorem 5.6, Lemma 5.7, Lemma 4.7). -/
theorem exists_crossing_field (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [DecidableEq M]
    {f : M → ℝ} {a' b' : ℝ} {p q : M} (h : IsCancellingPair I f a' b' p q) :
    ∃ V' : (x : M) → TangentSpace I x, IsCrossingField I f a' b' V' := by
  exact CrossField.crossfield_target h

end PoincareHighDim
