import Submission.Morse.Substrip
import Submission.Morse.CancelIndexZero

/-!
# The First Cancellation Theorem (Milnor 5.4) for an index-`0`/index-`1` pair

Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4 (First Cancellation Theorem), with
its preliminary lemmas 5.5 (the normal form of the gradient-like field along the single
connecting trajectory) and 5.6 (the alteration of the field near the trajectory); see also
J. Morgan's notes on the h-cobordism theorem, Chapter on the cancellation theorem.

* `exists_cancel_pair_index_zero` is the theorem in **strip form** for `λ = 0`, stated for a
  good pair (`GradientLikeStrip.GoodPair`, `Submission/Morse/Bridge.lean`): `p` of index `0`
  and `q` of index `1` are the only critical points of a regular strip `[a', b']`, `f p < f q`,
  the strip carries a gradient-like field `D` (`GradientLikeStrip`), and exactly one of the two
  arms of `q` descends into the basin of `p` (for `λ = 0` this is the statement that the left
  sphere of `q`, two points, meets the right sphere of `p` in exactly one point, and
  transversality is automatic).  The conclusion is a modification `g` of `f` within the strip
  which is a Morse function without critical points.  It is **proved** by `CancelData.main`
  (`Submission/Morse/CancelIndexZero.lean`), the end of the chain
  `CancelSetup` → `CancelTransverse` → `CancelModel` → `CancelField` → `CancelFlow*` →
  `CancelGood*` → `CancelFunction`: the tube chart along the connecting arc, the nowhere-zero
  alteration `V'` of the field, the crossing dynamics (`reaches_bottom`, `reaches_top`) and the
  function `g` built from the crossing times.  This is the only cancellation statement consumed
  downstream (`Submission/Morse/LowHandles.lean`).

* `exists_cancel_pair_strip` lifts the conclusion to an ambient strip `[a, b] ⊇ [a', b']`
  (`ModifiedWithin.morseStrip_of_substrip`), with the critical points, indices and values off the
  substrip unchanged.

The general-index First Cancellation Theorem (Milnor 5.4 for an index-`λ`/index-`λ + 1` pair
whose spheres meet transversally in one point, encoded with the Sard map of
`Submission/Morse/Transversality.lean`) is **not** stated here: nothing in the development needs
it, and the middle-dimensional node `product_of_middle_indices`
(`Submission/Morse/MiddleHandles.lean`) would need the Whitney trick on top of it.

Conventions: fields descend (`df(V) ∈ [-1, 0]`), spheres are fixed-time flow images, `morseNorm`
is the Euclidean norm.
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {a b : ℝ} {crit : Finset M}

/-! ### The index-`0` case from a good pair -/

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] {D : GradientLikeStrip I f a b crit}

/-- **The First Cancellation Theorem for index `0`** (Milnor 5.4 for `λ = 0`), **proved**:
`p` of index `0` and `q` of index `1` are the only critical points of the regular strip
`[a', b']`, exactly one arm of `q` descends into the basin of `p` (`GoodPair`), with the
constants `r₀² < 2ε`, `8ε < rm²`, `f p + 2ε < f q` and no small ball on the levels
`[f p + ε, f q - ε]` (the form delivered by `exists_isolated_pair`).  The hypotheses are exactly
the fields of `CancelData` (`Submission/Morse/CancelSetup.lean`), and the conclusion is
`CancelData.main` (`Submission/Morse/CancelIndexZero.lean`): the alteration of the field along
the connecting arc, the crossing dynamics and the reconstruction of `g` from the crossing times
are carried out in the modules `CancelSetup` … `CancelFunction`. -/
theorem exists_cancel_pair_index_zero [SigmaCompactSpace M] [DecidableEq M]
    {a' b' : ℝ} (hf : MorseStrip I f a' b') {p q : M}
    (D : GradientLikeStrip I f a' b' {p, q})
    (hcrit : ∀ x, x ∈ ({p, q} : Finset M) ↔ f x ∈ Ioo a' b' ∧ IsCriticalPt I f x)
    (hp : p ∈ ({p, q} : Finset M)) (hq : q ∈ ({p, q} : Finset M)) {ε : ℝ} (hε : 0 < ε)
    (hgood : GoodPair D ε p q hp hq)
    (hcst : ∀ p' hp', (D.chart p' hp').r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p' hp' ^ 2)
    (hlt : f p + 2 * ε < f q)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp') :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ IsCriticalPt I g x := by
  exact CancelData.main ⟨hf, D, hcrit, hp, hq, ε, hε, hgood, hcst, hlt, hlev⟩

/-- **Cancellation of an index-`0`/index-`1` pair inside an ambient strip.**  The conclusion of
`exists_cancel_pair_index_zero` lifted to a strip `[a, b] ⊇ [a', b']` on which `f` is a Morse
function: the modification is within `[a, b]`, is a Morse function on `[a, b]`, and off the
open substrip `(a', b')` keeps the values, critical points and Morse indices of `f`. -/
theorem exists_cancel_pair_strip [SigmaCompactSpace M] [DecidableEq M]
    (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ IsCriticalPt I f x)
    (hf' : MorseStrip I f a' b') {p q : M}
    (D : GradientLikeStrip I f a' b' {p, q})
    (hcrit : ∀ x, x ∈ ({p, q} : Finset M) ↔ f x ∈ Ioo a' b' ∧ IsCriticalPt I f x)
    (hp : p ∈ ({p, q} : Finset M)) (hq : q ∈ ({p, q} : Finset M)) {ε : ℝ} (hε : 0 < ε)
    (hgood : GoodPair D ε p q hp hq)
    (hcst : ∀ p' hp', (D.chart p' hp').r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p' hp' ^ 2)
    (hlt : f p + 2 * ε < f q)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp') :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, f x ∉ Ioo a' b' → g x = f x ∧ (IsCriticalPt I g x ↔ IsCriticalPt I f x) ∧
        (IsCriticalPt I f x → morseIndex I g x = morseIndex I f x)) ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ IsCriticalPt I g x := by
  obtain ⟨g, hmod, hg, hno⟩ :=
    exists_cancel_pair_index_zero hf' D hcrit hp hq hε hgood hcst hlt hlev
  obtain ⟨hgs, hoff⟩ := hmod.morseStrip_of_substrip hf ha hb hreg hg
  exact ⟨g, hmod, hmod.mono ha hb, hgs, fun x hx =>
    ⟨(hoff x hx).1, (hoff x hx).2.1, fun h => ((hoff x hx).2.2 h).2⟩, hno⟩

end GradientLikeStrip

end PoincareHighDim
