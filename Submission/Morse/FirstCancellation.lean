import Submission.Morse.CrossingField

/-!
# The First Cancellation Theorem for adjacent indices (Milnor 5.4)

Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4 (First Cancellation Theorem), with
the Preliminary Hypothesis 5.5, Assertions 1–6, Theorem 5.6 and Lemma 5.7; see also J. Morgan's
notes on the h-cobordism theorem.

* `IsCancellingPair I f a' b' p q` (defined in `Submission/Morse/CancellingPair.lean`) : `p` and `q` are the only critical points of the regular
  strip `[a', b']`, `f p < f q`, `index q = index p + 1`, and for some gradient-like field `D` the
  left sphere of `q` and the right sphere of `p` meet in exactly one point, transversally.  The
  meeting condition is written with the Sard map of `Submission/Morse/Transversality.lean` (with
  `η := ε`): a point `w₀` of the domain `D.sardDom p hq ε c ε hp` (nonzero vectors of `ℝ^{λ+1}`
  whose trajectory from the model left sphere of `q` lands in the model ball of `p` at the level
  `f p + ε`) with `D.sardMap p hq ε c ε hp w₀ = 0` (the landing point lies on the right sphere
  of `p`), uniqueness up to the ray (the Sard map is constant on rays), and transversality as the
  surjectivity of the derivative of the Sard map at `w₀` (the Sard map `ℝ^{λ+1} → ℝ^λ` is constant
  on rays, so its derivative is surjective iff the induced map of the sphere `S^λ` is regular at
  its unique zero, i.e. `S_L(q) ⋔ S_R(p)`).
* `exists_cancel_pair` : a cancelling pair can be removed: `f` is modified within the strip to a
  Morse function without critical points.  It is proved as
  `exists_modification_of_crossing ∘ exists_crossing_field` (`Submission/Morse/CrossingField.lean`).
* `exists_cancel_pair_strip_of_isCancellingPair` : the same inside an ambient strip
  `[a, b] ⊇ [a', b']`, keeping the values, critical points and indices off the substrip.

The index-`0` case in the form consumed by `Submission/Morse/LowHandles.lean` is
`GradientLikeStrip.exists_cancel_pair_index_zero` (`Submission/Morse/CancelPair.lean`).

Conventions: fields descend (`df(V) ∈ [-1, 0]`), spheres are fixed-time flow images, `morseNorm`
is the Euclidean norm.
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **The First Cancellation Theorem** (Milnor 5.4) in strip form: a cancelling pair can be
removed by modifying `f` within the strip; the result is a Morse function on the strip without
critical points.  (Milnor's proof: the Preliminary Hypothesis 5.5 — a chart around the connecting
trajectory in which the field is `(v(x₁), -x₂, …, -x_{λ+1}, x_{λ+2}, …, xₙ)` — is achieved by
Assertion 6, via Theorem 5.6, Lemma 5.7 and Lemma 4.7; then Assertions 1–5 alter the field near
the trajectory to a nowhere-zero field whose trajectories all cross the strip, and rebuild the
function from the crossing times.) -/
theorem exists_cancel_pair (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [DecidableEq M]
    {f : M → ℝ} {a' b' : ℝ} {p q : M} (h : IsCancellingPair I f a' b' p q) :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ IsCriticalPt I g x := by
  obtain ⟨V', hV'⟩ := exists_crossing_field I h
  exact exists_modification_of_crossing I h.1 hV'

/-- **Cancellation of a cancelling pair inside an ambient strip.**  The conclusion of
`exists_cancel_pair` lifted to a strip `[a, b] ⊇ [a', b']` on which `f` is a Morse function: the
modification is within `[a, b]`, is a Morse function on `[a, b]`, and off the open substrip
`(a', b')` keeps the values, critical points and Morse indices of `f`. -/
theorem exists_cancel_pair_strip_of_isCancellingPair (I : ModelWithCorners ℝ (Fin n → ℝ) H)
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [DecidableEq M]
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ IsCriticalPt I f x) {p q : M}
    (h : IsCancellingPair I f a' b' p q) :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, f x ∉ Ioo a' b' → g x = f x ∧ (IsCriticalPt I g x ↔ IsCriticalPt I f x) ∧
        (IsCriticalPt I f x → morseIndex I g x = morseIndex I f x)) ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ IsCriticalPt I g x := by
  obtain ⟨g, hmod, hg, hno⟩ := exists_cancel_pair I h
  obtain ⟨hgs, hoff⟩ := hmod.morseStrip_of_substrip hf ha hb hreg hg
  exact ⟨g, hmod, hmod.mono ha hb, hgs, fun x hx =>
    ⟨(hoff x hx).1, (hoff x hx).2.1, fun h => ((hoff x hx).2.2 h).2⟩, hno⟩

end PoincareHighDim
