import Submission.Morse.Cancellation.CancelPair

/-!
# Cancelling pairs

`IsCancellingPair I f a' b' p q` : `p` and `q` are the only critical points of the regular
strip `[a', b']`, `f p < f q`, `index q = index p + 1`, and for some gradient-like field `D` the
left sphere of `q` and the right sphere of `p` meet in exactly one point, transversally, in the
Sard-map encoding of `Submission/Morse/Rearrangement/Transversality.lean` (see
`Submission/Morse/Cancellation/FirstCancellation.lean` for the explanation of the encoding).  These are the
hypotheses of Milnor's First Cancellation Theorem 5.4.
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem mem_pair_left {α : Type*} [DecidableEq α] (p q : α) : p ∈ ({p, q} : Finset α) :=
  Finset.mem_insert_self p {q}

theorem mem_pair_right {α : Type*} [DecidableEq α] (p q : α) : q ∈ ({p, q} : Finset α) :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self q)

/-- **Cancelling pair** (the hypotheses of Milnor's First Cancellation Theorem 5.4 in strip
form): `f` is a Morse function on the regular strip `[a', b']` whose only critical points are
`p` and `q`, `f p < f q`, `index q = index p + 1`, and for some gradient-like field `D` and
constants `ε`, `c` (`r₀² < 2ε` and `8ε < rm²` at both points, `f p + ε < c < f q - ε`, no small
ball on the levels `[f p + ε, f q - ε]`) the left sphere of `q` meets the right sphere of `p` in
exactly one point, transversally, in the Sard-map encoding of the module docstring. -/
def IsCancellingPair (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [DecidableEq M] (f : M → ℝ) (a' b' : ℝ) (p q : M) : Prop :=
  MorseStrip I f a' b' ∧
    (∀ x, x ∈ ({p, q} : Finset M) ↔ f x ∈ Ioo a' b' ∧ IsCriticalPt I f x) ∧
    f p < f q ∧ morseIndex I f q = morseIndex I f p + 1 ∧
    ∃ D : GradientLikeStrip I f a' b' {p, q}, ∃ ε c : ℝ, 0 < ε ∧
      (D.chart p (mem_pair_left p q)).r₀ ^ 2 < 2 * ε ∧
      (D.chart q (mem_pair_right p q)).r₀ ^ 2 < 2 * ε ∧
      8 * ε < D.rm p (mem_pair_left p q) ^ 2 ∧ 8 * ε < D.rm q (mem_pair_right p q) ^ 2 ∧
      f p + ε < c ∧ c < f q - ε ∧
      (∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp') ∧
      ∃ w₀ ∈ D.sardDom p (mem_pair_right p q) ε c ε (mem_pair_left p q),
        D.sardMap p (mem_pair_right p q) ε c ε (mem_pair_left p q) w₀ = 0 ∧
        (∀ w ∈ D.sardDom p (mem_pair_right p q) ε c ε (mem_pair_left p q),
          D.sardMap p (mem_pair_right p q) ε c ε (mem_pair_left p q) w = 0 →
            ∃ t : ℝ, 0 < t ∧ w = t • w₀) ∧
        Function.Surjective
          (fderiv ℝ (D.sardMap p (mem_pair_right p q) ε c ε (mem_pair_left p q)) w₀)

end PoincareHighDim
