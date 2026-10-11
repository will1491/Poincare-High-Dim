/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Morse.Cancellation.Flow.CancelFlowExit

/-!
# Cancellation, step C4b: the backward completion (`reaches_top`)

Phase B, step C4b (`CancelFlowBack`). For the cancellation data `c : CancelData I f a' b' p q`,
transverse constants `k : c.CancelConsts` and the smallness hypotheses `hk : k.Good`
(module `CancelGood`), this module proves the backward counterpart of `reaches_bottom`
(module `CancelFlowExit`):

```
theorem reaches_top (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ f (k.Φ (-t) x) = b' ∧ ∀ s ∈ Ico 0 t, f (k.Φ (-s) x) < b'
```
(the first backward time at which the level `b'` is reached), together with the level
monotonicity and no-return lemmas used by C5:

* `f_Φ_le_b'` / `f_Φ_neg_ge_a'`: the strip is forward invariant below `b'` and backward
  invariant above `a'` (the modified field is the original, descending, field off `K`, and `K`
  lies strictly inside the strip);
* `f_Φ_lt_of_le_a'`: once the level `a'` is reached the trajectory stays strictly below `a'`
  (forward no-return; unit speed in the lower collar);
* `b'_lt_f_Φ_of_le` / `b'_lt_f_Φ_neg_of_lt`: once the level `b'` is reached the backward
  trajectory stays strictly above `b'` (backward no-return; unit speed in the upper collar).

**No backward dynamics** (plan §4, R5): `reaches_top` follows from `reaches_bottom` by an
α-limit argument. If the backward trajectory of `x` never reached the level `b'`, it would stay
in the compact strip `f⁻¹[a', b']` for all backward times (`f_Φ_neg_ge_a'`), so its ω-limit set
under the **time-reversed flow** `k.toFlow.reverse` (Mathlib's `Flow.reverse`) is a nonempty
compact subset of the strip, invariant under `Φ t` for every `t ∈ ℝ`
(`exists_alphaLimit_subset`). A point `w` of it reaches the level `a'` at some forward time
(`reaches_bottom`) and is strictly below `a'` one unit of time later (`f_Φ_lt_of_le_a'`) —
but that point of the invariant set lies in the strip, a contradiction
(`exists_b'_le_f_Φ_neg`). The first backward hit of the closed set `f⁻¹[b', ∞)` then gives
`reaches_top`, with equality at the hitting time by continuity.

The hypotheses on the constants are exactly the fields of `CancelConsts.Good` (as allowed by the
plan), used only through `reaches_bottom`.

Conventions: fields descend (`df(V) ∈ [-1, 0]`), `morseNorm` is the Euclidean norm while
`Metric.ball` on `Fin n → ℝ` is the sup-norm ball; all dynamical lemmas carry explicit region
hypotheses.
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace CancelData

variable [DecidableEq M] {a' b' : ℝ} {p q : M} {c : CancelData I f a' b' p q}

namespace CancelConsts

variable (k : c.CancelConsts)

/-! ### The backward trajectory -/

/-- The backward trajectory `s ↦ Φ (-s) x` is continuous. -/
theorem continuous_Φ_neg_curve (x : M) : Continuous (fun s => k.Φ (-s) x) :=
  (k.continuous_Φ_curve x).comp continuous_neg

/-- The level along the backward trajectory: derivative `-df(V')`. -/
theorem hasDerivAt_f_Φ_neg (x : M) (t : ℝ) :
    HasDerivAt (fun s => f (k.Φ (-s) x)) (-dfV I f k.V' (k.Φ (-t) x)) t := by
  have h := (k.hasDerivAt_f_Φ x (-t)).comp t (hasDerivAt_neg t)
  simpa [Function.comp_def, mul_neg_one] using h

/-! ### Invariance of the strip -/

/-- **Forward invariance below `b'`**: the level never exceeds `b'` in forward time. Above
`b' - η₀` the modified field is the original (descending) field. -/
theorem f_Φ_le_b' {x : M} (hx : f x ≤ b') {t : ℝ} (ht : 0 ≤ t) : f (k.Φ t x) ≤ b' := by
  have hmain := nonpos_of_deriv_le_mul (h := fun s => f (k.Φ s x) - b')
    (h' := fun s => dfV I f k.V' (k.Φ s x)) (K := 0) (a := 0) (b := t)
    (fun s _ => (k.hasDerivAt_f_Φ x s).sub_const b') (by simpa using hx)
    (fun s _ hle => by
      have hle' : b' ≤ f (k.Φ s x) := by simpa using hle
      have hnot : k.Φ s x ∉ k.K := k.notMem_K_of_lt_f (by linarith [c.η₀_pos])
      have := k.dfV_V'_nonpos_of_notMem hnot
      simp only [zero_mul]; exact this)
  have := hmain t (right_mem_Icc.2 ht)
  simpa using this

/-- **Backward invariance above `a'`**: the level never drops below `a'` in backward time.
Below `a' + η₀` the modified field is the original (descending) field. -/
theorem f_Φ_neg_ge_a' {x : M} (hx : a' ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    a' ≤ f (k.Φ (-t) x) := by
  have hmain := nonneg_of_deriv_ge_mul (h := fun s => f (k.Φ (-s) x) - a')
    (h' := fun s => -dfV I f k.V' (k.Φ (-s) x)) (K := 0) (a := 0) (b := t)
    (fun s _ => (k.hasDerivAt_f_Φ_neg x s).sub_const a') (by simpa using hx)
    (fun s _ hle => by
      have hle' : f (k.Φ (-s) x) ≤ a' := by simpa using hle
      have hnot : k.Φ (-s) x ∉ k.K := k.notMem_K_of_f_lt (by linarith [c.η₀_pos])
      have := k.dfV_V'_nonpos_of_notMem hnot
      simp only [zero_mul]; linarith)
  have := hmain t (right_mem_Icc.2 ht)
  simpa using this

/-! ### No return across the ends -/

/-- Below `a' + η₀` the level is non-increasing in forward time. -/
theorem f_Φ_le_of_lt_collar {y : M} (hy : f y < a' + c.η₀) {r : ℝ} (hr : 0 ≤ r) :
    f (k.Φ r y) ≤ f y := by
  rw [k.Φ_eq_flow_of_f_lt hy hr]; exact f_flow_le c.hfs y hr

/-- Above `b' - η₀` the level is non-increasing in backward time. -/
theorem le_f_Φ_of_lt_collar {y : M} (hy : b' - c.η₀ < f y) {r : ℝ} (hr : r ≤ 0) :
    f y ≤ f (k.Φ r y) := by
  rw [k.Φ_eq_flow_of_lt_f hy hr]; exact le_f_flow_of_nonpos c.hfs y hr

/-- **Forward no-return**: once the level `a'` is reached (or passed), the trajectory stays
strictly below `a'` at every later time. -/
theorem f_Φ_lt_of_le_a' {x : M} {t₀ s : ℝ} (h : f (k.Φ t₀ x) ≤ a') (hs : t₀ < s) :
    f (k.Φ s x) < a' := by
  obtain ⟨y, hy⟩ : ∃ y, k.Φ t₀ x = y := ⟨_, rfl⟩
  rw [hy] at h
  have hsy : k.Φ s x = k.Φ (s - t₀) y := by rw [← hy, k.Φ_Φ, add_sub_cancel]
  have hr : 0 < s - t₀ := by linarith
  rw [hsy]
  rcases h.lt_or_eq with hlt | heq
  · exact (k.f_Φ_le_of_lt_collar (by linarith [c.η₀_pos]) hr.le).trans_lt hlt
  · -- unit speed at the level `a'`: strictly below immediately afterwards
    have hd : HasDerivAt (fun u => f (k.Φ u y)) (-1) 0 := by
      have := k.hasDerivAt_f_Φ y 0
      rwa [k.Φ_zero, k.dfV_V'_lower_collar heq.ge (by linarith [c.η₀_pos])] at this
    have hev := eventually_lt_of_hasDerivAt_neg (by norm_num : (-1 : ℝ) < 0) hd
    obtain ⟨ε, hε1, hε2⟩ := (hev.and (Ioo_mem_nhdsGT hr)).exists
    rw [k.Φ_zero, heq] at hε1
    have hz : k.Φ (s - t₀) y = k.Φ (s - t₀ - ε) (k.Φ ε y) := by
      rw [k.Φ_Φ, add_sub_cancel]
    rw [hz]
    exact (k.f_Φ_le_of_lt_collar (by linarith [c.η₀_pos]) (by linarith [hε2.2])).trans_lt hε1

/-- **Backward no-return**: once the level `b'` is reached (or passed), the trajectory is
strictly above `b'` at every earlier time. -/
theorem b'_lt_f_Φ_of_le {x : M} {t₀ s : ℝ} (h : b' ≤ f (k.Φ t₀ x)) (hs : s < t₀) :
    b' < f (k.Φ s x) := by
  obtain ⟨y, hy⟩ : ∃ y, k.Φ t₀ x = y := ⟨_, rfl⟩
  rw [hy] at h
  have hsy : k.Φ s x = k.Φ (-(t₀ - s)) y := by rw [← hy, k.Φ_Φ]; congr 1; ring
  have hr : 0 < t₀ - s := by linarith
  rw [hsy]
  rcases h.lt_or_eq with hlt | heq
  · exact hlt.trans_le (k.le_f_Φ_of_lt_collar (by linarith [c.η₀_pos]) (by linarith))
  · -- unit speed at the level `b'`: strictly above immediately before
    have hd : HasDerivAt (fun u => f (k.Φ (-u) y)) 1 0 := by
      have := k.hasDerivAt_f_Φ_neg y 0
      rwa [neg_zero, k.Φ_zero, k.dfV_V'_upper_collar (by linarith [c.η₀_pos]) heq.ge,
        neg_neg] at this
    have hev := eventually_gt_of_hasDerivAt_pos (by norm_num : (0 : ℝ) < 1) hd
    obtain ⟨ε, hε1, hε2⟩ := (hev.and (Ioo_mem_nhdsGT hr)).exists
    rw [neg_zero, k.Φ_zero, ← heq] at hε1
    have hz : k.Φ (-(t₀ - s)) y = k.Φ (-(t₀ - s - ε)) (k.Φ (-ε) y) := by
      rw [k.Φ_Φ]; congr 1; ring
    rw [hz]
    exact hε1.trans_le (k.le_f_Φ_of_lt_collar (by linarith [c.η₀_pos]) (by linarith [hε2.2]))

/-- Backward no-return in the backward-time parametrisation: after the level `b'` is reached at
the backward time `t`, the backward trajectory is strictly above `b'`. -/
theorem b'_lt_f_Φ_neg_of_lt {x : M} {t s : ℝ} (h : b' ≤ f (k.Φ (-t) x)) (hs : t < s) :
    b' < f (k.Φ (-s) x) :=
  k.b'_lt_f_Φ_of_le h (by linarith)

/-! ### The α-limit set of a backward trajectory confined to a compact set -/

/-- **The α-limit set**: a backward trajectory staying in the compact set `C` forever has a
nonempty compact subset `Ω ⊆ C` invariant under `Φ t` for every `t ∈ ℝ` (the ω-limit set of
the time-reversed flow). -/
theorem exists_alphaLimit_subset {C : Set M} (hC : IsCompact C) {x : M}
    (hcon : ∀ t, 0 ≤ t → k.Φ (-t) x ∈ C) :
    ∃ Ω : Set M, Ω.Nonempty ∧ IsCompact Ω ∧ Ω ⊆ C ∧ ∀ t, MapsTo (k.Φ t) Ω Ω := by
  set ψ : Flow ℝ M := k.toFlow.reverse with hψ
  have hψ' : ∀ t y, ψ t y = k.Φ (-t) y := fun t y => rfl
  set Ω := omegaLimit atTop (⇑ψ) {x} with hΩ
  have himage : closure (image2 (⇑ψ) (Ici 0) {x}) ⊆ C := by
    refine closure_minimal ?_ hC.isClosed
    rintro _ ⟨t, ht, y, hy, rfl⟩
    rw [mem_singleton_iff] at hy
    subst hy
    rw [hψ']
    exact hcon t ht
  have hΩC : Ω ⊆ C :=
    (omegaLimit_subset_closure_image2 atTop (⇑ψ) {x} (Ici_mem_atTop (0 : ℝ))).trans himage
  have hΩne : Ω.Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop (⇑ψ) {x} hC
      ⟨Ici 0, Ici_mem_atTop 0, himage⟩ (singleton_nonempty x)
  have hΩc : IsCompact Ω := hC.of_isClosed_subset (isClosed_omegaLimit _ _ _) hΩC
  have hinv : ∀ t, MapsTo (ψ t) Ω Ω :=
    Flow.isInvariant_omegaLimit atTop ψ {x} fun t => tendsto_add_atTop t
  refine ⟨Ω, hΩne, hΩc, hΩC, fun t z hz => ?_⟩
  have := hinv (-t) hz
  change k.Φ (-(-t)) z ∈ Ω at this
  rwa [neg_neg] at this

/-! ### The backward completion -/

/-- Some backward time at which the level is at least `b'`: otherwise the backward trajectory
stays in the compact strip, and a point of its α-limit set would reach the level `a'`
(`reaches_bottom`) and then drop below `a'` inside the invariant α-limit set. -/
theorem exists_b'_le_f_Φ_neg (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ T, 0 ≤ T ∧ b' ≤ f (k.Φ (-T) x) := by
  by_contra hcon
  push Not at hcon
  set S : Set M := f ⁻¹' Icc a' b' with hS
  have hSc : IsCompact S := c.hf.compact
  have hcon' : ∀ t, 0 ≤ t → k.Φ (-t) x ∈ S := fun t ht =>
    ⟨k.f_Φ_neg_ge_a' hx.1 ht, (hcon t ht).le⟩
  obtain ⟨Ω, ⟨w, hw⟩, -, hΩS, hinv⟩ := k.exists_alphaLimit_subset hSc hcon'
  have hwS : f w ∈ Icc a' b' := hΩS hw
  obtain ⟨t₀, -, hft₀, -⟩ := k.reaches_bottom hk hwS
  have hlt : f (k.Φ (t₀ + 1) w) < a' := k.f_Φ_lt_of_le_a' hft₀.le (by linarith)
  have hmem : k.Φ (t₀ + 1) w ∈ Ω := hinv (t₀ + 1) hw
  exact absurd (hΩS hmem).1 (not_le.2 hlt)

/-- **The backward completion**: every point of the strip reaches the level `b'` in backward
time; `t` is the first backward time with `f = b'`. -/
theorem reaches_top (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ f (k.Φ (-t) x) = b' ∧ ∀ s ∈ Ico 0 t, f (k.Φ (-s) x) < b' := by
  obtain ⟨T, hT, hfT⟩ := k.exists_b'_le_f_Φ_neg hk hx
  have hcl : IsClosed (f ⁻¹' Ici b') := isClosed_Ici.preimage c.hfs.continuous
  obtain ⟨t, ht, htK, hmin⟩ := exists_first_time hcl (k.continuous_Φ_neg_curve x) (t := T)
    ⟨T, ⟨hT, le_rfl⟩, hfT⟩
  have hlt : ∀ s ∈ Ico 0 t, f (k.Φ (-s) x) < b' := fun s hs => not_le.1 (hmin s hs)
  refine ⟨t, ht.1, le_antisymm ?_ htK, hlt⟩
  rcases ht.1.eq_or_lt with h | h
  · rw [← h, neg_zero, k.Φ_zero]; exact hx.2
  · refine le_of_tendsto ((c.hfs.continuous.comp (k.continuous_Φ_neg_curve x)).continuousAt
      |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t))) ?_
    filter_upwards [Ico_mem_nhdsLT h] with s hs using (hlt s hs).le

/-- The backward hitting time of `b'` is positive unless `x` is already on the level `b'`. -/
theorem reaches_top_pos (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') (hb : f x < b') :
    ∃ t, 0 < t ∧ f (k.Φ (-t) x) = b' ∧ ∀ s ∈ Ico 0 t, f (k.Φ (-s) x) < b' := by
  obtain ⟨t, ht, hft, hlt⟩ := k.reaches_top hk hx
  refine ⟨t, lt_of_le_of_ne ht fun h => ?_, hft, hlt⟩
  rw [← h, neg_zero, k.Φ_zero] at hft
  exact hb.ne hft

end CancelConsts

end CancelData

end GradientLikeStrip

end

end PoincareHighDim
