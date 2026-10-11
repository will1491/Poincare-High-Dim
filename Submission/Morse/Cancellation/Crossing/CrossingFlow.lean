/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Morse.Cancellation.CancelFunction

set_option autoImplicit false

/-!
# Crossing data: the flow, the crossing times and the modified function

(Imported by `CrossingField.lean`.)

Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4, Assertions 4–5: a crossing field
for the Morse strip `[a', b']` yields a modification of `f` within the strip without critical
points.  This generalises `Submission/Morse/Cancellation/CancelFunction.lean` + `CancelFlowBack.lean` (+ the
flow API of `CancelFlow.lean`) from the index-`0` cancellation field `k.V'` to an arbitrary
crossing field, packaged as the structure `CrossingData I f a' b'`.

Reused ingredients: `CancelInterp.*` (`lam`, `Sfun`, `SfunD`, `Sfun_pos`, `Sfun_lt`,
`Sfun_of_le_half`, `Sfun_of_le_half_left`, `hasDerivAt_Sfun_line`, `SfunD_neg`,
`contDiffAt_Sfun_pair`), `eventually_lt_of_hasDerivAt_neg`, `nonneg_of_hasDerivAt_of_le_left`,
`exists_first_time`, `MonotoneShift.isCriticalPt_congr_nhds`, `ModifiedWithin.preimage_Icc`,
the vendored `curveAt*`, `exists_globalIntegralCurve_of_compactSupport`,
`contMDiff_globalFlow_joint_of_compactSupport`, `contMDiffAt_globalFlow_of_compactSupport`,
`hasDerivAt_df_comp_integralCurve`, and Mathlib's `Flow`, `Flow.reverse`, `omegaLimit` API.

The only genuinely new mathematics compared with the index-`0` construction: the crossing field is
arbitrary off the collars (no global descent), so the invariance / no-return / collar-descent
facts are derived from `df(V') = -1` **on the collar bands only**, via two one-variable lemmas
(`lt_of_le_of_hasDerivAt_level`, `eq_sub_of_hasDerivAt_band`).
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE

noncomputable section

namespace CrossFun

/-! ### One-variable lemmas -/

/-- **Level crossing in one direction.**  If `φ : ℝ → ℝ` is differentiable with derivative
`d s` at every `s`, and `d s < 0` whenever `φ s = c`, then once `φ ≤ c` it is strictly below
`c` at every later time. -/
theorem lt_of_le_of_hasDerivAt_level {φ d : ℝ → ℝ} {c : ℝ}
    (hd : ∀ s, HasDerivAt φ (d s) s) (hlev : ∀ s, φ s = c → d s < 0)
    {s₀ s : ℝ} (h₀ : φ s₀ ≤ c) (hs : s₀ < s) : φ s < c := by
  have hcont : Continuous φ := continuous_iff_continuousAt.2 fun s => (hd s).continuousAt
  -- the strict case
  have hA : ∀ u, φ u < c → ∀ v, u < v → φ v < c := by
    intro u hu v huv
    by_contra hv
    push Not at hv
    have hK : IsCompact {w | w ∈ Icc u v ∧ c ≤ φ w} :=
      isCompact_Icc.inter_right (isClosed_Ici.preimage hcont)
    obtain ⟨w₁, ⟨hw₁I, hw₁c⟩, hmin⟩ := hK.exists_isLeast ⟨v, ⟨huv.le, le_rfl⟩, hv⟩
    have hbelow : ∀ w ∈ Ico u w₁, φ w < c := fun w hw => by
      by_contra hc
      have := hmin ⟨⟨hw.1, hw.2.le.trans hw₁I.2⟩, not_lt.1 hc⟩
      linarith [hw.2]
    have huw : u < w₁ := lt_of_le_of_ne hw₁I.1 fun h => by
      rw [← h] at hw₁c; linarith
    have hle : φ w₁ ≤ c := by
      refine le_of_tendsto (hcont.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Iio w₁))) ?_
      filter_upwards [Ico_mem_nhdsLT huw] with w hw using (hbelow w hw).le
    have heq : φ w₁ = c := le_antisymm hle hw₁c
    have hnn := nonneg_of_hasDerivAt_of_le_left (ε := w₁ - u) (by linarith) (hd w₁)
      (fun w hw => by
        rw [heq]
        exact (hbelow w ⟨by linarith [hw.1], hw.2⟩).le)
    linarith [hlev w₁ heq]
  rcases h₀.lt_or_eq with hlt | heq
  · exact hA s₀ hlt s hs
  · have hev := eventually_lt_of_hasDerivAt_neg (hlev s₀ heq) (hd s₀)
    obtain ⟨u, hu1, hu2⟩ := (hev.and (Ioo_mem_nhdsGT hs)).exists
    rw [heq] at hu1
    exact hA u hu1 s hu2.2

/-- **Unit descent through a band.**  If `φ` has derivative `d s` at every `s`, with
`d s = -1` whenever `φ s ∈ [α, β]`, and `φ 0 ∈ [α, β]`, then `φ s = φ 0 - s` for all
`s ∈ [0, φ 0 - α]` (the curve cannot leave the band through the top, and descends at unit
speed until it reaches `α`). -/
theorem eq_sub_of_hasDerivAt_band {φ d : ℝ → ℝ} {α β : ℝ}
    (hd : ∀ s, HasDerivAt φ (d s) s) (hband : ∀ s, φ s ∈ Icc α β → d s = -1)
    (h0 : φ 0 ∈ Icc α β) : ∀ s ∈ Icc 0 (φ 0 - α), φ s = φ 0 - s := by
  have hcont : Continuous φ := continuous_iff_continuousAt.2 fun s => (hd s).continuousAt
  -- Step 1: below `β` in forward time
  have h1 : ∀ s, 0 ≤ s → φ s ≤ β := fun s hs => by
    rcases hs.eq_or_lt with h | h
    · rw [← h]; exact h0.2
    · exact (lt_of_le_of_hasDerivAt_level hd
        (fun u hu => by rw [hband u ⟨by rw [hu]; linarith [h0.1, h0.2], hu.le⟩]; norm_num)
        h0.2 h).le
  -- Step 2: unit descent while in the band
  have h2 : ∀ w, 0 ≤ w → (∀ u ∈ Icc 0 w, φ u ∈ Icc α β) → ∀ u ∈ Icc 0 w, φ u = φ 0 - u := by
    intro w _ hin u hu
    have hc := constant_of_has_deriv_right_zero (f := fun u => φ u + u) (a := 0) (b := w)
      ((hcont.add continuous_id).continuousOn) (fun x hx => by
        have := ((hd x).add (hasDerivAt_id' x)).hasDerivWithinAt (s := Ici x)
        rw [hband x (hin x ⟨hx.1, hx.2.le⟩), neg_add_cancel] at this
        exact this) u hu
    simp only [add_zero] at hc
    linarith
  -- Step 3: above `α` up to time `φ 0 - α`
  have h3 : ∀ s ∈ Icc 0 (φ 0 - α), α ≤ φ s := by
    intro s₁ hs₁
    by_contra hlt
    push Not at hlt
    have hK : IsCompact {w | w ∈ Icc 0 s₁ ∧ φ w ≤ α} :=
      isCompact_Icc.inter_right (isClosed_Iic.preimage hcont)
    obtain ⟨w₁, ⟨hw₁I, hw₁c⟩, hmin⟩ := hK.exists_isLeast ⟨s₁, ⟨hs₁.1, le_rfl⟩, hlt.le⟩
    have habove : ∀ w ∈ Ico 0 w₁, α < φ w := fun w hw => by
      by_contra hc
      have := hmin ⟨⟨hw.1, hw.2.le.trans hw₁I.2⟩, not_lt.1 hc⟩
      linarith [hw.2]
    have hge : α ≤ φ w₁ := by
      rcases hw₁I.1.eq_or_lt with h | h
      · rw [← h]; exact h0.1
      · refine ge_of_tendsto (hcont.continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Iio w₁))) ?_
        filter_upwards [Ico_mem_nhdsLT h] with w hw using (habove w hw).le
    have hin : ∀ u ∈ Icc 0 w₁, φ u ∈ Icc α β := fun u hu => by
      refine ⟨?_, h1 u hu.1⟩
      rcases hu.2.eq_or_lt with h | h
      · rw [h]; exact hge
      · exact (habove u ⟨hu.1, h⟩).le
    have := h2 w₁ hw₁I.1 hin w₁ ⟨hw₁I.1, le_rfl⟩
    have hαeq : φ w₁ = α := le_antisymm hw₁c hge
    have hw₁s : w₁ = s₁ := le_antisymm hw₁I.2 (by linarith [hs₁.2])
    rw [← hw₁s] at hlt
    linarith
  intro s hs
  exact h2 (φ 0 - α) (by linarith [h0.1]) (fun u hu => ⟨h3 u hu, h1 u hu.1⟩) s hs

end CrossFun

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **Crossing data** (the unpacked hypotheses of `exists_modification_of_crossing`): a Morse
strip `[a', b']` of `f` and a smooth compactly supported field `V` of unit descending speed on
the closed collars `[a', a' + η₀]`, `[b' - η₀, b']` (`0 < η₀`, `2 η₀ < b' - a'`) all of whose
integral curves starting in the strip reach the level `a'` (or below) in forward time. -/
structure CrossingData (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M]
    (f : M → ℝ) (a' b' : ℝ) where
  /-- the crossing field -/
  V : (x : M) → TangentSpace I x
  smooth : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M))
  compact : IsCompact (tsupport V)
  hf : MorseStrip I f a' b'
  /-- the collar width -/
  η₀ : ℝ
  η₀_pos : 0 < η₀
  two_η₀_lt : 2 * η₀ < b' - a'
  collar : ∀ x, f x ∈ Icc a' (a' + η₀) ∪ Icc (b' - η₀) b' → dfV I f V x = -1
  crosses : ∀ x, f x ∈ Icc a' b' → ∀ γ : ℝ → M, γ 0 = x → IsMIntegralCurve γ V →
    ∃ t, 0 ≤ t ∧ f (γ t) ≤ a'

namespace CrossingData

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] {f : M → ℝ} {a' b' : ℝ}
  (C : CrossingData I f a' b')

include C in
theorem lt : a' < b' := C.hf.lt

include C in
theorem hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := C.hf.smooth

theorem dfV_lower_collar {x : M} (h1 : a' ≤ f x) (h2 : f x ≤ a' + C.η₀) :
    dfV I f C.V x = -1 :=
  C.collar x (Or.inl ⟨h1, h2⟩)

theorem dfV_upper_collar {x : M} (h1 : b' - C.η₀ ≤ f x) (h2 : f x ≤ b') :
    dfV I f C.V x = -1 :=
  C.collar x (Or.inr ⟨h1, h2⟩)

theorem dfV_level_a' {x : M} (h : f x = a') : dfV I f C.V x = -1 :=
  C.dfV_lower_collar h.ge (by linarith [C.η₀_pos])

theorem dfV_level_b' {x : M} (h : f x = b') : dfV I f C.V x = -1 :=
  C.dfV_upper_collar (by linarith [C.η₀_pos]) h.le

/-! ### The global flow `Φ` of the crossing field -/

theorem smooth_one :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1 (fun x => (⟨x, C.V x⟩ : TangentBundle I M)) :=
  C.smooth.of_le (by norm_num)

variable [T2Space M] [I.Boundaryless]

/-- The crossing field is complete (compact support). -/
theorem hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ C.V :=
  exists_globalIntegralCurve_of_compactSupport C.V C.smooth C.compact

/-- The global flow of the crossing field. -/
def Φ (t : ℝ) (x : M) : M := curveAt C.V C.hcomplete x t

theorem isMIntegralCurve_Φ (x : M) : IsMIntegralCurve (fun t => C.Φ t x) C.V :=
  curveAt_integralCurve C.V C.hcomplete x

@[simp] theorem Φ_zero (x : M) : C.Φ 0 x = x := curveAt_zero C.V C.hcomplete x

theorem Φ_add (x : M) (s t : ℝ) : C.Φ (s + t) x = C.Φ t (C.Φ s x) :=
  curveAt_add C.V C.smooth_one C.hcomplete x s t

theorem Φ_Φ (x : M) (s t : ℝ) : C.Φ t (C.Φ s x) = C.Φ (s + t) x := (C.Φ_add x s t).symm

theorem Φ_neg_Φ (x : M) (t : ℝ) : C.Φ (-t) (C.Φ t x) = x := by
  rw [Φ_Φ, add_neg_cancel, Φ_zero]

theorem Φ_Φ_neg (x : M) (t : ℝ) : C.Φ t (C.Φ (-t) x) = x := by
  rw [Φ_Φ, neg_add_cancel, Φ_zero]

theorem contMDiff_Φ_joint :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => C.Φ z.1 z.2) :=
  contMDiff_globalFlow_joint_of_compactSupport C.V C.smooth C.compact

theorem continuous_Φ_joint : Continuous (fun z : ℝ × M => C.Φ z.1 z.2) :=
  C.contMDiff_Φ_joint.continuous

theorem contMDiff_Φ (t : ℝ) : ContMDiff I I ∞ (C.Φ t) := fun x =>
  contMDiffAt_globalFlow_of_compactSupport C.V C.smooth C.compact t x

theorem continuous_Φ (t : ℝ) : Continuous (C.Φ t) := (C.contMDiff_Φ t).continuous

theorem continuous_Φ_curve (x : M) : Continuous (fun t => C.Φ t x) :=
  (C.isMIntegralCurve_Φ x).continuous

theorem continuous_Φ_neg_curve (x : M) : Continuous (fun s => C.Φ (-s) x) :=
  (C.continuous_Φ_curve x).comp continuous_neg

/-- The flow `Φ` packaged as a Mathlib `Flow`. -/
def toFlow : Flow ℝ M where
  toFun := C.Φ
  cont' := C.continuous_Φ_joint
  map_add' := fun t₁ t₂ x => by rw [add_comm, C.Φ_add]
  map_zero' := C.Φ_zero

theorem toFlow_apply (t : ℝ) (x : M) : C.toFlow t x = C.Φ t x := rfl

/-! ### `f` along `Φ` -/

theorem hasDerivAt_f_Φ (x : M) (t : ℝ) :
    HasDerivAt (fun s => f (C.Φ s x)) (dfV I f C.V (C.Φ t x)) t :=
  hasDerivAt_df_comp_integralCurve f C.hfs C.V (C.isMIntegralCurve_Φ x) t

theorem hasDerivAt_f_Φ_neg (x : M) (t : ℝ) :
    HasDerivAt (fun s => f (C.Φ (-s) x)) (-dfV I f C.V (C.Φ (-t) x)) t := by
  have h := (C.hasDerivAt_f_Φ x (-t)).comp t (hasDerivAt_neg t)
  simpa [Function.comp_def, mul_neg_one] using h

/-! ### Level crossing: invariance and no-return from `df(V) = -1` on a level -/

/-- **One-way crossing of a unit-speed level** (generalises `f_Φ_lt_of_le_a'` of
`CancelFlowBack.lean`; there the proof used global descent below the strip, here only the
unit speed on the level `c`). -/
theorem f_Φ_lt_of_le_level {c : ℝ} (hc : ∀ y, f y = c → dfV I f C.V y = -1) {x : M}
    {t₀ s : ℝ} (h : f (C.Φ t₀ x) ≤ c) (hs : t₀ < s) : f (C.Φ s x) < c :=
  CrossFun.lt_of_le_of_hasDerivAt_level (C.hasDerivAt_f_Φ x)
    (fun u hu => by rw [hc _ hu]; norm_num) h hs

/-- The backward form: above a unit-speed level at time `t₀`, strictly above before. -/
theorem lt_f_Φ_of_level_le {c : ℝ} (hc : ∀ y, f y = c → dfV I f C.V y = -1) {x : M}
    {t₀ s : ℝ} (h : c ≤ f (C.Φ t₀ x)) (hs : s < t₀) : c < f (C.Φ s x) := by
  by_contra hcon
  have := C.f_Φ_lt_of_le_level hc (not_lt.1 hcon) hs
  linarith

/-- Forward no-return across `a'`. -/
theorem f_Φ_lt_of_le_a' {x : M} {t₀ s : ℝ} (h : f (C.Φ t₀ x) ≤ a') (hs : t₀ < s) :
    f (C.Φ s x) < a' :=
  C.f_Φ_lt_of_le_level (fun _ hy => C.dfV_level_a' hy) h hs

/-- **Forward invariance below `b'`.** -/
theorem f_Φ_le_b' {x : M} (hx : f x ≤ b') {t : ℝ} (ht : 0 ≤ t) : f (C.Φ t x) ≤ b' := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, C.Φ_zero]; exact hx
  · exact (C.f_Φ_lt_of_le_level (fun _ hy => C.dfV_level_b' hy)
      (by rw [C.Φ_zero]; exact hx) h).le

/-- Forward: strictly below `b'` stays strictly below `b'`. -/
theorem f_Φ_lt_b' {x : M} (hx : f x < b') {t : ℝ} (ht : 0 ≤ t) : f (C.Φ t x) < b' := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, C.Φ_zero]; exact hx
  · exact C.f_Φ_lt_of_le_level (fun _ hy => C.dfV_level_b' hy)
      (by rw [C.Φ_zero]; exact hx.le) h

/-- **Backward invariance above `a'`.** -/
theorem f_Φ_neg_ge_a' {x : M} (hx : a' ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    a' ≤ f (C.Φ (-t) x) := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, neg_zero, C.Φ_zero]; exact hx
  · exact (C.lt_f_Φ_of_level_le (fun _ hy => C.dfV_level_a' hy)
      (by rw [C.Φ_zero]; exact hx) (by linarith)).le

/-- Backward: strictly above `a'` stays strictly above `a'`. -/
theorem a'_lt_f_Φ_neg {x : M} (hx : a' < f x) {t : ℝ} (ht : 0 ≤ t) :
    a' < f (C.Φ (-t) x) := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, neg_zero, C.Φ_zero]; exact hx
  · exact C.lt_f_Φ_of_level_le (fun _ hy => C.dfV_level_a' hy)
      (by rw [C.Φ_zero]; exact hx.le) (by linarith)

/-! ### Unit descent through the collars -/

/-- **Forward unit descent through a unit-speed band** `[α, β]`. -/
theorem f_Φ_band_fwd {α β : ℝ} (hb : ∀ y, f y ∈ Icc α β → dfV I f C.V y = -1) {x : M}
    {t₀ : ℝ} (h0 : f (C.Φ t₀ x) ∈ Icc α β) :
    ∀ s ∈ Icc 0 (f (C.Φ t₀ x) - α), f (C.Φ (t₀ + s) x) = f (C.Φ t₀ x) - s := by
  intro s hs
  have key := CrossFun.eq_sub_of_hasDerivAt_band (φ := fun u => f (C.Φ u (C.Φ t₀ x)))
    (C.hasDerivAt_f_Φ (C.Φ t₀ x)) (fun u hu => hb _ hu) (by simpa using h0) s
    (by simpa using hs)
  simpa [C.Φ_Φ] using key

/-- **Backward unit ascent through a unit-speed band** `[α, β]`. -/
theorem f_Φ_band_bwd {α β : ℝ} (hb : ∀ y, f y ∈ Icc α β → dfV I f C.V y = -1) {x : M}
    {t₀ : ℝ} (h0 : f (C.Φ t₀ x) ∈ Icc α β) :
    ∀ s ∈ Icc 0 (β - f (C.Φ t₀ x)), f (C.Φ (t₀ - s) x) = f (C.Φ t₀ x) + s := by
  intro s hs
  set y := C.Φ t₀ x with hy
  have hd : ∀ u, HasDerivAt (fun u => -f (C.Φ (-u) y)) (dfV I f C.V (C.Φ (-u) y)) u :=
    fun u => by
      have h := (C.hasDerivAt_f_Φ_neg y u).neg
      rw [neg_neg] at h
      exact h
  have key := CrossFun.eq_sub_of_hasDerivAt_band (φ := fun u => -f (C.Φ (-u) y))
    (α := -β) (β := -α) hd
    (fun u hu => hb _ ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    (by simp only [neg_zero, C.Φ_zero]; exact ⟨by linarith [h0.2], by linarith [h0.1]⟩) s
    (by simp only [neg_zero, C.Φ_zero]; exact ⟨hs.1, by linarith [hs.2]⟩)
  simp only [neg_zero, C.Φ_zero] at key
  have : C.Φ (t₀ - s) x = C.Φ (-s) y := by rw [hy, C.Φ_Φ]; ring_nf
  rw [this]
  linarith

/-! ### The crossing times exist -/

/-- **The forward crossing** (from `crosses`, first hitting time of `f⁻¹(-∞, a']`): the first
forward time at which the level `a'` is reached. -/
theorem reaches_bottom {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ f (C.Φ t x) = a' ∧ ∀ s ∈ Ico 0 t, a' < f (C.Φ s x) := by
  obtain ⟨T, hT, hfT⟩ := C.crosses x hx (fun t => C.Φ t x) (C.Φ_zero x) (C.isMIntegralCurve_Φ x)
  have hcl : IsClosed (f ⁻¹' Iic a') := isClosed_Iic.preimage C.hfs.continuous
  obtain ⟨t, ht, htK, hmin⟩ := exists_first_time hcl (C.continuous_Φ_curve x) (t := T)
    ⟨T, ⟨hT, le_rfl⟩, hfT⟩
  have hlt : ∀ s ∈ Ico 0 t, a' < f (C.Φ s x) := fun s hs => not_le.1 (hmin s hs)
  refine ⟨t, ht.1, le_antisymm htK ?_, hlt⟩
  rcases ht.1.eq_or_lt with h | h
  · rw [← h, C.Φ_zero]; exact hx.1
  · refine ge_of_tendsto ((C.hfs.continuous.comp (C.continuous_Φ_curve x)).continuousAt
      |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t))) ?_
    filter_upwards [Ico_mem_nhdsLT h] with s hs using (hlt s hs).le

/-- **The α-limit set** of a backward trajectory confined to a compact set (as in
`CancelConsts.exists_alphaLimit_subset`, with `C.toFlow`). -/
theorem exists_alphaLimit_subset {K : Set M} (hK : IsCompact K) {x : M}
    (hcon : ∀ t, 0 ≤ t → C.Φ (-t) x ∈ K) :
    ∃ Ω : Set M, Ω.Nonempty ∧ IsCompact Ω ∧ Ω ⊆ K ∧ ∀ t, MapsTo (C.Φ t) Ω Ω := by
  set ψ : Flow ℝ M := C.toFlow.reverse with hψ
  have hψ' : ∀ t y, ψ t y = C.Φ (-t) y := fun t y => rfl
  set Ω := omegaLimit atTop (⇑ψ) {x} with hΩ
  have himage : closure (image2 (⇑ψ) (Ici 0) {x}) ⊆ K := by
    refine closure_minimal ?_ hK.isClosed
    rintro _ ⟨t, ht, y, hy, rfl⟩
    rw [mem_singleton_iff] at hy
    subst hy
    rw [hψ']
    exact hcon t ht
  have hΩK : Ω ⊆ K :=
    (omegaLimit_subset_closure_image2 atTop (⇑ψ) {x} (Ici_mem_atTop (0 : ℝ))).trans himage
  have hΩne : Ω.Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop (⇑ψ) {x} hK
      ⟨Ici 0, Ici_mem_atTop 0, himage⟩ (singleton_nonempty x)
  have hΩc : IsCompact Ω := hK.of_isClosed_subset (isClosed_omegaLimit _ _ _) hΩK
  have hinv : ∀ t, MapsTo (ψ t) Ω Ω :=
    Flow.isInvariant_omegaLimit atTop ψ {x} fun t =>
      tendsto_atTop_atTop.2 fun b => ⟨b - t, fun s hs => by linarith⟩
  refine ⟨Ω, hΩne, hΩc, hΩK, fun t z hz => ?_⟩
  have := hinv (-t) hz
  change C.Φ (-(-t)) z ∈ Ω at this
  rwa [neg_neg] at this

/-- Some backward time at which the level is at least `b'` (α-limit argument, as in
`CancelConsts.exists_b'_le_f_Φ_neg`). -/
theorem exists_b'_le_f_Φ_neg {x : M} (hx : f x ∈ Icc a' b') :
    ∃ T, 0 ≤ T ∧ b' ≤ f (C.Φ (-T) x) := by
  by_contra hcon
  push Not at hcon
  have hcon' : ∀ t, 0 ≤ t → C.Φ (-t) x ∈ f ⁻¹' Icc a' b' := fun t ht =>
    ⟨C.f_Φ_neg_ge_a' hx.1 ht, (hcon t ht).le⟩
  obtain ⟨Ω, ⟨w, hw⟩, -, hΩS, hinv⟩ := C.exists_alphaLimit_subset C.hf.compact hcon'
  have hwS : f w ∈ Icc a' b' := hΩS hw
  obtain ⟨t₀, -, hft₀, -⟩ := C.reaches_bottom hwS
  have hlt : f (C.Φ (t₀ + 1) w) < a' := C.f_Φ_lt_of_le_a' hft₀.le (by linarith)
  have hmem : C.Φ (t₀ + 1) w ∈ Ω := hinv (t₀ + 1) hw
  exact absurd (hΩS hmem).1 (not_le.2 hlt)

/-- **The backward crossing** (as in `CancelConsts.reaches_top`). -/
theorem reaches_top {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ f (C.Φ (-t) x) = b' ∧ ∀ s ∈ Ico 0 t, f (C.Φ (-s) x) < b' := by
  obtain ⟨T, hT, hfT⟩ := C.exists_b'_le_f_Φ_neg hx
  have hcl : IsClosed (f ⁻¹' Ici b') := isClosed_Ici.preimage C.hfs.continuous
  obtain ⟨t, ht, htK, hmin⟩ := exists_first_time hcl (C.continuous_Φ_neg_curve x) (t := T)
    ⟨T, ⟨hT, le_rfl⟩, hfT⟩
  have hlt : ∀ s ∈ Ico 0 t, f (C.Φ (-s) x) < b' := fun s hs => not_le.1 (hmin s hs)
  refine ⟨t, ht.1, le_antisymm ?_ htK, hlt⟩
  rcases ht.1.eq_or_lt with h | h
  · rw [← h, neg_zero, C.Φ_zero]; exact hx.2
  · refine le_of_tendsto ((C.hfs.continuous.comp (C.continuous_Φ_neg_curve x)).continuousAt
      |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t))) ?_
    filter_upwards [Ico_mem_nhdsLT h] with s hs using (hlt s hs).le

/-! ### The crossing times (generalising `CancelFunction.lean`) -/

open scoped Classical in
/-- The forward crossing time: the first time at which the `Φ`-trajectory reaches the level
`a'` (defined as `f x - a'` off the strip). -/
def τ₀ (x : M) : ℝ :=
  if h : f x ∈ Icc a' b' then Classical.choose (C.reaches_bottom h) else f x - a'

open scoped Classical in
/-- The backward crossing time: the first backward time at which the `Φ`-trajectory reaches
the level `b'` (defined as `b' - f x` off the strip). -/
def τ₁ (x : M) : ℝ :=
  if h : f x ∈ Icc a' b' then Classical.choose (C.reaches_top h) else b' - f x

theorem τ₀_spec {x : M} (hx : f x ∈ Icc a' b') :
    0 ≤ C.τ₀ x ∧ f (C.Φ (C.τ₀ x) x) = a' ∧ ∀ s ∈ Ico 0 (C.τ₀ x), a' < f (C.Φ s x) := by
  have := Classical.choose_spec (C.reaches_bottom hx)
  unfold τ₀
  rw [dite_eq_left hx]
  exact this

theorem τ₁_spec {x : M} (hx : f x ∈ Icc a' b') :
    0 ≤ C.τ₁ x ∧ f (C.Φ (-C.τ₁ x) x) = b' ∧ ∀ s ∈ Ico 0 (C.τ₁ x), f (C.Φ (-s) x) < b' := by
  have := Classical.choose_spec (C.reaches_top hx)
  unfold τ₁
  rw [dite_eq_left hx]
  exact this

theorem τ₀_unique {x : M} (hx : f x ∈ Icc a' b') {t : ℝ} (ht : 0 ≤ t) (hf : f (C.Φ t x) = a')
    (hlt : ∀ s ∈ Ico 0 t, a' < f (C.Φ s x)) : t = C.τ₀ x := by
  obtain ⟨h0, h1, h2⟩ := C.τ₀_spec hx
  rcases lt_trichotomy t (C.τ₀ x) with h | h | h
  · exact absurd hf (h2 t ⟨ht, h⟩).ne'
  · exact h
  · exact absurd h1 (hlt _ ⟨h0, h⟩).ne'

theorem τ₁_unique {x : M} (hx : f x ∈ Icc a' b') {t : ℝ} (ht : 0 ≤ t)
    (hf : f (C.Φ (-t) x) = b') (hlt : ∀ s ∈ Ico 0 t, f (C.Φ (-s) x) < b') : t = C.τ₁ x := by
  obtain ⟨h0, h1, h2⟩ := C.τ₁_spec hx
  rcases lt_trichotomy t (C.τ₁ x) with h | h | h
  · exact absurd hf (h2 t ⟨ht, h⟩).ne
  · exact h
  · exact absurd h1 (hlt _ ⟨h0, h⟩).ne

theorem τ₀_pos {x : M} (hx : f x ∈ Icc a' b') (h : a' < f x) : 0 < C.τ₀ x := by
  obtain ⟨h0, h1, -⟩ := C.τ₀_spec hx
  refine lt_of_le_of_ne h0 fun heq => ?_
  rw [← heq, C.Φ_zero] at h1
  exact h.ne' h1

theorem τ₁_pos {x : M} (hx : f x ∈ Icc a' b') (h : f x < b') : 0 < C.τ₁ x := by
  obtain ⟨h0, h1, -⟩ := C.τ₁_spec hx
  refine lt_of_le_of_ne h0 fun heq => ?_
  rw [← heq, neg_zero, C.Φ_zero] at h1
  exact h.ne h1

/-- Additivity of the forward crossing time. -/
theorem τ₀_add {x : M} (hx : f x ∈ Icc a' b') {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    (hlt : ∀ s ∈ Icc 0 t₁, a' < f (C.Φ s x)) : C.τ₀ x = t₁ + C.τ₀ (C.Φ t₁ x) := by
  have hy : f (C.Φ t₁ x) ∈ Icc a' b' :=
    ⟨(hlt t₁ (right_mem_Icc.2 ht₁)).le, C.f_Φ_le_b' hx.2 ht₁⟩
  obtain ⟨h0, h1, h2⟩ := C.τ₀_spec hy
  symm
  apply C.τ₀_unique hx (by linarith)
  · rw [← C.Φ_Φ]; exact h1
  · intro s hs
    rcases le_or_gt s t₁ with h | h
    · exact hlt s ⟨hs.1, h⟩
    · have := h2 (s - t₁) ⟨by linarith, by linarith [hs.2]⟩
      rwa [C.Φ_Φ, add_sub_cancel] at this

/-- Additivity of the backward crossing time. -/
theorem τ₁_add {x : M} (hx : f x ∈ Icc a' b') {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    (hlt : ∀ s ∈ Icc 0 t₁, f (C.Φ (-s) x) < b') :
    C.τ₁ x = t₁ + C.τ₁ (C.Φ (-t₁) x) := by
  have hy : f (C.Φ (-t₁) x) ∈ Icc a' b' :=
    ⟨C.f_Φ_neg_ge_a' hx.1 ht₁, (hlt t₁ (right_mem_Icc.2 ht₁)).le⟩
  obtain ⟨h0, h1, h2⟩ := C.τ₁_spec hy
  symm
  apply C.τ₁_unique hx (by linarith)
  · rw [C.Φ_Φ] at h1; rwa [neg_add]
  · intro s hs
    rcases le_or_gt s t₁ with h | h
    · exact hlt s ⟨hs.1, h⟩
    · have := h2 (s - t₁) ⟨by linarith, by linarith [hs.2]⟩
      rwa [C.Φ_Φ, show -t₁ + -(s - t₁) = -s by ring] at this

omit [T2Space M] [I.Boundaryless] in
theorem f_mem_of_lower_collar {x : M} (h1 : a' ≤ f x) (h2 : f x ≤ a' + C.η₀) :
    f x ∈ Icc a' b' :=
  ⟨h1, by linarith [C.two_η₀_lt, C.η₀_pos]⟩

omit [T2Space M] [I.Boundaryless] in
theorem f_mem_of_upper_collar {x : M} (h1 : b' - C.η₀ ≤ f x) (h2 : f x ≤ b') :
    f x ∈ Icc a' b' :=
  ⟨by linarith [C.two_η₀_lt, C.η₀_pos], h2⟩

/-- In the (closed) lower collar the forward crossing time is `f x - a'`. -/
theorem τ₀_collar {x : M} (h1 : a' ≤ f x) (h2 : f x ≤ a' + C.η₀) :
    C.τ₀ x = f x - a' := by
  have hx := C.f_mem_of_lower_collar h1 h2
  have hb := C.f_Φ_band_fwd (α := a') (β := a' + C.η₀)
    (fun y hy => C.dfV_lower_collar hy.1 hy.2) (x := x) (t₀ := 0) (by rw [C.Φ_zero]; exact ⟨h1, h2⟩)
  simp only [C.Φ_zero, zero_add] at hb
  symm
  apply C.τ₀_unique hx (by linarith)
  · rw [hb _ ⟨by linarith, le_rfl⟩]; ring
  · intro s hs
    rw [hb s ⟨hs.1, hs.2.le⟩]
    linarith [hs.2]

/-- In the (closed) upper collar the backward crossing time is `b' - f x`. -/
theorem τ₁_collar {x : M} (h1 : b' - C.η₀ ≤ f x) (h2 : f x ≤ b') :
    C.τ₁ x = b' - f x := by
  have hx := C.f_mem_of_upper_collar h1 h2
  have hb := C.f_Φ_band_bwd (α := b' - C.η₀) (β := b')
    (fun y hy => C.dfV_upper_collar hy.1 hy.2) (x := x) (t₀ := 0) (by rw [C.Φ_zero]; exact ⟨h1, h2⟩)
  simp only [C.Φ_zero, zero_sub] at hb
  symm
  apply C.τ₁_unique hx (by linarith)
  · rw [hb _ ⟨by linarith, le_rfl⟩]; ring
  · intro s hs
    rw [hb s ⟨hs.1, hs.2.le⟩]
    linarith [hs.2]

/-- A trajectory reaching `a'` within time `η₀` started in the lower collar. -/
theorem f_eq_add_τ₀_of_le {x : M} (hx : f x ∈ Icc a' b') (h : C.τ₀ x ≤ C.η₀) :
    f x = a' + C.τ₀ x := by
  obtain ⟨h0, h1, -⟩ := C.τ₀_spec hx
  have hb := C.f_Φ_band_bwd (α := a') (β := a' + C.η₀)
    (fun y hy => C.dfV_lower_collar hy.1 hy.2) (x := x) (t₀ := C.τ₀ x)
    (by rw [h1]; exact ⟨le_rfl, by linarith [C.η₀_pos]⟩) (C.τ₀ x) ⟨h0, by rw [h1]; linarith⟩
  rw [sub_self, C.Φ_zero, h1] at hb
  exact hb

/-- A backward trajectory reaching `b'` within time `η₀` started in the upper collar. -/
theorem f_eq_sub_τ₁_of_le {x : M} (hx : f x ∈ Icc a' b') (h : C.τ₁ x ≤ C.η₀) :
    f x = b' - C.τ₁ x := by
  obtain ⟨h0, h1, -⟩ := C.τ₁_spec hx
  have hb := C.f_Φ_band_fwd (α := b' - C.η₀) (β := b')
    (fun y hy => C.dfV_upper_collar hy.1 hy.2) (x := x) (t₀ := -C.τ₁ x)
    (by rw [h1]; exact ⟨by linarith [C.η₀_pos], le_rfl⟩) (C.τ₁ x) ⟨h0, by rw [h1]; linarith⟩
  rw [neg_add_cancel, C.Φ_zero, h1] at hb
  exact hb

theorem η₀_le_τ₀_of_le {x : M} (hx : f x ∈ Icc a' b') (h : a' + C.η₀ ≤ f x) :
    C.η₀ ≤ C.τ₀ x := by
  by_contra hc
  have := C.f_eq_add_τ₀_of_le hx (not_le.1 hc).le
  linarith [not_le.1 hc]

theorem η₀_le_τ₁_of_le {x : M} (hx : f x ∈ Icc a' b') (h : f x ≤ b' - C.η₀) :
    C.η₀ ≤ C.τ₁ x := by
  by_contra hc
  have := C.f_eq_sub_τ₁_of_le hx (not_le.1 hc).le
  linarith [not_le.1 hc]

/-- The two crossing times are never both small. -/
theorem η₀_le_τ₁_or_τ₀ {x : M} (hx : f x ∈ Icc a' b') :
    C.η₀ ≤ C.τ₁ x ∨ C.η₀ ≤ C.τ₀ x := by
  rcases le_or_gt (f x) (b' - C.η₀) with h | h
  · exact Or.inl (C.η₀_le_τ₁_of_le hx h)
  · exact Or.inr (C.η₀_le_τ₀_of_le hx (by linarith [C.two_η₀_lt]))

/-! ### Smoothness of the crossing times by the constant-shift trick -/

/-- **The constant-shift trick**: near a point of the open strip, `τ₀` is a constant `t₁` plus
the smooth function `f (Φ t₁ ·) - a'`. -/
theorem exists_shift_τ₀ {x₀ : M} (hx₀ : f x₀ ∈ Ioo a' b') :
    ∃ t₁, 0 ≤ t₁ ∧ ∀ᶠ x in 𝓝 x₀, C.τ₀ x = t₁ + (f (C.Φ t₁ x) - a') := by
  have hx₀' : f x₀ ∈ Icc a' b' := Ioo_subset_Icc_self hx₀
  obtain ⟨-, h1, h2⟩ := C.τ₀_spec hx₀'
  have hTpos : 0 < C.τ₀ x₀ := C.τ₀_pos hx₀' hx₀.1
  have hev : ∀ᶠ s in 𝓝[<] C.τ₀ x₀, f (C.Φ s x₀) < a' + C.η₀ := by
    have hc : ContinuousAt (fun s => f (C.Φ s x₀)) (C.τ₀ x₀) :=
      (C.hfs.continuous.comp (C.continuous_Φ_curve x₀)).continuousAt
    exact (hc.eventually_lt continuousAt_const (by rw [h1]; linarith [C.η₀_pos])).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨t₁, ht₁f, ht₁⟩ := (hev.and (Ioo_mem_nhdsLT hTpos)).exists
  refine ⟨t₁, ht₁.1.le, ?_⟩
  have hU₁ : ∀ᶠ x in 𝓝 x₀, ∀ s ∈ Icc 0 t₁, a' < f (C.Φ s x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hcont : Continuous (fun z : M × ℝ => f (C.Φ z.2 z.1)) :=
      C.hfs.continuous.comp (C.continuous_Φ_joint.comp (continuous_snd.prodMk continuous_fst))
    exact continuousAt_const.eventually_lt hcont.continuousAt
      (h2 s ⟨hs.1, by linarith [hs.2, ht₁.2]⟩)
  have hU₂ : ∀ᶠ x in 𝓝 x₀, a' < f (C.Φ t₁ x) ∧ f (C.Φ t₁ x) < a' + C.η₀ := by
    have hc : ContinuousAt (fun x => f (C.Φ t₁ x)) x₀ :=
      (C.hfs.continuous.comp (C.continuous_Φ t₁)).continuousAt
    exact (continuousAt_const.eventually_lt hc (h2 t₁ ⟨ht₁.1.le, ht₁.2⟩)).and
      (hc.eventually_lt continuousAt_const ht₁f)
  have hU₃ : ∀ᶠ x in 𝓝 x₀, f x ∈ Ioo a' b' :=
    C.hfs.continuous.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hx₀)
  filter_upwards [hU₁, hU₂, hU₃] with x h1x h2x h3x
  rw [C.τ₀_add (Ioo_subset_Icc_self h3x) ht₁.1.le h1x, C.τ₀_collar h2x.1.le h2x.2.le]

/-- The constant-shift trick for the backward crossing time. -/
theorem exists_shift_τ₁ {x₀ : M} (hx₀ : f x₀ ∈ Ioo a' b') :
    ∃ t₁, 0 ≤ t₁ ∧ ∀ᶠ x in 𝓝 x₀, C.τ₁ x = t₁ + (b' - f (C.Φ (-t₁) x)) := by
  have hx₀' : f x₀ ∈ Icc a' b' := Ioo_subset_Icc_self hx₀
  obtain ⟨-, h1, h2⟩ := C.τ₁_spec hx₀'
  have hTpos : 0 < C.τ₁ x₀ := C.τ₁_pos hx₀' hx₀.2
  have hev : ∀ᶠ s in 𝓝[<] C.τ₁ x₀, b' - C.η₀ < f (C.Φ (-s) x₀) := by
    have hc : ContinuousAt (fun s => f (C.Φ (-s) x₀)) (C.τ₁ x₀) :=
      (C.hfs.continuous.comp (C.continuous_Φ_neg_curve x₀)).continuousAt
    exact (continuousAt_const.eventually_lt hc (by rw [h1]; linarith [C.η₀_pos])).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨t₁, ht₁f, ht₁⟩ := (hev.and (Ioo_mem_nhdsLT hTpos)).exists
  refine ⟨t₁, ht₁.1.le, ?_⟩
  have hU₁ : ∀ᶠ x in 𝓝 x₀, ∀ s ∈ Icc 0 t₁, f (C.Φ (-s) x) < b' := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hcont : Continuous (fun z : M × ℝ => f (C.Φ (-z.2) z.1)) :=
      C.hfs.continuous.comp
        (C.continuous_Φ_joint.comp (continuous_snd.neg.prodMk continuous_fst))
    exact hcont.continuousAt.eventually_lt continuousAt_const
      (h2 s ⟨hs.1, by linarith [hs.2, ht₁.2]⟩)
  have hU₂ : ∀ᶠ x in 𝓝 x₀, b' - C.η₀ < f (C.Φ (-t₁) x) := by
    have hc : ContinuousAt (fun x => f (C.Φ (-t₁) x)) x₀ :=
      (C.hfs.continuous.comp (C.continuous_Φ (-t₁))).continuousAt
    exact continuousAt_const.eventually_lt hc ht₁f
  have hU₃ : ∀ᶠ x in 𝓝 x₀, f x ∈ Ioo a' b' :=
    C.hfs.continuous.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hx₀)
  filter_upwards [hU₁, hU₂, hU₃] with x h1x h2x h3x
  rw [C.τ₁_add (Ioo_subset_Icc_self h3x) ht₁.1.le h1x,
    C.τ₁_collar h2x.le (h1x t₁ (right_mem_Icc.2 ht₁.1.le)).le]

theorem contMDiffAt_τ₀ {x₀ : M} (hx₀ : f x₀ ∈ Ioo a' b') :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ C.τ₀ x₀ := by
  obtain ⟨t₁, -, hev⟩ := C.exists_shift_τ₀ hx₀
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => t₁ + (f (C.Φ t₁ x) - a')) x₀ :=
    contMDiffAt_const.add
      ((C.hfs.contMDiffAt.comp x₀ (C.contMDiff_Φ t₁).contMDiffAt).sub contMDiffAt_const)
  exact hs.congr_of_eventuallyEq hev

theorem contMDiffAt_τ₁ {x₀ : M} (hx₀ : f x₀ ∈ Ioo a' b') :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ C.τ₁ x₀ := by
  obtain ⟨t₁, -, hev⟩ := C.exists_shift_τ₁ hx₀
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => t₁ + (b' - f (C.Φ (-t₁) x))) x₀ :=
    contMDiffAt_const.add
      (contMDiffAt_const.sub (C.hfs.contMDiffAt.comp x₀ (C.contMDiff_Φ (-t₁)).contMDiffAt))
  exact hs.congr_of_eventuallyEq hev

/-- Along the flow, `τ₀` decreases and `τ₁` increases at unit rate (small times of either
sign), and the trajectory stays in the open strip. -/
theorem eventually_τ_Φ {x : M} (hx : f x ∈ Ioo a' b') :
    ∀ᶠ r in 𝓝 (0 : ℝ), f (C.Φ r x) ∈ Ioo a' b' ∧ C.τ₀ (C.Φ r x) = C.τ₀ x - r ∧
      C.τ₁ (C.Φ r x) = C.τ₁ x + r := by
  have hx' : f x ∈ Icc a' b' := Ioo_subset_Icc_self hx
  obtain ⟨-, -, h2⟩ := C.τ₀_spec hx'
  obtain ⟨-, -, h2'⟩ := C.τ₁_spec hx'
  have hτ₀ : 0 < C.τ₀ x := C.τ₀_pos hx' hx.1
  have hτ₁ : 0 < C.τ₁ x := C.τ₁_pos hx' hx.2
  have hfwd : ∀ u, 0 ≤ u → f (C.Φ u x) < b' := fun u hu => C.f_Φ_lt_b' hx.2 hu
  have hbwd : ∀ u, 0 ≤ u → a' < f (C.Φ (-u) x) := fun u hu => C.a'_lt_f_Φ_neg hx.1 hu
  filter_upwards [Ioo_mem_nhds (by linarith : -C.τ₁ x < 0) hτ₀] with r hr
  rcases le_or_gt 0 r with hr0 | hr0
  · have hfr : f (C.Φ r x) ∈ Ioo a' b' := ⟨h2 r ⟨hr0, hr.2⟩, hfwd r hr0⟩
    refine ⟨hfr, ?_, ?_⟩
    · have := C.τ₀_add hx' hr0 (fun s hs => h2 s ⟨hs.1, by linarith [hs.2, hr.2]⟩)
      linarith
    · have := C.τ₁_add (Ioo_subset_Icc_self hfr) hr0 (fun s hs => by
        rw [C.Φ_Φ]; exact hfwd (r + -s) (by linarith [hs.2]))
      rw [C.Φ_neg_Φ] at this
      linarith
  · obtain ⟨v, hv, rfl⟩ : ∃ v, 0 < v ∧ r = -v := ⟨-r, by linarith, by ring⟩
    have hfr : f (C.Φ (-v) x) ∈ Ioo a' b' := ⟨hbwd v hv.le, h2' v ⟨hv.le, by linarith [hr.1]⟩⟩
    refine ⟨hfr, ?_, ?_⟩
    · have := C.τ₀_add (Ioo_subset_Icc_self hfr) hv.le (fun s hs => by
        rw [C.Φ_Φ, show -v + s = -(v - s) by ring]; exact hbwd (v - s) (by linarith [hs.2]))
      rw [C.Φ_Φ_neg] at this
      linarith
    · have := C.τ₁_add hx' hv.le (fun s hs => h2' s ⟨hs.1, by linarith [hs.2, hr.1]⟩)
      linarith

/-! ### The modified function `g` -/

open scoped Classical in
/-- **The modified function**: `g = a' + Sfun (b' - a') η₀ (τ₁ x) (τ₀ x)` on the open strip,
`g = f` off it. -/
def g (x : M) : ℝ :=
  if f x ∈ Ioo a' b' then a' + CancelInterp.Sfun (b' - a') C.η₀ (C.τ₁ x) (C.τ₀ x) else f x

theorem g_of_mem {x : M} (hx : f x ∈ Ioo a' b') :
    C.g x = a' + CancelInterp.Sfun (b' - a') C.η₀ (C.τ₁ x) (C.τ₀ x) := by
  unfold g; rw [ite_eq_left hx]

theorem g_of_notMem {x : M} (hx : f x ∉ Ioo a' b') : C.g x = f x := by
  unfold g; rw [ite_eq_right hx]

theorem g_eq_f_of_le {x : M} (hx : f x ≤ a' + C.η₀ / 2) : C.g x = f x := by
  by_cases h : f x ∈ Ioo a' b'
  · rw [C.g_of_mem h, C.τ₀_collar h.1.le (by linarith [C.η₀_pos]),
      CancelInterp.Sfun_of_le_half C.η₀_pos (by linarith)]
    ring
  · exact C.g_of_notMem h

theorem g_eq_f_of_ge {x : M} (hx : b' - C.η₀ / 2 ≤ f x) : C.g x = f x := by
  by_cases h : f x ∈ Ioo a' b'
  · have hτ₀ : C.η₀ ≤ C.τ₀ x :=
      C.η₀_le_τ₀_of_le (Ioo_subset_Icc_self h) (by linarith [C.two_η₀_lt, C.η₀_pos])
    rw [C.g_of_mem h, C.τ₁_collar (by linarith [C.η₀_pos]) h.2.le,
      CancelInterp.Sfun_of_le_half_left C.η₀_pos (by linarith) hτ₀]
    ring
  · exact C.g_of_notMem h

theorem g_mem_Ioo {x : M} (hx : f x ∈ Ioo a' b') : C.g x ∈ Ioo a' b' := by
  have hx' := Ioo_subset_Icc_self hx
  rw [C.g_of_mem hx]
  have h1 := CancelInterp.Sfun_pos C.η₀_pos C.two_η₀_lt (C.τ₁_pos hx' hx.2) (C.τ₀_pos hx' hx.1)
  have h2 := CancelInterp.Sfun_lt C.η₀_pos C.two_η₀_lt (C.τ₁_pos hx' hx.2) (C.τ₀_pos hx' hx.1)
  constructor <;> linarith

theorem modifiedWithin_g : ModifiedWithin f a' b' C.g :=
  ⟨fun _ hx => C.g_of_notMem hx, fun _ hx => C.g_mem_Ioo hx⟩

/-- `g = f` near every point off the open strip or in the collars `f < a' + η₀/2`,
`f > b' - η₀/2`. -/
theorem g_eventuallyEq_f {x : M} (hx : f x < a' + C.η₀ / 2 ∨ b' - C.η₀ / 2 < f x) :
    C.g =ᶠ[𝓝 x] f := by
  rcases hx with hx | hx
  · filter_upwards [C.hfs.continuous.continuousAt.eventually_lt continuousAt_const hx] with y hy
    exact C.g_eq_f_of_le hy.le
  · filter_upwards [continuousAt_const.eventually_lt C.hfs.continuous.continuousAt hx] with y hy
    exact C.g_eq_f_of_ge hy.le

theorem contMDiff_g : ContMDiff I 𝓘(ℝ, ℝ) ∞ C.g := by
  intro x
  by_cases hx : f x ∈ Ioo a' b'
  · have hx' := Ioo_subset_Icc_self hx
    have hev : C.g =ᶠ[𝓝 x]
        fun y => a' + CancelInterp.Sfun (b' - a') C.η₀ (C.τ₁ y) (C.τ₀ y) := by
      filter_upwards [C.hfs.continuous.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hx)]
        with y hy
      exact C.g_of_mem hy
    have hne : C.τ₁ x + C.τ₀ x ≠ 0 := by
      have := C.τ₁_pos hx' hx.2
      have := C.τ₀_pos hx' hx.1
      linarith
    have hpair : ContMDiffAt I 𝓘(ℝ, ℝ × ℝ) ∞ (fun y => (C.τ₁ y, C.τ₀ y)) x :=
      (C.contMDiffAt_τ₁ hx).prodMk_space (C.contMDiffAt_τ₀ hx)
    have hS := ContDiffAt.comp_contMDiffAt (I := I) (f := fun y => (C.τ₁ y, C.τ₀ y))
      (x := x) (CancelInterp.contDiffAt_Sfun_pair (b' - a') C.η₀
        (p := (C.τ₁ x, C.τ₀ x)) hne) hpair
    exact (contMDiffAt_const.add hS).congr_of_eventuallyEq hev
  · have hx2 : f x < a' + C.η₀ / 2 ∨ b' - C.η₀ / 2 < f x := by
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
      rcases hx with h | h
      · left; linarith [C.η₀_pos]
      · right; linarith [C.η₀_pos]
    exact (C.hfs x).congr_of_eventuallyEq (C.g_eventuallyEq_f hx2)

theorem hasDerivAt_g_Φ {x : M} (hx : f x ∈ Ioo a' b') :
    HasDerivAt (fun r => C.g (C.Φ r x))
      (CancelInterp.SfunD (b' - a') C.η₀ (C.τ₁ x) (C.τ₀ x)) 0 := by
  have h := (CancelInterp.hasDerivAt_Sfun_line (b' - a') C.η₀ (C.τ₁ x) (C.τ₀ x)).const_add a'
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [C.eventually_τ_Φ hx] with r hr
  rw [C.g_of_mem hr.1, hr.2.1, hr.2.2]

theorem SfunD_g_neg {x : M} (hx : f x ∈ Ioo a' b') :
    CancelInterp.SfunD (b' - a') C.η₀ (C.τ₁ x) (C.τ₀ x) < 0 :=
  CancelInterp.SfunD_neg C.η₀_pos C.two_η₀_lt (C.τ₁_pos (Ioo_subset_Icc_self hx) hx.2)
    (C.τ₀_pos (Ioo_subset_Icc_self hx) hx.1) (C.η₀_le_τ₁_or_τ₀ (Ioo_subset_Icc_self hx))

theorem not_isCriticalPt_g {x : M} (hx : C.g x ∈ Ioo a' b') : ¬ IsCriticalPt I C.g x := by
  have hfx : f x ∈ Ioo a' b' := by
    by_contra h
    rw [C.g_of_notMem h] at hx
    exact h hx
  intro hcrit
  have h1 := hasDerivAt_df_comp_integralCurve C.g C.contMDiff_g C.V (C.isMIntegralCurve_Φ x) 0
  have h2 := C.hasDerivAt_g_Φ hfx
  have hD := C.SfunD_g_neg hfx
  unfold IsCriticalPt at hcrit
  have h1' : HasDerivAt (fun r => C.g (C.Φ r x))
      ((mfderiv I 𝓘(ℝ, ℝ) C.g (C.Φ 0 x)) (C.V (C.Φ 0 x))) 0 := h1
  rw [C.Φ_zero, hcrit] at h1'
  have := h1'.unique h2
  rw [zero_apply] at this
  exact hD.ne this.symm

theorem morseStrip_g : MorseStrip I C.g a' b' := by
  refine ⟨C.contMDiff_g, C.hf.lt, ?_, ?_, ?_⟩
  · rw [C.modifiedWithin_g.preimage_Icc]; exact C.hf.compact
  · intro x hx
    have hnot : f x ∉ Ioo a' b' := fun h => by
      have := C.g_mem_Ioo h
      rcases hx with hx | hx <;> rw [hx] at this <;> simp at this
    have hfx : f x = a' ∨ f x = b' := by rwa [C.g_of_notMem hnot] at hx
    have hev : C.g =ᶠ[𝓝 x] f := C.g_eventuallyEq_f (by
      rcases hfx with h | h
      · left; linarith [C.η₀_pos]
      · right; linarith [C.η₀_pos])
    rw [MonotoneShift.isCriticalPt_congr_nhds hev]
    exact C.hf.regular x hfx
  · intro x hx hc
    exact absurd hc (C.not_isCriticalPt_g hx)

include C in
/-- **Crossing data yield a modification without critical points.** -/
theorem exists_modification :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ IsCriticalPt I g x :=
  ⟨C.g, C.modifiedWithin_g, C.morseStrip_g, fun _ hx => C.not_isCriticalPt_g hx⟩

end CrossingData

end

end PoincareHighDim
