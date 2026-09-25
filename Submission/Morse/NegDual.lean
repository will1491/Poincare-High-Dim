import Submission.Morse.MonotoneShift

/-!
# The dual Morse function `-f`

Milnor's elimination theorems (*Lectures on the h-cobordism theorem*, Theorem 8.1) are proved
for the low indices `0` and `1` and then transferred to the high indices `n` and `n - 1` by
passing to the dual function `-f` on the reflected strip `[-b, -a]`.  This file provides the
transfer:

* `NegDual.preimage_neg_Icc`, `preimage_neg_Ioo`, `preimage_neg_singleton` : the strip, the open
  strip and the level sets of `-f` on `[-b, -a]` are those of `f` on `[a, b]`.
* `NegDual.hessianAt_neg`, `isCriticalPt_neg_iff`, `isNondegenerateCriticalPt_neg_iff` :
  critical points and nondegeneracy are unchanged, the Hessian changes sign.
* `NegDual.morseIndex_neg_add` : at a nondegenerate critical point the indices of `f` and `-f`
  add up to `n` (Sylvester: `sigPos Q + sigNeg Q = n` for a nondegenerate form on `Fin n → ℝ`),
  so index `0` of `-f` is index `n` of `f`.
* `MorseStrip.neg`, `IsSelfIndexing.neg`, `ModifiedWithin.neg` and their converses
  `MorseStrip.of_neg`, `IsSelfIndexing.of_neg`, `ModifiedWithin.of_neg`.
* `NegDual.connectedSpace_neg_strip_iff`, `simplyConnectedSpace_neg_strip_iff`,
  `nonempty_neg_level_iff`, `simplyConnectedSpace_neg_level_iff` : the topological hypotheses on
  the strip and its ends transfer verbatim.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff Topology
open Set

namespace NegDual

/-! ### Sets -/

section Sets

variable {M : Type*} {f : M → ℝ} {a b c : ℝ}

theorem neg_mem_Icc_iff {x : ℝ} : -x ∈ Icc (-b) (-a) ↔ x ∈ Icc a b := by
  simp only [mem_Icc, neg_le_neg_iff]
  exact and_comm

theorem neg_mem_Ioo_iff {x : ℝ} : -x ∈ Ioo (-b) (-a) ↔ x ∈ Ioo a b := by
  simp only [mem_Ioo, neg_lt_neg_iff]
  exact and_comm

theorem neg_mem_Iic_iff {x : ℝ} : -x ∈ Iic (-c) ↔ x ∈ Ici c := by
  simp only [mem_Iic, mem_Ici, neg_le_neg_iff]

theorem preimage_neg_Icc : (fun x => -f x) ⁻¹' Icc (-b) (-a) = f ⁻¹' Icc a b := by
  ext x
  exact neg_mem_Icc_iff

theorem preimage_neg_Ioo : (fun x => -f x) ⁻¹' Ioo (-b) (-a) = f ⁻¹' Ioo a b := by
  ext x
  exact neg_mem_Ioo_iff

theorem preimage_neg_singleton : (fun x => -f x) ⁻¹' {-c} = f ⁻¹' {c} := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, neg_inj]

theorem preimage_neg_Iic : (fun x => -f x) ⁻¹' Iic (-c) = f ⁻¹' Ici c := by
  ext x
  exact neg_mem_Iic_iff

theorem neg_neg_fun : (fun x => -(-f x)) = f := by
  funext x
  exact neg_neg _

/-- The strip of `-f` on `[-b, -a]` is connected iff the strip of `f` on `[a, b]` is. -/
theorem connectedSpace_neg_strip_iff [TopologicalSpace M] :
    ConnectedSpace ((fun x => -f x) ⁻¹' Icc (-b) (-a)) ↔
      ConnectedSpace (f ⁻¹' Icc a b) := by
  rw [preimage_neg_Icc]

theorem simplyConnectedSpace_neg_strip_iff [TopologicalSpace M] :
    SimplyConnectedSpace ((fun x => -f x) ⁻¹' Icc (-b) (-a)) ↔
      SimplyConnectedSpace (f ⁻¹' Icc a b) := by
  rw [preimage_neg_Icc]

theorem nonempty_neg_level_iff :
    ((fun x => -f x) ⁻¹' {-c}).Nonempty ↔ (f ⁻¹' {c}).Nonempty := by
  rw [preimage_neg_singleton]

theorem simplyConnectedSpace_neg_level_iff [TopologicalSpace M] :
    SimplyConnectedSpace ((fun x => -f x) ⁻¹' {-c}) ↔ SimplyConnectedSpace (f ⁻¹' {c}) := by
  rw [preimage_neg_singleton]

end Sets

/-! ### Hessians and critical points -/

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chartHessianAt_neg (g : E → ℝ) (x : E) :
    chartHessianAt (fun y => -g y) x = -chartHessianAt g x := by
  have h1 : fderiv ℝ (fun y => -g y) = fun y => -fderiv ℝ g y := funext fun _ => fderiv_fun_neg
  ext v
  rw [neg_apply, MonotoneShift.chartHessianAt_apply, MonotoneShift.chartHessianAt_apply, h1,
    fderiv_fun_neg]
  simp

/-- `SeparatingLeft` is invariant under negation of the associated bilinear form. -/
theorem separatingLeft_associated_neg_iff (Q : QuadraticForm ℝ E) :
    (QuadraticMap.associated (R := ℝ) (-Q)).SeparatingLeft ↔
      (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft := by
  rw [map_neg]
  simp only [LinearMap.SeparatingLeft, LinearMap.neg_apply, neg_eq_zero]

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem hessianAt_neg (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) :
    hessianAt I (fun x => -f x) p = -hessianAt I f p :=
  chartHessianAt_neg (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)

theorem isCriticalPt_neg_iff (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) :
    IsCriticalPt I (fun x => -f x) x ↔ IsCriticalPt I f x := by
  unfold IsCriticalPt
  have h : mfderiv I 𝓘(ℝ, ℝ) (fun x => -f x) x = -mfderiv I 𝓘(ℝ, ℝ) f x := mfderiv_neg
  rw [h]
  exact neg_eq_zero

theorem isNondegenerateCriticalPt_neg_iff (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) :
    IsNondegenerateCriticalPt I (fun x => -f x) p ↔ IsNondegenerateCriticalPt I f p := by
  unfold IsNondegenerateCriticalPt
  rw [isCriticalPt_neg_iff, hessianAt_neg, separatingLeft_associated_neg_iff]

/-- Critical points of `-f` in the open strip `(-b, -a)` are the critical points of `f` in
`(a, b)`. -/
theorem crit_neg_iff (I : ModelWithCorners ℝ E H) (f : M → ℝ) {a b : ℝ} (x : M) :
    ((fun x => -f x) x ∈ Ioo (-b) (-a) ∧ IsCriticalPt I (fun x => -f x) x) ↔
      (f x ∈ Ioo a b ∧ IsCriticalPt I f x) := by
  rw [isCriticalPt_neg_iff]
  exact and_congr_left fun _ => neg_mem_Ioo_iff

end Hessian

/-! ### The Morse index of `-f` -/

section Index

/-- Sylvester's law for a nondegenerate quadratic form on `Fin n → ℝ`:
`sigPos Q + sigNeg Q = n`. -/
theorem sigPos_add_sigNeg_of_separatingLeft {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) : sigPos Q + sigNeg Q = n := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (𝕜 := ℝ) (Q := Q)
  have hrad : Q.radical = ⊥ := by
    rw [QuadraticMap.radical_eq_ker_associated, ← LinearMap.separatingLeft_iff_ker_eq_bot]
    exact hQ
  rw [hrad, finrank_bot, add_zero, Module.finrank_fin_fun] at h
  exact h

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {p : M}

theorem morseIndex_neg (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f : M → ℝ) (p : M) :
    morseIndex I (fun x => -f x) p = sigPos (hessianAt I f p) := by
  unfold morseIndex
  rw [hessianAt_neg, sigNeg_neg]

/-- At a nondegenerate critical point the indices of `-f` and `f` add up to `n`. -/
theorem morseIndex_neg_add (hp : IsNondegenerateCriticalPt I f p) :
    morseIndex I (fun x => -f x) p + morseIndex I f p = n := by
  rw [morseIndex_neg]
  exact sigPos_add_sigNeg_of_separatingLeft _ hp.2

/-- The same identity assuming nondegeneracy of `-f`. -/
theorem morseIndex_neg_add' (hp : IsNondegenerateCriticalPt I (fun x => -f x) p) :
    morseIndex I (fun x => -f x) p + morseIndex I f p = n :=
  morseIndex_neg_add ((isNondegenerateCriticalPt_neg_iff I f p).1 hp)

theorem morseIndex_le (hp : IsNondegenerateCriticalPt I f p) : morseIndex I f p ≤ n := by
  have := morseIndex_neg_add hp
  omega

theorem morseIndex_neg_eq (hp : IsNondegenerateCriticalPt I f p) :
    morseIndex I (fun x => -f x) p = n - morseIndex I f p := by
  have := morseIndex_neg_add hp
  omega

theorem morseIndex_eq_sub_neg (hp : IsNondegenerateCriticalPt I f p) :
    morseIndex I f p = n - morseIndex I (fun x => -f x) p := by
  have := morseIndex_neg_add hp
  omega

/-- Index `0` for `-f` is index `n` for `f`. -/
theorem morseIndex_neg_eq_zero_iff (hp : IsNondegenerateCriticalPt I f p) :
    morseIndex I (fun x => -f x) p = 0 ↔ morseIndex I f p = n := by
  have := morseIndex_neg_add hp
  omega

theorem morseIndex_neg_pos_iff (hp : IsNondegenerateCriticalPt I f p) :
    0 < morseIndex I (fun x => -f x) p ↔ morseIndex I f p < n := by
  have := morseIndex_neg_add hp
  omega

theorem morseIndex_neg_lt_iff (hp : IsNondegenerateCriticalPt I f p) :
    morseIndex I (fun x => -f x) p < n ↔ 0 < morseIndex I f p := by
  have := morseIndex_neg_add hp
  omega

end Index

end NegDual

/-! ### Transfer of the strip-level structures -/

section Structures

open NegDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {f g : M → ℝ} {a b : ℝ}

/-- `-f` is a Morse function on the reflected strip `[-b, -a]`. -/
theorem MorseStrip.neg (hf : MorseStrip I f a b) : MorseStrip I (fun x => -f x) (-b) (-a) where
  smooth := hf.smooth.neg
  lt := neg_lt_neg hf.lt
  compact := by
    rw [preimage_neg_Icc]
    exact hf.compact
  regular := fun x hx => by
    rw [isCriticalPt_neg_iff]
    apply hf.regular
    rcases hx with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  nondegenerate := fun x hx hc => by
    rw [isNondegenerateCriticalPt_neg_iff]
    exact hf.nondegenerate x (neg_mem_Ioo_iff.1 hx) ((isCriticalPt_neg_iff I f x).1 hc)

theorem MorseStrip.of_neg (hf : MorseStrip I (fun x => -f x) (-b) (-a)) : MorseStrip I f a b := by
  have h := hf.neg
  simpa only [neg_neg_fun, neg_neg] using h

/-- Self-indexing is preserved by the dual: index `k ↦ n - k` reverses the order of indices
and `f ↦ -f` reverses the order of values. -/
theorem IsSelfIndexing.neg {n : ℕ} {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    (hf : MorseStrip I f a b) (h : IsSelfIndexing I f a b) :
    IsSelfIndexing I (fun x => -f x) (-b) (-a) := by
  intro p q hp hq hcp hcq hlt
  rw [neg_mem_Ioo_iff] at hp hq
  rw [isCriticalPt_neg_iff] at hcp hcq
  have hnp := hf.nondegenerate p hp hcp
  have hnq := hf.nondegenerate q hq hcq
  have h1 := morseIndex_neg_add hnp
  have h2 := morseIndex_neg_add hnq
  have hqp : morseIndex I f q < morseIndex I f p := by omega
  have := h q p hq hp hcq hcp hqp
  show -f p < -f q
  linarith

theorem IsSelfIndexing.of_neg {n : ℕ} {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    (hf : MorseStrip I f a b) (h : IsSelfIndexing I (fun x => -f x) (-b) (-a)) :
    IsSelfIndexing I f a b := by
  have h' := h.neg hf.neg
  simpa only [neg_neg_fun, neg_neg] using h'

omit [TopologicalSpace M] in
/-- A modification of `f` within `(a, b)` is, after negation, a modification of `-f` within
`(-b, -a)`. -/
theorem ModifiedWithin.neg (h : ModifiedWithin f a b g) :
    ModifiedWithin (fun x => -f x) (-b) (-a) (fun x => -g x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [preimage_neg_Ioo] at hx
    show -g x = -f x
    rw [h.eqOn hx]
  · rw [preimage_neg_Ioo] at hx
    exact neg_mem_Ioo_iff.2 (h.mapsTo hx)

omit [TopologicalSpace M] in
theorem ModifiedWithin.of_neg (h : ModifiedWithin (fun x => -f x) (-b) (-a) (fun x => -g x)) :
    ModifiedWithin f a b g := by
  have h' := h.neg
  simpa only [neg_neg_fun, neg_neg] using h'

omit [TopologicalSpace M] in
theorem modifiedWithin_neg_iff :
    ModifiedWithin (fun x => -f x) (-b) (-a) (fun x => -g x) ↔ ModifiedWithin f a b g :=
  ⟨ModifiedWithin.of_neg, ModifiedWithin.neg⟩

end Structures

end PoincareHighDim
