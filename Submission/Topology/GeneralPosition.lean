import Submission.ChartDisks
import Submission.Topology.SphereSimplyConnected
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# General position for maps of the square into `ℝⁿ`, `n ≥ 3`, and chart cutoffs

This module collects the analytic ingredients used to push a null-homotopy of a loop off the
centre of a chart ball (`Submission.Topology.PushOff`).

## Sard-type avoidance

* `exists_differentiable_near`: every continuous map `I × I → ℝⁿ` is uniformly approximable by
  the restriction of a differentiable map `ℝ × ℝ → ℝⁿ` (Stone–Weierstrass on the square,
  applied coordinatewise to the subalgebra `diffSubalgebra` of restrictions of differentiable
  functions).
* `exists_notMem_range_of_differentiable`: the range of a differentiable map `ℝ × ℝ → ℝⁿ`,
  `n ≥ 3`, has dense complement (its Hausdorff dimension is at most `2 < n`,
  `Differentiable.dense_compl_range_of_finrank_lt_finrank`), so it misses points arbitrarily
  close to `0`.
* `exists_continuous_near_avoiding`: the interface consumed by the push-off lemma: a small
  continuous displacement `g` of a continuous `f : I × I → ℝⁿ` together with a small vector `d`
  with `g z ≠ d` for all `z`.

## Chart cutoffs

* `chartCutoff φ c a b : M → ℝ`: the radial cutoff read through the chart `φ`, equal to `1` on
  `‖φ x - c‖ ≤ a`, to `0` on `‖φ x - c‖ ≥ b` and off `φ.source`, and continuous on all of `M`
  when `closedBall c b ⊆ φ.target` and `M` is Hausdorff (`chartCutoff_continuous`).
* `continuous_chartCutoff_smul`: the cutoff chart vector field `x ↦ κ x • (φ x - c)` is
  continuous on `M`.
-/

namespace PoincareHighDim

open Metric Set unitInterval Module Topology Filter

/-! ### Stone–Weierstrass approximation on the square -/

/-- Continuous functions on `I × I` that are restrictions of differentiable functions on
`ℝ × ℝ`. -/
def diffSubalgebra : Subalgebra ℝ C(I × I, ℝ) where
  carrier := {g | ∃ G : ℝ × ℝ → ℝ, Differentiable ℝ G ∧
    ∀ z : I × I, g z = G ((z.1 : ℝ), (z.2 : ℝ))}
  mul_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    exact ⟨F * G, hF.mul hG, fun z => by simp [hf z, hg z]⟩
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    exact ⟨F + G, hF.add hG, fun z => by simp [hf z, hg z]⟩
  algebraMap_mem' r := ⟨fun _ => r, differentiable_const r, fun z => rfl⟩

/-- The coordinate functions separate the points of the square. -/
theorem diffSubalgebra_separatesPoints : diffSubalgebra.SeparatesPoints := by
  intro z w hzw
  by_cases h1 : (z.1 : ℝ) = w.1
  · have h2 : (z.2 : ℝ) ≠ w.2 := by
      intro h2
      exact hzw (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
    refine ⟨fun z : I × I => (z.2 : ℝ), ⟨⟨fun z : I × I => (z.2 : ℝ), by fun_prop⟩,
      ⟨Prod.snd, differentiable_snd, fun z => rfl⟩, rfl⟩, h2⟩
  · refine ⟨fun z : I × I => (z.1 : ℝ), ⟨⟨fun z : I × I => (z.1 : ℝ), by fun_prop⟩,
      ⟨Prod.fst, differentiable_fst, fun z => rfl⟩, rfl⟩, h1⟩

/-- Real-valued continuous functions on the square are uniformly approximable by restrictions
of differentiable functions on the plane (Stone–Weierstrass). -/
theorem exists_differentiable_near_real {f : I × I → ℝ} (hf : Continuous f) {ε : ℝ}
    (hε : 0 < ε) : ∃ G : ℝ × ℝ → ℝ, Differentiable ℝ G ∧
      ∀ z : I × I, |G ((z.1 : ℝ), (z.2 : ℝ)) - f z| < ε := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    diffSubalgebra diffSubalgebra_separatesPoints f hf ε hε
  obtain ⟨G, hG, hgG⟩ := g.2
  refine ⟨G, hG, fun z => ?_⟩
  have := hg z
  rw [Real.norm_eq_abs, hgG z] at this
  exact this

/-- Vector-valued version of `exists_differentiable_near_real`. -/
theorem exists_differentiable_near {n : ℕ} {f : I × I → EuclideanSpace ℝ (Fin n)}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ × ℝ → EuclideanSpace ℝ (Fin n), Differentiable ℝ G ∧
      ∀ z : I × I, ‖G ((z.1 : ℝ), (z.2 : ℝ)) - f z‖ < ε := by
  have hε' : 0 < ε / (n + 1) := by positivity
  have hcomp : ∀ i : Fin n, ∃ G : ℝ × ℝ → ℝ, Differentiable ℝ G ∧
      ∀ z : I × I, |G ((z.1 : ℝ), (z.2 : ℝ)) - f z i| < ε / (n + 1) := fun i =>
    exists_differentiable_near_real (by fun_prop) hε'
  choose G hG hGf using hcomp
  refine ⟨fun x => WithLp.toLp 2 (fun i => G i x), ?_, fun z => ?_⟩
  · exact differentiable_euclidean.2 fun i => hG i
  · show ‖WithLp.toLp 2 (fun i => G i ((z.1 : ℝ), (z.2 : ℝ))) - f z‖ < ε
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ i, ‖(WithLp.toLp 2 (fun i => G i ((z.1 : ℝ), (z.2 : ℝ))) - f z) i‖ ^ 2
        ≤ ∑ _i : Fin n, (ε / (n + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have := hGf i z
      simp only [PiLp.sub_apply, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this.le 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    refine (Real.sqrt_le_sqrt hsum).trans_lt ?_
    rw [Real.sqrt_lt' hε, div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hε2 : 0 < ε ^ 2 := by positivity
    nlinarith [mul_nonneg hε2.le (sq_nonneg (n : ℝ)), mul_nonneg hε2.le hn, hε2]

/-! ### Sard-type avoidance via Hausdorff dimension -/

/-- The image of `I × I` under a differentiable map `ℝ × ℝ → ℝⁿ`, `n ≥ 3`, misses points
arbitrarily close to `0`: the range has Hausdorff dimension at most `2 < n`, hence dense
complement. -/
theorem exists_notMem_range_of_differentiable {n : ℕ} (hn : 3 ≤ n)
    {G : ℝ × ℝ → EuclideanSpace ℝ (Fin n)} (hG : Differentiable ℝ G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : EuclideanSpace ℝ (Fin n), ‖d‖ < δ ∧ ∀ z : I × I, G ((z.1 : ℝ), (z.2 : ℝ)) ≠ d := by
  have hlt : finrank ℝ (ℝ × ℝ) < finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]; omega
  obtain ⟨d, hdG, hd⟩ := (hG.dense_compl_range_of_finrank_lt_finrank hlt).exists_mem_open
    isOpen_ball (nonempty_ball.2 hδ : (ball (0 : EuclideanSpace ℝ (Fin n)) δ).Nonempty)
  exact ⟨d, mem_ball_zero_iff.1 hd, fun z hz => hdG ⟨_, hz⟩⟩

/-- The interface consumed by the push-off lemma: a small continuous displacement `g` of a
continuous map `f : I × I → ℝⁿ` (`n ≥ 3`) missing a point `d` near the origin. -/
theorem exists_continuous_near_avoiding {n : ℕ} (hn : 3 ≤ n)
    {f : I × I → EuclideanSpace ℝ (Fin n)} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : I × I → EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin n)),
      Continuous g ∧ ‖d‖ < ε ∧ (∀ z, ‖g z - f z‖ < ε) ∧ ∀ z, g z ≠ d := by
  obtain ⟨G, hG, hGf⟩ := exists_differentiable_near hf hε
  obtain ⟨d, hd, hdG⟩ := exists_notMem_range_of_differentiable hn hG hε
  exact ⟨fun z => G ((z.1 : ℝ), (z.2 : ℝ)), d, hG.continuous.comp (by fun_prop), hd, hGf, hdG⟩

/-! ### Chart cutoffs -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

/-- Radial cutoff read through a chart: `1` on `‖φ x - c‖ ≤ a`, `0` on `‖φ x - c‖ ≥ b` and off
the chart source. -/
noncomputable def chartCutoff (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n)) (a b : ℝ) : M → ℝ :=
  φ.source.indicator fun x => clamp01 ((b - ‖φ x - c‖) / (b - a))

variable {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {c : EuclideanSpace ℝ (Fin n)}
  {a b : ℝ}

theorem chartCutoff_of_mem {x : M} (hx : x ∈ φ.source) :
    chartCutoff φ c a b x = clamp01 ((b - ‖φ x - c‖) / (b - a)) :=
  Set.indicator_of_mem hx _

theorem chartCutoff_of_notMem {x : M} (hx : x ∉ φ.source) : chartCutoff φ c a b x = 0 :=
  Set.indicator_of_notMem hx _

theorem chartCutoff_eq_one (hab : a < b) {x : M} (hx : x ∈ φ.source) (h : ‖φ x - c‖ ≤ a) :
    chartCutoff φ c a b x = 1 := by
  rw [chartCutoff_of_mem hx, clamp01_of_one_le]
  rw [le_div_iff₀ (by linarith)]; linarith

theorem chartCutoff_eq_zero (hab : a < b) {x : M} (h : x ∉ φ.source ∨ b ≤ ‖φ x - c‖) :
    chartCutoff φ c a b x = 0 := by
  rcases h with h | h
  · exact chartCutoff_of_notMem h
  · by_cases hx : x ∈ φ.source
    · rw [chartCutoff_of_mem hx, clamp01_of_nonpos]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · exact chartCutoff_of_notMem hx

theorem chartCutoff_mem_Icc (x : M) : chartCutoff φ c a b x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : x ∈ φ.source
  · rw [chartCutoff_of_mem hx]
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  · rw [chartCutoff_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩

theorem lt_of_chartCutoff_pos (hab : a < b) {x : M} (h : 0 < chartCutoff φ c a b x) :
    x ∈ φ.source ∧ ‖φ x - c‖ < b := by
  by_contra hcon
  rw [not_and_or, not_lt] at hcon
  rw [chartCutoff_eq_zero hab hcon] at h
  exact lt_irrefl _ h

theorem lt_of_chartCutoff_lt_one (hab : a < b) {x : M} (hx : x ∈ φ.source)
    (h : chartCutoff φ c a b x < 1) : a < ‖φ x - c‖ := by
  by_contra hcon
  rw [chartCutoff_eq_one hab hx (not_lt.1 hcon)] at h
  exact lt_irrefl _ h

/-- The closed chart ball is closed in `M`: it is the image of a compact set under the
continuous map `φ.symm`, and `M` is Hausdorff. -/
theorem isClosed_symm_image_closedBall [T2Space M] (hsub : closedBall c b ⊆ φ.target) :
    IsClosed (φ.symm '' closedBall c b) :=
  ((isCompact_closedBall c b).image_of_continuousOn (φ.continuousOn_symm.mono hsub)).isClosed

/-- The chart cutoff is continuous on all of `M`. -/
theorem chartCutoff_continuous [T2Space M] (hab : a < b) (hsub : closedBall c b ⊆ φ.target) :
    Continuous (chartCutoff φ c a b) := by
  refine continuous_of_cover_nhds (s := fun i : Bool => if i then φ.source
    else (φ.symm '' closedBall c b)ᶜ) (fun x => ?_) (fun i => ?_)
  · by_cases hx : x ∈ φ.source
    · exact ⟨true, by simpa using φ.open_source.mem_nhds hx⟩
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      refine (isClosed_symm_image_closedBall hsub).isOpen_compl.mem_nhds ?_
      rintro ⟨y, hy, rfl⟩
      exact hx (φ.map_target (hsub hy))
  · cases i with
    | true =>
      simp only [ite_true]
      refine ContinuousOn.congr (f := fun x => clamp01 ((b - ‖φ x - c‖) / (b - a))) ?_
        fun x hx => chartCutoff_of_mem hx
      exact continuous_clamp01.comp_continuousOn
        ((continuousOn_const.sub ((φ.continuousOn.sub continuousOn_const).norm)).div_const _)
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      refine ContinuousOn.congr (f := fun _ => (0 : ℝ)) continuousOn_const fun x hx => ?_
      by_cases hs : x ∈ φ.source
      · refine chartCutoff_eq_zero hab (Or.inr (not_lt.1 fun hlt => hx ⟨φ x, ?_, φ.left_inv hs⟩))
        rw [mem_closedBall_iff_norm]; exact hlt.le
      · exact chartCutoff_of_notMem hs

/-- The cutoff chart vector field `x ↦ κ x • (φ x - c)` is continuous on all of `M`. -/
theorem continuous_chartCutoff_smul [T2Space M] (hab : a < b) (hsub : closedBall c b ⊆ φ.target) :
    Continuous fun x => chartCutoff φ c a b x • (φ x - c) := by
  refine continuous_of_cover_nhds (s := fun i : Bool => if i then φ.source
    else (φ.symm '' closedBall c b)ᶜ) (fun x => ?_) (fun i => ?_)
  · by_cases hx : x ∈ φ.source
    · exact ⟨true, by simpa using φ.open_source.mem_nhds hx⟩
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      refine (isClosed_symm_image_closedBall hsub).isOpen_compl.mem_nhds ?_
      rintro ⟨y, hy, rfl⟩
      exact hx (φ.map_target (hsub hy))
  · cases i with
    | true =>
      simp only [ite_true]
      exact ((chartCutoff_continuous hab hsub).continuousOn).smul
        (φ.continuousOn.sub continuousOn_const)
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      refine ContinuousOn.congr (f := fun _ => (0 : EuclideanSpace ℝ (Fin n))) continuousOn_const
        fun x hx => ?_
      by_cases hs : x ∈ φ.source
      · rw [chartCutoff_eq_zero hab (Or.inr (not_lt.1 fun hlt => hx ⟨φ x, ?_, φ.left_inv hs⟩)),
          zero_smul]
        rw [mem_closedBall_iff_norm]; exact hlt.le
      · rw [chartCutoff_of_notMem hs, zero_smul]

end PoincareHighDim
