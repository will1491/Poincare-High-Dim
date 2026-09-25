import Submission.Morse.CancelField
import Mathlib.Dynamics.OmegaLimit

/-!
# Cancellation, step C4a: the flow of the modified field and the forward dynamics

Phase B, step C4a (`CancelFlow`).  For the cancellation data `c : CancelData I f a' b' p q`
and transverse constants `k : c.CancelConsts` (module `CancelField`), this module provides

* **the global flow `Φ` of the modified field `V'`** (`CancelConsts.Φ`, from the vendored
  `exists_globalIntegralCurve_of_compactSupport`): group law (`Φ_add`, `Φ_Φ`, `Φ_neg_Φ`),
  injectivity, joint smoothness (`contMDiff_Φ_joint`), continuity of the time-`t` maps and of
  the trajectories, the `Flow` structure `toFlow`;
* **agreement with the original flow off `K`** in both time directions and with the hypothesis
  on either trajectory (`Φ_eq_flow_of_avoid`, `flow_eq_Φ_of_avoid`, `Φ_eq_flow_of_avoid_neg`,
  `flow_eq_Φ_of_avoid_neg`, `Φ_eq_flow_of_avoid_uIcc`), from the general
  `integralCurve_eq_on_Icc_of_agree` (two `C¹` fields agreeing on an open set);
* **derivative facts**: `hasDerivAt_f_Φ` (`df (V')` along `Φ`), the unit-speed collars
  (`dfV_V'_lower_collar`, `f_Φ_lower_collar`, `Φ_eq_flow_of_f_lt`, and the upper versions), the
  chart ODEs `hasDerivAt_symm_Φ_p` / `hasDerivAt_symm_Φ_q` with the explicit pulled-back fields
  `Vp` / `Vq`, the transverse coordinate along `Φ` (`hasDerivAt_ζ_Φ`, `dζ_V'`,
  `deriv_normSq_ζ_Φ_nonpos`), and `dfV_V'_tube` / `dfV_V'_mid` (`df (V') = -1 + 2 βm ψm` on the
  tube where the pushers vanish; `push_Yp'_eq_zero_of_lo₂_le`, `push_Yq'_eq_zero_of_le_hi₁`);
* **a dynamical toolkit** for the crossing property: uniform times by compactness
  (`exists_uniform_time`), the LaSalle principle through ω-limit sets
  (`exists_omegaLimit_subset`, `exists_exit_of_lyapunov_pair`, `exists_exit_of_lyapunov_weak`,
  `exists_exit_of_deriv_pos`, `exists_uniform_exit_of_deriv_pos`, `exists_notMem_of_two_pieces`),
  first hitting times (`exists_first_hit`), and one-sided derivative facts;
* **the forward exit lemmas proved so far**:
  - the middle band of the tube `Tmid := Sσ ∩ {lo₂ ≤ f ≤ hi₁}` (`exists_exit_mid_band`): a
    trajectory stays in the band until it reaches the level `hi₁` (with `‖ζ‖ < 2δ` unless at time
    `0`) or the level `lo₂`;
  - the ball of `p` (`exists_reach_Tmid_of_mem_Wball`): every trajectory starting in the closed
    chart ball `Wball` of radius `ρB` reaches the middle band at the level `lo₂`, staying in the
    ball region meanwhile.  This is proved with the two-stage LaSalle principle on the inner
    region `Wp1` (weak Lyapunov function `Lp y = ‖y‖ (‖y‖ - ⟪y, e₁⟫)`, second function the axial
    coordinate) and on the outer region `Wp2` (weak Lyapunov function `Bm`), under the explicit
    transverse lower bound `hζmin` (`‖ζ‖ ≥ 2δ` on the part of the annulus outside the angular
    threshold `b₀ = τ²/4`), which is a smallness condition on `δ` obtainable by shrinking the
    constants (`δ`, `τ` may be shrunk without affecting `hdB`, `hcone`).

**Not delivered here** (see the NOTES of the build): the `q`-ball exit, the no-return lemma
along the other arm, `descend_outside_K` and `reaches_bottom`.  The obstruction found is the
"partial reversal" zone `δ < ‖ζ‖ < 2δ` of the tube: a trajectory can descend from the middle
band back into the ball of `p` and be pushed up again; excluding infinitely many such cycles
needs a global weak Lyapunov function (the transported angle `Bm ∘ Gσ ∘ ζ`, extended to the
chart of `q` through the invariant `‖u‖ ‖v‖`), which is not in the plan.

Conventions: fields descend (`df(V) ∈ [-1, 0]`), `morseNorm` is the Euclidean norm while
`Metric.ball` on `Fin n → ℝ` is the sup-norm ball; all dynamical lemmas carry explicit `hstay`
or region hypotheses.
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split recombine_decompose)
open CancelModel

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

/-! ### A cluster-point lemma -/

section ClusterPt

variable {X : Type*} [TopologicalSpace X]

/-- A cluster point of a filter supported in `C` sees the eventual properties within `C`. -/
theorem frequently_of_clusterPt_within {C : Set X} {F : Filter X} {z : X} (hz : ClusterPt z F)
    (hF : F ≤ 𝓟 C) {P : X → Prop} (hP : ∀ᶠ y in 𝓝[C] z, P y) : ∃ᶠ y in F, P y := by
  have hne := hz.neBot
  have h1 : 𝓝 z ⊓ F ≤ 𝓝[C] z := le_inf inf_le_left (inf_le_right.trans hF)
  exact (Eventually.frequently (h1 hP)).filter_mono inf_le_right

end ClusterPt

/-- A positive derivative at `0` gives a strictly larger value at some small positive time. -/
theorem exists_pos_lt_of_hasDerivAt_pos {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : HasDerivAt g r 0) : ∃ t₀ : ℝ, 0 < t₀ ∧ g 0 < g t₀ := by
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hg)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < slope g 0 t :=
    ((tendsto_order.1 (hslope.mono_left (nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne'))).1
      0 hr)
  obtain ⟨t₀, ht₀, hpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht₀' : (0 : ℝ) < t₀ := hpos
  rw [slope_def_field, sub_zero] at ht₀
  refine ⟨t₀, ht₀', ?_⟩
  have := (div_pos_iff_of_pos_right ht₀').1 ht₀
  linarith

/-- A derivative at `t` with values on the left not exceeding the value at `t` is
nonnegative. -/
theorem nonneg_of_hasDerivAt_of_le_left {g : ℝ → ℝ} {r t ε : ℝ} (hε : 0 < ε)
    (hg : HasDerivAt g r t) (hle : ∀ s ∈ Ico (t - ε) t, g s ≤ g t) : 0 ≤ r := by
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hg)
  have h1 : Tendsto (slope g t) (𝓝[<] t) (𝓝 r) :=
    hslope.mono_left (nhdsWithin_mono _ fun s (hs : s < t) => hs.ne)
  refine ge_of_tendsto h1 ?_
  filter_upwards [Ico_mem_nhdsLT (show t - ε < t by linarith)] with s hs
  rw [slope_def_field]
  have hst : s - t < 0 := by linarith [hs.2]
  have := hle s hs
  exact div_nonneg_of_nonpos (by linarith) hst.le

/-- A positive derivative at `t`: the values just after `t` exceed `g t`. -/
theorem eventually_gt_of_hasDerivAt_pos {g : ℝ → ℝ} {r t : ℝ} (hr : 0 < r)
    (hg : HasDerivAt g r t) : ∀ᶠ s in 𝓝[>] t, g t < g s := by
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hg)
  have hev : ∀ᶠ s in 𝓝[>] t, 0 < slope g t s :=
    ((tendsto_order.1 (hslope.mono_left (nhdsWithin_mono _ fun s (hs : t < s) => hs.ne'))).1
      0 hr)
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hts
  have hts' : t < s := hts
  rw [slope_def_field] at hs
  have := (div_pos_iff_of_pos_right (by linarith)).1 hs
  linarith

/-- A negative derivative at `t`: the values just after `t` are below `g t`. -/
theorem eventually_lt_of_hasDerivAt_neg {g : ℝ → ℝ} {r t : ℝ} (hr : r < 0)
    (hg : HasDerivAt g r t) : ∀ᶠ s in 𝓝[>] t, g s < g t := by
  have := eventually_gt_of_hasDerivAt_pos (g := fun s => -g s) (r := -r) (by linarith) hg.neg
  filter_upwards [this] with s hs
  linarith

/-- A negative derivative at `0` gives a strictly smaller value at some small positive time. -/
theorem exists_pos_gt_of_hasDerivAt_neg {g : ℝ → ℝ} {r : ℝ} (hr : r < 0)
    (hg : HasDerivAt g r 0) : ∃ t₀ : ℝ, 0 < t₀ ∧ g t₀ < g 0 := by
  obtain ⟨t₀, ht₀, h⟩ := exists_pos_lt_of_hasDerivAt_pos (g := fun t => -g t) (r := -r)
    (by linarith) hg.neg
  exact ⟨t₀, ht₀, by simpa using h⟩

/-! ### Integral curves of two fields agreeing on an open set -/

section Agree

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

/-- If two `C¹` fields agree on an open set `U`, two integral curves with the same initial point
agree on `[0, T]` as soon as the first one stays in `U` on `[0, T)`. -/
theorem integralCurve_eq_on_Icc_of_agree {V₁ V₂ : (x : M) → TangentSpace I x}
    (hV₁ : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1 (fun x => (⟨x, V₁ x⟩ : TangentBundle I M)))
    {U : Set M} (hU : IsOpen U) (hV : ∀ x ∈ U, V₁ x = V₂ x) {γ₁ γ₂ : ℝ → M}
    (hγ₁ : IsMIntegralCurve γ₁ V₁) (hγ₂ : IsMIntegralCurve γ₂ V₂) (h0 : γ₁ 0 = γ₂ 0) {T : ℝ}
    (hmem : ∀ s ∈ Ico 0 T, γ₁ s ∈ U) : ∀ s ∈ Icc 0 T, γ₂ s = γ₁ s := by
  have hQ : IsClosed {s : ℝ | γ₂ s = γ₁ s} := isClosed_eq hγ₂.continuous hγ₁.continuous
  refine Icc_subset_of_isClosed_of_step hQ (by simp [h0]) fun t ht hIcc => ?_
  have hxt : γ₂ t = γ₁ t := hIcc (right_mem_Icc.2 ht.1)
  have hc₁ : IsMIntegralCurveAt γ₁ V₁ t := hγ₁.isMIntegralCurveAt t
  have hc₂ : IsMIntegralCurveAt γ₂ V₁ t := by
    have hev : ∀ᶠ s in 𝓝 t, γ₂ s ∈ U :=
      hγ₂.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds (hxt ▸ hmem t ht))
    filter_upwards [hev] with s hs
    have := hγ₂ s
    rwa [← hV _ hs] at this
  have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
    hV₁.contMDiffAt hc₁ hc₂ hxt.symm
  exact nhdsWithin_le_nhds (heq.mono fun s hs => hs.symm)

/-- Backwards version. -/
theorem integralCurve_eq_on_Icc_neg_of_agree {V₁ V₂ : (x : M) → TangentSpace I x}
    (hV₁ : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1 (fun x => (⟨x, V₁ x⟩ : TangentBundle I M)))
    {U : Set M} (hU : IsOpen U) (hV : ∀ x ∈ U, V₁ x = V₂ x) {γ₁ γ₂ : ℝ → M}
    (hγ₁ : IsMIntegralCurve γ₁ V₁) (hγ₂ : IsMIntegralCurve γ₂ V₂) (h0 : γ₁ 0 = γ₂ 0) {T : ℝ}
    (hmem : ∀ s ∈ Ioc (-T) 0, γ₁ s ∈ U) : ∀ s ∈ Icc (-T) 0, γ₂ s = γ₁ s := by
  have hV₁' : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1
      (fun x => (⟨x, -V₁ x⟩ : TangentBundle I M)) := hV₁.neg_section
  have hr₁ : IsMIntegralCurve (fun s => γ₁ (-s)) (-V₁) := by
    have hc := hγ₁.comp_mul (-1)
    have e : (γ₁ ∘ fun s : ℝ => s * (-1)) = fun s => γ₁ (-s) := by
      funext s; simp [Function.comp]
    have e' : (-1 : ℝ) • V₁ = -V₁ := by funext y; exact neg_one_smul ℝ (V₁ y)
    rwa [e, e'] at hc
  have hr₂ : IsMIntegralCurve (fun s => γ₂ (-s)) (-V₂) := by
    have hc := hγ₂.comp_mul (-1)
    have e : (γ₂ ∘ fun s : ℝ => s * (-1)) = fun s => γ₂ (-s) := by
      funext s; simp [Function.comp]
    have e' : (-1 : ℝ) • V₂ = -V₂ := by funext y; exact neg_one_smul ℝ (V₂ y)
    rwa [e, e'] at hc
  have h := integralCurve_eq_on_Icc_of_agree (V₁ := -V₁) (V₂ := -V₂) hV₁' hU
    (fun x hx => by simp only [Pi.neg_apply, hV x hx]) hr₁ hr₂ (by simpa using h0) (T := T)
    (fun s hs => hmem (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  intro s hs
  have := h (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  simpa using this

end Agree

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace CancelData

variable [DecidableEq M] {a' b' : ℝ} {p q : M} (c : CancelData I f a' b' p q)

/-! ### Preliminaries in the `CancelData` namespace -/

/-- The small balls have `f`-values in `(a' + η₀, b' - η₀)`. -/
theorem f_mem_of_mem_smallBall {x : M} {p' : M} {hp' : p' ∈ ({p, q} : Finset M)}
    (hx : x ∈ c.D.smallBall p' hp') : a' + c.η₀ < f x ∧ f x < b' - c.η₀ :=
  c.η₀_spec p' hp' x (image_mono (fun y (hy : morseNorm n y < _) =>
    hy.le.trans (c.D.r₀_lt_R p' hp').le) hx)

/-- The derivative of `ζ` along a section. -/
def dζ (V : (x : M) → TangentSpace I x) (x : M) : EuclideanSpace ℝ (Fin (n - c.d.k)) :=
  (NormedSpace.fromTangentSpace (c.ζ x))
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) c.ζ x (V x))

theorem dζ_add (V W : (x : M) → TangentSpace I x) (x : M) :
    c.dζ (fun x => V x + W x) x = c.dζ V x + c.dζ W x := by
  unfold dζ; simp

theorem dζ_smul (a : ℝ) (V : (x : M) → TangentSpace I x) (x : M) :
    c.dζ (fun x => a • V x) x = a • c.dζ V x := by
  unfold dζ; simp

theorem dζ_V_eq_zero {x : M} (hx : x ∈ c.TubeOpen) : c.dζ c.D.V x = 0 := c.dζ_V hx

theorem dζ_Z_eq {x : M} (hx : x ∈ c.TubeOpen) : c.dζ c.Z x = -c.ζ x := c.dζ_Z hx

theorem dζ_zero (x : M) : c.dζ (fun _ => 0) x = 0 := by
  unfold dζ; simp

/-! ### Level sets used by the middle-band analysis -/

theorem isClosed_mid_levels : IsClosed {y : M | c.lo₂ ≤ f y ∧ f y ≤ c.hi₁} :=
  (isClosed_Icc.preimage c.hfs.continuous)

theorem lo₂_mem_levels : c.c₁ - c.η / 2 ≤ c.lo₂ := by
  unfold lo₂; linarith [c.η_pos]

theorem hi₁_mem_levels : c.hi₁ ≤ c.c₂ + c.η / 2 := by
  unfold hi₁; linarith [c.η_pos]

/-- The closed set of the end levels of the middle band. -/
def Emid : Set M := {y | f y ≤ c.lo₂ ∨ c.hi₁ ≤ f y}

theorem isClosed_Emid : IsClosed c.Emid :=
  (isClosed_Iic.preimage c.hfs.continuous).union (isClosed_Ici.preimage c.hfs.continuous)

theorem lt_of_notMem_Emid {y : M} (hy : y ∉ c.Emid) : c.lo₂ < f y ∧ f y < c.hi₁ := by
  simp only [Emid, mem_ofPred_eq, not_or, not_le] at hy
  exact hy

/-! ### The contraction field in the chart of `p`, extended by zero -/

open scoped Classical in
/-- The contraction field at a chart point of `p` (zero off the tube). -/
def Zp' (y : Fin n → ℝ) : Fin n → ℝ := if c.e.χ y ∈ c.TubeOpenσ then c.Zp y else 0

theorem Zp'_of_mem {y : Fin n → ℝ} (h : c.e.χ y ∈ c.TubeOpenσ) : c.Zp' y = c.Zp y := by
  classical simp [Zp', h]

theorem Zp'_of_notMem {y : Fin n → ℝ} (h : c.e.χ y ∉ c.TubeOpenσ) : c.Zp' y = 0 := by
  classical simp [Zp', h]

/-- `Zp'` is orthogonal to `y` (level-tangent = sphere-tangent). -/
theorem dot_Zp' {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) : dot y (c.Zp' y) = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.TubeOpenσ
  · rw [c.Zp'_of_mem hT, dot_eq_sum]
    exact c.Z_chart_p_orth (c.morseNorm_lt_rmp_of_sq_lt hy) hT.1
  · rw [c.Zp'_of_notMem hT, dot_zero_right]

theorem Zp'_eq_zero_of_ζ {y : Fin n → ℝ} (hT : c.e.χ y ∈ c.TubeOpenσ)
    (hζ : c.ζ (c.e.χ y) = 0) : c.Zp' y = 0 := by
  rw [c.Zp'_of_mem hT]
  unfold Zp
  rw [(c.Z_eq_zero_iff hT.1).2 hζ, map_zero]
  rfl

namespace CancelConsts

variable {c} (k : c.CancelConsts)

/-! ### The global flow `Φ` of the modified field -/

theorem smooth_one' :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1 (fun x => (⟨x, k.V' x⟩ : TangentBundle I M)) :=
  k.contMDiff_V'.of_le (by norm_num)

/-- The modified field is complete (compact support). -/
theorem hcomplete' : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ k.V' :=
  exists_globalIntegralCurve_of_compactSupport k.V' k.contMDiff_V' k.isCompact_tsupport_V'

/-- The global flow of the modified field `V'`. -/
def Φ (t : ℝ) (x : M) : M := curveAt k.V' k.hcomplete' x t

theorem isMIntegralCurve_Φ (x : M) : IsMIntegralCurve (fun t => k.Φ t x) k.V' :=
  curveAt_integralCurve k.V' k.hcomplete' x

@[simp] theorem Φ_zero (x : M) : k.Φ 0 x = x := curveAt_zero k.V' k.hcomplete' x

theorem Φ_add (x : M) (s t : ℝ) : k.Φ (s + t) x = k.Φ t (k.Φ s x) :=
  curveAt_add k.V' k.smooth_one' k.hcomplete' x s t

theorem Φ_Φ (x : M) (s t : ℝ) : k.Φ t (k.Φ s x) = k.Φ (s + t) x := (k.Φ_add x s t).symm

theorem Φ_neg_Φ (x : M) (t : ℝ) : k.Φ (-t) (k.Φ t x) = x := by
  rw [Φ_Φ, add_neg_cancel, Φ_zero]

theorem Φ_Φ_neg (x : M) (t : ℝ) : k.Φ t (k.Φ (-t) x) = x := by
  rw [Φ_Φ, neg_add_cancel, Φ_zero]

theorem Φ_injective (t : ℝ) : Function.Injective (k.Φ t) :=
  curveAt_injective' k.V' k.smooth_one' k.hcomplete' t

theorem Φ_eq_self_of_notMem_tsupport {x : M} (hx : x ∉ tsupport k.V') (t : ℝ) :
    k.Φ t x = x :=
  curveAt_eq_self_of_not_mem_tsupport k.V' k.contMDiff_V' k.hcomplete' hx t

theorem contMDiff_Φ_joint :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => k.Φ z.1 z.2) :=
  contMDiff_globalFlow_joint_of_compactSupport k.V' k.contMDiff_V' k.isCompact_tsupport_V'

theorem continuous_Φ_joint : Continuous (fun z : ℝ × M => k.Φ z.1 z.2) :=
  k.contMDiff_Φ_joint.continuous

theorem contMDiff_Φ (t : ℝ) : ContMDiff I I ∞ (k.Φ t) := fun x =>
  contMDiffAt_globalFlow_of_compactSupport k.V' k.contMDiff_V' k.isCompact_tsupport_V' t x

theorem continuous_Φ (t : ℝ) : Continuous (k.Φ t) := (k.contMDiff_Φ t).continuous

theorem continuous_Φ_curve (x : M) : Continuous (fun t => k.Φ t x) :=
  (k.isMIntegralCurve_Φ x).continuous

/-- A time interval on which the `Φ`-trajectory stays in an open set. -/
theorem exists_Icc_Φ_mem_open {O : Set M} (hO : IsOpen O) {x : M} {t : ℝ}
    (ht : k.Φ t x ∈ O) : ∃ δ > 0, ∀ s ∈ Icc (t - δ) (t + δ), k.Φ s x ∈ O := by
  have hmem : {s | k.Φ s x ∈ O} ∈ 𝓝 t :=
    (k.continuous_Φ_curve x).continuousAt.preimage_mem_nhds (hO.mem_nhds ht)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨ε / 2, by positivity, fun s hs => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hs.1, hs.2]

/-! ### Agreement with the original flow off `K` -/

theorem V'_eq_V_on_compl : ∀ x ∈ k.Kᶜ, k.V' x = c.D.V x := fun _ hx => k.V'_eq_V_of_notMem hx

/-- Forward agreement, hypothesis on the `Φ`-trajectory. -/
theorem flow_eq_Φ_of_avoid {x : M} {T : ℝ} (h : ∀ s ∈ Ico 0 T, k.Φ s x ∉ k.K) :
    ∀ s ∈ Icc 0 T, c.D.flow s x = k.Φ s x :=
  integralCurve_eq_on_Icc_of_agree k.smooth_one' k.isClosed_K.isOpen_compl k.V'_eq_V_on_compl
    (k.isMIntegralCurve_Φ x) (c.D.isMIntegralCurve_flow x) (by simp) h

/-- Forward agreement, hypothesis on the `D`-trajectory. -/
theorem Φ_eq_flow_of_avoid {x : M} {T : ℝ} (h : ∀ s ∈ Ico 0 T, c.D.flow s x ∉ k.K) :
    ∀ s ∈ Icc 0 T, k.Φ s x = c.D.flow s x :=
  integralCurve_eq_on_Icc_of_agree c.D.smooth_one k.isClosed_K.isOpen_compl
    (fun x hx => (k.V'_eq_V_on_compl x hx).symm) (c.D.isMIntegralCurve_flow x)
    (k.isMIntegralCurve_Φ x) (by simp) h

/-- Backward agreement, hypothesis on the `Φ`-trajectory. -/
theorem flow_eq_Φ_of_avoid_neg {x : M} {T : ℝ} (h : ∀ s ∈ Ioc (-T) 0, k.Φ s x ∉ k.K) :
    ∀ s ∈ Icc (-T) 0, c.D.flow s x = k.Φ s x :=
  integralCurve_eq_on_Icc_neg_of_agree k.smooth_one' k.isClosed_K.isOpen_compl
    k.V'_eq_V_on_compl (k.isMIntegralCurve_Φ x) (c.D.isMIntegralCurve_flow x) (by simp) h

/-- Backward agreement, hypothesis on the `D`-trajectory. -/
theorem Φ_eq_flow_of_avoid_neg {x : M} {T : ℝ} (h : ∀ s ∈ Ioc (-T) 0, c.D.flow s x ∉ k.K) :
    ∀ s ∈ Icc (-T) 0, k.Φ s x = c.D.flow s x :=
  integralCurve_eq_on_Icc_neg_of_agree c.D.smooth_one k.isClosed_K.isOpen_compl
    (fun x hx => (k.V'_eq_V_on_compl x hx).symm) (c.D.isMIntegralCurve_flow x)
    (k.isMIntegralCurve_Φ x) (by simp) h

/-- Two-sided agreement (hypothesis on the `D`-trajectory over `uIcc 0 t`, excluding the
endpoint). -/
theorem Φ_eq_flow_of_avoid_uIcc {x : M} {t : ℝ}
    (h : ∀ s ∈ uIcc 0 t, s ≠ t → c.D.flow s x ∉ k.K) : k.Φ t x = c.D.flow t x := by
  rcases le_or_gt 0 t with ht | ht
  · exact k.Φ_eq_flow_of_avoid (fun s hs => h s (by rw [uIcc_of_le ht]; exact ⟨hs.1, hs.2.le⟩)
      hs.2.ne) t (right_mem_Icc.2 ht)
  · have := k.Φ_eq_flow_of_avoid_neg (T := -t) (fun s hs => h s
      (by rw [uIcc_of_ge ht.le]; rw [neg_neg] at hs; exact ⟨hs.1.le, hs.2⟩)
      (by rw [neg_neg] at hs; exact hs.1.ne')) t ⟨by rw [neg_neg], ht.le⟩
    exact this


/-! ### `f` along `Φ` -/

theorem hasDerivAt_f_Φ (x : M) (t : ℝ) :
    HasDerivAt (fun s => f (k.Φ s x)) (dfV I f k.V' (k.Φ t x)) t :=
  hasDerivAt_df_comp_integralCurve f c.hfs k.V' (k.isMIntegralCurve_Φ x) t

theorem dfV_V'_eq_of_notMem {x : M} (hx : x ∉ k.K) : dfV I f k.V' x = dfV I f c.D.V x := by
  unfold dfV; rw [k.V'_eq_V_of_notMem hx]

/-- Off `K`, on the strip, off the small balls: unit speed. -/
theorem dfV_V'_eq_neg_one {x : M} (hx : x ∉ k.K) (hf : f x ∈ Icc a' b')
    (hsb : ∀ p' hp', x ∉ c.D.smallBall p' hp') : dfV I f k.V' x = -1 := by
  rw [k.dfV_V'_eq_of_notMem hx]; exact c.D.unit x hf hsb

theorem dfV_V'_nonpos_of_notMem {x : M} (hx : x ∉ k.K) : dfV I f k.V' x ≤ 0 := by
  rw [k.dfV_V'_eq_of_notMem hx]; exact (c.D.dfV_rate x).2

theorem neg_one_le_dfV_V'_of_notMem {x : M} (hx : x ∉ k.K) : -1 ≤ dfV I f k.V' x := by
  rw [k.dfV_V'_eq_of_notMem hx]; exact (c.D.dfV_rate x).1

/-! ### The collars near the ends -/

theorem notMem_K_of_f_lt {x : M} (hx : f x < a' + c.η₀) : x ∉ k.K := fun h =>
  absurd (k.K_subset_strip h).1 (not_le.2 hx)

theorem notMem_K_of_lt_f {x : M} (hx : b' - c.η₀ < f x) : x ∉ k.K := fun h =>
  absurd (k.K_subset_strip h).2 (not_le.2 hx)

/-- In the lower collar `a' ≤ f x < a' + η₀`, the modified field descends at unit speed. -/
theorem dfV_V'_lower_collar {x : M} (h1 : a' ≤ f x) (h2 : f x < a' + c.η₀) :
    dfV I f k.V' x = -1 :=
  k.dfV_V'_eq_neg_one (k.notMem_K_of_f_lt h2)
    ⟨h1, by linarith [c.η₀_pos, c.f_p_mem.2, c.a'_add_η₀_lt_f_p]⟩
    fun p' hp' hmem => absurd (c.f_mem_of_mem_smallBall hmem).1 (not_lt.2 h2.le)

/-- In the upper collar `b' - η₀ < f x ≤ b'`, the modified field descends at unit speed. -/
theorem dfV_V'_upper_collar {x : M} (h1 : b' - c.η₀ < f x) (h2 : f x ≤ b') :
    dfV I f k.V' x = -1 :=
  k.dfV_V'_eq_neg_one (k.notMem_K_of_lt_f h1)
    ⟨by linarith [c.η₀_pos, c.f_p_mem.1, c.a'_add_η₀_lt_f_p, c.hlt, c.hε, c.f_q_add_η₀_lt_b'], h2⟩
    fun p' hp' hmem => absurd (c.f_mem_of_mem_smallBall hmem).2 (not_lt.2 h1.le)

/-- Unit-speed descent of `Φ` while the trajectory stays in the lower collar. -/
theorem f_Φ_lower_collar {x : M} {t : ℝ} (ht : 0 ≤ t)
    (hstay : ∀ s ∈ Icc 0 t, a' ≤ f (k.Φ s x) ∧ f (k.Φ s x) < a' + c.η₀) :
    f (k.Φ t x) = f x - t := by
  have := f_eq_sub_of_integralCurve_on_set f c.hfs k.V' {y | a' ≤ f y ∧ f y < a' + c.η₀}
    (fun y hy => k.dfV_V'_lower_collar hy.1 hy.2) (k.isMIntegralCurve_Φ x) ht hstay
  simpa using this

/-- Unit-speed descent of `Φ` while the trajectory stays in the upper collar. -/
theorem f_Φ_upper_collar {x : M} {t : ℝ} (ht : 0 ≤ t)
    (hstay : ∀ s ∈ Icc 0 t, b' - c.η₀ < f (k.Φ s x) ∧ f (k.Φ s x) ≤ b') :
    f (k.Φ t x) = f x - t := by
  have := f_eq_sub_of_integralCurve_on_set f c.hfs k.V' {y | b' - c.η₀ < f y ∧ f y ≤ b'}
    (fun y hy => k.dfV_V'_upper_collar hy.1 hy.2) (k.isMIntegralCurve_Φ x) ht hstay
  simpa using this

/-- Below the strip, `Φ` is the original flow. -/
theorem Φ_eq_flow_of_f_lt {x : M} (hx : f x < a' + c.η₀) {t : ℝ} (ht : 0 ≤ t) :
    k.Φ t x = c.D.flow t x :=
  k.Φ_eq_flow_of_avoid (fun _ hs => k.notMem_K_of_f_lt
    (lt_of_le_of_lt (f_flow_le c.hfs x hs.1) hx)) t (right_mem_Icc.2 ht)

/-- Above the strip, `Φ` is the original flow (backwards). -/
theorem Φ_eq_flow_of_lt_f {x : M} (hx : b' - c.η₀ < f x) {t : ℝ} (ht : t ≤ 0) :
    k.Φ t x = c.D.flow t x :=
  k.Φ_eq_flow_of_avoid_neg (T := -t) (fun s hs => k.notMem_K_of_lt_f
    (lt_of_lt_of_le hx (le_f_flow_of_nonpos c.hfs x hs.2))) t ⟨by rw [neg_neg], ht⟩

/-! ### Chart ODEs -/

/-- The chart coordinates of a `Φ`-trajectory satisfy the ODE of the pulled-back field. -/
theorem hasDerivAt_symm_Φ_of_pullback {r : M} (d : MorseChartData I f r)
    {Y : (Fin n → ℝ) → Fin n → ℝ} {x : M} {s : ℝ} (hs : k.Φ s x ∈ d.χ '' Metric.ball 0 d.R')
    (hY : mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (k.Φ s x) (k.V' (k.Φ s x)) =
      Y (d.χ.symm (k.Φ s x))) :
    HasDerivAt (fun s => d.χ.symm (k.Φ s x)) (Y (d.χ.symm (k.Φ s x))) s := by
  have hγ := k.isMIntegralCurve_Φ x
  have hsymm : HasMFDerivAt I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (k.Φ s x)
      (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (k.Φ s x)) :=
    (d.mdifferentiableAt_symm hs).hasMFDerivAt
  have hcomp := HasMFDerivAt.comp s hsymm (hγ s)
  have hfd := hasMFDerivAt_iff_hasFDerivAt.1 hcomp
  rw [hasDerivAt_iff_hasFDerivAt]
  refine (hfd.congr_fderiv ?_)
  apply ContinuousLinearMap.ext
  intro r
  show (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (k.Φ s x)) ((id r : ℝ) • k.V' (k.Φ s x)) =
    (id r : ℝ) • Y (d.χ.symm (k.Φ s x))
  rw [map_smul, hY]
  rfl

open scoped Classical in
/-- The pulled-back modified field in the chart of `p`. -/
def Vp (y : Fin n → ℝ) : Fin n → ℝ :=
  ModelField.modelField 0 c.e.r₀ y + k.Yp' y +
    (if c.e.χ y ∈ c.TubeOpenσ then
      (2 * (k.βm (c.e.χ y) * c.ψm (c.e.χ y))) • (-ModelField.modelField 0 c.e.r₀ y) +
        (2 * (c.lam * (k.βm' (c.e.χ y) * c.ψm' (c.e.χ y)))) • c.Zp y
    else 0)

open scoped Classical in
/-- The pulled-back modified field in the chart of `q`. -/
def Vq (y : Fin n → ℝ) : Fin n → ℝ :=
  ModelField.modelField c.d.k c.d.r₀ y + k.Yq' y +
    (if c.d.χ y ∈ c.TubeOpenσ then
      (2 * (k.βm (c.d.χ y) * c.ψm (c.d.χ y))) • (-ModelField.modelField c.d.k c.d.r₀ y) +
        (2 * (c.lam * (k.βm' (c.d.χ y) * c.ψm' (c.d.χ y)))) • c.Zq y
    else 0)

theorem pullback_V'_p' {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ y) (k.V' (c.e.χ y)) : Fin n → ℝ) = k.Vp y := by
  classical
  rw [k.pullback_V'_p hy]; rfl

theorem pullback_V'_q' {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm (c.d.χ y) (k.V' (c.d.χ y)) : Fin n → ℝ) = k.Vq y := by
  classical
  rw [k.pullback_V'_q hy]; rfl

theorem symm_Φ_p_sq_lt {x : M} {s : ℝ} (hs : k.Φ s x ∈ c.pBall') :
    morseNorm n (c.e.χ.symm (k.Φ s x)) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, hyx⟩ := hs
  rw [← hyx, c.chart_p_symm_eq' hy]; exact hy

theorem symm_Φ_q_sq_lt {x : M} {s : ℝ} (hs : k.Φ s x ∈ c.qBall') :
    morseNorm n (c.d.χ.symm (k.Φ s x)) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, hyx⟩ := hs
  rw [← hyx, c.chart_q_symm_eq' hy]; exact hy

/-- **The chart ODE in the chart of `p`.** -/
theorem hasDerivAt_symm_Φ_p {x : M} {s : ℝ} (hs : k.Φ s x ∈ c.pBall') :
    HasDerivAt (fun s => c.e.χ.symm (k.Φ s x)) (k.Vp (c.e.χ.symm (k.Φ s x))) s := by
  refine k.hasDerivAt_symm_Φ_of_pullback c.e (c.pBall'_subset_image_ball hs) ?_
  have hy := k.symm_Φ_p_sq_lt hs
  have := k.pullback_V'_p' hy
  rwa [c.e.symm_image_eq (c.pBall'_subset_image_ball hs)] at this

/-- **The chart ODE in the chart of `q`.** -/
theorem hasDerivAt_symm_Φ_q {x : M} {s : ℝ} (hs : k.Φ s x ∈ c.qBall') :
    HasDerivAt (fun s => c.d.χ.symm (k.Φ s x)) (k.Vq (c.d.χ.symm (k.Φ s x))) s := by
  refine k.hasDerivAt_symm_Φ_of_pullback c.d (c.qBall'_subset_image_ball hs) ?_
  have hy := k.symm_Φ_q_sq_lt hs
  have := k.pullback_V'_q' hy
  rwa [c.d.symm_image_eq (c.qBall'_subset_image_ball hs)] at this

theorem hasDerivAt_symm_Φ_p_Icc {x : M} {t₀ t₁ : ℝ}
    (h : ∀ s ∈ Icc t₀ t₁, k.Φ s x ∈ c.pBall') :
    ∀ s ∈ Icc t₀ t₁, HasDerivAt (fun s => c.e.χ.symm (k.Φ s x)) (k.Vp (c.e.χ.symm (k.Φ s x))) s :=
  fun s hs => k.hasDerivAt_symm_Φ_p (h s hs)

theorem hasDerivAt_symm_Φ_q_Icc {x : M} {t₀ t₁ : ℝ}
    (h : ∀ s ∈ Icc t₀ t₁, k.Φ s x ∈ c.qBall') :
    ∀ s ∈ Icc t₀ t₁, HasDerivAt (fun s => c.d.χ.symm (k.Φ s x)) (k.Vq (c.d.χ.symm (k.Φ s x))) s :=
  fun s hs => k.hasDerivAt_symm_Φ_q (h s hs)

/-! ### The transverse coordinate along `Φ` -/

theorem hasDerivAt_ζ_Φ {x : M} {t : ℝ} (ht : k.Φ t x ∈ c.TubeOpen) :
    HasDerivAt (fun s => c.ζ (k.Φ s x)) (c.dζ k.V' (k.Φ t x)) t :=
  hasDerivAt_comp_integralCurve (k.isMIntegralCurve_Φ x) (c.mdifferentiableAt_ζ ht)

/-- `dζ` of the tube piece: `-(2 λ βm' ψm') • ζ` on the one-sided tube. -/
theorem dζ_Ym {x : M} (hx : x ∈ c.TubeOpenσ) :
    c.dζ k.Ym x = -(2 * (c.lam * (k.βm' x * c.ψm' x))) • c.ζ x := by
  have h : c.dζ k.Ym x = c.dζ k.YmFun x := by
    unfold dζ; rw [k.Ym_of_mem hx]
  rw [h]
  unfold YmFun dζ
  simp only [map_add, map_smul, map_neg]
  have h1 := c.dζ_V hx.1
  have h2 := c.dζ_Z hx.1
  rw [h1, h2]
  simp [neg_smul]

/-- On the one-sided tube where the pushers vanish, `dζ (V') = -(2 λ βm' ψm') • ζ`. -/
theorem dζ_V' {x : M} (hx : x ∈ c.TubeOpenσ) (hp : c.e.push k.Yp' x = 0)
    (hq : c.d.push k.Yq' x = 0) :
    c.dζ k.V' x = -(2 * (c.lam * (k.βm' x * c.ψm' x))) • c.ζ x := by
  have e : k.V' = fun x => (fun x => (fun x => c.D.V x + c.e.push k.Yp' x) x + c.d.push k.Yq' x) x
      + k.Ym x := rfl
  rw [e, c.dζ_add, c.dζ_add, c.dζ_add, c.dζ_V_eq_zero hx.1, k.dζ_Ym hx]
  have hp' : c.dζ (c.e.push k.Yp') x = 0 := by unfold dζ; rw [hp]; simp
  have hq' : c.dζ (c.d.push k.Yq') x = 0 := by unfold dζ; rw [hq]; simp
  rw [hp', hq']; simp

/-- `‖ζ‖²` along `Φ`: derivative `2 ⟪ζ, dζ (V')⟫`. -/
theorem hasDerivAt_normSq_ζ_Φ {x : M} {t : ℝ} (ht : k.Φ t x ∈ c.TubeOpen) :
    HasDerivAt (fun s => ‖c.ζ (k.Φ s x)‖ ^ 2)
      (2 * inner ℝ (c.ζ (k.Φ t x)) (c.dζ k.V' (k.Φ t x))) t := by
  have := (k.hasDerivAt_ζ_Φ ht).norm_sq
  convert this using 1

/-- Where the pushers vanish on the one-sided tube, `‖ζ‖²` is non-increasing along `Φ`. -/
theorem deriv_normSq_ζ_Φ_nonpos {x : M} {t : ℝ} (ht : k.Φ t x ∈ c.TubeOpenσ)
    (hp : c.e.push k.Yp' (k.Φ t x) = 0) (hq : c.d.push k.Yq' (k.Φ t x) = 0) :
    HasDerivAt (fun s => ‖c.ζ (k.Φ s x)‖ ^ 2)
      (-(4 * (c.lam * (k.βm' (k.Φ t x) * c.ψm' (k.Φ t x)))) * ‖c.ζ (k.Φ t x)‖ ^ 2) t := by
  have h := k.hasDerivAt_normSq_ζ_Φ ht.1
  rw [k.dζ_V' ht hp hq, inner_smul_right, real_inner_self_eq_norm_sq] at h
  convert h using 1; ring


/-! ### Dynamical tools: uniform times and Lyapunov exits -/

/-- **Uniform time by compactness**: if every point of a compact set `C` reaches an open set `O`
in nonnegative time, the times can be bounded uniformly. -/
theorem exists_uniform_time {C O : Set M} (hC : IsCompact C) (hO : IsOpen O)
    (h : ∀ x ∈ C, ∃ t, 0 ≤ t ∧ k.Φ t x ∈ O) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ x ∈ C, ∃ t ∈ Icc 0 T, k.Φ t x ∈ O := by
  set U : {t : ℝ // 0 ≤ t} → Set M := fun t => k.Φ t.1 ⁻¹' O with hU
  have hUo : ∀ t, IsOpen (U t) := fun t => hO.preimage (k.continuous_Φ t.1)
  have hcov : C ⊆ ⋃ t, U t := fun x hx => by
    obtain ⟨t, ht, hmem⟩ := h x hx
    exact mem_iUnion.2 ⟨⟨t, ht⟩, hmem⟩
  obtain ⟨sf, hsf⟩ := hC.elim_finite_subcover U hUo hcov
  classical
  refine ⟨∑ t ∈ sf, t.1, Finset.sum_nonneg fun t _ => t.2, fun x hx => ?_⟩
  obtain ⟨t, ht, hmem⟩ := mem_iUnion₂.1 (hsf hx)
  exact ⟨t.1, ⟨t.2, Finset.single_le_sum (f := fun t : {t : ℝ // 0 ≤ t} => t.1)
    (fun t _ => t.2) ht⟩, hmem⟩

/-- Time translation of a derivative along `Φ`. -/
theorem hasDerivAt_comp_Φ_shift {L : M → ℝ} {x : M} {t r : ℝ}
    (h : HasDerivAt (fun s => L (k.Φ s (k.Φ t x))) r 0) :
    HasDerivAt (fun s => L (k.Φ s x)) r t := by
  have h2 : HasDerivAt (fun s => L (k.Φ (t + s) x)) r 0 := by
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    show L (k.Φ (t + s) x) = L (k.Φ s (k.Φ t x))
    rw [k.Φ_Φ]
  have h2' : HasDerivAt (fun s => L (k.Φ (t + s) x)) r (t - t) := by rwa [sub_self]
  have h3 := h2'.comp_sub_const t t
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show L (k.Φ s x) = L (k.Φ (t + (s - t)) x)
  rw [add_sub_cancel]

/-- The flow `Φ` packaged as a `Flow`. -/
def toFlow : Flow ℝ M where
  toFun := k.Φ
  cont' := k.continuous_Φ_joint
  map_add' := fun t₁ t₂ x => by rw [add_comm, k.Φ_add]
  map_zero' := k.Φ_zero

theorem toFlow_apply (t : ℝ) (x : M) : k.toFlow t x = k.Φ t x := rfl

theorem tendsto_add_atTop (t : ℝ) : Tendsto (t + ·) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b - t, fun s hs => by linarith⟩

/-- **The ω-limit set of a trajectory confined to a compact set, under a weak Lyapunov
function**: if `L₁` is continuous on the compact set `C`, non-increasing along `Φ` on `C` and
strictly decreasing off `Z`, then a trajectory staying in `C` forever has a nonempty compact
invariant ω-limit set contained in `C ∩ Z`. -/
theorem exists_omegaLimit_subset {C : Set M} (hC : IsCompact C) {L₁ : M → ℝ}
    (hL₁ : ContinuousOn L₁ C) {Z : Set M}
    (hd₁ : ∀ x ∈ C, ∃ r : ℝ, r ≤ 0 ∧ HasDerivAt (fun s => L₁ (k.Φ s x)) r 0 ∧ (r = 0 → x ∈ Z))
    {x : M} (hcon : ∀ t, 0 ≤ t → k.Φ t x ∈ C) :
    ∃ Ω : Set M, Ω.Nonempty ∧ IsCompact Ω ∧ Ω ⊆ C ∩ Z ∧ ∀ t, MapsTo (k.Φ t) Ω Ω := by
  set g : ℝ → ℝ := fun t => L₁ (k.Φ t x) with hg
  -- the derivative at every nonnegative time
  have hder : ∀ t, 0 ≤ t → ∃ r : ℝ, r ≤ 0 ∧ HasDerivAt g r t := by
    intro t ht
    obtain ⟨r, hr, hd', -⟩ := hd₁ _ (hcon t ht)
    exact ⟨r, hr, k.hasDerivAt_comp_Φ_shift hd'⟩
  -- `g` is antitone on `Ici 0`
  have hanti : AntitoneOn g (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · intro t ht
      obtain ⟨r, -, h⟩ := hder t ht
      exact h.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      obtain ⟨r, -, h⟩ := hder t ht.le
      exact h.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      obtain ⟨r, hr, h⟩ := hder t ht.le
      rw [h.deriv]; exact hr
  -- `L₁` is bounded on `C`
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hL₁
  set G : ℝ → ℝ := fun t => g (max t 0) with hG
  have hGanti : Antitone G := fun a b hab =>
    hanti (by simp) (by simp) (max_le_max hab le_rfl)
  have hGbdd : BddBelow (range G) := ⟨-B, by
    rintro _ ⟨m, rfl⟩
    have h1 := hB _ (hcon (max m 0) (le_max_right _ _))
    rw [Real.norm_eq_abs] at h1
    have := neg_abs_le (L₁ (k.Φ (max m 0) x))
    show -B ≤ L₁ (k.Φ (max m 0) x)
    linarith⟩
  set ℓ := ⨅ m, G m with hℓ
  have hGℓ : Tendsto G atTop (𝓝 ℓ) := tendsto_atTop_ciInf hGanti hGbdd
  have hGle : ∀ m, ℓ ≤ G m := fun m => ciInf_le hGbdd m
  have hGeq : ∀ t, 0 ≤ t → G t = L₁ (k.Φ t x) := fun t ht => by
    simp only [hG, hg, max_eq_left ht]
  -- the ω-limit set
  set Ω := omegaLimit atTop (⇑k.toFlow) {x} with hΩ
  have himage : closure (image2 (⇑k.toFlow) (Ici 0) {x}) ⊆ C := by
    refine closure_minimal ?_ hC.isClosed
    rintro _ ⟨t, ht, y, hy, rfl⟩
    rw [mem_singleton_iff] at hy
    subst hy
    exact hcon t ht
  have hΩC : Ω ⊆ C :=
    (omegaLimit_subset_closure_image2 atTop (⇑k.toFlow) {x} (Ici_mem_atTop (0 : ℝ))).trans
      himage
  have hΩne : Ω.Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop (⇑k.toFlow) {x} hC
      ⟨Ici 0, Ici_mem_atTop 0, himage⟩ (singleton_nonempty x)
  have hΩc : IsCompact Ω := hC.of_isClosed_subset (isClosed_omegaLimit _ _ _) hΩC
  have hinv : ∀ t, MapsTo (k.Φ t) Ω Ω :=
    Flow.isInvariant_omegaLimit atTop k.toFlow {x} fun t => tendsto_add_atTop t
  -- the filter of the forward trajectory
  set u : ℝ → M := fun t => k.Φ t x with hu
  set F : Filter M := map u atTop with hF
  have hFC : F ≤ 𝓟 C := by
    rw [hF, le_principal_iff, mem_map]
    exact eventually_atTop.2 ⟨0, fun t ht => hcon t ht⟩
  -- the ω-limit set lies in `Z`
  have hΩZ : ∀ z ∈ Ω, z ∈ Z := by
    intro z hz
    have hzC : z ∈ C := hΩC hz
    obtain ⟨r, hr0, hdz, hrZ⟩ := hd₁ z hzC
    by_contra hzZ
    have hrneg : r < 0 := lt_of_le_of_ne hr0 fun h => hzZ (hrZ h)
    have hzF : ClusterPt z F :=
      ((mem_omegaLimit_singleton_iff_mapClusterPt atTop (⇑k.toFlow) x z).1 hz).clusterPt
    -- `L₁ z = ℓ`
    have hLz : L₁ z = ℓ := by
      by_contra hne
      set ε := |L₁ z - ℓ| / 2 with hε
      have hε0 : 0 < ε := by
        have : 0 < |L₁ z - ℓ| := abs_pos.2 (sub_ne_zero.2 hne)
        positivity
      have h1 : ∀ᶠ y in 𝓝[C] z, |L₁ y - L₁ z| < ε :=
        (hL₁ z hzC).tendsto (Metric.ball_mem_nhds (L₁ z) hε0)
      have h2 : ∀ᶠ y in F, |L₁ y - ℓ| < ε := by
        rw [hF, eventually_map]
        filter_upwards [hGℓ (Metric.ball_mem_nhds ℓ hε0), eventually_ge_atTop 0] with t ht ht0
        rw [← hGeq t ht0]; exact ht
      obtain ⟨y, hy1, hy2⟩ :=
        ((frequently_of_clusterPt_within hzF hFC h1).and_eventually h2).exists
      have := abs_sub_le (L₁ z) (L₁ y) ℓ
      rw [abs_sub_comm (L₁ z) (L₁ y)] at this
      linarith
    obtain ⟨t₀, ht₀, hlt⟩ := exists_pos_gt_of_hasDerivAt_neg hrneg hdz
    rw [k.Φ_zero, hLz] at hlt
    set F' : Filter M := map (k.Φ t₀) F with hF'
    have hF'C : F' ≤ 𝓟 C := by
      rw [hF', hF, map_map, le_principal_iff, mem_map]
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      show k.Φ t₀ (k.Φ t x) ∈ C
      rw [k.Φ_Φ]; exact hcon _ (by positivity)
    have hzF' : ClusterPt (k.Φ t₀ z) F' :=
      hzF.map (k.continuous_Φ t₀).continuousAt tendsto_map
    have hzC' : k.Φ t₀ z ∈ C := by
      rw [← hC.isClosed.closure_eq, mem_closure_iff_clusterPt]
      exact hzF'.mono hF'C
    have h1 : ∀ᶠ y in 𝓝[C] (k.Φ t₀ z), L₁ y < ℓ := (hL₁ _ hzC').tendsto (Iio_mem_nhds hlt)
    have h2 : ∀ᶠ y in F', ℓ ≤ L₁ y := by
      rw [hF', hF, map_map, eventually_map]
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      show ℓ ≤ L₁ (k.Φ t₀ (k.Φ t x))
      rw [k.Φ_Φ, ← hGeq _ (by positivity)]
      exact hGle _
    obtain ⟨y, hy1, hy2⟩ :=
      ((frequently_of_clusterPt_within hzF' hF'C h1).and_eventually h2).exists
    linarith
  exact ⟨Ω, hΩne, hΩc, fun z hz => ⟨hΩC hz, hΩZ z hz⟩, hinv⟩

/-- **Lyapunov exit (LaSalle), two-stage version**: `L₁` is non-increasing along `Φ` on the
compact set `C`, strictly decreasing off `Z`, and `L₂` strictly increases along `Φ` on `C ∩ Z`;
then every trajectory leaves `C`. -/
theorem exists_exit_of_lyapunov_pair {C : Set M} (hC : IsCompact C) {L₁ L₂ : M → ℝ}
    (hL₁ : ContinuousOn L₁ C) (hL₂ : ContinuousOn L₂ C) {Z : Set M}
    (hd₁ : ∀ x ∈ C, ∃ r : ℝ, r ≤ 0 ∧ HasDerivAt (fun s => L₁ (k.Φ s x)) r 0 ∧ (r = 0 → x ∈ Z))
    (hd₂ : ∀ x ∈ C ∩ Z, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => L₂ (k.Φ s x)) r 0) :
    ∀ x ∈ C, ∃ t, 0 ≤ t ∧ k.Φ t x ∉ C := by
  intro x _
  by_contra hcon
  push Not at hcon
  obtain ⟨Ω, hΩne, hΩc, hΩCZ, hinv⟩ := k.exists_omegaLimit_subset hC hL₁ hd₁ hcon
  obtain ⟨w, hwΩ, hwmax⟩ := hΩc.exists_isMaxOn hΩne (hL₂.mono fun z hz => (hΩCZ hz).1)
  obtain ⟨r, hr, hdw⟩ := hd₂ w (hΩCZ hwΩ)
  obtain ⟨t₀, -, hgt⟩ := exists_pos_lt_of_hasDerivAt_pos hr hdw
  have h1 : L₂ (k.Φ 0 w) < L₂ (k.Φ t₀ w) := hgt
  rw [k.Φ_zero] at h1
  have h2 : L₂ (k.Φ t₀ w) ≤ L₂ w := hwmax (hinv t₀ hwΩ)
  linarith

/-- **Lyapunov exit (LaSalle), weak version**: `L₁` is non-increasing along `Φ` on the compact
set `C`, strictly decreasing off `Z`, and no point of `C ∩ Z` stays in `C ∩ Z` for all times;
then every trajectory leaves `C`. -/
theorem exists_exit_of_lyapunov_weak {C : Set M} (hC : IsCompact C) {L₁ : M → ℝ}
    (hL₁ : ContinuousOn L₁ C) {Z : Set M}
    (hd₁ : ∀ x ∈ C, ∃ r : ℝ, r ≤ 0 ∧ HasDerivAt (fun s => L₁ (k.Φ s x)) r 0 ∧ (r = 0 → x ∈ Z))
    (hZ : ∀ z ∈ C ∩ Z, ∃ t : ℝ, k.Φ t z ∉ C ∩ Z) :
    ∀ x ∈ C, ∃ t, 0 ≤ t ∧ k.Φ t x ∉ C := by
  intro x _
  by_contra hcon
  push Not at hcon
  obtain ⟨Ω, ⟨w, hwΩ⟩, -, hΩCZ, hinv⟩ := k.exists_omegaLimit_subset hC hL₁ hd₁ hcon
  obtain ⟨t, ht⟩ := hZ w (hΩCZ hwΩ)
  exact ht (hΩCZ (hinv t hwΩ))

/-- A trajectory starting in a closed set `A` and reaching a closed set `B` disjoint from `A`
leaves `A ∪ B` in between. -/
theorem exists_notMem_union_of_disjoint_closed {A B : Set M} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) {z : M} (hz : z ∈ A) {t : ℝ} (ht : 0 ≤ t) (htB : k.Φ t z ∈ B) :
    ∃ s ∈ Icc 0 t, k.Φ s z ∉ A ∪ B := by
  by_contra hcon
  push Not at hcon
  have hpre : IsPreconnected (Icc (0 : ℝ) t) := isPreconnected_Icc
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hpre
  have h1 : IsClosed ((fun s => k.Φ s z) ⁻¹' A) := hA.preimage (k.continuous_Φ_curve z)
  have h2 : IsClosed ((fun s => k.Φ s z) ⁻¹' B) := hB.preimage (k.continuous_Φ_curve z)
  have h3 : Icc (0 : ℝ) t ⊆ (fun s => k.Φ s z) ⁻¹' A ∪ (fun s => k.Φ s z) ⁻¹' B :=
    fun s hs => hcon s hs
  have h4 : Icc (0 : ℝ) t ∩ ((fun s => k.Φ s z) ⁻¹' A ∩ (fun s => k.Φ s z) ⁻¹' B) = ∅ := by
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
    intro _ hsA hsB
    exact hAB.notMem_of_mem_left hsA hsB
  rcases hpre _ _ h1 h2 h3 h4 with h | h
  · have := h (right_mem_Icc.2 ht)
    exact hAB.notMem_of_mem_left this htB
  · have := h (left_mem_Icc.2 ht)
    rw [mem_preimage, k.Φ_zero] at this
    exact hAB.notMem_of_mem_left hz this

/-- **Lyapunov exit (LaSalle)**: if `L` is continuous on the compact set `C` and strictly
increases (positive derivative) along `Φ` at every point of `C`, every trajectory leaves `C`. -/
theorem exists_exit_of_deriv_pos {C : Set M} (hC : IsCompact C) {L : M → ℝ}
    (hL : ContinuousOn L C)
    (hd : ∀ x ∈ C, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => L (k.Φ s x)) r 0) :
    ∀ x ∈ C, ∃ t, 0 ≤ t ∧ k.Φ t x ∉ C :=
  k.exists_exit_of_lyapunov_pair hC (L₁ := fun y => -L y) (L₂ := L) hL.neg hL (Z := ∅)
    (fun x hx => by
      obtain ⟨r, hr, hd'⟩ := hd x hx
      exact ⟨-r, by linarith, hd'.neg, fun h => absurd h (by linarith)⟩)
    (fun x hx => absurd hx.2 (notMem_empty x))

/-- Exit from `C ∩ Z` for the weak Lyapunov argument, when `C ∩ Z` splits into two disjoint
compact pieces on each of which some continuous function strictly increases along `Φ`. -/
theorem exists_notMem_of_two_pieces {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) {LA LB : M → ℝ} (hLA : ContinuousOn LA A) (hLB : ContinuousOn LB B)
    (hdA : ∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => LA (k.Φ s x)) r 0)
    (hdB : ∀ x ∈ B, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => LB (k.Φ s x)) r 0) :
    ∀ z ∈ A ∪ B, ∃ t : ℝ, k.Φ t z ∉ A ∪ B := by
  rintro z (hz | hz)
  · obtain ⟨t, ht, htA⟩ := k.exists_exit_of_deriv_pos hA hLA hdA z hz
    by_cases htB : k.Φ t z ∈ B
    · obtain ⟨s, -, hs⟩ := k.exists_notMem_union_of_disjoint_closed hA.isClosed hB.isClosed hAB
        hz ht htB
      exact ⟨s, hs⟩
    · exact ⟨t, fun h => h.elim htA htB⟩
  · obtain ⟨t, ht, htB⟩ := k.exists_exit_of_deriv_pos hB hLB hdB z hz
    by_cases htA : k.Φ t z ∈ A
    · obtain ⟨s, -, hs⟩ := k.exists_notMem_union_of_disjoint_closed hB.isClosed hA.isClosed
        hAB.symm hz ht htA
      exact ⟨s, fun h => hs (h.symm)⟩
    · exact ⟨t, fun h => h.elim htA htB⟩

/-- **Uniform Lyapunov exit.** -/
theorem exists_uniform_exit_of_deriv_pos {C : Set M} (hC : IsCompact C) {L : M → ℝ}
    (hL : ContinuousOn L C)
    (hd : ∀ x ∈ C, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => L (k.Φ s x)) r 0) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ x ∈ C, ∃ t ∈ Icc 0 T, k.Φ t x ∉ C :=
  k.exists_uniform_time hC hC.isClosed.isOpen_compl (k.exists_exit_of_deriv_pos hC hL hd)

/-- First time a closed set is hit along `Φ`. -/
theorem exists_first_hit {C : Set M} (hC : IsClosed C) {x : M} {t : ℝ} (ht : 0 ≤ t)
    (hhit : k.Φ t x ∈ C) :
    ∃ t₁ ∈ Icc 0 t, k.Φ t₁ x ∈ C ∧ ∀ s ∈ Ico 0 t₁, k.Φ s x ∉ C := by
  obtain ⟨s₀, hs₀, hs₀K, hmin⟩ := exists_first_time hC (k.continuous_Φ_curve x)
    (t := t) ⟨t, ⟨ht, le_rfl⟩, hhit⟩
  exact ⟨s₀, hs₀, hs₀K, hmin⟩


/-! ### The support set `Sσ` and the pushers at the tube levels -/

/-- `Sσ` in terms of the tube, the levels and the transverse coordinate. -/
theorem mem_Sσ_iff {x : M} : x ∈ k.Sσ ↔ x ∈ c.TubeOpenσ ∧
    f x ∈ Icc (c.c₁ - c.η / 2) (c.c₂ + c.η / 2) ∧ ‖c.ζ x‖ ≤ k.δ' := by
  constructor
  · intro hx
    have hT := k.Sσ_subset_TubeOpenσ hx
    refine ⟨hT, hx.1, ?_⟩
    obtain ⟨y, hy, hyx⟩ := hx.2
    have hw : c.w x = y := by
      unfold w
      rw [← hyx, c.d.χ.left_inv (c.d.hsrc y ((k.morseNorm_lt_rm_of_mem_Sq hy).le.trans
        (c.D.hrm q c.hq).2))]
    have h1 : morseNorm n y ^ 2 ≤ 2 * k.δ' ^ 2 + 2 * c.ε₂ := hy.1
    rw [morseNorm_sq_eq_negPart_add_posPart c.d.hk, ← hw, c.normSq_negPart_w hT.1,
      ← c.ζ_def] at h1
    have h2 : ‖c.ζ x‖ ^ 2 ≤ k.δ' ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.δ'_pos.le two_ne_zero).1 h2
  · rintro ⟨hT, hf, hζ⟩
    refine ⟨hf, ?_⟩
    show c.D.π c.c₂ x ∈ c.d.χ '' k.Sq
    refine ⟨c.w x, ⟨?_, hT.2.le⟩, c.chart_w hT.1⟩
    have h := c.normSq_negPart_w hT.1
    rw [morseNorm_sq_eq_negPart_add_posPart c.d.hk, h, ← c.ζ_def]
    have := pow_le_pow_left₀ (norm_nonneg _) hζ 2
    linarith

theorem mem_TubeOpenσ_of_mem_Sσ {x : M} (hx : x ∈ k.Sσ) : x ∈ c.TubeOpenσ :=
  k.Sσ_subset_TubeOpenσ hx

theorem norm_ζ_le_of_mem_Sσ {x : M} (hx : x ∈ k.Sσ) : ‖c.ζ x‖ ≤ k.δ' :=
  (k.mem_Sσ_iff.1 hx).2.2

theorem continuousOn_ζ_Sσ : ContinuousOn c.ζ k.Sσ :=
  c.continuousOn_ζ.mono fun _ hx => (k.mem_TubeOpenσ_of_mem_Sσ hx).1

/-- The pusher at `p` vanishes at the levels `≥ lo₂`. -/
theorem push_Yp'_eq_zero_of_lo₂_le {x : M} (hx : c.lo₂ ≤ f x) : c.e.push k.Yp' x = 0 := by
  by_cases hK : x ∈ c.e.χ '' Kp k.δ k.τ c.e₁ c.ρB
  · obtain ⟨y, hy, rfl⟩ := hK
    have hyR : morseNorm n y ≤ c.e.R := hy.1.trans c.ρB_le_R
    rw [MorseChartData.push_apply_chart _ (c.e.mem_ball_of_le hyR)]
    have hf := c.f_chart_p hyR
    have hρ : c.ρB ≤ morseNorm n y := by
      have h := c.ρB_sq_eq
      have : c.ρB ^ 2 ≤ morseNorm n y ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ c.ρB_pos.le (ModelField.morseNorm_nonneg y) two_ne_zero).1 this
    have : k.Yp' y = 0 := by
      show Yp c.m' k.δ k.τ c.ρA c.ρB c.e₁ y = 0
      rw [Yp, ψp_eq_zero c.ρA_pos.le c.ρA_lt_ρB hρ, mul_zero, mul_zero, zero_smul]
    rw [this]
    exact (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.e.χ y).map_zero
  · exact k.push_Yp'_eq_zero_of_notMem hK

/-- The pusher at `q` vanishes at the levels `≤ hi₁`. -/
theorem push_Yq'_eq_zero_of_le_hi₁ {x : M} (hx : f x ≤ c.hi₁) : c.d.push k.Yq' x = 0 := by
  by_cases hK : x ∈ c.d.χ '' Kq c.d.hk c.hkq k.δ k.τ c.σ c.uB
  · obtain ⟨y, hy, rfl⟩ := hK
    have hyR : morseNorm n y ≤ c.d.R := by
      have := (morseNorm_sq_le_of_mem_Kq c.d.hk c.hkq hy).trans k.Kq_radius_lt.le
      exact ((Real.le_sqrt (ModelField.morseNorm_nonneg y) (by linarith [c.hε])).2 this).trans
        (by linarith [c.sqrt_three_ε_lt_rmq, (c.D.hrm q c.hq).2])
    rw [MorseChartData.push_apply_chart _ (c.d.mem_ball_of_le hyR)]
    have hf := c.f_chart_q hyR
    have hu : c.uB ^ 2 ≤ uq c.d.hk c.hkq y ^ 2 := by
      have h := c.uB_sq_eq
      nlinarith [sq_nonneg ‖posPart c.d.hk y‖]
    have : k.Yq' y = 0 := by
      show Yq c.d.hk c.hkq k.δ k.τ c.σ c.m' c.uA c.uB y = 0
      rw [Yq, ψq_eq_zero c.d.hk c.hkq c.uA_pos.le c.uA_lt_uB hu, mul_zero, mul_zero, neg_zero,
        zero_smul]
    rw [this]
    exact (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.d.χ y).map_zero
  · exact k.push_Yq'_eq_zero_of_notMem hK

/-! ### `f` and `ζ` along `Φ` on the tube where the pushers vanish -/

theorem dfV_Ym {x : M} (hx : x ∈ c.TubeOpenσ) :
    dfV I f k.Ym x = 2 * (k.βm x * c.ψm x) := by
  have h : dfV I f k.Ym x = dfV I f k.YmFun x := by unfold dfV; rw [k.Ym_of_mem hx]
  rw [h]
  unfold YmFun dfV
  simp only [map_add, map_smul, map_neg]
  have h1 := c.dfV_V_eq_neg_one_of_mem_tube hx.1.1
  have h2 := c.df_Z hx.1
  unfold dfV at h1 h2
  rw [h1, h2]
  simp

/-- On the one-sided tube where the pushers vanish, `df (V') = -1 + 2 βm ψm`. -/
theorem dfV_V'_tube {x : M} (hx : x ∈ c.TubeOpenσ) (hp : c.e.push k.Yp' x = 0)
    (hq : c.d.push k.Yq' x = 0) : dfV I f k.V' x = -1 + 2 * (k.βm x * c.ψm x) := by
  have e : k.V' = fun x => (fun x => (fun x => c.D.V x + c.e.push k.Yp' x) x + c.d.push k.Yq' x) x
      + k.Ym x := rfl
  rw [e, dfV_add, dfV_add, dfV_add, c.dfV_V_eq_neg_one_of_mem_tube hx.1.1, k.dfV_Ym hx]
  have hp' : dfV I f (c.e.push k.Yp') x = 0 := by unfold dfV; rw [hp]; simp
  have hq' : dfV I f (c.d.push k.Yq') x = 0 := by unfold dfV; rw [hq]; simp
  rw [hp', hq']; ring

/-- In the middle levels `[lo₂, hi₁]` both pushers vanish, `ψm = 1` and `ψm' = 1`. -/
theorem dfV_V'_mid {x : M} (hx : x ∈ c.TubeOpenσ) (h1 : c.lo₂ ≤ f x) (h2 : f x ≤ c.hi₁) :
    dfV I f k.V' x = -1 + 2 * k.βm x := by
  rw [k.dfV_V'_tube hx (k.push_Yp'_eq_zero_of_lo₂_le h1) (k.push_Yq'_eq_zero_of_le_hi₁ h2),
    c.ψm_eq_one h1 h2, mul_one]

theorem dζ_V'_mid {x : M} (hx : x ∈ c.TubeOpenσ) (h1 : c.lo₂ ≤ f x) (h2 : f x ≤ c.hi₁) :
    c.dζ k.V' x = -(2 * (c.lam * k.βm' x)) • c.ζ x := by
  rw [k.dζ_V' hx (k.push_Yp'_eq_zero_of_lo₂_le h1) (k.push_Yq'_eq_zero_of_le_hi₁ h2),
    c.ψm'_eq_one (c.lo₁_lt_lo₂.le.trans h1) (h2.trans c.hi₁_lt_hi₂.le), mul_one]

/-- Derivative of `‖ζ‖²` along `Φ` at time `0` in the middle levels. -/
theorem hasDerivAt_normSq_ζ_Φ_mid {x : M} (hx : x ∈ c.TubeOpenσ) (h1 : c.lo₂ ≤ f x)
    (h2 : f x ≤ c.hi₁) :
    HasDerivAt (fun s => ‖c.ζ (k.Φ s x)‖ ^ 2) (-(4 * (c.lam * k.βm' x)) * ‖c.ζ x‖ ^ 2) 0 := by
  have h := k.hasDerivAt_normSq_ζ_Φ (t := 0) (by rw [k.Φ_zero]; exact hx.1)
  rw [k.Φ_zero, k.dζ_V'_mid hx h1 h2, inner_smul_right, real_inner_self_eq_norm_sq] at h
  convert h using 1; ring

/-- Derivative of `f` along `Φ` at time `0` in the middle levels. -/
theorem hasDerivAt_f_Φ_mid {x : M} (hx : x ∈ c.TubeOpenσ) (h1 : c.lo₂ ≤ f x)
    (h2 : f x ≤ c.hi₁) : HasDerivAt (fun s => f (k.Φ s x)) (-1 + 2 * k.βm x) 0 := by
  have h := k.hasDerivAt_f_Φ x 0
  rwa [k.Φ_zero, k.dfV_V'_mid hx h1 h2] at h


/-! ### The middle band of the tube: ascent through the core -/

/-- The compact middle band `Sσ ∩ {lo₂ ≤ f ≤ hi₁}`. -/
def Tmid : Set M := k.Sσ ∩ {y | c.lo₂ ≤ f y ∧ f y ≤ c.hi₁}

theorem isCompact_Tmid : IsCompact k.Tmid :=
  k.isCompact_Sσ.inter_right c.isClosed_mid_levels

theorem Tmid_subset_TubeOpenσ : k.Tmid ⊆ c.TubeOpenσ := fun _ hx =>
  k.mem_TubeOpenσ_of_mem_Sσ hx.1

theorem continuousOn_ζ_Tmid : ContinuousOn c.ζ k.Tmid :=
  k.continuousOn_ζ_Sσ.mono inter_subset_left

/-- **Every trajectory leaves the middle band** (LaSalle with `‖ζ‖²` and `±f`). -/
theorem exists_exit_Tmid : ∀ x ∈ k.Tmid, ∃ t, 0 ≤ t ∧ k.Φ t x ∉ k.Tmid := by
  have hlam := c.lam_pos
  set A : Set M := k.Tmid ∩ c.ζ ⁻¹' {0} with hA
  set B : Set M := k.Tmid ∩ c.ζ ⁻¹' {v | k.δ' ≤ ‖v‖} with hB
  have hAc : IsCompact A := k.isCompact_Tmid.of_isClosed_subset
    (k.continuousOn_ζ_Tmid.preimage_isClosed_of_isClosed k.isCompact_Tmid.isClosed
      isClosed_singleton) inter_subset_left
  have hBc : IsCompact B := k.isCompact_Tmid.of_isClosed_subset
    (k.continuousOn_ζ_Tmid.preimage_isClosed_of_isClosed k.isCompact_Tmid.isClosed
      (isClosed_le continuous_const continuous_norm)) inter_subset_left
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro y ⟨-, hy1⟩ ⟨-, hy2⟩
    have h1 : c.ζ y = 0 := hy1
    have h2 : k.δ' ≤ ‖c.ζ y‖ := hy2
    rw [h1, norm_zero] at h2
    linarith [k.δ'_pos]
  refine k.exists_exit_of_lyapunov_weak k.isCompact_Tmid (L₁ := fun y => ‖c.ζ y‖ ^ 2)
    (k.continuousOn_ζ_Tmid.norm.pow 2) (Z := {y | c.ζ y = 0 ∨ k.δ' ≤ ‖c.ζ y‖}) ?_ ?_
  · intro y hy
    have hT := k.Tmid_subset_TubeOpenσ hy
    refine ⟨-(4 * (c.lam * k.βm' y)) * ‖c.ζ y‖ ^ 2, ?_, k.hasDerivAt_normSq_ζ_Φ_mid hT hy.2.1 hy.2.2,
      ?_⟩
    · have := k.βm'_nonneg y
      have : 0 ≤ 4 * (c.lam * k.βm' y) * ‖c.ζ y‖ ^ 2 := by positivity
      linarith
    · intro h0
      rcases mul_eq_zero.1 h0 with h | h
      · right
        have hβ : k.βm' y = 0 := by
          rcases mul_eq_zero.1 (neg_eq_zero.1 h) with h' | h'
          · norm_num at h'
          · rcases mul_eq_zero.1 h' with h'' | h''
            · exact absurd h'' hlam.ne'
            · exact h''
        have := (cut_eq_zero_iff k.two_δ_sq_lt_δ'_sq).1 hβ
        exact (pow_le_pow_iff_left₀ k.δ'_pos.le (norm_nonneg _) two_ne_zero).1 this
      · left
        exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  · have hTZ : k.Tmid ∩ {y | c.ζ y = 0 ∨ k.δ' ≤ ‖c.ζ y‖} = A ∪ B := by
      ext y
      simp only [hA, hB, mem_inter_iff, mem_union, mem_ofPred_eq, mem_preimage,
        mem_singleton_iff]
      tauto
    rw [hTZ]
    refine k.exists_notMem_of_two_pieces hAc hBc hAB (LA := f) (LB := fun y => -f y)
      (c.hfs.continuous.continuousOn) (c.hfs.continuous.neg.continuousOn) ?_ ?_
    · rintro y ⟨hy, hζ⟩
      have hζ' : c.ζ y = 0 := hζ
      have hT := k.Tmid_subset_TubeOpenσ hy
      refine ⟨-1 + 2 * k.βm y, ?_, k.hasDerivAt_f_Φ_mid hT hy.2.1 hy.2.2⟩
      rw [k.βm_eq_one_of_ζ_eq_zero hζ']; norm_num
    · rintro y ⟨hy, hζ⟩
      have hζ' : k.δ' ≤ ‖c.ζ y‖ := hζ
      have hT := k.Tmid_subset_TubeOpenσ hy
      have hβ : k.βm y = 0 := by
        by_contra h
        have := k.norm_ζ_lt_of_βm_ne_zero h
        linarith [k.hδδ']
      refine ⟨-(-1 + 2 * k.βm y), ?_, (k.hasDerivAt_f_Φ_mid hT hy.2.1 hy.2.2).neg⟩
      rw [hβ]; norm_num

/-- The derivative of `‖ζ‖²` along `Φ` at any time `u` with `Φ u x` in the middle band. -/
theorem hasDerivAt_normSq_ζ_Φ_mid' {x : M} {u : ℝ} (hu : k.Φ u x ∈ c.TubeOpenσ)
    (h1 : c.lo₂ ≤ f (k.Φ u x)) (h2 : f (k.Φ u x) ≤ c.hi₁) :
    HasDerivAt (fun s => ‖c.ζ (k.Φ s x)‖ ^ 2)
      (-(4 * (c.lam * k.βm' (k.Φ u x))) * ‖c.ζ (k.Φ u x)‖ ^ 2) u :=
  k.hasDerivAt_comp_Φ_shift (L := fun y => ‖c.ζ y‖ ^ 2) (k.hasDerivAt_normSq_ζ_Φ_mid hu h1 h2)

theorem hasDerivAt_f_Φ_mid' {x : M} {u : ℝ} (hu : k.Φ u x ∈ c.TubeOpenσ)
    (h1 : c.lo₂ ≤ f (k.Φ u x)) (h2 : f (k.Φ u x) ≤ c.hi₁) :
    HasDerivAt (fun s => f (k.Φ s x)) (-1 + 2 * k.βm (k.Φ u x)) u :=
  k.hasDerivAt_comp_Φ_shift (L := f) (k.hasDerivAt_f_Φ_mid hu h1 h2)

/-- **Invariance of the middle band until the end levels are hit.** -/
theorem Φ_mem_Tmid_of_notMem_Emid {x : M} (hx : x ∈ k.Tmid) {t : ℝ}
    (hE : ∀ s ∈ Icc 0 t, k.Φ s x ∉ c.Emid) : ∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Tmid := by
  have hQ : IsClosed {s : ℝ | k.Φ s x ∈ k.Tmid} :=
    k.isCompact_Tmid.isClosed.preimage (k.continuous_Φ_curve x)
  refine Icc_subset_of_isClosed_of_step hQ (by simp [hx]) fun s hs hIcc => ?_
  have hsT : k.Φ s x ∈ k.Tmid := hIcc (right_mem_Icc.2 hs.1)
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open c.isOpen_TubeOpenσ
    (k.Tmid_subset_TubeOpenσ hsT)
  refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (s + ε) t, lt_min (by linarith) hs.2,
    fun s' hs' => ?_⟩
  have hs'ε : s' ≤ s + ε := hs'.2.trans (min_le_left _ _)
  have hs't : s' ≤ t := hs'.2.trans (min_le_right _ _)
  have hs'0 : 0 ≤ s' := hs.1.trans hs'.1.le
  -- every intermediate time is in the open tube with levels in `(lo₂, hi₁)`
  have hmid : ∀ u ∈ Icc s s', k.Φ u x ∈ c.TubeOpenσ ∧
      c.lo₂ ≤ f (k.Φ u x) ∧ f (k.Φ u x) ≤ c.hi₁ := by
    intro u hu
    have hu' := c.lt_of_notMem_Emid (hE u ⟨hs.1.trans hu.1, hu.2.trans hs't⟩)
    exact ⟨hεO u ⟨by linarith [hu.1], hu.2.trans hs'ε⟩, hu'.1.le, hu'.2.le⟩
  -- `‖ζ‖²` is antitone on `[s, s']`
  have hanti : AntitoneOn (fun u => ‖c.ζ (k.Φ u x)‖ ^ 2) (Icc s s') := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s s') ?_ ?_ ?_
    · intro u hu
      exact (k.hasDerivAt_normSq_ζ_Φ_mid' (hmid u hu).1 (hmid u hu).2.1
        (hmid u hu).2.2).continuousAt.continuousWithinAt
    · intro u hu
      have hu' := interior_subset hu
      exact (k.hasDerivAt_normSq_ζ_Φ_mid' (hmid u hu').1 (hmid u hu').2.1
        (hmid u hu').2.2).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' := interior_subset hu
      rw [(k.hasDerivAt_normSq_ζ_Φ_mid' (hmid u hu').1 (hmid u hu').2.1 (hmid u hu').2.2).deriv]
      have := k.βm'_nonneg (k.Φ u x)
      have := c.lam_pos
      have : 0 ≤ 4 * (c.lam * k.βm' (k.Φ u x)) * ‖c.ζ (k.Φ u x)‖ ^ 2 := by positivity
      linarith
  have hζ := hanti (left_mem_Icc.2 hs'.1.le) (right_mem_Icc.2 hs'.1.le) hs'.1.le
  have hζs := k.norm_ζ_le_of_mem_Sσ hsT.1
  have hζ' : ‖c.ζ (k.Φ s' x)‖ ≤ k.δ' := by
    have h1 : ‖c.ζ (k.Φ s' x)‖ ^ 2 ≤ k.δ' ^ 2 :=
      hζ.trans (pow_le_pow_left₀ (norm_nonneg _) hζs 2)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.δ'_pos.le two_ne_zero).1 h1
  have hlev := (hmid s' (right_mem_Icc.2 hs'.1.le))
  refine ⟨k.mem_Sσ_iff.2 ⟨hlev.1, ⟨?_, ?_⟩, hζ'⟩, hlev.2⟩
  · linarith [hlev.2.1, c.lo₂_mem_levels]
  · linarith [hlev.2.2, c.hi₁_mem_levels]

/-- **Exit from the middle band through an end level**: a trajectory starting in the middle
band stays in it until it reaches the level `hi₁` (with `‖ζ‖ < 2δ` unless at time `0`) or the
level `lo₂`. -/
theorem exists_exit_mid_band {x : M} (hx : x ∈ k.Tmid) :
    ∃ t, 0 ≤ t ∧ (∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Tmid) ∧
      (∀ s ∈ Ico 0 t, c.lo₂ < f (k.Φ s x) ∧ f (k.Φ s x) < c.hi₁) ∧
      ((f (k.Φ t x) = c.hi₁ ∧ (0 < t → ‖c.ζ (k.Φ t x)‖ < 2 * k.δ)) ∨ f (k.Φ t x) = c.lo₂) := by
  obtain ⟨t, ht, htT⟩ := k.exists_exit_Tmid x hx
  have hhit : ∃ s ∈ Icc 0 t, k.Φ s x ∈ c.Emid := by
    by_contra h
    push Not at h
    exact htT (k.Φ_mem_Tmid_of_notMem_Emid hx h t (right_mem_Icc.2 ht))
  obtain ⟨s₀, hs₀, hs₀E, hmin⟩ := exists_first_time c.isClosed_Emid (k.continuous_Φ_curve x) hhit
  have hbefore : ∀ s ∈ Ico 0 s₀, k.Φ s x ∈ k.Tmid := fun s hs =>
    k.Φ_mem_Tmid_of_notMem_Emid hx (fun u hu => hmin u ⟨hu.1, hu.2.trans_lt hs.2⟩) s
      (right_mem_Icc.2 hs.1)
  have hs₀T : k.Φ s₀ x ∈ k.Tmid := by
    rcases hs₀.1.eq_or_lt with h | h
    · rw [← h, k.Φ_zero]; exact hx
    · refine k.isCompact_Tmid.isClosed.mem_of_tendsto
        ((k.continuous_Φ_curve x).continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Iio s₀))) ?_
      filter_upwards [Ico_mem_nhdsLT h] with s hs using hbefore s hs
  have hall : ∀ s ∈ Icc 0 s₀, k.Φ s x ∈ k.Tmid := fun s hs => by
    rcases hs.2.eq_or_lt with h | h
    · rw [h]; exact hs₀T
    · exact hbefore s ⟨hs.1, h⟩
  have hopen : ∀ s ∈ Ico 0 s₀, c.lo₂ < f (k.Φ s x) ∧ f (k.Φ s x) < c.hi₁ := fun s hs =>
    c.lt_of_notMem_Emid (hmin s hs)
  refine ⟨s₀, hs₀.1, hall, hopen, ?_⟩
  rcases hs₀E with h | h
  · right
    exact le_antisymm h hs₀T.2.1
  · left
    have hf : f (k.Φ s₀ x) = c.hi₁ := le_antisymm hs₀T.2.2 h
    refine ⟨hf, fun hpos => ?_⟩
    have hd := k.hasDerivAt_f_Φ_mid' (k.Tmid_subset_TubeOpenσ hs₀T) hs₀T.2.1 hs₀T.2.2
    have hr := nonneg_of_hasDerivAt_of_le_left hpos hd fun s hs => by
      have := (hopen s ⟨by linarith [hs.1], hs.2⟩).2
      rw [hf]; exact this.le
    have hβ : k.βm (k.Φ s₀ x) ≠ 0 := by
      intro h0; rw [h0] at hr; linarith
    exact k.norm_ζ_lt_of_βm_ne_zero hβ


/-! ### The chart of `p`: coefficients and components of the pulled-back field -/

open scoped Classical in
/-- The reversal coefficient `βm ψm` at a chart point of `p` (zero off the one-sided tube). -/
def Cp (y : Fin n → ℝ) : ℝ := if c.e.χ y ∈ c.TubeOpenσ then k.βm (c.e.χ y) * c.ψm (c.e.χ y) else 0

open scoped Classical in
/-- The contraction coefficient `βm' ψm'` at a chart point of `p` (zero off the tube). -/
def Bp (y : Fin n → ℝ) : ℝ :=
  if c.e.χ y ∈ c.TubeOpenσ then k.βm' (c.e.χ y) * c.ψm' (c.e.χ y) else 0

theorem Cp_of_mem {y : Fin n → ℝ} (h : c.e.χ y ∈ c.TubeOpenσ) :
    k.Cp y = k.βm (c.e.χ y) * c.ψm (c.e.χ y) := by classical simp [Cp, h]

theorem Cp_of_notMem {y : Fin n → ℝ} (h : c.e.χ y ∉ c.TubeOpenσ) : k.Cp y = 0 := by
  classical simp [Cp, h]

theorem Bp_of_mem {y : Fin n → ℝ} (h : c.e.χ y ∈ c.TubeOpenσ) :
    k.Bp y = k.βm' (c.e.χ y) * c.ψm' (c.e.χ y) := by classical simp [Bp, h]

theorem Bp_of_notMem {y : Fin n → ℝ} (h : c.e.χ y ∉ c.TubeOpenσ) : k.Bp y = 0 := by
  classical simp [Bp, h]

theorem Cp_nonneg (y : Fin n → ℝ) : 0 ≤ k.Cp y := by
  classical
  unfold Cp; split_ifs
  · exact mul_nonneg (k.βm_nonneg _) (c.ψm_nonneg _)
  · exact le_rfl

theorem Cp_le_one (y : Fin n → ℝ) : k.Cp y ≤ 1 := by
  classical
  unfold Cp; split_ifs
  · exact (mul_le_mul (k.βm_le_one _) (c.ψm_le_one _) (c.ψm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  · exact zero_le_one

theorem Bp_nonneg (y : Fin n → ℝ) : 0 ≤ k.Bp y := by
  classical
  unfold Bp; split_ifs
  · exact mul_nonneg (k.βm'_nonneg _) (c.ψm'_nonneg _)
  · exact le_rfl

theorem Bp_le_one (y : Fin n → ℝ) : k.Bp y ≤ 1 := by
  classical
  unfold Bp; split_ifs
  · exact (mul_le_mul (k.βm'_le_one _) (c.ψm'_le_one _) (c.ψm'_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  · exact zero_le_one

theorem Cp_eq_zero_of_Bp_eq_zero {y : Fin n → ℝ} (h : k.Bp y = 0) : k.Cp y = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.TubeOpenσ
  · rw [k.Bp_of_mem hT] at h
    rw [k.Cp_of_mem hT]
    exact k.βm_mul_ψm_eq_zero h
  · exact k.Cp_of_notMem hT

theorem Bp_eq_one_of_Cp_ne_zero {y : Fin n → ℝ} (h : k.Cp y ≠ 0) : k.Bp y = 1 := by
  classical
  by_cases hT : c.e.χ y ∈ c.TubeOpenσ
  · rw [k.Cp_of_mem hT] at h
    rw [k.Bp_of_mem hT]
    exact k.βm'_mul_ψm'_eq_one h
  · exact absurd (k.Cp_of_notMem hT) h

theorem mem_of_Bp_ne_zero {y : Fin n → ℝ} (h : k.Bp y ≠ 0) :
    c.e.χ y ∈ c.TubeOpenσ ∧ ‖c.ζ (c.e.χ y)‖ < k.δ' := by
  classical
  by_cases hT : c.e.χ y ∈ c.TubeOpenσ
  · rw [k.Bp_of_mem hT] at h
    exact ⟨hT, k.norm_ζ_lt_of_βm'_ne_zero (mul_ne_zero_iff.1 h).1⟩
  · exact absurd (k.Bp_of_notMem hT) h

theorem Cp_eq_zero_of_norm_ζ {y : Fin n → ℝ} (h : c.e.χ y ∈ c.TubeOpenσ → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖) :
    k.Cp y = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.TubeOpenσ
  · rw [k.Cp_of_mem hT]
    have : k.βm (c.e.χ y) = 0 := by
      by_contra h'
      exact absurd (k.norm_ζ_lt_of_βm_ne_zero h') (not_lt.2 (h hT))
    rw [this, zero_mul]
  · exact k.Cp_of_notMem hT

theorem Cp_eq_zero_of_f_le {y : Fin n → ℝ} (h : f (c.e.χ y) ≤ c.lo₁) : k.Cp y = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.TubeOpenσ
  · rw [k.Cp_of_mem hT, c.ψm_eq_zero_of_le h, mul_zero]
  · exact k.Cp_of_notMem hT

theorem Bp_eq_zero_of_f_le {y : Fin n → ℝ} (h : f (c.e.χ y) ≤ c.c₁ - c.η / 2) : k.Bp y = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.TubeOpenσ
  · rw [k.Bp_of_mem hT]
    have : c.ψm' (c.e.χ y) = 0 := plateau_eq_zero_of_le c.c₁_sub_half_lt_lo₁ h
    rw [this, mul_zero]
  · exact k.Bp_of_notMem hT

/-- The pulled-back field in the chart of `p` in terms of the coefficients. -/
theorem Vp_eq (y : Fin n → ℝ) :
    k.Vp y = (1 - 2 * k.Cp y) • ModelField.modelField 0 c.e.r₀ y + k.Yp' y +
      (2 * (c.lam * k.Bp y)) • c.Zp' y := by
  classical
  unfold Vp
  by_cases hT : c.e.χ y ∈ c.TubeOpenσ
  · rw [k.Cp_of_mem hT, k.Bp_of_mem hT, c.Zp'_of_mem hT]
    simp only [hT, ite_true]
    module
  · rw [k.Cp_of_notMem hT, k.Bp_of_notMem hT, c.Zp'_of_notMem hT]
    simp only [hT, ite_false]
    module

/-- The radial component of the pulled-back field. -/
theorem dot_Vp {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    dot y (k.Vp y) = -((1 - 2 * k.Cp y) * (ModelField.theta c.e.r₀ y * morseNorm n y ^ 2)) +
      c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * axial c.e₁ y := by
  rw [k.Vp_eq, dot_add_right, dot_add_right, dot_smul_right, dot_smul_right, c.dot_Zp' hy,
    modelField_index_zero, dot_neg_right, dot_smul_right, dot_self]
  have : k.Yp' y = (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := rfl
  rw [this, dot_smul_right]
  simp only [axial, mul_zero, add_zero]
  ring

/-- The axial component of the pulled-back field. -/
theorem axial_Vp (y : Fin n → ℝ) :
    axial c.e₁ (k.Vp y) = -((1 - 2 * k.Cp y) * (ModelField.theta c.e.r₀ y * axial c.e₁ y)) +
      c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) +
      2 * (c.lam * k.Bp y) * axial c.e₁ (c.Zp' y) := by
  rw [k.Vp_eq, axial_add, axial_add, axial_smul, axial_smul, modelField_index_zero, axial_neg,
    axial_smul]
  have : k.Yp' y = (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := rfl
  have he : axial c.e₁ c.e₁ = 1 := by rw [axial, dot_self, c.morseNorm_e₁]; norm_num
  rw [this, axial_smul, he]
  ring

/-- The derivative of `Bm` along the pulled-back field. -/
theorem BmDeriv_Vp {y : Fin n → ℝ} (hy0 : y ≠ 0) :
    BmDeriv c.e₁ y (k.Vp y) =
      c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * BmDeriv c.e₁ y c.e₁ +
      2 * (c.lam * k.Bp y) * BmDeriv c.e₁ y (c.Zp' y) := by
  rw [k.Vp_eq, map_add, map_add, map_smul, map_smul, modelField_index_zero, map_neg, map_smul,
    BmDeriv_self c.e₁ hy0]
  have : k.Yp' y = (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := rfl
  rw [this, map_smul]
  simp only [smul_eq_mul, mul_zero, neg_zero, zero_add]

/-- Off the arc, the contraction field increases the axial coordinate. -/
theorem axial_Zp'_pos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hT : c.e.χ y ∈ c.TubeOpenσ) (hζ0 : 0 < ‖c.ζ (c.e.χ y)‖) (hζ : ‖c.ζ (c.e.χ y)‖ < k.δ') :
    0 < axial c.e₁ (c.Zp' y) := by
  have hy0 : y ≠ 0 := c.ne_zero_of_mem_TubeOpen hy hT.1
  have h := k.hdB y hy hT hζ0 hζ
  rw [c.Zp'_of_mem hT]
  rw [BmDeriv_apply] at h
  have horth : dot y (c.Zp y) = 0 := by
    rw [dot_eq_sum]; exact c.Z_chart_p_orth (c.morseNorm_lt_rmp_of_sq_lt hy) hT.1
  rw [horth, mul_zero, zero_sub, neg_lt_zero] at h
  have hρ := morseNorm_pos hy0
  rw [axial, dot_comm]
  exact pos_of_mul_pos_right h (inv_pos.2 hρ).le

theorem BmDeriv_Zp'_nonpos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hB : k.Bp y ≠ 0) : BmDeriv c.e₁ y (c.Zp' y) ≤ 0 := by
  obtain ⟨hT, hζ⟩ := k.mem_of_Bp_ne_zero hB
  by_cases hζ0 : c.ζ (c.e.χ y) = 0
  · rw [c.Zp'_eq_zero_of_ζ hT hζ0, map_zero]
  · rw [c.Zp'_of_mem hT]
    exact (k.hdB y hy hT (norm_pos_iff.2 hζ0) hζ).le

/-- **`Bm` is non-increasing along the pulled-back field** in the ball of `p`. -/
theorem BmDeriv_Vp_nonpos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) (hy0 : y ≠ 0) :
    BmDeriv c.e₁ y (k.Vp y) ≤ 0 := by
  rw [k.BmDeriv_Vp hy0]
  have h1 : c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * BmDeriv c.e₁ y c.e₁ ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact mul_nonneg c.m'_pos.le (mul_nonneg (βp_nonneg _) (ψp_nonneg _))
    · rw [BmDeriv_e₁ c.morseNorm_e₁ hy0]
      have := perpSq_nonneg c.morseNorm_e₁ y
      have := morseNorm_pos hy0
      have : 0 ≤ perpSq c.e₁ y / morseNorm n y ^ 3 := by positivity
      linarith
  have h2 : 2 * (c.lam * k.Bp y) * BmDeriv c.e₁ y (c.Zp' y) ≤ 0 := by
    by_cases hB : k.Bp y = 0
    · rw [hB]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos
        (by have := c.lam_pos; have := k.Bp_nonneg y; positivity) (k.BmDeriv_Zp'_nonpos hy hB)
  linarith

/-- Where `dBm (Vp) = 0`: either the pusher is off or `y` is on the axis; and either the
contraction is off or `ζ = 0`. -/
theorem of_BmDeriv_Vp_eq_zero {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) (hy0 : y ≠ 0)
    (h : BmDeriv c.e₁ y (k.Vp y) = 0) :
    (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y = 0 ∨ perpSq c.e₁ y = 0) ∧
      (k.Bp y = 0 ∨ (c.e.χ y ∈ c.TubeOpenσ ∧ c.ζ (c.e.χ y) = 0)) := by
  rw [k.BmDeriv_Vp hy0] at h
  have hA0 : 0 ≤ βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y := mul_nonneg (βp_nonneg _) (ψp_nonneg _)
  have hBe : BmDeriv c.e₁ y c.e₁ ≤ 0 := by
    rw [BmDeriv_e₁ c.morseNorm_e₁ hy0]
    have := perpSq_nonneg c.morseNorm_e₁ y
    have := morseNorm_pos hy0
    have : 0 ≤ perpSq c.e₁ y / morseNorm n y ^ 3 := by positivity
    linarith
  have h1 : c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * BmDeriv c.e₁ y c.e₁ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg c.m'_pos.le hA0) hBe
  have h2 : 2 * (c.lam * k.Bp y) * BmDeriv c.e₁ y (c.Zp' y) ≤ 0 := by
    by_cases hB : k.Bp y = 0
    · rw [hB]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos
        (by have := c.lam_pos; have := k.Bp_nonneg y; positivity) (k.BmDeriv_Zp'_nonpos hy hB)
  have h1' : c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * BmDeriv c.e₁ y c.e₁ = 0 := by
    linarith
  have h2' : 2 * (c.lam * k.Bp y) * BmDeriv c.e₁ y (c.Zp' y) = 0 := by linarith
  constructor
  · rcases mul_eq_zero.1 h1' with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 c.m'_pos.ne'
      · exact Or.inl h4
    · right
      rw [BmDeriv_e₁ c.morseNorm_e₁ hy0, neg_eq_zero, div_eq_zero_iff] at h3
      rcases h3 with h3 | h3
      · exact h3
      · exact absurd h3 (pow_ne_zero _ (morseNorm_pos hy0).ne')
  · by_cases hB : k.Bp y = 0
    · exact Or.inl hB
    · right
      obtain ⟨hT, hζ⟩ := k.mem_of_Bp_ne_zero hB
      refine ⟨hT, ?_⟩
      by_contra hζ0
      have := k.hdB y hy hT (norm_pos_iff.2 hζ0) hζ
      rw [← c.Zp'_of_mem hT] at this
      have hpos : 0 < 2 * (c.lam * k.Bp y) := by
        have := c.lam_pos
        have := lt_of_le_of_ne (k.Bp_nonneg y) (Ne.symm hB)
        positivity
      have := mul_neg_of_pos_of_neg hpos this
      linarith

/-! ### Chart quantities along `Φ` in the ball of `p` -/

theorem hasDerivAt_morseNormSq_Φ_p {x : M} {s : ℝ} (hs : k.Φ s x ∈ c.pBall') :
    HasDerivAt (fun s => morseNorm n (c.e.χ.symm (k.Φ s x)) ^ 2)
      (2 * dot (c.e.χ.symm (k.Φ s x)) (k.Vp (c.e.χ.symm (k.Φ s x)))) s := by
  have h := (hasFDerivAt_morseNorm_sq (c.e.χ.symm (k.Φ s x))).comp_hasDerivAt s
    (k.hasDerivAt_symm_Φ_p hs)
  refine h.congr_deriv ?_
  simp [dotL_apply]

theorem hasDerivAt_axial_Φ_p {x : M} {s : ℝ} (hs : k.Φ s x ∈ c.pBall') :
    HasDerivAt (fun s => axial c.e₁ (c.e.χ.symm (k.Φ s x)))
      (axial c.e₁ (k.Vp (c.e.χ.symm (k.Φ s x)))) s := by
  have h := (hasFDerivAt_axial c.e₁ (c.e.χ.symm (k.Φ s x))).comp_hasDerivAt s
    (k.hasDerivAt_symm_Φ_p hs)
  refine h.congr_deriv ?_
  rw [dotL_apply, axial, dot_comm]

theorem hasDerivAt_Bm_Φ_p {x : M} {s : ℝ} (hs : k.Φ s x ∈ c.pBall')
    (hy0 : c.e.χ.symm (k.Φ s x) ≠ 0) :
    HasDerivAt (fun s => Bm c.e₁ (c.e.χ.symm (k.Φ s x)))
      (BmDeriv c.e₁ (c.e.χ.symm (k.Φ s x)) (k.Vp (c.e.χ.symm (k.Φ s x)))) s := by
  have h := (hasFDerivAt_Bm c.e₁ hy0).comp_hasDerivAt s (k.hasDerivAt_symm_Φ_p hs)
  exact h


end CancelConsts

/-! ### The ball of `p`: the split radius and the two regions -/

/-- `ψp ≥ 9/10` on a ball of radius slightly larger than `ρA`. -/
theorem exists_ρs : ∃ ρ : ℝ, c.ρA ≤ ρ ∧ ρ < c.ρB ∧
    ∀ y : Fin n → ℝ, morseNorm n y ≤ ρ → 9 / 10 ≤ ψp c.ρA c.ρB y := by
  have hAB : c.ρA ^ 2 < c.ρB ^ 2 := pow_lt_pow_left₀ c.ρA_lt_ρB c.ρA_pos.le two_ne_zero
  have hc : ContinuousAt (cut (c.ρA ^ 2) (c.ρB ^ 2)) (c.ρA ^ 2) :=
    (contDiff_cut _ _).continuous.continuousAt
  have h1 : cut (c.ρA ^ 2) (c.ρB ^ 2) (c.ρA ^ 2) = 1 := cut_eq_one hAB le_rfl
  have hev : ∀ᶠ t in 𝓝 (c.ρA ^ 2), 9 / 10 < cut (c.ρA ^ 2) (c.ρB ^ 2) t :=
    hc (Ioi_mem_nhds (by rw [h1]; norm_num))
  obtain ⟨w, hw, hball⟩ := Metric.mem_nhds_iff.1 hev
  set w' := min (w / 2) ((c.ρB ^ 2 - c.ρA ^ 2) / 2) with hw'
  have hw'0 : 0 < w' := lt_min (by positivity) (by linarith)
  refine ⟨Real.sqrt (c.ρA ^ 2 + w'), ?_, ?_, fun y hy => ?_⟩
  · rw [Real.le_sqrt c.ρA_pos.le (by positivity)]; linarith
  · rw [Real.sqrt_lt' c.ρB_pos]
    have : w' ≤ (c.ρB ^ 2 - c.ρA ^ 2) / 2 := min_le_right _ _
    linarith
  · have hy2 : morseNorm n y ^ 2 ≤ c.ρA ^ 2 + w' := by
      have := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy 2
      rwa [Real.sq_sqrt (by positivity)] at this
    have hmono := cut_antitone hAB hy2
    have hmem : c.ρA ^ 2 + w' ∈ Metric.ball (c.ρA ^ 2) w := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hw'0]
      have : w' ≤ w / 2 := min_le_left _ _
      linarith
    have := hball hmem
    exact le_trans this.le hmono

/-- The split radius of the ball of `p`: `ρA ≤ ρs < ρB` with `ψp ≥ 9/10` for `‖y‖ ≤ ρs`. -/
def ρs : ℝ := c.exists_ρs.choose

theorem ρA_le_ρs : c.ρA ≤ c.ρs := c.exists_ρs.choose_spec.1
theorem ρs_lt_ρB : c.ρs < c.ρB := c.exists_ρs.choose_spec.2.1
theorem ψp_ge_of_le_ρs {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.ρs) :
    9 / 10 ≤ ψp c.ρA c.ρB y := c.exists_ρs.choose_spec.2.2 y hy
theorem ρs_pos : 0 < c.ρs := c.ρA_pos.trans_le c.ρA_le_ρs
theorem r₀p_lt_ρs : c.e.r₀ < c.ρs := c.r₀p_lt_ρA.trans_le c.ρA_le_ρs

/-- The radial speed `θ ‖y‖ = 1 / ‖y‖ < m' / 3` at radius `≥ ρs`. -/
theorem theta_mul_lt_third {y : Fin n → ℝ} (hy : c.ρs ≤ morseNorm n y) :
    ModelField.theta c.e.r₀ y * morseNorm n y < c.m' / 3 := by
  have hr := c.e.hr₀
  have hρ : c.e.r₀ < morseNorm n y := c.r₀p_lt_ρs.trans_le hy
  rw [ModelField.theta_eq c.e.hr₀ (by linarith)]
  have hpos : 0 < morseNorm n y := by linarith
  have h1 : (morseNorm n y ^ 2)⁻¹ * morseNorm n y = 1 / morseNorm n y := by field_simp
  rw [h1]
  have h2 : 1 / morseNorm n y < 1 / c.e.r₀ := one_div_lt_one_div_of_lt hr hρ
  have h3 := c.three_div_r₀p_lt_m'
  have : 1 / c.e.r₀ = 3 / c.e.r₀ / 3 := by ring
  linarith

/-- `ψp + ψm = 1` on the closed ball of radius `ρB`. -/
theorem ψp_add_ψm {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.ρB) :
    ψp c.ρA c.ρB y + c.ψm (c.e.χ y) = 1 := by
  have hyR : morseNorm n y ≤ c.e.R := hy.trans c.ρB_le_R
  have hf := c.f_chart_p hyR
  have hle : f p + morseNorm n y ^ 2 / 2 ≤ c.hi₁ := by
    have h1 := c.ρB_sq_eq
    have h2 : morseNorm n y ^ 2 ≤ c.ρB ^ 2 := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy 2
    have := c.lo₂_lt_hi₁
    linarith
  have := ψp_add_plateau (n := n) c.lo₁_lt_lo₂ c.hi₁_lt_hi₂ c.ρA_sq_eq c.ρB_sq_eq hle
  unfold CancelData.ψm
  rw [hf]; exact this

theorem ρB_sq_lt_three_ε : c.ρB ^ 2 < 3 * c.ε := by linarith [c.ρB_sq_lt, c.hε]

theorem sq_lt_three_ε_of_le_ρB {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.ρB) :
    morseNorm n y ^ 2 < 3 * c.ε :=
  (pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy 2).trans_lt c.ρB_sq_lt_three_ε

/-- The closed ball region of `p` (radius `ρB`). -/
def Wball : Set M := c.e.χ '' {y | morseNorm n y ≤ c.ρB}

theorem isCompact_Wball : IsCompact c.Wball := c.e.isCompact_image_le c.ρB_lt_R'

theorem Wball_subset_pBall' : c.Wball ⊆ c.pBall' := image_mono fun _ hy =>
  c.sq_lt_three_ε_of_le_ρB hy

theorem Wball_subset_image_ball : c.Wball ⊆ c.e.χ '' Metric.ball 0 c.e.R' :=
  c.Wball_subset_pBall'.trans c.pBall'_subset_image_ball

/-- Chart coordinates of a point of the ball region. -/
theorem symm_mem_of_mem_Wball {x : M} (hx : x ∈ c.Wball) : morseNorm n (c.e.χ.symm x) ≤ c.ρB := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB hy)]; exact hy

theorem mem_Wball_iff {x : M} (hx : x ∈ c.e.χ '' Metric.ball 0 c.e.R') :
    x ∈ c.Wball ↔ morseNorm n (c.e.χ.symm x) ≤ c.ρB :=
  ⟨c.symm_mem_of_mem_Wball, fun h => c.e.mem_image_of_symm_mem hx h⟩

theorem continuousOn_symm_Wball : ContinuousOn c.e.χ.symm c.Wball :=
  c.e.hχsymm.continuousOn.mono c.Wball_subset_image_ball

/-- The open ball region of radius `ρB`. -/
theorem isOpen_ball_ρB : IsOpen (c.e.χ '' {y | morseNorm n y < c.ρB}) :=
  c.e.isOpen_image_of_lt c.ρB_lt_R'.le

theorem ball_ρB_subset_Wball : c.e.χ '' {y | morseNorm n y < c.ρB} ⊆ c.Wball :=
  image_mono fun _ (hy : morseNorm n _ < c.ρB) => le_of_lt hy

theorem continuousOn_Bm_annulus :
    ContinuousOn (Bm c.e₁) {y : Fin n → ℝ | c.ρs ≤ morseNorm n y} := fun y hy =>
  (contDiffAt_Bm c.e₁ (by
    rintro rfl; have : c.ρs ≤ morseNorm n (0 : Fin n → ℝ) := hy
    rw [morseNorm_zero] at this; linarith [c.ρs_pos])).continuousAt.continuousWithinAt

namespace CancelConsts

variable {c} (k : c.CancelConsts)

/-- The angular threshold `b₀ = τ²/4` of the plateau cone. -/
def b₀ : ℝ := k.τ ^ 2 / 4

theorem b₀_pos : 0 < k.b₀ := by unfold b₀; have := k.hτ; positivity

theorem b₀_le : k.b₀ ≤ 1 / 16 := by unfold b₀; have := k.hτ1; linarith

/-- Elementary consequences of `Bm y ≤ b₀` at radius `≥ ρs`. -/
theorem of_Bm_le {y : Fin n → ℝ} (hy : c.ρs ≤ morseNorm n y) (hB : Bm c.e₁ y ≤ k.b₀) :
    0 < axial c.e₁ y ∧ (1 - k.b₀) ^ 2 * morseNorm n y ^ 2 ≤ axial c.e₁ y ^ 2 ∧
      perpSq c.e₁ y ≤ morseNorm n y ^ 2 * (2 * k.b₀) := by
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [morseNorm_zero] at hy; linarith [c.ρs_pos]
  have hρ := morseNorm_pos hy0
  have hb := k.b₀_le
  have hBm : Bm c.e₁ y = 1 - axial c.e₁ y / morseNorm n y := rfl
  have h1b : 0 < 1 - k.b₀ := by linarith
  have ha' : (1 - k.b₀) * morseNorm n y ≤ axial c.e₁ y := by
    have : 1 - axial c.e₁ y / morseNorm n y ≤ k.b₀ := hBm ▸ hB
    have h2 : 1 - k.b₀ ≤ axial c.e₁ y / morseNorm n y := by linarith
    exact (le_div_iff₀ hρ).1 h2
  have hapos : 0 < axial c.e₁ y := lt_of_lt_of_le (mul_pos h1b hρ) ha'
  have hsq : ((1 - k.b₀) * morseNorm n y) ^ 2 ≤ axial c.e₁ y ^ 2 :=
    pow_le_pow_left₀ (mul_pos h1b hρ).le ha' 2
  rw [mul_pow] at hsq
  refine ⟨hapos, hsq, ?_⟩
  have hperp : perpSq c.e₁ y = morseNorm n y ^ 2 - axial c.e₁ y ^ 2 := rfl
  have e : (1 - k.b₀) ^ 2 * morseNorm n y ^ 2 =
      morseNorm n y ^ 2 - 2 * k.b₀ * morseNorm n y ^ 2 + k.b₀ ^ 2 * morseNorm n y ^ 2 := by ring
  have := mul_nonneg (sq_nonneg k.b₀) (sq_nonneg (morseNorm n y))
  rw [hperp]; nlinarith

/-- Inside the angular threshold, a point of radius `≥ ρs` lies in the plateau of the pusher
cone (`βp = 1`). -/
theorem βp_eq_one_of_Bm_le {y : Fin n → ℝ} (hy : c.ρs ≤ morseNorm n y)
    (hB : Bm c.e₁ y ≤ k.b₀) : βp k.δ k.τ c.e₁ y = 1 := by
  obtain ⟨hapos, hsq, hperp⟩ := k.of_Bm_le hy hB
  have hb := k.b₀_le
  have hδ := k.hδ
  refine βp_eq_one k.hδ ?_ (by linarith)
  have hb₀ : 2 * k.b₀ = k.τ ^ 2 / 2 := by unfold b₀; ring
  have h3 : 1 / 2 ≤ (1 - k.b₀) ^ 2 := by nlinarith
  have hτ2 := sq_nonneg k.τ
  have hρ2 := sq_nonneg (morseNorm n y)
  have h4 : morseNorm n y ^ 2 * (2 * k.b₀) ≤ k.τ ^ 2 * axial c.e₁ y ^ 2 := by
    rw [hb₀]
    have : k.τ ^ 2 * (1 / 2 * morseNorm n y ^ 2) ≤ k.τ ^ 2 * ((1 - k.b₀) ^ 2 * morseNorm n y ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hτ2
    have h5 : k.τ ^ 2 * ((1 - k.b₀) ^ 2 * morseNorm n y ^ 2) ≤ k.τ ^ 2 * axial c.e₁ y ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hτ2
    linarith
  have := sq_nonneg k.δ
  linarith

/-- Inside the angular threshold, a point of the annulus lies in the one-sided tube with
`‖ζ‖ < δ'` (from the cone inclusion `hcone`). -/
theorem mem_tube_of_Bm_le {y : Fin n → ℝ} (hy1 : c.ρs ≤ morseNorm n y) (hy2 : morseNorm n y ≤ c.ρB)
    (hB : Bm c.e₁ y ≤ k.b₀) : c.e.χ y ∈ c.TubeOpenσ ∧ ‖c.ζ (c.e.χ y)‖ < k.δ' := by
  obtain ⟨hapos, -, hperp⟩ := k.of_Bm_le hy1 hB
  refine k.hcone y (c.ρA_le_ρs.trans hy1) hy2 ?_ hapos
  have hb₀ : 2 * k.b₀ = k.τ ^ 2 / 2 := by unfold b₀; ring
  have hτ := k.hτ
  have hρ : 0 < morseNorm n y := c.ρs_pos.trans_le hy1
  have hpos : 0 < 2 * k.δ ^ 2 / c.ρA ^ 2 := by have := k.hδ; have := c.ρA_pos; positivity
  have : morseNorm n y ^ 2 * (2 * k.b₀) < (k.τ ^ 2 + 2 * k.δ ^ 2 / c.ρA ^ 2) * morseNorm n y ^ 2 := by
    rw [hb₀]; nlinarith [sq_nonneg k.τ, mul_pos hpos (pow_pos hρ 2), mul_pos (pow_pos hτ 2) (pow_pos hρ 2)]
  linarith

/-- The inner region: the ball of radius `ρs` together with the part of the annulus outside the
angular threshold. -/
def Wp1 : Set M :=
  c.e.χ '' {y | morseNorm n y ≤ c.ρs ∨
    (c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ Bm c.e₁ y)}

/-- The outer region: the annulus inside the angular threshold. -/
def Wp2 : Set M :=
  c.e.χ '' {y | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ Bm c.e₁ y ≤ k.b₀}

theorem isClosed_annulus_Bm_ge :
    IsClosed {y : Fin n → ℝ | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ Bm c.e₁ y} := by
  have h : {y : Fin n → ℝ | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ Bm c.e₁ y} =
      {y | c.ρs ≤ morseNorm n y} ∩ (Bm c.e₁) ⁻¹' Ici k.b₀ ∩ {y | morseNorm n y ≤ c.ρB} := by
    ext y; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici]; tauto
  rw [h]
  exact (c.continuousOn_Bm_annulus.preimage_isClosed_of_isClosed
    (isClosed_le continuous_const continuous_morseNorm) isClosed_Ici).inter
    (isClosed_le continuous_morseNorm continuous_const)

theorem isClosed_annulus_Bm_le :
    IsClosed {y : Fin n → ℝ | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ Bm c.e₁ y ≤ k.b₀} := by
  have h : {y : Fin n → ℝ | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ Bm c.e₁ y ≤ k.b₀} =
      {y | c.ρs ≤ morseNorm n y} ∩ (Bm c.e₁) ⁻¹' Iic k.b₀ ∩ {y | morseNorm n y ≤ c.ρB} := by
    ext y; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iic]; tauto
  rw [h]
  exact (c.continuousOn_Bm_annulus.preimage_isClosed_of_isClosed
    (isClosed_le continuous_const continuous_morseNorm) isClosed_Iic).inter
    (isClosed_le continuous_morseNorm continuous_const)

theorem isCompact_Wp1 : IsCompact k.Wp1 :=
  c.e.isCompact_image_of_subset
    (((isCompact_morseNorm_le c.ρB).of_isClosed_subset
      ((isClosed_le continuous_morseNorm continuous_const).union k.isClosed_annulus_Bm_ge)
      (fun _ hy => by
        rcases hy with h | h
        · exact h.trans c.ρs_lt_ρB.le
        · exact h.2.1))) c.ρB_lt_R' fun _ hy => by
    rcases hy with h | h
    · exact h.trans c.ρs_lt_ρB.le
    · exact h.2.1

theorem isCompact_Wp2 : IsCompact k.Wp2 :=
  c.e.isCompact_image_of_subset
    ((isCompact_morseNorm_le c.ρB).of_isClosed_subset k.isClosed_annulus_Bm_le fun _ hy => hy.2.1)
    c.ρB_lt_R' fun _ hy => hy.2.1

theorem Wp1_subset_Wball : k.Wp1 ⊆ c.Wball := image_mono fun _ hy => by
  rcases hy with h | h
  · exact h.trans c.ρs_lt_ρB.le
  · exact h.2.1

theorem Wp2_subset_Wball : k.Wp2 ⊆ c.Wball := image_mono fun _ hy => hy.2.1

theorem mem_Wp1_iff {x : M} (hx : x ∈ c.e.χ '' Metric.ball 0 c.e.R') :
    x ∈ k.Wp1 ↔ (morseNorm n (c.e.χ.symm x) ≤ c.ρs ∨
      (c.ρs ≤ morseNorm n (c.e.χ.symm x) ∧ morseNorm n (c.e.χ.symm x) ≤ c.ρB ∧
        k.b₀ ≤ Bm c.e₁ (c.e.χ.symm x))) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyB : morseNorm n y ≤ c.ρB := by
      rcases hy with h | h
      · exact h.trans c.ρs_lt_ρB.le
      · exact h.2.1
    rw [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB hyB)]; exact hy
  · intro h; exact c.e.mem_image_of_symm_mem hx h

theorem mem_Wp2_iff {x : M} (hx : x ∈ c.e.χ '' Metric.ball 0 c.e.R') :
    x ∈ k.Wp2 ↔ (c.ρs ≤ morseNorm n (c.e.χ.symm x) ∧ morseNorm n (c.e.χ.symm x) ≤ c.ρB ∧
        Bm c.e₁ (c.e.χ.symm x) ≤ k.b₀) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB hy.2.1)]; exact hy
  · intro h; exact c.e.mem_image_of_symm_mem hx h

theorem Wball_eq_union : c.Wball = k.Wp1 ∪ k.Wp2 := by
  ext x
  constructor
  · intro hx
    have hx' := c.Wball_subset_image_ball hx
    have hρ := c.symm_mem_of_mem_Wball hx
    rw [mem_union, k.mem_Wp1_iff hx', k.mem_Wp2_iff hx']
    rcases le_or_gt (morseNorm n (c.e.χ.symm x)) c.ρs with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt k.b₀ (Bm c.e₁ (c.e.χ.symm x)) with hb | hb
      · exact Or.inl (Or.inr ⟨h.le, hρ, hb⟩)
      · exact Or.inr ⟨h.le, hρ, hb.le⟩
  · rintro (hx | hx)
    · exact k.Wp1_subset_Wball hx
    · exact k.Wp2_subset_Wball hx


end CancelConsts

/-! ### The inner region of the ball of `p`: the weak Lyapunov function `‖y‖² - a ‖y‖` -/

/-- The weak Lyapunov function of the inner region: `‖y‖ (‖y‖ - ⟪y, e₁⟫)`. -/
def Lp (y : Fin n → ℝ) : ℝ := morseNorm n y ^ 2 - axial c.e₁ y * morseNorm n y

theorem Lp_eq (y : Fin n → ℝ) : c.Lp y = morseNorm n y * (morseNorm n y - axial c.e₁ y) := by
  unfold Lp; ring

theorem Lp_nonneg (y : Fin n → ℝ) : 0 ≤ c.Lp y := by
  rw [c.Lp_eq]
  apply mul_nonneg (ModelField.morseNorm_nonneg y)
  have := abs_dot_le y c.e₁
  rw [c.morseNorm_e₁, mul_one] at this
  have := (abs_le.1 this).2
  unfold axial; linarith

theorem continuous_Lp : Continuous c.Lp :=
  (continuous_morseNorm.pow 2).sub ((continuous_axial c.e₁).mul continuous_morseNorm)

/-- `Lp y = 0` iff `y` lies on the nonnegative `e₁`-axis. -/
theorem Lp_eq_zero_iff (y : Fin n → ℝ) : c.Lp y = 0 ↔ y = axial c.e₁ y • c.e₁ ∧ 0 ≤ axial c.e₁ y := by
  rw [c.Lp_eq]
  by_cases hy0 : y = 0
  · subst hy0; simp [axial_zero, morseNorm_zero]
  have hρ := morseNorm_pos hy0
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h0 | h0
    · exact absurd h0 hρ.ne'
    · have ha : axial c.e₁ y = morseNorm n y := by linarith
      have hB : Bm c.e₁ y = 0 := by
        unfold Bm; rw [ha, div_self hρ.ne', sub_self]
      have := (Bm_eq_zero_iff c.morseNorm_e₁ hy0).1 hB
      refine ⟨?_, ha ▸ ModelField.morseNorm_nonneg y⟩
      rw [ha]; exact this
  · rintro ⟨hy, ha⟩
    have : morseNorm n y = axial c.e₁ y := by
      conv_lhs => rw [hy]
      rw [morseNorm_smul_self c.morseNorm_e₁, abs_of_nonneg ha]
    rw [this, sub_self, mul_zero]

/-- The rate of `Lp` along a vector `v` at `y`. -/
def LpRate (y v : Fin n → ℝ) : ℝ :=
  2 * dot y v - axial c.e₁ v * morseNorm n y - axial c.e₁ y * dot y v / morseNorm n y

/-- The derivative of `a ‖y‖` along a curve through `0` vanishes. -/
theorem hasDerivAt_axial_mul_morseNorm_of_eq_zero {y : ℝ → Fin n → ℝ} {y' : Fin n → ℝ} {s₀ : ℝ}
    (hy : HasDerivAt y y' s₀) (h0 : y s₀ = 0) :
    HasDerivAt (fun s => axial c.e₁ (y s) * morseNorm n (y s)) 0 s₀ := by
  -- `q s := ‖y s‖²` has derivative `0` at `s₀`
  have hq : HasDerivAt (fun s => morseNorm n (y s) ^ 2) 0 s₀ := by
    have := (hasFDerivAt_morseNorm_sq (y s₀)).comp_hasDerivAt s₀ hy
    refine this.congr_deriv ?_
    simp [dotL_apply, h0, dot_zero_left]
  have hq' := hasDerivAt_iff_tendsto.1 hq
  rw [hasDerivAt_iff_tendsto]
  have hbound : ∀ᶠ s in 𝓝 s₀, ‖s - s₀‖⁻¹ * ‖axial c.e₁ (y s) * morseNorm n (y s) -
      axial c.e₁ (y s₀) * morseNorm n (y s₀) - (s - s₀) • (0 : ℝ)‖ ≤
        ‖s - s₀‖⁻¹ * ‖morseNorm n (y s) ^ 2 - morseNorm n (y s₀) ^ 2 - (s - s₀) • (0 : ℝ)‖ := by
    refine Eventually.of_forall fun s => ?_
    rw [h0, axial_zero, morseNorm_zero]
    simp only [mul_zero, sub_zero, smul_zero, zero_pow two_ne_zero]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (ModelField.morseNorm_nonneg (y s)), abs_of_nonneg (sq_nonneg (morseNorm n (y s)))]
    have h1 := abs_dot_le (y s) c.e₁
    rw [c.morseNorm_e₁, mul_one] at h1
    rw [sq]; exact mul_le_mul_of_nonneg_right h1 (ModelField.morseNorm_nonneg _)
  exact squeeze_zero' (Eventually.of_forall fun s => by positivity) hbound hq'

/-- The derivative of `Lp` along a curve. -/
theorem hasDerivAt_Lp_curve {y : ℝ → Fin n → ℝ} {y' : Fin n → ℝ} {s₀ : ℝ}
    (hy : HasDerivAt y y' s₀) :
    HasDerivAt (fun s => c.Lp (y s)) (c.LpRate (y s₀) y') s₀ := by
  have h1 : HasDerivAt (fun s => morseNorm n (y s) ^ 2) (2 * dot (y s₀) y') s₀ := by
    have := (hasFDerivAt_morseNorm_sq (y s₀)).comp_hasDerivAt s₀ hy
    refine this.congr_deriv ?_
    simp [dotL_apply]
  have h2 : HasDerivAt (fun s => axial c.e₁ (y s)) (axial c.e₁ y') s₀ := by
    have := (hasFDerivAt_axial c.e₁ (y s₀)).comp_hasDerivAt s₀ hy
    refine this.congr_deriv ?_
    rw [dotL_apply, axial, dot_comm]
  by_cases h0 : y s₀ = 0
  · have h3 := c.hasDerivAt_axial_mul_morseNorm_of_eq_zero hy h0
    have := h1.sub h3
    refine this.congr_deriv ?_
    unfold LpRate
    rw [h0, dot_zero_left, morseNorm_zero, axial_zero]; ring
  · have h3 : HasDerivAt (fun s => morseNorm n (y s)) (dot (y s₀) y' / morseNorm n (y s₀)) s₀ := by
      have := (hasFDerivAt_morseNorm h0).comp_hasDerivAt s₀ hy
      refine this.congr_deriv ?_
      simp [dotL_apply, div_eq_inv_mul]
    have := h1.sub (h2.mul h3)
    refine this.congr_deriv ?_
    unfold LpRate
    have hρ := morseNorm_pos h0
    field_simp
    ring

namespace CancelConsts

variable {c} (k : c.CancelConsts)

/-- The rate of `Lp` along the pulled-back field, in closed form (for `y ≠ 0`). -/
theorem LpRate_Vp {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) (hy0 : y ≠ 0) :
    c.LpRate y (k.Vp y) =
      -(2 * ((1 - 2 * k.Cp y) * ModelField.theta c.e.r₀ y) * morseNorm n y *
          (morseNorm n y - axial c.e₁ y) +
        c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * (morseNorm n y - axial c.e₁ y) ^ 2 /
          morseNorm n y +
        2 * (c.lam * k.Bp y) * axial c.e₁ (c.Zp' y) * morseNorm n y) := by
  unfold LpRate
  rw [k.dot_Vp hy, k.axial_Vp]
  have hρ := morseNorm_pos hy0
  field_simp
  ring

/-- On the inner region, `Cp ≤ 1/10` (inner ball) or `Cp = 0` (outer annulus, by the transverse
lower bound `hζmin`). -/
theorem Cp_le_of_mem_Wp1
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ Bm c.e₁ y → c.e.χ y ∈ c.TubeOpenσ → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {y : Fin n → ℝ}
    (hy : morseNorm n y ≤ c.ρs ∨ (c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ Bm c.e₁ y)) :
    k.Cp y ≤ 1 / 10 := by
  classical
  rcases hy with h | ⟨h1, h2, h3⟩
  · by_cases hT : c.e.χ y ∈ c.TubeOpenσ
    · rw [k.Cp_of_mem hT]
      have hψ := c.ψp_add_ψm (h.trans c.ρs_lt_ρB.le)
      have hψp := c.ψp_ge_of_le_ρs h
      have hβ := k.βm_le_one (c.e.χ y)
      have hβ0 := k.βm_nonneg (c.e.χ y)
      have hm0 := c.ψm_nonneg (c.e.χ y)
      nlinarith
    · rw [k.Cp_of_notMem hT]; norm_num
  · have := k.Cp_eq_zero_of_norm_ζ fun hT => hζmin y (c.ρA_le_ρs.trans h1) h2 h3 hT
    rw [this]; norm_num

/-- `Lp` is non-increasing along `Φ` on the inner region, strictly off the nonnegative axis. -/
theorem LpRate_Vp_nonpos
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ Bm c.e₁ y → c.e.χ y ∈ c.TubeOpenσ → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {y : Fin n → ℝ}
    (hy : morseNorm n y ≤ c.ρs ∨ (c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ Bm c.e₁ y)) :
    c.LpRate y (k.Vp y) ≤ 0 ∧ (c.LpRate y (k.Vp y) = 0 → c.Lp y = 0) := by
  have hyB : morseNorm n y ≤ c.ρB := by
    rcases hy with h | h
    · exact h.trans c.ρs_lt_ρB.le
    · exact h.2.1
  have hy3 := c.sq_lt_three_ε_of_le_ρB hyB
  by_cases hy0 : y = 0
  · subst hy0
    refine ⟨?_, fun _ => ?_⟩
    · unfold LpRate; rw [dot_zero_left, morseNorm_zero, axial_zero]; simp
    · unfold Lp; rw [morseNorm_zero, axial_zero]; ring
  rw [k.LpRate_Vp hy3 hy0]
  have hC := k.Cp_le_of_mem_Wp1 hζmin hy
  have hθ := ModelField.theta_pos c.e.hr₀ y
  have hρ := morseNorm_pos hy0
  have hB : 0 ≤ morseNorm n y - axial c.e₁ y := by
    have := abs_dot_le y c.e₁
    rw [c.morseNorm_e₁, mul_one] at this
    have := (abs_le.1 this).2
    unfold axial; linarith
  have hA : 0 ≤ c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) :=
    mul_nonneg c.m'_pos.le (mul_nonneg (βp_nonneg _) (ψp_nonneg _))
  have hZ : 0 ≤ 2 * (c.lam * k.Bp y) * axial c.e₁ (c.Zp' y) := by
    by_cases hBp : k.Bp y = 0
    · rw [hBp]; simp
    · obtain ⟨hT, hζ⟩ := k.mem_of_Bp_ne_zero hBp
      by_cases hζ0 : c.ζ (c.e.χ y) = 0
      · rw [c.Zp'_eq_zero_of_ζ hT hζ0, axial_zero, mul_zero]
      · have := k.axial_Zp'_pos hy3 hT (norm_pos_iff.2 hζ0) hζ
        have := c.lam_pos
        have := k.Bp_nonneg y
        positivity
  have h1 : 0 ≤ 2 * ((1 - 2 * k.Cp y) * ModelField.theta c.e.r₀ y) * morseNorm n y *
      (morseNorm n y - axial c.e₁ y) := by
    have : 0 < 1 - 2 * k.Cp y := by linarith
    positivity
  have h2 : 0 ≤ c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * (morseNorm n y - axial c.e₁ y) ^ 2 /
      morseNorm n y := by positivity
  have h3 : 0 ≤ 2 * (c.lam * k.Bp y) * axial c.e₁ (c.Zp' y) * morseNorm n y := by positivity
  refine ⟨by linarith, fun h0 => ?_⟩
  have h1' : 2 * ((1 - 2 * k.Cp y) * ModelField.theta c.e.r₀ y) * morseNorm n y *
      (morseNorm n y - axial c.e₁ y) = 0 := by linarith
  have hpos : 0 < 2 * ((1 - 2 * k.Cp y) * ModelField.theta c.e.r₀ y) * morseNorm n y := by
    have : 0 < 1 - 2 * k.Cp y := by linarith
    positivity
  have : morseNorm n y - axial c.e₁ y = 0 := by
    rcases mul_eq_zero.1 h1' with h | h
    · exact absurd h hpos.ne'
    · exact h
  rw [c.Lp_eq, this, mul_zero]

/-- On the nonnegative axis inside the inner ball the axial coordinate strictly increases. -/
theorem axial_Vp_pos_axis {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ c.ρB) :
    0 < axial c.e₁ (k.Vp (a • c.e₁)) := by
  classical
  set y := a • c.e₁ with hy
  have hnorm : morseNorm n y = a := by
    rw [hy, morseNorm_smul_self c.morseNorm_e₁, abs_of_nonneg ha0]
  have hyB : morseNorm n y ≤ c.ρB := by rw [hnorm]; exact ha
  have hy3 := c.sq_lt_three_ε_of_le_ρB hyB
  have hβ : βp k.δ k.τ c.e₁ y = 1 := βp_smul_self c.morseNorm_e₁ k.hδ (by linarith [k.hδ])
  have haxial : axial c.e₁ y = a := axial_smul_self c.morseNorm_e₁ a
  -- the contraction term vanishes on the axis
  have hZ : 2 * (c.lam * k.Bp y) * axial c.e₁ (c.Zp' y) = 0 := by
    by_cases hT : c.e.χ y ∈ c.TubeOpenσ
    · have hζ : c.ζ (c.e.χ y) = 0 := by
        by_cases hr : c.e.r₀ < a
        · exact (c.axis_p_mem_TubeOpenσ hr (by rw [← hnorm]; exact hy3) hT.1.1).2
        · exfalso
          -- points of the axis at radius `≤ r₀` are not in the tube (level too low)
          have hfy := c.f_chart_p (hyB.trans c.ρB_le_R)
          have h1 := hT.1.1.1
          rw [hfy, hnorm] at h1
          have := c.f_p_add_lt_c₁_sub_η
          push Not at hr
          nlinarith [c.e.hr₀]
      rw [c.Zp'_eq_zero_of_ζ hT hζ, axial_zero, mul_zero]
    · rw [c.Zp'_of_notMem hT, axial_zero, mul_zero]
  rw [k.axial_Vp, hZ, add_zero, hβ, one_mul, haxial]
  -- `Cp = βm ψm = ψm` on the axis (`βm = 1` there), and `ψp = 1 - ψm`
  have hψ := c.ψp_add_ψm hyB
  have hCp : k.Cp y = c.ψm (c.e.χ y) := by
    by_cases hT : c.e.χ y ∈ c.TubeOpenσ
    · rw [k.Cp_of_mem hT]
      have hζ : c.ζ (c.e.χ y) = 0 := by
        by_cases hr : c.e.r₀ < a
        · exact (c.axis_p_mem_TubeOpenσ hr (by rw [← hnorm]; exact hy3) hT.1.1).2
        · exfalso
          have hfy := c.f_chart_p (hyB.trans c.ρB_le_R)
          have h1 := hT.1.1.1
          rw [hfy, hnorm] at h1
          have := c.f_p_add_lt_c₁_sub_η
          push Not at hr
          nlinarith [c.e.hr₀]
      rw [k.βm_eq_one_of_ζ_eq_zero hζ, one_mul]
    · rw [k.Cp_of_notMem hT]
      have : c.ψm (c.e.χ y) = 0 := by
        apply c.ψm_eq_zero_of_le
        rw [c.f_chart_p (hyB.trans c.ρB_le_R), hnorm]
        -- not in the tube: either the level is below `c₁ - η` (then `≤ lo₁`) or above; the
        -- axis points in the ball at tube levels are in the tube
        by_contra hlt
        push Not at hlt
        have hr : c.e.r₀ < a := by
          have := c.f_p_add_lt_c₁_sub_η
          unfold lo₁ at hlt
          have hη := c.η_pos
          by_contra hle; push Not at hle
          nlinarith [c.e.hr₀]
        have hlev : f (c.e.χ (a • c.e₁)) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η) := by
          rw [c.f_chart_p (hyB.trans c.ρB_le_R), hnorm]
          have := c.η_pos
          have := c.ρB_sq_eq
          have h2 : a ^ 2 ≤ c.ρB ^ 2 := pow_le_pow_left₀ ha0 ha 2
          have := c.lo₂_lt_hi₁
          unfold lo₁ lo₂ hi₁ at *
          constructor <;> linarith
        exact hT (c.axis_p_mem_TubeOpenσ hr (by rw [← hnorm]; exact hy3) hlev).1
      rw [this]
  rw [hCp]
  have hψp : ψp c.ρA c.ρB y = 1 - c.ψm (c.e.χ y) := by linarith
  rw [hψp]
  rcases ha0.eq_or_lt with h | h
  · rw [← h]
    have := c.m'_pos
    have h0 : c.ψm (c.e.χ y) = 0 := by
      apply c.ψm_eq_zero_of_le
      rw [c.f_chart_p (hyB.trans c.ρB_le_R), hnorm, ← h]
      have := c.f_p_add_lt_c₁_sub_η; have := c.η_pos
      unfold lo₁; nlinarith [sq_nonneg c.e.r₀]
    rw [h0]; norm_num; exact this
  · have hθa : 0 < ModelField.theta c.e.r₀ y * a := mul_pos (ModelField.theta_pos c.e.hr₀ y) h
    have hθm : ModelField.theta c.e.r₀ y * a < c.m' := by rw [← hnorm]; exact c.hm_p y
    have := axis_ineq_p hθa hθm (c.ψm_nonneg (c.e.χ y)) (c.ψm_le_one (c.e.χ y))
    linarith


/-! ### Dynamics on the inner region -/

theorem hasDerivAt_Lp_Φ {x : M} {s : ℝ} (hs : k.Φ s x ∈ c.pBall') :
    HasDerivAt (fun s => c.Lp (c.e.χ.symm (k.Φ s x)))
      (c.LpRate (c.e.χ.symm (k.Φ s x)) (k.Vp (c.e.χ.symm (k.Φ s x)))) s :=
  c.hasDerivAt_Lp_curve (k.hasDerivAt_symm_Φ_p hs)

theorem Wp1_subset_pBall' : k.Wp1 ⊆ c.pBall' := k.Wp1_subset_Wball.trans c.Wball_subset_pBall'
theorem Wp2_subset_pBall' : k.Wp2 ⊆ c.pBall' := k.Wp2_subset_Wball.trans c.Wball_subset_pBall'

/-- **Every trajectory leaves the inner region** (LaSalle with `Lp` and the axial
coordinate). -/
theorem exists_exit_Wp1
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ Bm c.e₁ y → c.e.χ y ∈ c.TubeOpenσ → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖) :
    ∀ x ∈ k.Wp1, ∃ t, 0 ≤ t ∧ k.Φ t x ∉ k.Wp1 := by
  refine k.exists_exit_of_lyapunov_pair k.isCompact_Wp1 (L₁ := fun x => c.Lp (c.e.χ.symm x))
    (L₂ := fun x => axial c.e₁ (c.e.χ.symm x))
    (c.continuous_Lp.comp_continuousOn (c.continuousOn_symm_Wball.mono k.Wp1_subset_Wball))
    ((continuous_axial c.e₁).comp_continuousOn
      (c.continuousOn_symm_Wball.mono k.Wp1_subset_Wball))
    (Z := {x | c.Lp (c.e.χ.symm x) = 0}) ?_ ?_
  · intro x hx
    have hx' := k.Wp1_subset_Wball hx
    have hy := (k.mem_Wp1_iff (c.Wball_subset_image_ball hx')).1 hx
    obtain ⟨h1, h2⟩ := k.LpRate_Vp_nonpos hζmin hy
    have hd := k.hasDerivAt_Lp_Φ (x := x) (s := 0) (by rw [k.Φ_zero]; exact c.Wball_subset_pBall' hx')
    rw [k.Φ_zero] at hd
    exact ⟨_, h1, hd, fun h => h2 h⟩
  · rintro x ⟨hx, hZ⟩
    have hx' := k.Wp1_subset_Wball hx
    have hZ' : c.Lp (c.e.χ.symm x) = 0 := hZ
    obtain ⟨hax, ha0⟩ := (c.Lp_eq_zero_iff _).1 hZ'
    have hρ := c.symm_mem_of_mem_Wball hx'
    have hd := k.hasDerivAt_axial_Φ_p (x := x) (s := 0)
      (by rw [k.Φ_zero]; exact c.Wball_subset_pBall' hx')
    rw [k.Φ_zero] at hd
    refine ⟨_, ?_, hd⟩
    have hnorm : morseNorm n (c.e.χ.symm x) = axial c.e₁ (c.e.χ.symm x) := by
      conv_lhs => rw [hax]
      rw [morseNorm_smul_self c.morseNorm_e₁, abs_of_nonneg ha0]
    have := k.axial_Vp_pos_axis ha0 (by rw [← hnorm]; exact hρ)
    rw [← hax] at this
    exact this

/-- At a point of the outer part of the inner region on the sphere of radius `ρB`, the radius
strictly decreases. -/
theorem dot_Vp_neg_of_sphere
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ Bm c.e₁ y → c.e.χ y ∈ c.TubeOpenσ → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {y : Fin n → ℝ} (hy : morseNorm n y = c.ρB) (hB : k.b₀ ≤ Bm c.e₁ y) :
    dot y (k.Vp y) < 0 := by
  have hy3 : morseNorm n y ^ 2 < 3 * c.ε := by rw [hy]; exact c.ρB_sq_lt_three_ε
  rw [k.dot_Vp hy3]
  have hC : k.Cp y = 0 := k.Cp_eq_zero_of_norm_ζ fun hT =>
    hζmin y (by rw [hy]; exact c.ρA_lt_ρB.le) hy.le hB hT
  have hψ : ψp c.ρA c.ρB y = 0 := ψp_eq_zero c.ρA_pos.le c.ρA_lt_ρB hy.ge
  rw [hC, hψ]
  have hθ := ModelField.theta_pos c.e.hr₀ y
  have : 0 < morseNorm n y := by rw [hy]; exact c.ρB_pos
  simp only [mul_zero, zero_mul, add_zero, sub_zero, one_mul]
  have : 0 < ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 := by positivity
  linarith

/-- **From the inner region to the outer region**: a trajectory starting in `Wp1` stays in the
ball region until it reaches `Wp2`. -/
theorem exists_reach_Wp2
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ Bm c.e₁ y → c.e.χ y ∈ c.TubeOpenσ → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {x : M} (hx : x ∈ k.Wp1) :
    ∃ t, 0 ≤ t ∧ k.Φ t x ∈ k.Wp2 ∧ ∀ s ∈ Icc 0 t, k.Φ s x ∈ c.Wball := by
  obtain ⟨t₀, ht₀, hexit⟩ := k.exists_exit_Wp1 hζmin x hx
  -- while `Wp2` is not hit, the trajectory stays in the ball region
  have hinv : ∀ t, 0 ≤ t → (∀ s ∈ Icc 0 t, k.Φ s x ∉ k.Wp2) →
      ∀ s ∈ Icc 0 t, k.Φ s x ∈ c.Wball := by
    intro t _ hno
    have hQ : IsClosed {s : ℝ | k.Φ s x ∈ c.Wball} :=
      c.isCompact_Wball.isClosed.preimage (k.continuous_Φ_curve x)
    refine Icc_subset_of_isClosed_of_step hQ (by simp [k.Wp1_subset_Wball hx]) fun s hs hIcc => ?_
    have hsW : k.Φ s x ∈ c.Wball := hIcc (right_mem_Icc.2 hs.1)
    have hs1 : k.Φ s x ∈ k.Wp1 := by
      have := (k.Wball_eq_union ▸ hsW : k.Φ s x ∈ k.Wp1 ∪ k.Wp2)
      exact this.resolve_right (hno s ⟨hs.1, hs.2.le⟩)
    have hρ := c.symm_mem_of_mem_Wball hsW
    rcases hρ.lt_or_eq with hlt | heq
    · -- strictly inside: the open ball is a neighbourhood
      have hmem : k.Φ s x ∈ c.e.χ '' {y | morseNorm n y < c.ρB} :=
        c.e.mem_image_of_symm_mem (c.Wball_subset_image_ball hsW) hlt
      obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open c.isOpen_ball_ρB hmem
      refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨s + ε, by simp [hε], fun s' hs' => ?_⟩
      exact c.ball_ρB_subset_Wball (hεO s' ⟨by linarith [hs'.1], hs'.2⟩)
    · -- on the sphere: the radius strictly decreases
      have hB : k.b₀ ≤ Bm c.e₁ (c.e.χ.symm (k.Φ s x)) := by
        rcases (k.mem_Wp1_iff (c.Wball_subset_image_ball hsW)).1 hs1 with h | h
        · exfalso; rw [heq] at h; linarith [c.ρs_lt_ρB]
        · exact h.2.2
      have hd := k.hasDerivAt_morseNormSq_Φ_p (c.Wball_subset_pBall' hsW)
      have hneg := k.dot_Vp_neg_of_sphere hζmin heq hB
      have hev := eventually_lt_of_hasDerivAt_neg (by linarith : 2 * dot (c.e.χ.symm (k.Φ s x))
        (k.Vp (c.e.χ.symm (k.Φ s x))) < 0) hd
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1
        (hev.and (k.exists_Icc_Φ_mem_open c.e.isOpen_image_ball (c.Wball_subset_image_ball hsW)
          |> fun ⟨ε, hε, hεO⟩ => by
            refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨s + ε, by simp [hε], fun s' hs' => ?_⟩
            exact hεO s' ⟨by linarith [hs'.1], hs'.2⟩))
      refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨u, hu, fun s' hs' => ?_⟩
      obtain ⟨h1, h2⟩ := hsub hs'
      rw [heq] at h1
      refine c.e.mem_image_of_symm_mem h2 ?_
      show morseNorm n (c.e.χ.symm (k.Φ s' x)) ≤ c.ρB
      have : morseNorm n (c.e.χ.symm (k.Φ s' x)) ^ 2 < c.ρB ^ 2 := h1
      exact ((pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg _) c.ρB_pos.le two_ne_zero).1
        this).le
  -- the trajectory hits `Wp2`
  have hhit : ∃ s ∈ Icc 0 t₀, k.Φ s x ∈ k.Wp2 := by
    by_contra h
    push Not at h
    have hW := hinv t₀ ht₀ h t₀ (right_mem_Icc.2 ht₀)
    have := (k.Wball_eq_union ▸ hW : k.Φ t₀ x ∈ k.Wp1 ∪ k.Wp2)
    exact hexit (this.resolve_right (h t₀ (right_mem_Icc.2 ht₀)))
  obtain ⟨s₀, hs₀, hs₀W, hmin⟩ := exists_first_time k.isCompact_Wp2.isClosed
    (k.continuous_Φ_curve x) hhit
  refine ⟨s₀, hs₀.1, hs₀W, fun s hs => ?_⟩
  rcases hs.2.eq_or_lt with h | h
  · rw [h]; exact k.Wp2_subset_Wball hs₀W
  · exact hinv s hs.1 (fun u hu => hmin u ⟨hu.1, hu.2.trans_lt h⟩) s (right_mem_Icc.2 hs.1)


end CancelConsts

/-! ### Dynamics on the outer region -/

/-- An open neighbourhood of the annulus inside `pBall'`, away from `p`. -/
def Op : Set M := c.e.χ '' {y | c.ρs / 2 < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε}

theorem isOpen_Op : IsOpen c.Op := by
  refine (OpenPartialHomeomorph.isOpen_image_iff_of_subset_source c.e.χ fun y hy => ?_).2 ?_
  · exact c.e.hball (c.mem_ball_p_of_sq_lt hy.2)
  · exact (isOpen_lt continuous_const continuous_morseNorm).inter
      (isOpen_lt (continuous_morseNorm.pow 2) continuous_const)

theorem Op_subset_pBall' : c.Op ⊆ c.pBall' := image_mono fun _ hy => hy.2

theorem symm_ne_zero_of_mem_Op {x : M} (hx : x ∈ c.Op) : c.e.χ.symm x ≠ 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' hy.2]
  rintro rfl
  have := hy.1; rw [morseNorm_zero] at this; linarith [c.ρs_pos]

theorem symm_sq_lt_of_mem_Op {x : M} (hx : x ∈ c.Op) : morseNorm n (c.e.χ.symm x) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' hy.2]; exact hy.2

/-- The open annulus `{ρs < ‖y‖, ‖y‖² < 3ε}`. -/
theorem isOpen_annulus_gt :
    IsOpen (c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε}) := by
  refine (OpenPartialHomeomorph.isOpen_image_iff_of_subset_source c.e.χ fun y hy => ?_).2 ?_
  · exact c.e.hball (c.mem_ball_p_of_sq_lt hy.2)
  · exact (isOpen_lt continuous_const continuous_morseNorm).inter
      (isOpen_lt (continuous_morseNorm.pow 2) continuous_const)

namespace CancelConsts

variable {c} (k : c.CancelConsts)

theorem Wp2_subset_Op : k.Wp2 ⊆ c.Op := image_mono fun y hy => by
  show c.ρs / 2 < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε
  have h1 : c.ρs ≤ morseNorm n y := hy.1
  exact ⟨by have := c.ρs_pos; linarith, c.sq_lt_three_ε_of_le_ρB hy.2.1⟩

/-- On the outer region: `βp = 1`, tube membership, `‖ζ‖ < δ'`, and `Bp > 0`. -/
theorem Bp_pos_of_mem_Wp2 {y : Fin n → ℝ} (hy1 : c.ρs ≤ morseNorm n y)
    (hy2 : morseNorm n y ≤ c.ρB) (hB : Bm c.e₁ y ≤ k.b₀) : 0 < k.Bp y := by
  obtain ⟨hT, hζ⟩ := k.mem_tube_of_Bm_le hy1 hy2 hB
  rw [k.Bp_of_mem hT]
  have hβ : 0 < k.βm' (c.e.χ y) := by
    apply cut_pos_of_lt k.two_δ_sq_lt_δ'_sq
    exact pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero
  have hψ : c.ψm' (c.e.χ y) = 1 := by
    apply c.ψm'_eq_one
    · rw [c.f_chart_p (hy2.trans c.ρB_le_R)]
      have h1 := c.ρA_sq_eq
      have h2 : c.ρA ^ 2 ≤ morseNorm n y ^ 2 :=
        pow_le_pow_left₀ c.ρA_pos.le (c.ρA_le_ρs.trans hy1) 2
      linarith
    · rw [c.f_chart_p (hy2.trans c.ρB_le_R)]
      have h1 := c.ρB_sq_eq
      have h2 : morseNorm n y ^ 2 ≤ c.ρB ^ 2 := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy2 2
      have := c.lo₂_lt_hi₁; have := c.hi₁_lt_hi₂
      linarith
  rw [hψ, mul_one]; exact hβ

/-- On the outer region, `dBm (Vp) = 0` only on the positive axis. -/
theorem axis_of_BmDeriv_Vp_eq_zero {y : Fin n → ℝ} (hy1 : c.ρs ≤ morseNorm n y)
    (hy2 : morseNorm n y ≤ c.ρB) (hB : Bm c.e₁ y ≤ k.b₀)
    (h : BmDeriv c.e₁ y (k.Vp y) = 0) : y = morseNorm n y • c.e₁ := by
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [morseNorm_zero] at hy1; linarith [c.ρs_pos]
  obtain ⟨-, h2⟩ := k.of_BmDeriv_Vp_eq_zero (c.sq_lt_three_ε_of_le_ρB hy2) hy0 h
  rcases h2 with h2 | ⟨hT, hζ⟩
  · exact absurd h2 (k.Bp_pos_of_mem_Wp2 hy1 hy2 hB).ne'
  · exact (c.axis_of_ζ_eq_zero_p (c.sq_lt_three_ε_of_le_ρB hy2) hT hζ).1

/-- **Every trajectory leaves the outer region** (LaSalle with `Bm` and the axial coordinate). -/
theorem exists_exit_Wp2 : ∀ x ∈ k.Wp2, ∃ t, 0 ≤ t ∧ k.Φ t x ∉ k.Wp2 := by
  refine k.exists_exit_of_lyapunov_pair k.isCompact_Wp2 (L₁ := fun x => Bm c.e₁ (c.e.χ.symm x))
    (L₂ := fun x => axial c.e₁ (c.e.χ.symm x))
    (c.continuousOn_Bm_annulus.comp (c.continuousOn_symm_Wball.mono k.Wp2_subset_Wball)
      fun x hx => ((k.mem_Wp2_iff (c.Wball_subset_image_ball (k.Wp2_subset_Wball hx))).1 hx).1)
    ((continuous_axial c.e₁).comp_continuousOn
      (c.continuousOn_symm_Wball.mono k.Wp2_subset_Wball))
    (Z := {x | c.e.χ.symm x = morseNorm n (c.e.χ.symm x) • c.e₁}) ?_ ?_
  · intro x hx
    have hx' := k.Wp2_subset_Wball hx
    obtain ⟨h1, h2, h3⟩ := (k.mem_Wp2_iff (c.Wball_subset_image_ball hx')).1 hx
    have hy0 : c.e.χ.symm x ≠ 0 := c.symm_ne_zero_of_mem_Op (k.Wp2_subset_Op hx)
    have hd := k.hasDerivAt_Bm_Φ_p (x := x) (s := 0)
      (by rw [k.Φ_zero]; exact c.Wball_subset_pBall' hx') (by rw [k.Φ_zero]; exact hy0)
    rw [k.Φ_zero] at hd
    exact ⟨_, k.BmDeriv_Vp_nonpos (c.sq_lt_three_ε_of_le_ρB h2) hy0, hd,
      fun h => k.axis_of_BmDeriv_Vp_eq_zero h1 h2 h3 h⟩
  · rintro x ⟨hx, hZ⟩
    have hx' := k.Wp2_subset_Wball hx
    have hZ' : c.e.χ.symm x = morseNorm n (c.e.χ.symm x) • c.e₁ := hZ
    have hρ := c.symm_mem_of_mem_Wball hx'
    have hd := k.hasDerivAt_axial_Φ_p (x := x) (s := 0)
      (by rw [k.Φ_zero]; exact c.Wball_subset_pBall' hx')
    rw [k.Φ_zero] at hd
    refine ⟨_, ?_, hd⟩
    have := k.axial_Vp_pos_axis (ModelField.morseNorm_nonneg (c.e.χ.symm x)) hρ
    rw [← hZ'] at this
    exact this

/-- At the inner sphere of the outer region, the radius strictly increases. -/
theorem dot_Vp_pos_of_inner_sphere {y : Fin n → ℝ} (hy : morseNorm n y = c.ρs)
    (hB : Bm c.e₁ y ≤ k.b₀) : 0 < dot y (k.Vp y) := by
  have hy3 : morseNorm n y ^ 2 < 3 * c.ε := c.sq_lt_three_ε_of_le_ρB (hy ▸ c.ρs_lt_ρB.le)
  rw [k.dot_Vp hy3, k.βp_eq_one_of_Bm_le hy.ge hB]
  obtain ⟨hapos, hsq, -⟩ := k.of_Bm_le hy.ge hB
  have hψ := c.ψp_ge_of_le_ρs hy.le
  have hθ := c.theta_mul_lt_third hy.ge
  have hθ0 := ModelField.theta_pos c.e.hr₀ y
  have hρ : 0 < morseNorm n y := hy ▸ c.ρs_pos
  have hC0 := k.Cp_nonneg y
  have hb := k.b₀_le
  have hm := c.m'_pos
  have h1b : 0 < 1 - k.b₀ := by linarith
  have ha' : (1 - k.b₀) * morseNorm n y ≤ axial c.e₁ y :=
    (pow_le_pow_iff_left₀ (by positivity) hapos.le two_ne_zero).1 (by rw [mul_pow]; exact hsq)
  have h1 : (1 - 2 * k.Cp y) * (ModelField.theta c.e.r₀ y * morseNorm n y ^ 2) ≤
      ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 := by
    have : 0 ≤ ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 := by positivity
    nlinarith
  have h2 : ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 < c.m' / 3 * morseNorm n y := by
    have : ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 =
        (ModelField.theta c.e.r₀ y * morseNorm n y) * morseNorm n y := by ring
    rw [this]; exact mul_lt_mul_of_pos_right hθ hρ
  have h3 : c.m' * (9 / 10) * ((1 - k.b₀) * morseNorm n y) ≤
      c.m' * (1 * ψp c.ρA c.ρB y) * axial c.e₁ y := by
    rw [one_mul]
    have := mul_le_mul hψ ha' (by positivity) (ψp_nonneg _)
    have := mul_le_mul_of_nonneg_left this hm.le
    linarith
  have h4 : c.m' * (9 / 10) * (15 / 16 * morseNorm n y) ≤
      c.m' * (9 / 10) * ((1 - k.b₀) * morseNorm n y) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hρ.le
    linarith
  nlinarith

/-- **From the outer region to the middle band**: a trajectory starting in `Wp2` stays in
`Wp2` until it reaches the sphere of radius `ρB`, where it lies in the middle band at the level
`lo₂`. -/
theorem exists_reach_Tmid_of_mem_Wp2 {x : M} (hx : x ∈ k.Wp2) :
    ∃ t, 0 ≤ t ∧ k.Φ t x ∈ k.Tmid ∧ f (k.Φ t x) = c.lo₂ ∧ ∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Wp2 := by
  obtain ⟨t₀, ht₀, hexit⟩ := k.exists_exit_Wp2 x hx
  set Ob : Set M := c.e.χ '' {y | morseNorm n y < c.ρB} with hOb
  have hOb_symm : ∀ {z : M}, z ∈ Ob → morseNorm n (c.e.χ.symm z) < c.ρB := by
    rintro z ⟨y, hy, rfl⟩
    rw [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB (le_of_lt hy))]; exact hy
  -- while the radius stays below `ρB`, the trajectory stays in `Wp2`
  have hinv : ∀ t, 0 ≤ t → (∀ s ∈ Icc 0 t, k.Φ s x ∈ Ob) →
      ∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Wp2 := by
    intro t _ hlt
    have hQ : IsClosed {s : ℝ | k.Φ s x ∈ k.Wp2} :=
      k.isCompact_Wp2.isClosed.preimage (k.continuous_Φ_curve x)
    refine Icc_subset_of_isClosed_of_step hQ (by simp [hx]) fun s hs hIcc => ?_
    have hsW : k.Φ s x ∈ k.Wp2 := hIcc (right_mem_Icc.2 hs.1)
    have hsWb := k.Wp2_subset_Wball hsW
    have hsO := k.Wp2_subset_Op hsW
    obtain ⟨h1, h2, h3⟩ := (k.mem_Wp2_iff (c.Wball_subset_image_ball hsWb)).1 hsW
    obtain ⟨ε₁, hε₁, hO⟩ := k.exists_Icc_Φ_mem_open c.isOpen_Op hsO
    -- eventually the radius is `≥ ρs`
    have hev₁ : ∀ᶠ s' in 𝓝[>] s, c.ρs ≤ morseNorm n (c.e.χ.symm (k.Φ s' x)) := by
      rcases h1.lt_or_eq with hlt' | heq
      · have hmem : k.Φ s x ∈ c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε} :=
          c.e.mem_image_of_symm_mem (c.Wball_subset_image_ball hsWb)
            ⟨hlt', c.sq_lt_three_ε_of_le_ρB h2⟩
        obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open c.isOpen_annulus_gt hmem
        refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨s + ε, by simp [hε], fun s' hs' => ?_⟩
        obtain ⟨y, hy, hyx⟩ := hεO s' ⟨by linarith [hs'.1], hs'.2⟩
        show c.ρs ≤ morseNorm n (c.e.χ.symm (k.Φ s' x))
        rw [← hyx, c.chart_p_symm_eq' hy.2]; exact hy.1.le
      · have hd := k.hasDerivAt_morseNormSq_Φ_p (c.Wball_subset_pBall' hsWb)
        have hpos := k.dot_Vp_pos_of_inner_sphere heq.symm h3
        have := eventually_gt_of_hasDerivAt_pos (by linarith : 0 < 2 * dot (c.e.χ.symm (k.Φ s x))
          (k.Vp (c.e.χ.symm (k.Φ s x)))) hd
        filter_upwards [this] with s' hs'
        show c.ρs ≤ morseNorm n (c.e.χ.symm (k.Φ s' x))
        have : c.ρs ^ 2 < morseNorm n (c.e.χ.symm (k.Φ s' x)) ^ 2 := by rw [heq]; exact hs'
        exact ((pow_lt_pow_iff_left₀ c.ρs_pos.le (ModelField.morseNorm_nonneg _) two_ne_zero).1
          this).le
    obtain ⟨u₁, hu₁, hsub₁⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev₁
    refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (min u₁ (s + ε₁)) t,
      lt_min (lt_min hu₁ (by linarith)) hs.2, fun s' hs' => ?_⟩
    have hs'u : s' ≤ u₁ := hs'.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hs'ε : s' ≤ s + ε₁ := hs'.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hs't : s' ≤ t := hs'.2.trans (min_le_right _ _)
    have hOp : ∀ u ∈ Icc s s', k.Φ u x ∈ c.Op := fun u hu =>
      hO u ⟨by linarith [hu.1], hu.2.trans hs'ε⟩
    -- `Bm` is antitone on `[s, s']`
    have hanti : AntitoneOn (fun u => Bm c.e₁ (c.e.χ.symm (k.Φ u x))) (Icc s s') := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc s s') ?_ ?_ ?_
      · intro u hu
        exact (k.hasDerivAt_Bm_Φ_p (c.Op_subset_pBall' (hOp u hu))
          (c.symm_ne_zero_of_mem_Op (hOp u hu))).continuousAt.continuousWithinAt
      · intro u hu
        have hu' := interior_subset hu
        exact (k.hasDerivAt_Bm_Φ_p (c.Op_subset_pBall' (hOp u hu'))
          (c.symm_ne_zero_of_mem_Op (hOp u hu'))).differentiableAt.differentiableWithinAt
      · intro u hu
        have hu' := interior_subset hu
        rw [(k.hasDerivAt_Bm_Φ_p (c.Op_subset_pBall' (hOp u hu'))
          (c.symm_ne_zero_of_mem_Op (hOp u hu'))).deriv]
        exact k.BmDeriv_Vp_nonpos (c.symm_sq_lt_of_mem_Op (hOp u hu'))
          (c.symm_ne_zero_of_mem_Op (hOp u hu'))
    have hB' := hanti (left_mem_Icc.2 hs'.1.le) (right_mem_Icc.2 hs'.1.le) hs'.1.le
    have hs'O := hOp s' (right_mem_Icc.2 hs'.1.le)
    refine (k.mem_Wp2_iff (c.pBall'_subset_image_ball (c.Op_subset_pBall' hs'O))).2
      ⟨hsub₁ ⟨hs'.1, hs'u⟩, (hOb_symm (hlt s' ⟨hs.1.trans hs'.1.le, hs't⟩)).le, hB'.trans h3⟩
  -- the trajectory leaves the open ball region
  have hhit : ∃ s ∈ Icc 0 t₀, k.Φ s x ∈ Obᶜ := by
    by_contra h
    push Not at h
    exact hexit (hinv t₀ ht₀ (fun s hs => not_not.1 (h s hs)) t₀ (right_mem_Icc.2 ht₀))
  obtain ⟨s₀, hs₀, hs₀E, hmin⟩ := exists_first_time c.isOpen_ball_ρB.isClosed_compl
    (k.continuous_Φ_curve x) hhit
  have hbefore : ∀ s ∈ Ico 0 s₀, k.Φ s x ∈ k.Wp2 := fun s hs =>
    hinv s hs.1 (fun u hu => not_not.1 (hmin u ⟨hu.1, hu.2.trans_lt hs.2⟩)) s
      (right_mem_Icc.2 hs.1)
  have hs₀W : k.Φ s₀ x ∈ k.Wp2 := by
    rcases hs₀.1.eq_or_lt with h | h
    · rw [← h, k.Φ_zero]; exact hx
    · refine k.isCompact_Wp2.isClosed.mem_of_tendsto
        ((k.continuous_Φ_curve x).continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Iio s₀))) ?_
      filter_upwards [Ico_mem_nhdsLT h] with s hs using hbefore s hs
  have hall : ∀ s ∈ Icc 0 s₀, k.Φ s x ∈ k.Wp2 := fun s hs => by
    rcases hs.2.eq_or_lt with h | h
    · rw [h]; exact hs₀W
    · exact hbefore s ⟨hs.1, h⟩
  -- the radius at the exit is exactly `ρB`
  have hs₀Wb := k.Wp2_subset_Wball hs₀W
  obtain ⟨h1, h2, h3⟩ := (k.mem_Wp2_iff (c.Wball_subset_image_ball hs₀Wb)).1 hs₀W
  have hρ : morseNorm n (c.e.χ.symm (k.Φ s₀ x)) = c.ρB := by
    refine le_antisymm h2 ?_
    by_contra hlt
    push Not at hlt
    exact hs₀E (c.e.mem_image_of_symm_mem (c.Wball_subset_image_ball hs₀Wb) hlt)
  set y := c.e.χ.symm (k.Φ s₀ x) with hy
  have hχy : c.e.χ y = k.Φ s₀ x := c.e.symm_image_eq (c.Wball_subset_image_ball hs₀Wb)
  have hf : f (k.Φ s₀ x) = c.lo₂ := by
    rw [← hχy, c.f_chart_p (h2.trans c.ρB_le_R), hρ, c.ρB_sq_eq]; ring
  obtain ⟨hT, hζ⟩ := k.mem_tube_of_Bm_le h1 h2 h3
  rw [hχy] at hT hζ
  refine ⟨s₀, hs₀.1, ⟨k.mem_Sσ_iff.2 ⟨hT, ⟨?_, ?_⟩, hζ.le⟩, hf.ge, ?_⟩, hf, hall⟩
  · rw [hf]; exact c.lo₂_mem_levels
  · rw [hf]; linarith [c.lo₂_lt_hi₁, c.hi₁_mem_levels]
  · rw [hf]; exact c.lo₂_lt_hi₁.le

/-- **The ball of `p` feeds the middle band**: every trajectory starting in the ball region of
radius `ρB` reaches the middle band at the level `lo₂`. -/
theorem exists_reach_Tmid_of_mem_Wball
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ Bm c.e₁ y → c.e.χ y ∈ c.TubeOpenσ → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {x : M} (hx : x ∈ c.Wball) :
    ∃ t, 0 ≤ t ∧ k.Φ t x ∈ k.Tmid ∧ f (k.Φ t x) = c.lo₂ ∧ ∀ s ∈ Icc 0 t, k.Φ s x ∈ c.Wball := by
  have hx' := (k.Wball_eq_union ▸ hx : x ∈ k.Wp1 ∪ k.Wp2)
  rcases hx' with hx1 | hx2
  · obtain ⟨t₁, ht₁, hW2, hball⟩ := k.exists_reach_Wp2 hζmin hx1
    obtain ⟨t₂, ht₂, hT, hf, hW⟩ := k.exists_reach_Tmid_of_mem_Wp2 hW2
    refine ⟨t₁ + t₂, by positivity, by rw [k.Φ_add]; exact hT, by rw [k.Φ_add]; exact hf,
      fun s hs => ?_⟩
    rcases le_or_gt s t₁ with h | h
    · exact hball s ⟨hs.1, h⟩
    · have := hW (s - t₁) ⟨by linarith, by linarith [hs.2]⟩
      rw [k.Φ_Φ, add_sub_cancel] at this
      exact k.Wp2_subset_Wball this
  · obtain ⟨t₂, ht₂, hT, hf, hW⟩ := k.exists_reach_Tmid_of_mem_Wp2 hx2
    exact ⟨t₂, ht₂, hT, hf, fun s hs => k.Wp2_subset_Wball (hW s hs)⟩

end CancelConsts

end CancelData

end GradientLikeStrip

end

end PoincareHighDim
