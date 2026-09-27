import Submission.Morse.Cancellation.Flow.CancelFlowTools

/-!
# Cancellation, step C4c (constants): the `Good` hypotheses and the transported angle

For `k : c.CancelConsts` this module provides

* the derived constants `Q' = δ'² (2ε₂ + δ'²)`, `νm² = Q' / (2ε₂ - η)`,
  `ν² = νm² + τ² uB² + 2δ²` bounding the `v`-coordinate in the region of `q`;
* the structure `CancelConsts.Good` of the additional smallness hypotheses on the constants
  used by the forward completion (`CancelFlowExit`): the holonomy radius `δ''` (transport of
  the transverse coordinate into the ball of `p`, with the angular derivative estimate
  `hLσ`), the smallness `8δ'² ≤ ε`, the transverse lower bound `hζmin` on the annulus outside
  the angular threshold, the radius bound `hδq` of the region of `q`, and the terminal descent
  `harm` of the other arm (a neighbourhood of `z₁` in the level `f q - ε` descends to the
  level `a'` avoiding the modification region);
* the **transported angle** `Lσ v = Bm (Gσ v)` with its derivative (`hasFDerivAt_Lσ`), the
  radial monotonicity `Lσ_smul_le` / `Lσ_smul_lt` (strict), and the annulus identity
  `Lσ_eq_Bm` (`Lσ (ζ x) = Bm (χ_p.symm x)` on the tube inside the ball of `p`);
* the inclusions `Sσ_subset_basin` and `Sσ_low_subset_Wball` (the support set of the tube
  piece below the level `lo₂` lies in the ball region of `p`).

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

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace CancelData

variable [DecidableEq M] {a' b' : ℝ} {p q : M} (c : CancelData I f a' b' p q)

/-! ### A bound for `θ` on the chart balls -/

theorem exists_theta_le_q : ∃ Kθ : ℝ, 0 ≤ Kθ ∧ ∀ y : Fin n → ℝ, morseNorm n y ^ 2 ≤ 3 * c.ε →
    ModelField.theta c.d.r₀ y ≤ Kθ := by
  obtain ⟨C, hC⟩ := (isCompact_morseNorm_le (Real.sqrt (3 * c.ε))).exists_bound_of_continuousOn
    (ModelField.continuous_theta c.d.hr₀).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  have := hC y (Real.le_sqrt_of_sq_le hy)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

theorem two_ε₂_sub_η_pos : 0 < 2 * c.ε₂ - c.η := by
  have := c.ε₂_sub_η_pos; have := c.ε₂_pos; linarith

/-! ### The transported angle -/

/-- The transported angle: the angular function `Bm` of the ball of `p` evaluated at the
holonomy image of the transverse coordinate. -/
def Lσ (v : EuclideanSpace ℝ (Fin (n - c.d.k))) : ℝ := Bm c.e₁ (c.Gσ v)

theorem Lσ_zero : c.Lσ 0 = 0 := by
  unfold Lσ
  rw [c.Gσ_zero, Bm_smul_self c.morseNorm_e₁ (Real.sqrt_pos.2 (by linarith [c.ε₁_pos]))]

theorem Lσ_nonneg (v : EuclideanSpace ℝ (Fin (n - c.d.k))) : 0 ≤ c.Lσ v :=
  Bm_nonneg c.morseNorm_e₁ _

namespace CancelConsts

variable {c} (k : c.CancelConsts)

/-! ### Derived constants -/

/-- `Q' = g(δ')` where `g(s) = s² (2ε₂ + s²)` is the conserved product `u² ‖v‖²` of a tube
point with `‖ζ‖ = s`. -/
def Q' : ℝ := k.δ' ^ 2 * (2 * c.ε₂ + k.δ' ^ 2)

theorem Q'_pos : 0 < k.Q' := by
  unfold Q'; have := k.δ'_pos; have := c.ε₂_pos; positivity

/-- The bound for `‖v‖` on the upper part of the support set of the tube piece. -/
def νm : ℝ := Real.sqrt (k.Q' / (2 * c.ε₂ - c.η))

theorem νm_sq : k.νm ^ 2 = k.Q' / (2 * c.ε₂ - c.η) :=
  Real.sq_sqrt (div_nonneg k.Q'_pos.le c.two_ε₂_sub_η_pos.le)

theorem νm_nonneg : 0 ≤ k.νm := Real.sqrt_nonneg _

/-- The bound for `‖v‖` on the region of `q`. -/
def ν : ℝ := Real.sqrt (k.νm ^ 2 + k.τ ^ 2 * c.uB ^ 2 + 2 * k.δ ^ 2)

theorem ν_sq : k.ν ^ 2 = k.νm ^ 2 + k.τ ^ 2 * c.uB ^ 2 + 2 * k.δ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem ν_pos : 0 < k.ν := Real.sqrt_pos.2 (by have := k.hδ; positivity)

theorem νm_le_ν : k.νm ≤ k.ν := by
  rw [← Real.sqrt_sq k.νm_nonneg]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg k.τ, sq_nonneg c.uB, sq_nonneg k.δ])

/-! ### The additional hypotheses on the constants -/

/-- **The additional smallness hypotheses on the constants** used by the forward completion of
the cancellation dynamics. All of them are obtainable by shrinking the constants
(`exists_good`); they are collected here as explicit hypotheses. -/
structure Good where
  /-- the holonomy radius: the transverse coordinates of norm `< δ''` transport into the ball
  of `p` -/
  δ'' : ℝ
  hδ'δ'' : k.δ' < δ''
  hδ''ε : δ'' ^ 2 < c.ε
  hHσ : ∀ v : EuclideanSpace ℝ (Fin (n - c.d.k)), ‖v‖ < δ'' →
    ‖v‖ ^ 2 < c.ε ∧ c.Hσ v ∈ c.pBall' ∧ 0 < axial c.e₁ (c.Gσ v)
  /-- the angular derivative estimate along the transported direction -/
  hLσ : ∀ v : EuclideanSpace ℝ (Fin (n - c.d.k)), v ≠ 0 → ‖v‖ < δ'' →
    BmDeriv c.e₁ (c.Gσ v) (c.Zp (c.Gσ v)) < 0
  hδ'8 : 8 * k.δ' ^ 2 ≤ c.ε
  /-- the transverse lower bound on the annulus outside the angular threshold -/
  hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
    k.b₀ ≤ Bm c.e₁ y → c.e.χ y ∈ c.TubeOpenσ → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖
  /-- the radius bound of the region of `q` -/
  hδq : 4 * k.δ ^ 2 < 3 * c.ε - (1 + 2 * k.τ ^ 2) * c.uB ^ 2 - 2 * k.νm ^ 2
  /-- the terminal descent of the other arm: the level-`(f q - ε)` points on the side of
  `z₁` with small conserved product descend to the level `a'` avoiding `K` -/
  ρ₁ : ℝ
  T₂ : ℝ
  hρ₁ : 0 < ρ₁
  hT₂ : 0 ≤ T₂
  harm : ∀ y : Fin n → ℝ, morseNormalForm c.d.hk (f q) y = f q - c.ε →
    c.σ * uq c.d.hk c.hkq y < 0 →
    4 * (‖negPart c.d.hk y‖ ^ 2 * ‖posPart c.d.hk y‖ ^ 2) ≤ ρ₁ ^ 4 →
    (∀ s ∈ Icc 0 T₂, c.D.flow s (c.d.χ y) ∉ k.K) ∧ f (c.D.flow T₂ (c.d.χ y)) < a'
  hδarm : 16 * k.δ ^ 2 * k.ν ^ 2 ≤ ρ₁ ^ 4

namespace Good

variable {k}

theorem δ''_pos (hk : k.Good) : 0 < hk.δ'' := k.δ'_pos.trans hk.hδ'δ''

theorem δ'_lt_δ'' (hk : k.Good) : k.δ' < hk.δ'' := hk.hδ'δ''

/-- The radius bound of the region of `q`: `uB² + 2ν² < 3ε`. -/
theorem uB_sq_add_two_ν_sq_lt (hk : k.Good) : c.uB ^ 2 + 2 * k.ν ^ 2 < 3 * c.ε := by
  rw [k.ν_sq]; have := hk.hδq; nlinarith

theorem ν_sq_lt_ε (hk : k.Good) : k.ν ^ 2 < c.ε := by
  have h1 := hk.uB_sq_add_two_ν_sq_lt
  have h2 := c.uB_sq
  have h3 : c.ε / 2 ≤ c.ε₂ := by unfold ε₂; nlinarith [sq_nonneg c.d.r₀]
  have h4 := c.η_pos
  nlinarith

/-- `‖v‖ ≤ ν` and `f ≥ hi₁` put a chart point of `q` inside the ball `qBall'`. -/
theorem sq_lt_three_ε_of_le_ν (hk : k.Good) {y : Fin n → ℝ} (hv : ‖posPart c.d.hk y‖ ≤ k.ν)
    (hyR : morseNorm n y ≤ c.d.R) (hf : c.hi₁ ≤ f (c.d.χ y)) :
    morseNorm n y ^ 2 < 3 * c.ε := by
  have h1 := c.f_chart_q hyR
  have h2 := morseNorm_sq_eq_uq c.d.hk c.hkq y
  have h3 := c.uB_sq_eq
  have h4 := hk.uB_sq_add_two_ν_sq_lt
  have h5 : ‖posPart c.d.hk y‖ ^ 2 ≤ k.ν ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
  nlinarith

/-! ### The transported angle: derivative and radial monotonicity -/

theorem hHσ' (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ < hk.δ'') :
    ‖v‖ ^ 2 < c.ε ∧ c.Hσ v ∈ c.pBall' := ⟨(hk.hHσ v hv).1, (hk.hHσ v hv).2.1⟩

theorem hasFDerivAt_Lσ (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ < hk.δ'') :
    HasFDerivAt c.Lσ ((BmDeriv c.e₁ (c.Gσ v)).comp (fderiv ℝ c.Gσ v)) v := by
  obtain ⟨hv2, hH⟩ := hk.hHσ' hv
  have hG : HasFDerivAt c.Gσ (fderiv ℝ c.Gσ v) v :=
    ((c.contDiffAt_Gσ hv2 (c.pBall'_subset_image_ball hH)).differentiableAt
      (by simp)).hasFDerivAt
  exact (hasFDerivAt_Bm c.e₁ (c.Gσ_ne_zero hv2 hH)).comp v hG

theorem continuousAt_Lσ (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ < hk.δ'') :
    ContinuousAt c.Lσ v :=
  (hk.hasFDerivAt_Lσ hv).continuousAt

/-- The radial derivative of the transported angle is positive off `0`. -/
theorem fderiv_Lσ_self_pos (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv0 : v ≠ 0)
    (hv : ‖v‖ < hk.δ'') : 0 < fderiv ℝ c.Lσ v v := by
  obtain ⟨hv2, hH⟩ := hk.hHσ' hv
  rw [(hk.hasFDerivAt_Lσ hv).fderiv, ContinuousLinearMap.comp_apply]
  have hdiff : DifferentiableAt ℝ c.Gσ v :=
    (c.contDiffAt_Gσ hv2 (c.pBall'_subset_image_ball hH)).differentiableAt (by simp)
  have hZ := c.Zp_Gσ hv2 hH hdiff
  have hneg := hk.hLσ v hv0 hv
  rw [hZ, map_neg] at hneg
  linarith

theorem fderiv_Lσ_self_nonneg (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))}
    (hv : ‖v‖ < hk.δ'') : 0 ≤ fderiv ℝ c.Lσ v v := by
  by_cases hv0 : v = 0
  · subst hv0; simp
  · exact (hk.fderiv_Lσ_self_pos hv0 hv).le

/-- The derivative of `r ↦ Lσ (r • v)`. -/
theorem hasDerivAt_Lσ_smul (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))}
    (hv : ‖v‖ < hk.δ'') {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    HasDerivAt (fun r : ℝ => c.Lσ (r • v)) (fderiv ℝ c.Lσ (r • v) v) r := by
  have hrv : ‖r • v‖ < hk.δ'' := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    nlinarith [norm_nonneg v]
  have h1 : HasDerivAt (fun r : ℝ => r • v) v r := by
    simpa using (hasDerivAt_id r).smul_const v
  have := (hk.hasFDerivAt_Lσ hrv).comp_hasDerivAt r h1
  rw [(hk.hasFDerivAt_Lσ hrv).fderiv]
  exact this

theorem fderiv_Lσ_smul_nonneg (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))}
    (hv : ‖v‖ < hk.δ'') {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : 0 ≤ fderiv ℝ c.Lσ (r • v) v := by
  have hrv : ‖r • v‖ < hk.δ'' := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0.le]
    nlinarith [norm_nonneg v]
  have h := hk.fderiv_Lσ_self_nonneg hrv
  rw [map_smul, smul_eq_mul] at h
  exact nonneg_of_mul_nonneg_right h hr0

theorem fderiv_Lσ_smul_pos (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv0 : v ≠ 0)
    (hv : ‖v‖ < hk.δ'') {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    0 < fderiv ℝ c.Lσ (r • v) v := by
  have hrv : ‖r • v‖ < hk.δ'' := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0.le]
    nlinarith [norm_nonneg v]
  have h := hk.fderiv_Lσ_self_pos (smul_ne_zero hr0.ne' hv0) hrv
  rw [map_smul, smul_eq_mul] at h
  exact pos_of_mul_pos_right h hr0.le

/-- **Radial monotonicity of the transported angle**: `Lσ (a • v) ≤ Lσ v` for `0 < a ≤ 1`. -/
theorem Lσ_smul_le (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ < hk.δ'')
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) : c.Lσ (a • v) ≤ c.Lσ v := by
  have hmono : MonotoneOn (fun r : ℝ => c.Lσ (r • v)) (Icc a 1) := by
    refine monotoneOn_Icc_of_hasDerivAt_nonneg
      (g' := fun r => fderiv ℝ c.Lσ (r • v) v) (fun r hr => ?_) (fun r hr => ?_)
    · exact hk.hasDerivAt_Lσ_smul hv (ha0.le.trans hr.1) hr.2
    · exact hk.fderiv_Lσ_smul_nonneg hv (ha0.trans_le hr.1) hr.2
  have := hmono (left_mem_Icc.2 ha1) (right_mem_Icc.2 ha1) ha1
  simpa using this

/-- Strict radial monotonicity off `0`. -/
theorem Lσ_smul_lt (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv0 : v ≠ 0)
    (hv : ‖v‖ < hk.δ'') {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : c.Lσ (a • v) < c.Lσ v := by
  have hmono : StrictMonoOn (fun r : ℝ => c.Lσ (r • v)) (Icc a 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a 1) ?_ ?_
    · intro r hr
      exact (hk.hasDerivAt_Lσ_smul hv (ha0.le.trans hr.1) hr.2).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      rw [(hk.hasDerivAt_Lσ_smul hv (ha0.le.trans hr.1.le) hr.2.le).deriv]
      exact hk.fderiv_Lσ_smul_pos hv0 hv (ha0.trans hr.1) hr.2.le
  have := hmono (left_mem_Icc.2 ha1.le) (right_mem_Icc.2 ha1.le) ha1
  simpa using this

/-! ### The annulus identity -/

/-- **The transported angle of a tube point in the ball of `p` is its angle**:
`Lσ (ζ x) = Bm (χ_p.symm x)`. -/
theorem Lσ_eq_Bm (hk : k.Good) {x : M} (hx : x ∈ c.pBall') (hT : x ∈ c.TubeOpenσ)
    (hζ : ‖c.ζ x‖ < hk.δ'') : c.Lσ (c.ζ x) = Bm c.e₁ (c.e.χ.symm x) := by
  obtain ⟨hv2, hH⟩ := hk.hHσ' hζ
  have hHσ := c.Hσ_ζ hT hv2
  obtain ⟨y, hy, rfl⟩ := hx
  have hyrm := c.morseNorm_lt_rmp_of_sq_lt hy
  rw [c.chart_p_symm_eq' hy]
  unfold Lσ Gσ
  rcases le_or_gt c.c₁ (f (c.e.χ y)) with hc | hc
  · obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero (D := c.D) c.hkp hyrm
      (t := f (c.e.χ y) - c.c₁) (by linarith)
    rw [hHσ, hl]
    have hy' : morseNorm n y ^ 2 < 3 * c.ε := hy
    have hly : morseNorm n (l • y) ^ 2 < 3 * c.ε := by
      rw [ModelField.morseNorm_smul, abs_of_pos hl0, mul_pow]
      have hl2 : l ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hl2 (sq_nonneg (morseNorm n y))]
    rw [c.chart_p_symm_eq' hly, Bm_smul c.e₁ hl0]
  · obtain ⟨z, hz, hzx⟩ := hH
    have hzrm := c.morseNorm_lt_rmp_of_sq_lt hz
    rw [← hzx, c.chart_p_symm_eq' hz]
    have hxz : c.e.χ y = c.D.flow (c.c₁ - f (c.e.χ y)) (c.e.χ z) := by
      rw [hzx, hHσ, flow_flow]
      rw [show f (c.e.χ y) - c.c₁ + (c.c₁ - f (c.e.χ y)) = 0 by ring, c.D.flow_zero]
    obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero (D := c.D) c.hkp hzrm
      (t := c.c₁ - f (c.e.χ y)) (by linarith)
    rw [hl] at hxz
    have hz' : morseNorm n z ^ 2 < 3 * c.ε := hz
    have hlz : morseNorm n (l • z) ^ 2 < 3 * c.ε := by
      rw [ModelField.morseNorm_smul, abs_of_pos hl0, mul_pow]
      have hl2 : l ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hl2 (sq_nonneg (morseNorm n z))]
    have hyz : y = l • z := by
      have := congrArg c.e.χ.symm hxz
      rwa [c.chart_p_symm_eq' hy, c.chart_p_symm_eq' hlz] at this
    rw [hyz, Bm_smul c.e₁ hl0]

/-! ### The support set of the tube piece below `lo₂` -/

/-- Every point of `Sσ` lies in the basin of `p`. -/
theorem Sσ_subset_basin (hk : k.Good) : k.Sσ ⊆ c.D.basin p c.hp := by
  intro x hx
  have hT := k.mem_TubeOpenσ_of_mem_Sσ hx
  have hζ : ‖c.ζ x‖ < hk.δ'' := (k.norm_ζ_le_of_mem_Sσ hx).trans_lt hk.hδ'δ''
  obtain ⟨hv2, hH⟩ := hk.hHσ' hζ
  have hHσ := c.Hσ_ζ hT hv2
  rw [← flow_mem_basin_iff (D := c.D) c.hkp (f x - c.c₁), ← hHσ]
  exact ⟨0, le_rfl, by rw [c.D.flow_zero]; exact c.pBall'_subset_pBall hH⟩

/-- **The support set of the tube piece below the level `lo₂` lies in the ball region `Wball`
of `p`.** -/
theorem Sσ_low_subset_Wball (hk : k.Good) : k.Sσ ∩ {x | f x ≤ c.lo₂} ⊆ c.Wball := by
  rintro x ⟨hx, hf⟩
  have hf' : f x ≤ c.lo₂ := hf
  have hbasin := hk.Sσ_subset_basin hx
  have hmem := mem_modelBall_of_mem_basin_index_zero c.hfs (D := c.D) c.hkp hbasin
    (by have := c.ρB_sq_eq; have := c.ρB_sq_lt; have := c.hrmp; have := c.hε; linarith)
  obtain ⟨y, hy, rfl⟩ := hmem
  have hy' : morseNorm n y < c.D.rm p c.hp := hy
  refine ⟨y, ?_, rfl⟩
  show morseNorm n y ≤ c.ρB
  have h1 := c.f_chart_p (hy'.le.trans (c.D.hrm p c.hp).2)
  have h2 := c.ρB_sq_eq
  have h3 : morseNorm n y ^ 2 ≤ c.ρB ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (ModelField.morseNorm_nonneg y) c.ρB_pos.le two_ne_zero).1 h3

/-- The points of `Sσ` at the level `lo₂` have radius exactly `ρB` in the chart of `p`. -/
theorem Sσ_lo₂_radius (hk : k.Good) {x : M} (hx : x ∈ k.Sσ) (hf : f x = c.lo₂) :
    x ∈ c.pBall' ∧ morseNorm n (c.e.χ.symm x) = c.ρB := by
  have hW : x ∈ c.Wball := hk.Sσ_low_subset_Wball ⟨hx, hf.le⟩
  refine ⟨c.Wball_subset_pBall' hW, ?_⟩
  obtain ⟨y, hy, rfl⟩ := hW
  have hy' : morseNorm n y ≤ c.ρB := hy
  rw [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB hy')]
  have h1 := c.f_chart_p (hy'.trans c.ρB_le_R)
  have h2 := c.ρB_sq_eq
  have h3 : morseNorm n y ^ 2 = c.ρB ^ 2 := by linarith
  exact (pow_left_inj₀ (ModelField.morseNorm_nonneg y) c.ρB_pos.le two_ne_zero).1 h3

end Good

end CancelConsts

end CancelData

end GradientLikeStrip

end

end PoincareHighDim
